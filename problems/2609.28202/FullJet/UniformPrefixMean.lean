import FullJet.FiniteMean

open scoped BigOperators

namespace FullJet

/-- The actual initial segment of a pre-sampled finite seed sequence. -/
def samplePrefix {α : Type*} {t m : ℕ} (h : t ≤ m) (samples : Fin m → α) : Fin t → α :=
  fun i => samples (i.castLE h)

@[simp] theorem samplePrefix_refl {α : Type*} {t : ℕ} (samples : Fin t → α) :
    samplePrefix le_rfl samples = samples := rfl

theorem samplePrefix_trans {α : Type*} {s t m : ℕ} (hst : s ≤ t) (htm : t ≤ m)
    (samples : Fin m → α) :
    samplePrefix hst (samplePrefix htm samples) = samplePrefix (hst.trans htm) samples := rfl

theorem samplePrefix_snoc {α : Type*} {t m : ℕ} (h : t ≤ m) (past : Fin m → α) (a : α) :
    samplePrefix (h.trans (Nat.le_succ m)) (Fin.snoc past a) = samplePrefix h past := by
  funext i
  change Fin.snoc (α := fun _ : Fin (m + 1) => α) past a (i.castLE h).castSucc = past (i.castLE h)
  simp only [Fin.snoc_castSucc]

theorem samplePrefix_init {α : Type*} {t m : ℕ} (h : t + 1 ≤ m) (samples : Fin m → α) :
    Fin.init (samplePrefix h samples) = samplePrefix (Nat.le_of_succ_le h) samples := rfl

theorem samplePrefix_last {α : Type*} {t m : ℕ} (h : t + 1 ≤ m) (samples : Fin m → α) :
    samplePrefix h samples (Fin.last t) = samples ⟨t, by omega⟩ := rfl

theorem samplePrefix_succ {α : Type*} {t m : ℕ} (h : t + 1 ≤ m) (samples : Fin m → α) :
    samplePrefix h samples = Fin.snoc (samplePrefix (Nat.le_of_succ_le h) samples)
      (samples ⟨t, by omega⟩) := by
  rw [← samplePrefix_init h samples, ← samplePrefix_last h samples]
  exact (Fin.snoc_init_self _).symm

section Mean
variable {α β E : Type*} [Fintype α] [Nonempty α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reading the first t labels from an actual uniform m-label seed preserves
the uniform law, including the empty prefix. -/
theorem uniformMean_samplePrefix {t m : ℕ} (h : t ≤ m) (X : (Fin t → α) → E) :
    uniformMean (fun samples : Fin m → α => X (samplePrefix h samples)) = uniformMean X := by
  induction m generalizing t with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    simp only [samplePrefix_refl]
  | succ m ih =>
    by_cases htm : t ≤ m
    · rw [uniformMean_snoc]
      simp only [samplePrefix_snoc htm, uniformMean_const]
      exact ih htm X
    · have ht : t = m + 1 := by omega
      subst t
      simp only [samplePrefix_refl]

/-- The first t labels and label t have the true product law even when a longer
sequence was sampled in advance. -/
theorem uniformMean_prefix_next {t m : ℕ} (h : t < m) (X : (Fin t → α) → α → E) :
    uniformMean (fun samples : Fin m → α =>
      X (samplePrefix (Nat.le_of_lt h) samples) (samples ⟨t, h⟩)) =
        uniformMean (fun past : Fin t → α => uniformMean (fun a => X past a)) := by
  have he := uniformMean_samplePrefix (Nat.succ_le_of_lt h)
    (fun samples : Fin (t + 1) → α => X (Fin.init samples) (samples (Fin.last t)))
  simp only [samplePrefix_init, samplePrefix_last] at he
  rw [he, uniformMean_snoc]
  simp only [Fin.init_snoc, Fin.snoc_last]

theorem uniformMean_sum {ι : Type*} [Fintype ι] (X : α → ι → E) :
    uniformMean (fun a => ∑ i, X a i) = ∑ i, uniformMean (fun a => X a i) := by
  unfold uniformMean pmfMean
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]

theorem uniformMean_comm [Fintype β] [Nonempty β] (X : α → β → E) :
    uniformMean (fun a => uniformMean (fun b => X a b)) =
      uniformMean (fun b => uniformMean (fun a => X a b)) := by
  unfold uniformMean pmfMean
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact smul_comm _ _ _

end Mean

end FullJet
