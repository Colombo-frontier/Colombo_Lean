import FullJet.EpochDescent

open scoped BigOperators

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {p n B m H : ℕ}

/-- The next snapshot is taken at the actual endpoint of the preceding epoch. -/
noncomputable def multiEpochCenter (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    (e : ℕ) → (Fin e → Fin m → Fin B → Fin n) → E
  | 0, _ => 0
  | e + 1, samples => epochPathPoint hp f
      (multiEpochCenter hp f M r hr m e (Fin.init samples)) M r hr
      (samples (Fin.last e)) (Fin.last m)

noncomputable def multiEpochStart (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin H → Fin m → Fin B → Fin n) (e : Fin (H + 1)) : E :=
  multiEpochCenter hp f M r hr m e.val (samplePrefix (Nat.le_of_lt_succ e.isLt) samples)

noncomputable def multiEpochBoundaryCount (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin H → Fin m → Fin B → Fin n) : ℝ :=
  ∑ e : Fin H, epochBoundaryCount hp f (multiEpochStart hp f M r hr samples e.castSucc)
    M r hr (samples e)

noncomputable def multiEpochError (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin H → Fin m → Fin B → Fin n) (e : Fin H) (t : Fin m) : ℝ :=
  epochPathError hp f (multiEpochStart hp f M r hr samples e.castSucc) M r hr (samples e) t

noncomputable def multiEpochErrorSum (hp : 1 ≤ p) (f : Fin n → E → ℝ)
    (M r : ℝ) (hr : 0 ≤ r) (samples : Fin H → Fin m → Fin B → Fin n) : ℝ :=
  ∑ e : Fin H, ∑ t : Fin m, multiEpochError hp f M r hr samples e t

section Path
variable (hp : 1 ≤ p) (f : Fin n → E → ℝ) (M r : ℝ) (hr : 0 ≤ r)
  (samples : Fin H → Fin m → Fin B → Fin n)

theorem multiEpochStart_zero : multiEpochStart hp f M r hr samples 0 = 0 := rfl

theorem multiEpochStart_succ (e : Fin H) :
    multiEpochStart hp f M r hr samples e.succ =
      epochPathPoint hp f (multiEpochStart hp f M r hr samples e.castSucc) M r hr
        (samples e) (Fin.last m) := rfl

theorem multiEpochBoundaryCount_nonneg : 0 ≤ multiEpochBoundaryCount hp f M r hr samples :=
  Finset.sum_nonneg (fun e _ => epochBoundaryCount_nonneg hp f _ M r hr (samples e))

theorem multiEpochError_nonneg (e : Fin H) (t : Fin m) :
    0 ≤ multiEpochError hp f M r hr samples e t := epochPathError_nonneg hp f _ M r hr _ t

end Path

/-- The endpoint terms cancel across actual snapshot resets. The global gap
is used once, rather than incorrectly charged once per epoch. -/
theorem Admissible.multiEpoch_boundary_budget {f : Fin n → E → ℝ} {Δ L : ℝ}
    (hf : Admissible p n Δ L f) (hp : 1 ≤ p) (hL : 0 ≤ L) (hm : 0 < m)
    (M r : ℝ) (hr : 0 ≤ r) (hA : 0 ≤ M / ((p + 1).factorial : ℝ) - L)
    (samples : Fin H → Fin m → Fin B → Fin n) :
    (M / ((p + 1).factorial : ℝ) - L) * r ^ (p + 1) *
      multiEpochBoundaryCount hp f M r hr samples ≤
      Δ + r * multiEpochErrorSum hp f M r hr samples +
        (H : ℝ) * m * ((p : ℝ) * L * (m : ℝ) ^ (p - 1)) * r ^ (p + 1) := by
  let A := M / ((p + 1).factorial : ℝ) - L
  let D := (p : ℝ) * L * (m : ℝ) ^ (p - 1)
  let F := fun e : Fin (H + 1) => average f (multiEpochStart hp f M r hr samples e)
  let count := fun e : Fin H => epochBoundaryCount hp f
    (multiEpochStart hp f M r hr samples e.castSucc) M r hr (samples e)
  let error := fun e : Fin H => ∑ t : Fin m, multiEpochError hp f M r hr samples e t
  have hstep (e : Fin H) : F e.succ ≤ F e.castSucc - A * r ^ (p + 1) * count e +
      (r * error e + (m : ℝ) * D * r ^ (p + 1)) := by
    have hb := hf.epoch_boundary_budget hp hL hm
      (multiEpochStart hp f M r hr samples e.castSucc) M r hr hA (samples e)
    rw [← multiEpochStart_succ] at hb
    change A * r ^ (p + 1) * count e ≤ F e.castSucc - F e.succ +
      r * error e + (m : ℝ) * D * r ^ (p + 1) at hb
    linarith
  have hb := finite_descent_budget F (fun e => A * r ^ (p + 1) * count e)
    (fun e => r * error e + (m : ℝ) * D * r ^ (p + 1)) hstep
  have hgap : F 0 - F (Fin.last H) ≤ Δ := by
    simpa only [F, multiEpochStart_zero] using hf.gap (multiEpochStart hp f M r hr samples (Fin.last H))
  have heq : (∑ e : Fin H, (r * error e + (m : ℝ) * D * r ^ (p + 1))) =
      r * multiEpochErrorSum hp f M r hr samples + (H : ℝ) * m * D * r ^ (p + 1) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, multiEpochErrorSum, error]
    ring
  rw [heq, ← Finset.mul_sum] at hb
  change A * r ^ (p + 1) * multiEpochBoundaryCount hp f M r hr samples ≤ _ at hb
  change A * r ^ (p + 1) * multiEpochBoundaryCount hp f M r hr samples ≤
    Δ + r * multiEpochErrorSum hp f M r hr samples + (H : ℝ) * m * D * r ^ (p + 1)
  linarith

section Mean
variable [Nonempty (Fin n)]

/-- An epoch's future samples remain fresh even though its center depends
on all preceding epochs. This uses the actual finite seed distribution. -/
theorem multiEpochError_mean_le {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (M r : ℝ) (hr : 0 ≤ r) (e : Fin H) (t : Fin m) :
    uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
      multiEpochError (p := k + 2) (by omega) f M r hr samples e t) ≤
        epochNoiseBound (k + 2) L m r B := by
  let X := fun (past : Fin e.val → Fin m → Fin B → Fin n) (batch : Fin m → Fin B → Fin n) =>
    epochPathError (p := k + 2) (by omega) f (multiEpochCenter (p := k + 2) (by omega) f M r hr m e.val past)
      M r hr batch t
  change uniformMean (fun samples => X (samplePrefix (Nat.le_of_lt e.isLt) samples) (samples e)) ≤ _
  rw [uniformMean_prefix_next e.isLt]
  apply uniformMean_le_const
  intro past
  exact epochPathError_mean_le hf hB L hL hlip _ M r hr t

theorem multiEpochErrorSum_mean_le {f : Fin n → E → ℝ} {k : ℕ}
    (hf : ∀ i, ContDiff ℝ (k + 2) (f i)) (hB : 0 < B) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i a b, ‖iteratedFDeriv ℝ (k + 2) (f i) a -
      iteratedFDeriv ℝ (k + 2) (f i) b‖ ≤ L * ‖a - b‖)
    (M r : ℝ) (hr : 0 ≤ r) :
    uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
      multiEpochErrorSum (p := k + 2) (by omega) f M r hr samples) ≤
        (H : ℝ) * m * epochNoiseBound (k + 2) L m r B := by
  unfold multiEpochErrorSum
  simp only [uniformMean_sum]
  calc
    _ ≤ ∑ _e : Fin H, ∑ _t : Fin m, epochNoiseBound (k + 2) L m r B :=
      Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun t _ =>
        multiEpochError_mean_le hf hB L hL hlip M r hr e t))
    _ = _ := by simp; ring

theorem Admissible.multiEpoch_mean_boundary_budget {f : Fin n → E → ℝ} {Δ L : ℝ} {k : ℕ}
    (hf : Admissible (k + 2) n Δ L f) (hB : 0 < B) (hL : 0 ≤ L) (hm : 0 < m)
    (M r : ℝ) (hr : 0 ≤ r) (hA : 0 ≤ M / ((k + 2 + 1).factorial : ℝ) - L) :
    (M / ((k + 2 + 1).factorial : ℝ) - L) * r ^ (k + 2 + 1) *
      uniformMean (fun samples : Fin H → Fin m → Fin B → Fin n =>
        multiEpochBoundaryCount (p := k + 2) (by omega) f M r hr samples) ≤
      Δ + (H : ℝ) * m * (r * epochNoiseBound (k + 2) L m r B +
        ((k + 2 : ℕ) : ℝ) * L * (m : ℝ) ^ (k + 2 - 1) * r ^ (k + 2 + 1)) := by
  have hb := uniformMean_mono (fun samples : Fin H → Fin m → Fin B → Fin n =>
    hf.multiEpoch_boundary_budget (by omega) hL hm M r hr hA samples)
  simp only [uniformMean_add, uniformMean_mul, uniformMean_const] at hb
  have hn := multiEpochErrorSum_mean_le (H := H) (m := m) hf.smooth hB L hL hf.derivative_lipschitz M r hr
  have hn' := mul_le_mul_of_nonneg_left hn hr
  nlinarith

end Mean

end FullJet
