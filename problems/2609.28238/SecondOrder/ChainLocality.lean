import SecondOrder.LocalSmoothness

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

def chainSupport {T : ℕ} (i : Fin T) : Finset (Fin (T+1)) := {i.castSucc, i.succ}

/-- An open chain has at most two local edge terms at any coordinate block. -/
theorem chainSupport_overlap (T : ℕ) (j : Fin (T+1)) :
    (Finset.univ.filter (fun i : Fin T => j ∈ chainSupport i)).card ≤ 2 := by
  let s := Finset.univ.filter (fun i : Fin T => j ∈ chainSupport i)
  have hsub : s.image Fin.val ⊆ {j.val, j.val-1} := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    have hm : j = i.castSucc ∨ j = i.succ := by simpa [s, chainSupport] using hi
    rcases hm with h | h
    · simp [h]
    · simp [h]
  calc
    s.card = (s.image Fin.val).card := (Finset.card_image_of_injective s Fin.val_injective).symm
    _ ≤ ({j.val, j.val-1} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- Unary regularizers and neighboring links are a single local-term family. -/
def regularizedChainSupport {T : ℕ} : Sum (Fin (T+1)) (Fin T) → Finset (Fin (T+1))
  | .inl j => {j}
  | .inr i => chainSupport i

theorem regularizedChainSupport_overlap (T : ℕ) (j : Fin (T+1)) :
    (Finset.univ.filter (fun i : Sum (Fin (T+1)) (Fin T) => j ∈ regularizedChainSupport i)).card ≤ 3 := by
  have he : (Finset.univ.filter (fun i : Sum (Fin (T+1)) (Fin T) =>
      j ∈ regularizedChainSupport i)).card =
        1+(Finset.univ.filter (fun i : Fin T => j ∈ chainSupport i)).card := by
    simp only [Finset.card_filter, Fintype.sum_sum_type, regularizedChainSupport,
      Finset.mem_singleton, Finset.sum_ite_eq]
    simp
  rw [he]
  have h := chainSupport_overlap T j
  omega

variable {T : ℕ} (E : Fin (T+1) → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chainObjective_second_bound
    (φ : ∀ i : Fin T, LocalBlockSpace E (chainSupport i) → F)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M) (x : BlockSpace E) :
    ‖iteratedFDeriv ℝ 2 (localObjective E chainSupport φ) x‖ ≤ 2*M := by
  simpa using localObjective_second_bound E chainSupport 2 (by intro j; convert chainSupport_overlap T j using 1; congr 1; ext i; simp) φ hφ hM hbound x

theorem chainObjective_third_bound
    (φ : ∀ i : Fin T, LocalBlockSpace E (chainSupport i) → F)
    (hφ : ∀ i, ContDiff ℝ 3 (φ i)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i y, ‖iteratedFDeriv ℝ 3 (φ i) y‖ ≤ M) (x : BlockSpace E) :
    ‖iteratedFDeriv ℝ 3 (localObjective E chainSupport φ) x‖ ≤ 2*M := by
  simpa using localObjective_third_bound E chainSupport 2 (by intro j; convert chainSupport_overlap T j using 1; congr 1; ext i; simp) φ hφ hM hbound x

theorem regularizedChainObjective_second_bound
    (φ : ∀ i : Sum (Fin (T+1)) (Fin T), LocalBlockSpace E (regularizedChainSupport i) → F)
    (hφ : ∀ i, ContDiff ℝ 2 (φ i)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M) (x : BlockSpace E) :
    ‖iteratedFDeriv ℝ 2 (localObjective E regularizedChainSupport φ) x‖ ≤ 3*M := by
  simpa using localObjective_second_bound E regularizedChainSupport 3
    (by intro j; convert regularizedChainSupport_overlap T j using 1; congr 1; ext i; simp) φ hφ hM hbound x

theorem regularizedChainObjective_third_bound
    (φ : ∀ i : Sum (Fin (T+1)) (Fin T), LocalBlockSpace E (regularizedChainSupport i) → F)
    (hφ : ∀ i, ContDiff ℝ 3 (φ i)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i y, ‖iteratedFDeriv ℝ 3 (φ i) y‖ ≤ M) (x : BlockSpace E) :
    ‖iteratedFDeriv ℝ 3 (localObjective E regularizedChainSupport φ) x‖ ≤ 3*M := by
  simpa using localObjective_third_bound E regularizedChainSupport 3
    (by intro j; convert regularizedChainSupport_overlap T j using 1; congr 1; ext i; simp) φ hφ hM hbound x

end
end SecondOrder
