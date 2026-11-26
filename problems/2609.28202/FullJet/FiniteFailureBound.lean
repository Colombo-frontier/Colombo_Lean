import FullJet.UniformPrefixMean

open scoped BigOperators

namespace FullJet

/-- An event's actual finite probability is the expectation of its indicator. -/
theorem pmf_event_eq_mean_indicator {α : Type*} [Fintype α] (p : PMF α) (A : Set α)
    [DecidablePred (· ∈ A)] :
    (p.toOuterMeasure A).toReal = pmfMean p (fun a => if a ∈ A then (1 : ℝ) else 0) := by
  classical
  rw [pmf_event_toReal, pmfMean_real]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ A <;> simp [ha]

/-- A failed interior candidate must spend at least half the gradient tolerance
in estimation error. Boundary candidates are counted separately. -/
theorem failure_indicator_le_boundary_error (ε g s r C ζ : ℝ) (hε : 0 < ε) (hζ : 0 ≤ ζ)
    (hs : s ≤ r) (hC : C ≤ ε / 2) (hinterior : s < r → g ≤ C + ζ) :
    (if ε < g then (1 : ℝ) else 0) ≤ (if s = r then 1 else 0) + (2 / ε) * ζ := by
  classical
  by_cases hg : ε < g
  · simp only [if_pos hg]
    by_cases hb : s = r
    · simp only [if_pos hb]
      have hnon : 0 ≤ (2 / ε) * ζ := by positivity
      linarith
    · simp only [if_neg hb, zero_add]
      have hζ' : ε / 2 ≤ ζ := by
        have hi := hinterior (lt_of_le_of_ne hs hb)
        linarith
      calc
        1 = (2 / ε) * (ε / 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hζ' (by positivity)
  · simp only [if_neg hg]
    have hb : 0 ≤ (if s = r then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    positivity

theorem uniformMean_fin_pair {H m : ℕ} [Nonempty (Fin H)] [Nonempty (Fin m)]
    (X : Fin H → Fin m → ℝ) :
    uniformMean (fun index : Fin H × Fin m => X index.1 index.2) =
      (∑ e : Fin H, ∑ t : Fin m, X e t) / ((H : ℝ) * m) := by
  rw [uniformMean_eq]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Fintype.sum_prod_type, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

end FullJet
