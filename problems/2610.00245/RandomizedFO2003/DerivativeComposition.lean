import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace RandomizedFO2003.Cascade.Calculus

open scoped BigOperators

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_comp_linear_le (A : E →L[ℝ] F) (n : ℕ)
    {f : F → G} (hf : ContDiff ℝ n f) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ n f (A x)‖ * ‖A‖ ^ n := by
  rw [A.iteratedFDeriv_comp_right hf x le_rfl]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (A x)).norm_compContinuousLinearMap_le (fun _ : Fin n => A)

theorem norm_iteratedFDeriv_linear_comp_le (A : F →L[ℝ] G) (n : ℕ)
    {f : E → F} (hf : ContDiff ℝ n f) (x : E) :
    ‖iteratedFDeriv ℝ n (A ∘ f) x‖ ≤ ‖A‖ * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [A.iteratedFDeriv_comp_left hf.contDiffAt le_rfl]
  exact A.norm_compContinuousMultilinearMap_le _

theorem norm_iteratedFDeriv_comp_contraction_le (A : E →L[ℝ] F) (hA : ‖A‖ ≤ 1) (n : ℕ)
    {f : F → G} (hf : ContDiff ℝ n f) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ n f (A x)‖ := by
  apply (norm_iteratedFDeriv_comp_linear_le A n hf x).trans
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg A) hA)

theorem iteratedFDeriv_const_add (n : ℕ) (hn : 1 ≤ n) (c : F)
    {f : E → F} (hf : ContDiff ℝ n f) (x : E) :
    iteratedFDeriv ℝ n (fun y => c + f y) x = iteratedFDeriv ℝ n f x := by
  rw [iteratedFDeriv_add_apply' contDiffAt_const hf.contDiffAt,
    iteratedFDeriv_const_of_ne (by omega : n ≠ 0), Pi.zero_apply, zero_add]

end RandomizedFO2003.Cascade.Calculus
