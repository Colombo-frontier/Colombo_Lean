import SecondOrder.LocalSmoothness
import SecondOrder.Interpolation
import SecondOrder.Model

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem norm_iteratedFDeriv_gradient (f : E → ℝ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (gradient f) x‖ = ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  change ‖iteratedFDeriv ℝ k ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f) x‖ = _
  rw [(InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left,
    norm_iteratedFDeriv_fderiv]

theorem norm_fderiv_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_first_iteratedFDeriv, norm_iteratedFDeriv_gradient]

theorem gradient_lipschitz_of_second_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) (x y : E) :
    ‖gradient f y-gradient f x‖ ≤ M*‖y-x‖ := by
  simpa only [gradient, ← map_sub, LinearIsometryEquiv.norm_map] using
    fderiv_lipschitz_of_second_bound hf hM x y

theorem fderiv_gradient_lipschitz_of_third_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ M) (x y : E) :
    ‖fderiv ℝ (gradient f) y-fderiv ℝ (gradient f) x‖ ≤ M*‖y-x‖ := by
  have hg : ContDiff ℝ 2 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  apply fderiv_lipschitz_of_second_bound hg (fun z => ?_) x y
  rw [norm_iteratedFDeriv_gradient]
  exact hM z

end Hilbert

variable {J I : Type*} [Fintype J] [Fintype I] (E : J → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
  [∀ j, CompleteSpace (E j)]

instance blockSpace_complete : CompleteSpace (BlockSpace E) := Pi.complete E

variable (S : I → Finset J) (r : ℕ)
  (hr : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ r)

include hr

theorem localObjective_gradient_lipschitz
    (φ : ∀ i, LocalBlockSpace E (S i) → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M)
    (x y : BlockSpace E) :
    ‖gradient (localObjective E S φ) y-gradient (localObjective E S φ) x‖ ≤ (r:ℝ)*M*‖y-x‖ :=
  gradient_lipschitz_of_second_bound (localObjective_contDiff E S φ hφ)
    (localObjective_second_bound E S r hr φ hφ hM hbound) x y

theorem localObjective_hessian_bound
    (φ : ∀ i, LocalBlockSpace E (S i) → ℝ) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M)
    (x : BlockSpace E) :
    ‖fderiv ℝ (gradient (localObjective E S φ)) x‖ ≤ (r:ℝ)*M := by
  rw [norm_fderiv_gradient]
  exact localObjective_second_bound E S r hr φ hφ hM hbound x

theorem localObjective_hessian_lipschitz
    (φ : ∀ i, LocalBlockSpace E (S i) → ℝ) (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 3 (φ i) y‖ ≤ M)
    (x y : BlockSpace E) :
    ‖fderiv ℝ (gradient (localObjective E S φ)) y-
      fderiv ℝ (gradient (localObjective E S φ)) x‖ ≤ (r:ℝ)*M*‖y-x‖ :=
  fderiv_gradient_lipschitz_of_third_bound (localObjective_contDiff E S φ hφ)
    (localObjective_third_bound E S r hr φ hφ hM hbound) x y

/-- Local second and third derivative bounds give the manuscript's Hessian Hölder
constant with no dependence on the number of terms. -/
theorem localObjective_hessian_holder
    (φ : ∀ i, LocalBlockSpace E (S i) → ℝ) (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {M K ν : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hsecond : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M)
    (hthird : ∀ i y, ‖iteratedFDeriv ℝ 3 (φ i) y‖ ≤ K) (x y : BlockSpace E) :
    ‖fderiv ℝ (gradient (localObjective E S φ)) x-
      fderiv ℝ (gradient (localObjective E S φ)) y‖ ≤
      (2*((r:ℝ)*M))^(1-ν)*((r:ℝ)*K)^ν*‖x-y‖^ν := by
  exact holder_of_bounded_lipschitz (fderiv ℝ (gradient (localObjective E S φ))) (mul_nonneg (Nat.cast_nonneg r) hM)
    (mul_nonneg (Nat.cast_nonneg r) hK) hν0 hν1
    (localObjective_hessian_bound E S r hr φ (fun i => (hφ i).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)) hM hsecond)
    (fun x y => localObjective_hessian_lipschitz E S r hr φ hφ hK hthird y x) x y

end
end SecondOrder
