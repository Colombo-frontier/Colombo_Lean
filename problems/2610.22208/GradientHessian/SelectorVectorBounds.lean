import GradientHessian.SelectorMassBounds

/-! The actual mass vector in ℓ¹, with operator bounds for its first three
Fréchet derivatives, independent of the number of outcomes or registers. -/

namespace GradientHessian.SelectorVectorBounds
open SelectorBernoulli SelectorPortBounds SelectorCoordinateBounds SelectorPortJets
  SelectorChainRule SelectorMassBounds
open Classical
open scoped BigOperators
noncomputable section

abbrev L1Vector (κ : Type*) := PiLp 1 (fun _ : κ => ℝ)

theorem l1_norm {κ : Type*} [Fintype κ] (a : L1Vector κ) : ‖a‖ = ∑ i, |a i| := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one, Real.norm_eq_abs]

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def massVector (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (x : F) : L1Vector (ι → Bool) :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι → Bool => ℝ)).symm
    (fun ω => mass (fun i => coordinatePort R v A i x) ω)

theorem massVector_contDiff (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) :
    ContDiff ℝ 3 (massVector R v A) := by
  exact (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι → Bool => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr (fun ω => mass_contDiff (coordinatePort R v A) (coordinatePort_contDiff R v A) ω))

theorem massVector_derivative_apply (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (x : F)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → F) (ω : ι → Bool) :
    (iteratedFDeriv ℝ n (massVector R v A) x w) ω =
      iteratedFDeriv ℝ n (fun y => mass (fun i => coordinatePort R v A i y) ω) x w := by
  have h := (PiLp.proj (𝕜 := ℝ) 1 (fun _ : ι → Bool => ℝ) ω).iteratedFDeriv_comp_left
    (x := x) (massVector_contDiff R v A).contDiffAt (by exact_mod_cast hn : (n : WithTop ℕ∞) ≤ 3)
  exact (congrArg (fun T => T w) h).symm

theorem massConstant_nonneg (n : ℕ) : 0 ≤ massConstant n := by
  unfold massConstant
  have hC := zero_le_one.trans portConstant_ge_one
  positivity

theorem massVector_derivative_bound {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A) (x : F)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (massVector R v A) x‖ ≤ massConstant n/R^n := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (div_nonneg (massConstant_nonneg n) (pow_nonneg hR.le _))
  intro w
  rw [l1_norm]
  simp_rw [massVector_derivative_apply R v A x hn]
  exact mass_derivative_sum_bound hR v hv A hA x hn w

theorem massVector_norm (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (x : F) :
    ‖massVector R v A x‖ = 1 := by
  rw [l1_norm]
  change (∑ ω, |mass (fun i => coordinatePort R v A i x) ω|) = 1
  simp_rw [abs_of_nonneg (mass_nonneg (coordinatePort_mem R v A x) _)]
  exact mass_sum _

end
end GradientHessian.SelectorVectorBounds
