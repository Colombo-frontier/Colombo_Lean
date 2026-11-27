import Nonsmooth.SoftplusVectorDerivatives
import Nonsmooth.FirstOrder

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def realInnerBilinear : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

def softVectorPotential (ρ : ℝ) (f : ι → E → ℝ) (x : E) : ℝ :=
  ρ / 2 * ‖x‖ ^ 2 + ∑ i, softplus (f i x)

def softVectorScore (ρ : ℝ) (f : ι → E → ℝ) (s : ι → E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℝ :=
  ρ • realInnerBilinear x + ∑ i, softplusSlope (f i x) • s i x

def softVectorHessian (ρ : ℝ) (f : ι → E → ℝ) (s : ι → E → E →L[ℝ] ℝ)
    (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ρ • realInnerBilinear + ∑ i,
    (softplusSlope (f i x) • H i x + softplusCurvature (f i x) • (s i x).smulRight (s i x))

theorem softVectorPotential_contDiff (ρ : ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (softVectorPotential ρ f) := by
  apply (contDiff_const.mul (contDiff_norm_sq ℝ)).add
  apply ContDiff.sum
  intro i _
  exact (softplus_contDiff.of_le (by simp)).comp (hf i)

theorem softVectorPotential_hasFDerivAt (ρ : ℝ) (f : ι → E → ℝ)
    (s : ι → E → E →L[ℝ] ℝ) (hd : ∀ i x, HasFDerivAt (f i) (s i x) x) (x : E) :
    HasFDerivAt (softVectorPotential ρ f) (softVectorScore ρ f s x) x := by
  have hbase : HasFDerivAt (fun x : E => ρ / 2 * ‖x‖ ^ 2) (ρ • innerSL ℝ x) x := by
    convert! (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (ρ / 2) using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hsum : HasFDerivAt (fun z => ∑ i, softplus (f i z))
      (∑ i, softplusSlope (f i x) • s i x) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => softplus_composition_hasFDerivAt (f i) (s i x) x (hd i x))
  convert! hbase.fun_add hsum using 1 <;> rfl

theorem softVectorScore_hasFDerivAt (ρ : ℝ) (f : ι → E → ℝ)
    (s : ι → E → E →L[ℝ] ℝ) (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ i x, HasFDerivAt (f i) (s i x) x)
    (hds : ∀ i x, HasFDerivAt (s i) (H i x) x) (x : E) :
    HasFDerivAt (softVectorScore ρ f s) (softVectorHessian ρ f s H x) x := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hsum : HasFDerivAt (fun z => ∑ i, softplusSlope (f i z) • s i z)
      (∑ i, (softplusSlope (f i x) • H i x + softplusCurvature (f i x) • (s i x).smulRight (s i x))) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => softplus_vector_score_hasFDerivAt (f i) (s i) (H i x) x (hd i x) (hds i x))
  convert! (B.hasFDerivAt.const_smul ρ).fun_add hsum using 1 <;> rfl

theorem softVectorPotential_fderiv_fderiv (ρ : ℝ) (f : ι → E → ℝ)
    (s : ι → E → E →L[ℝ] ℝ) (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ i x, HasFDerivAt (f i) (s i x) x)
    (hds : ∀ i x, HasFDerivAt (s i) (H i x) x) (x : E) :
    fderiv ℝ (fderiv ℝ (softVectorPotential ρ f)) x = softVectorHessian ρ f s H x := by
  have he : fderiv ℝ (softVectorPotential ρ f) = softVectorScore ρ f s := by
    funext z
    exact (softVectorPotential_hasFDerivAt ρ f s hd z).fderiv
  rw [he]
  exact (softVectorScore_hasFDerivAt ρ f s H hd hds x).fderiv

end
end Nonsmooth
