import FreshGradientMinimax.JointGradient
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual partial gradients of a jointly C1 scalar function are continuous.
The product is used only as a coordinate pair, with the existing Euclidean blocks. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def actualJointGradient {dx dy : ℕ} (f : Euclid dx → Euclid dy → ℝ) (z : Joint dx dy) : Joint dx dy :=
  (gradient (fun x => f x z.2) z.1, gradient (f z.1) z.2)

theorem partialGradient_fst_eq {dx dy : ℕ} {f : Euclid dx → Euclid dy → ℝ} (z : Joint dx dy)
    (hf : DifferentiableAt ℝ (fun w : Joint dx dy => f w.1 w.2) z) :
    gradient (fun x => f x z.2) z.1 = (InnerProductSpace.toDual ℝ (Euclid dx)).symm
      ((fderiv ℝ (fun w : Joint dx dy => f w.1 w.2) z).comp ((ContinuousLinearMap.id ℝ (Euclid dx)).prod 0)) := by
  have hd : HasFDerivAt (fun w : Joint dx dy => f w.1 w.2)
      (fderiv ℝ (fun w : Joint dx dy => f w.1 w.2) z) (z.1, z.2) := hf.hasFDerivAt
  have hx := hd.comp z.1 ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk (hasFDerivAt_const z.2 z.1))
  exact hx.hasGradientAt.gradient

theorem partialGradient_snd_eq {dx dy : ℕ} {f : Euclid dx → Euclid dy → ℝ} (z : Joint dx dy)
    (hf : DifferentiableAt ℝ (fun w : Joint dx dy => f w.1 w.2) z) :
    gradient (f z.1) z.2 = (InnerProductSpace.toDual ℝ (Euclid dy)).symm
      ((fderiv ℝ (fun w : Joint dx dy => f w.1 w.2) z).comp
        ((0 : Euclid dy →L[ℝ] Euclid dx).prod (ContinuousLinearMap.id ℝ (Euclid dy)))) := by
  have hd : HasFDerivAt (fun w : Joint dx dy => f w.1 w.2)
      (fderiv ℝ (fun w : Joint dx dy => f w.1 w.2) z) (z.1, z.2) := hf.hasFDerivAt
  have hy := hd.comp z.2 ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2))
  exact hy.hasGradientAt.gradient

theorem actualJointGradient_continuous {dx dy : ℕ} {f : Euclid dx → Euclid dy → ℝ}
    (hf : ContDiff ℝ 1 (fun z : Joint dx dy => f z.1 z.2)) : Continuous (actualJointGradient f) := by
  have hc := hf.continuous_fderiv (by norm_num : 1 ≤ (1 : WithTop ℕ∞))
  have hx : Continuous (fun z : Joint dx dy => (InnerProductSpace.toDual ℝ (Euclid dx)).symm
      ((fderiv ℝ (fun w : Joint dx dy => f w.1 w.2) z).comp ((ContinuousLinearMap.id ℝ (Euclid dx)).prod 0))) :=
    (InnerProductSpace.toDual ℝ (Euclid dx)).symm.continuous.comp (hc.clm_comp continuous_const)
  have hy : Continuous (fun z : Joint dx dy => (InnerProductSpace.toDual ℝ (Euclid dy)).symm
      ((fderiv ℝ (fun w : Joint dx dy => f w.1 w.2) z).comp
        ((0 : Euclid dy →L[ℝ] Euclid dx).prod (ContinuousLinearMap.id ℝ (Euclid dy))))) :=
    (InnerProductSpace.toDual ℝ (Euclid dy)).symm.continuous.comp (hc.clm_comp continuous_const)
  convert hx.prodMk hy using 1
  funext z
  apply Prod.ext
  · exact partialGradient_fst_eq z (hf.differentiable (by norm_num) z)
  · exact partialGradient_snd_eq z (hf.differentiable (by norm_num) z)

theorem actualJointGradient_objective {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ) :
    actualJointGradient O.f = O.jointGradient := by
  funext z
  apply Prod.ext
  · exact (hasGradientAt_iff_hasFDerivAt.mpr (O.derivative_x z.1 z.2)).gradient
  · exact (hasGradientAt_iff_hasFDerivAt.mpr (O.derivative_y z.1 z.2)).gradient

end FreshGradientMinimax
