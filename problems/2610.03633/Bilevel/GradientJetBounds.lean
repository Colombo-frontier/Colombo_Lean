import Bilevel.HessianLowerBound
import Bilevel.CompensatedMeanJets

/-! Riesz identification preserves the operator norms needed to turn actual
scalar second/third jets into gradient and Hessian bounds. -/

noncomputable section
namespace Bilevel.GradientJetBounds
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_contDiff {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by norm_num))

theorem gradient_jet_norm {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E)
    (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (gradient f) x‖ = ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  let L := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  change ‖iteratedFDeriv ℝ k (L ∘ fderiv ℝ f) x‖ = _
  rw [L.iteratedFDeriv_comp_left hd.contDiffAt (show (k:WithTop ℕ∞) ≤ 2 by exact_mod_cast hk)]
  change ‖(InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap
    (iteratedFDeriv ℝ k (fderiv ℝ f) x)‖ = _
  rw [LinearIsometry.norm_compContinuousMultilinearMap,norm_iteratedFDeriv_fderiv]

theorem gradient_norm_eq {f : E → ℝ} (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map _

theorem hessian_norm_eq {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  have h := gradient_jet_norm hf x 1 (by norm_num)
  rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero] at h
  exact h

theorem third_norm_eq {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ = ‖iteratedFDeriv ℝ 3 f x‖ := by
  have h := gradient_jet_norm hf x 2 (by norm_num)
  rw [← norm_iteratedFDeriv_fderiv (n:=1),← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero] at h
  exact h

theorem gradient_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f) (L : ℝ)
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ L) (x y : E) :
    ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => ((gradient_contDiff hf).differentiable (by norm_num) v).hasFDerivAt.hasFDerivWithinAt)
    (fun v _ => (hessian_norm_eq hf v).le.trans (hb v)) (Set.mem_univ y) (Set.mem_univ x)

theorem hessian_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f) (ρ : ℝ)
    (hb : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ ρ) (x y : E) :
    ‖fderiv ℝ (gradient f) x-fderiv ℝ (gradient f) y‖ ≤ ρ*‖x-y‖ := by
  have hd : ContDiff ℝ 1 (fderiv ℝ (gradient f)) := (gradient_contDiff hf).fderiv_right (by norm_num)
  apply convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => (hd.differentiable (by norm_num) v).hasFDerivAt.hasFDerivWithinAt)
    (fun v _ => (third_norm_eq hf v).le.trans (hb v)) (Set.mem_univ y) (Set.mem_univ x)

end Bilevel.GradientJetBounds
