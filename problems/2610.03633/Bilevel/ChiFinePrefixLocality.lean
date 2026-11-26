import Bilevel.ChiFineInactiveLocality
import Bilevel.ChiFineCouplingCore

/-! Actual incoming-profile support of the revised fine frontier. A small
latent source coordinate kills every selector derivative, leaving exactly
the displayed incoming derivative. No support premise is assumed. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain

theorem selected_gradient_coordinate {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Space n) (j : Fin (n+1)) (hj : |z j|≤1/4) :
    gradient (selected n f) z j=selector n j z*deriv f (z j) := by
  have hi (i : Fin (n+1)) := (selector_hasFDerivAt n i z).mul
    (((hf.differentiable (by norm_num) (z i)).hasDerivAt.hasFDerivAt).comp z
      (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt)
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun i _ => hi i)
  change HasFDerivAt (selected n f) _ z at hs
  have hzero (i : Fin (n+1)) : selectorDerivative n i z (ZeroChain.basis j)=0 :=
    selectorDerivative_basis_small i j z hj
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hs]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    hzero,smul_zero,add_zero]
  simp [ZeroChain.basis,EuclideanSpace.single_apply]

theorem selected_gradient_support {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (r : ℕ) (z : Space n) (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (selected n f) z j=0 := by
  rw [selected_gradient_coordinate hf z j (hz j (by omega))]
  have hsel : selector n j z=0 := by
    revert hj
    refine Fin.cases (by simp) (fun k hk => ?_) j
    have hsmall := hz k.castSucc (by change r≤k.val;simp only [Fin.val_succ] at hk;omega)
    simp only [selector,Fin.cases_succ,evenGate_zero (show |z k.castSucc|≤1/2 by linarith),zero_mul]
  rw [hsel,zero_mul]

theorem flattened_gradient_small {n : ℕ} (δ : ℝ) (hδ : 0<δ) (hs : δ≤1/16)
    (z : Space n) (j : Fin (n+1)) (hj : |z j|≤δ) : gradient (flattened n δ) z j=0 := by
  have hh := inactive_gradient_coordinate_zero n 1 1 δ (by norm_num) hδ hs z j hj
  have he : flatFrontier n 1 1 δ=flattened n δ := by funext x;simp [flatFrontier,ZeroChainResidualScaled.scaled]
  rwa [he] at hh

theorem approximation_gradient_support (n J : ℕ) (δ : ℕ → ℝ) (k r : ℕ)
    (z : Space n) (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (approximation n J δ k) z j=0 := by
  by_cases hk : k<J
  · rw [show approximation n J δ k=flattened n (δ k) by funext x;simp [approximation,hk]]
    exact selected_gradient_support (flatProfile_contDiff (δ k)) r z hz j hj
  · rw [show approximation n J δ k=centeredResidual n by funext x;simp [approximation,hk]]
    exact centeredResidual_gradient_support r z hz j hj

theorem piece_gradient_support (n J : ℕ) (δ : ℕ → ℝ) (k r : ℕ)
    (z : Space n) (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (piece n J δ k) z j=0 := by
  cases k with
  | zero => exact approximation_gradient_support n J δ 0 r z hz j hj
  | succ k =>
    have hleft := ((approximation_contDiff n J δ (k+1)).differentiable (by norm_num) z).hasGradientAt.hasFDerivAt
    have hright := ((approximation_contDiff n J δ k).differentiable (by norm_num) z).hasGradientAt.hasFDerivAt
    have hgrad : HasGradientAt (piece n J δ (k+1))
        (gradient (approximation n J δ (k+1)) z-gradient (approximation n J δ k) z) z := by
      apply hasGradientAt_iff_hasFDerivAt.mpr
      simpa only [map_sub] using hleft.sub hright
    rw [hgrad.gradient,PiLp.sub_apply,approximation_gradient_support n J δ (k+1) r z hz j hj,
      approximation_gradient_support n J δ k r z hz j hj,sub_self]

end Bilevel.ChiFine
