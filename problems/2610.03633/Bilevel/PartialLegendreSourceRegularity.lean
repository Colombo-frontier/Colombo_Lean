import Bilevel.PartialLegendreJointHessian

/-! Adapter from the paper's Hessian norm and Hessian variation assumptions
to the globally constructed actual partial conjugate. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G : Joint X Y → Joint X Y}

omit [CompleteSpace X] [CompleteSpace Y] in
theorem fullGradient_lipschitz_of_hessian
    (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hDG : ∀ z,HasFDerivAt G (B z) z) (hB : ∀ z,‖B z‖≤(δ:ℝ)) :
    LipschitzWith δ G := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hDG z).differentiableAt)
  intro z
  rw [(hDG z).fderiv]
  exact_mod_cast hB z

/-- In the paper's delta≤1/4 regime the actual Hessian assumptions construct
the inverse and conjugate, and imply its complete joint C2,1 estimates. -/
theorem source_jointConjugate_regular
    (P : Joint X Y → ℝ) (hP : ∀ z,HasGradientAt P (G z) z)
    (hquarter : (δ:ℝ)≤1/4)
    (B : Joint X Y → Joint X Y →L[ℝ] Joint X Y)
    (hDG : ∀ z,HasFDerivAt G (B z) z) (hB : ∀ z,‖B z‖≤(δ:ℝ))
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ∃ (hG : LipschitzWith δ G) (hδ : δ<1)
      (K : Joint X Y → Joint X Y →L[ℝ] Joint X Y),
      ContDiff ℝ 2 (jointConjugate hG hδ P) ∧
      (∀ q,HasGradientAt (jointConjugate hG hδ P) (jointGradient hG hδ q) q) ∧
      (∀ q,HasFDerivAt (gradient (jointConjugate hG hδ P)) (K q) q) ∧
      (∀ q,‖K q-lowerProjection‖≤2*(δ:ℝ) ∧ ‖K q‖≤2) ∧
      (∀ q r,‖K q-K r‖≤3*H*‖q-r‖) := by
  have hδ : δ<1 := by exact_mod_cast (show (δ:ℝ)<1 by linarith)
  have hG := fullGradient_lipschitz_of_hessian B hDG hB
  obtain ⟨K,hC,hD,hN,hV⟩ :=
    jointConjugate_quarter_hessian_control hδ hG P hP hquarter B hDG hH hLip
  exact ⟨hG,hδ,K,hC,jointConjugate_hasGradientAt hG hδ P hP,hD,hN,hV⟩

end Bilevel.PartialLegendre
