import Bilevel.PartialLegendreEnvelope
import Bilevel.PartialLegendreDerivative

/-! The partial inverse as one full near-identity inverse on the Euclidean
product. This yields the joint derivative, including all macro directions. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

def lowerProjection : Joint X Y →L[ℝ] Joint X Y :=
  (packLinear (X := X) (Y := Y)).comp
    ((0 : Joint X Y →L[ℝ] X).prod
      ((ContinuousLinearMap.snd ℝ X Y).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).toContinuousLinearMap))

theorem lowerProjection_apply (q : Joint X Y) : lowerProjection q=pack (0:X) q.snd := rfl

theorem lowerProjection_norm : ‖(lowerProjection : Joint X Y →L[ℝ] Joint X Y)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  rw [lowerProjection_apply,norm_pack_zero_left,one_mul]
  exact WithLp.norm_snd_le X q

theorem lowerProjection_comp_norm (B : Joint X Y →L[ℝ] Joint X Y) :
    ‖lowerProjection.comp B‖≤‖B‖ := by
  have hh := ContinuousLinearMap.opNorm_comp_le (lowerProjection : Joint X Y →L[ℝ] Joint X Y) B
  have hm := mul_le_mul_of_nonneg_right (lowerProjection_norm (X := X) (Y := Y)) (norm_nonneg B)
  exact hh.trans (by simpa only [one_mul] using hm)

def lowerLift (G : Joint X Y → Joint X Y) (q : Joint X Y) : Joint X Y := lowerProjection (G q)

variable {δ : NNReal} {G : Joint X Y → Joint X Y} (hG : LipschitzWith δ G)
include hG in
theorem lowerLift_lipschitz : LipschitzWith δ (lowerLift G) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [dist_eq_norm,dist_eq_norm]
  have hh := hG.dist_le_mul q r
  rw [dist_eq_norm,dist_eq_norm] at hh
  change ‖pack (0:X) (G q).snd-pack 0 (G r).snd‖≤_
  change ‖pack ((0:X)-0) ((G q).snd-(G r).snd)‖≤_
  rw [sub_self,norm_pack_zero_left]
  exact (WithLp.norm_snd_le X (G q-G r)).trans hh

variable [CompleteSpace X] [CompleteSpace Y] (hδ : δ<1)

def jointInverse (q : Joint X Y) : Joint X Y := pack q.fst (jointSolution hG hδ q.fst q.snd)

omit [CompleteSpace X] in
theorem jointInverse_equation (q : Joint X Y) :
    jointInverse hG hδ q+lowerLift G (jointInverse hG hδ q)=q := by
  change pack (q.fst+0) (jointSolution hG hδ q.fst q.snd+
    (G (pack q.fst (jointSolution hG hδ q.fst q.snd))).snd)=q
  rw [add_zero,jointSolution_equation]
  rfl

theorem jointInverse_eq_solution (q : Joint X Y) :
    jointInverse hG hδ q=solution hδ (lowerLift_lipschitz hG) q :=
  solution_of_equation hδ (lowerLift_lipschitz hG) q _ (jointInverse_equation hG hδ q)

theorem jointInverse_lipschitz_bound (q r : Joint X Y) :
    ‖jointInverse hG hδ q-jointInverse hG hδ r‖≤‖q-r‖/(1-(δ:ℝ)) := by
  rw [jointInverse_eq_solution,jointInverse_eq_solution]
  exact solution_lipschitz_bound hδ (lowerLift_lipschitz hG) q r

theorem jointInverse_continuous : Continuous (jointInverse hG hδ) := by
  rw [show jointInverse hG hδ=solution hδ (lowerLift_lipschitz hG) from funext (jointInverse_eq_solution hG hδ)]
  exact solution_continuous hδ (lowerLift_lipschitz hG)

def jointInverseDerivative (B : Joint X Y →L[ℝ] Joint X Y) (hB : ‖B‖≤(δ:ℝ)) :
    Joint X Y →L[ℝ] Joint X Y :=
  (linearEquiv hδ (lowerProjection.comp B) ((lowerProjection_comp_norm B).trans hB)).symm

theorem jointInverseDerivative_norm (B : Joint X Y →L[ℝ] Joint X Y) (hB : ‖B‖≤(δ:ℝ)) :
    ‖jointInverseDerivative hδ B hB‖≤1/(1-(δ:ℝ)) :=
  linearEquiv_inverse_bound hδ (lowerProjection.comp B) ((lowerProjection_comp_norm B).trans hB)

theorem jointInverseDerivative_equation (B : Joint X Y →L[ℝ] Joint X Y) (hB : ‖B‖≤(δ:ℝ))
    (v : Joint X Y) :
    jointInverseDerivative hδ B hB v+lowerProjection (B (jointInverseDerivative hδ B hB v))=v :=
  (linearEquiv hδ (lowerProjection.comp B) ((lowerProjection_comp_norm B).trans hB)).apply_symm_apply v

theorem jointInverse_hasFDerivAt (q : Joint X Y) (B : Joint X Y →L[ℝ] Joint X Y)
    (hB : ‖B‖≤(δ:ℝ)) (hDG : HasFDerivAt G B (jointInverse hG hδ q)) :
    HasFDerivAt (jointInverse hG hδ) (jointInverseDerivative hδ B hB) q := by
  have hh := (lowerProjection : Joint X Y →L[ℝ] Joint X Y).hasFDerivAt.comp
    (jointInverse hG hδ q) hDG
  rw [jointInverse_eq_solution hG hδ q] at hh
  rw [show jointInverse hG hδ=solution hδ (lowerLift_lipschitz hG) from funext (jointInverse_eq_solution hG hδ)]
  exact solution_hasFDerivAt hδ (lowerLift_lipschitz hG) q (lowerProjection.comp B)
    ((lowerProjection_comp_norm B).trans hB) hh

omit [CompleteSpace X] in
theorem jointGradient_representation (q : Joint X Y) :
    jointGradient hG hδ q=lowerProjection q-G (jointInverse hG hδ q) := by
  let z := jointSolution hG hδ q.fst q.snd
  have he : z+(G (pack q.fst z)).snd=q.snd := jointSolution_equation hG hδ q.fst q.snd
  change pack (-(G (pack q.fst z)).fst) z=
    pack (0-(G (pack q.fst z)).fst) (q.snd-(G (pack q.fst z)).snd)
  rw [zero_sub,← he,add_sub_cancel_right]

def jointHessian (B : Joint X Y →L[ℝ] Joint X Y) (hB : ‖B‖≤(δ:ℝ)) :
    Joint X Y →L[ℝ] Joint X Y := lowerProjection-B.comp (jointInverseDerivative hδ B hB)

theorem jointConjugate_gradient_hasFDerivAt (P : Joint X Y → ℝ)
    (hP : ∀ q,HasGradientAt P (G q) q) (q : Joint X Y)
    (B : Joint X Y →L[ℝ] Joint X Y) (hB : ‖B‖≤(δ:ℝ))
    (hDG : HasFDerivAt G B (jointInverse hG hδ q)) :
    HasFDerivAt (gradient (jointConjugate hG hδ P)) (jointHessian hδ B hB) q := by
  rw [show gradient (jointConjugate hG hδ P)=jointGradient hG hδ from
    funext (jointConjugate_gradient hG hδ P hP)]
  rw [show jointGradient hG hδ=(fun v => lowerProjection v-G (jointInverse hG hδ v)) from
    funext (jointGradient_representation hG hδ)]
  exact (lowerProjection : Joint X Y →L[ℝ] Joint X Y).hasFDerivAt.sub
    (hDG.comp q (jointInverse_hasFDerivAt hG hδ q B hB hDG))

end Bilevel.PartialLegendre
