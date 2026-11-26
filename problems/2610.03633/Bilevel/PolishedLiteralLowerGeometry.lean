import Bilevel.PolishedLiteralSmallness
import Bilevel.PolishedLiteralSelection

/-! Euclidean contraction from actual full source variables ((x,v),(u,s))
into the already differentiated compensated perturbation variables (x,u,s).
The dummy scalar remains fixed at zero and is never an extra source lower
variable. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

abbrev FullMeanSpace := Joint (Joint X U) (Joint U ℝ)

def fullLowerEmbedLM : FullMeanSpace (X:=X) (U:=U) →ₗ[ℝ]
    PolishedLiteralCompensated.LowerSpace (Joint X U) where
  toFun q := PolishedLiteralCompensated.pack _ (pack q.fst.fst q.snd.fst) q.snd.snd 0
  map_add' a b := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · rfl
    · change (a.snd.snd+b.snd.snd) • EuclideanSpace.single 0 1 + (0:ℝ) • EuclideanSpace.single 1 1 =
        (a.snd.snd • EuclideanSpace.single 0 1 + (0:ℝ) • EuclideanSpace.single 1 1)+
        (b.snd.snd • EuclideanSpace.single 0 1 + (0:ℝ) • EuclideanSpace.single 1 1)
      simp only [zero_smul,add_zero,add_smul]
  map_smul' c a := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · rfl
    · change (c*a.snd.snd) • EuclideanSpace.single 0 1 + (0:ℝ) • EuclideanSpace.single 1 1 =
        c • (a.snd.snd • EuclideanSpace.single 0 1 + (0:ℝ) • EuclideanSpace.single 1 1)
      simp only [zero_smul,add_zero,smul_smul]

omit [CompleteSpace X] [CompleteSpace U] in
theorem fullLowerEmbedLM_norm (q : FullMeanSpace (X:=X) (U:=U)) :
    ‖fullLowerEmbedLM q‖≤‖q‖ := by
  have h := PolishedLiteralCompensated.pack_norm_sq (pack q.fst.fst q.snd.fst) q.snd.snd 0
  have hq := PrimitiveGeometry.norm_sq q
  have hx := PrimitiveGeometry.norm_sq q.fst
  have hy := PrimitiveGeometry.norm_sq q.snd
  have hs := PrimitiveGeometry.norm_sq (pack q.fst.fst q.snd.fst)
  change ‖fullLowerEmbedLM q‖^2=‖pack q.fst.fst q.snd.fst‖^2+q.snd.snd^2+(0:ℝ)^2 at h
  simp only [Real.norm_eq_abs,sq_abs] at hy
  change ‖pack q.fst.fst q.snd.fst‖^2=‖q.fst.fst‖^2+‖q.snd.fst‖^2 at hs
  nlinarith [norm_nonneg q,norm_nonneg (fullLowerEmbedLM q),sq_nonneg ‖q.fst.snd‖]

def fullLowerEmbed : FullMeanSpace (X:=X) (U:=U) →L[ℝ]
    PolishedLiteralCompensated.LowerSpace (Joint X U) :=
  fullLowerEmbedLM.mkContinuous 1 (fun q => by simpa only [one_mul] using fullLowerEmbedLM_norm q)

omit [CompleteSpace X] [CompleteSpace U] in
theorem fullLowerEmbed_norm : ‖fullLowerEmbed (X:=X) (U:=U)‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun q => by simpa only [one_mul] using fullLowerEmbedLM_norm q)

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

def sourceLower (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  PolishedLiteralJointMean.lower P.data q.fst.fst q.fst.snd q.snd

def sourcePerturbation (q : FullMeanSpace (X:=X) (U:=U)) : ℝ :=
  PolishedLiteralJointMean.perturbation P.data q.fst.fst q.snd

theorem sourcePerturbation_eq : P.sourcePerturbation=P.data.perturbation ∘ fullLowerEmbed := by
  funext q
  exact PolishedLiteralJointMean.perturbation_eq_embed P.data q.fst.fst q.snd

theorem sourcePerturbation_jet_le (q : FullMeanSpace (X:=X) (U:=U)) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k P.sourcePerturbation q‖≤
      ‖iteratedFDeriv ℝ k P.data.perturbation (fullLowerEmbed q)‖ := by
  rw [P.sourcePerturbation_eq]
  let T : FullMeanSpace (X:=X) (U:=U) →L[ℝ] PolishedLiteralCompensated.LowerSpace (Joint X U) := fullLowerEmbed
  have hf : ContDiff ℝ 3 P.data.perturbation := PolishedLiteralCompensated.Data.perturbation_contDiff P.data
  have hT : ‖T‖≤1 := fullLowerEmbed_norm (X:=X) (U:=U)
  exact ChiOuter.contraction_jet_bound T hT hf q k hk

end Parameters
end Bilevel.PolishedLiteral
