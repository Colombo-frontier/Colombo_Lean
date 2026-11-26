import Bilevel.MultiscaleFreshOracle
import Bilevel.MultiscaleMeanCertificate

/-! Named literal full-query replies and mean loss for the macro-free
family. Both upper derivatives and both conservative lower sample
derivatives are retained; no prefix or information premise appears here. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev InnerQuery (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  E × LowerSpace E

abbrev InnerReply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  InnerQuery E × InnerQuery E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

def innerOriginalReply (P : Parameters (E:=E) n) (p : ℝ) (q : InnerQuery E)
    (b : Bool) : InnerReply E :=
  ((P.data.upperX q.1 q.2,P.data.upperY q.1 q.2),
    (P.sampleLowerX p q.1 q.2 b,P.sampleLowerY p q.1 q.2 b))

def innerOriginalLoss (P : Parameters (E:=E) n) (x : E) : ℝ :=
  ‖gradient P.realized x‖

theorem innerOriginalReply_derivatives (P : Parameters (E:=E) n) (p : ℝ)
    (q : InnerQuery E) (b : Bool) :
    (innerOriginalReply P p q b).1.1=gradient (fun x => P.data.upper x q.2) q.1 ∧
    (innerOriginalReply P p q b).1.2=gradient (P.data.upper q.1) q.2 ∧
    (innerOriginalReply P p q b).2.1=gradient (fun x => P.sampleLower p x q.2 b) q.1 ∧
    (innerOriginalReply P p q b).2.2=gradient (fun y => P.sampleLower p q.1 y b) q.2 :=
  ⟨(P.data.upper_hasGradientX q.1 q.2).gradient.symm,
    (P.data.upper_hasGradientY q.1 q.2).gradient.symm,
    (P.sampleLower_hasGradientX p q.1 q.2 b).gradient.symm,
    (P.sampleLower_hasGradientY p q.1 q.2 b).gradient.symm⟩

theorem innerOriginalLoss_continuous (P : Parameters (E:=E) n) :
    Continuous (innerOriginalLoss P) := by
  have hF : ContDiff ℝ 3 P.realized :=
    P.outer_contDiff.comp (contDiff_const.smul contDiff_id)
  exact (GradientJetBounds.gradient_contDiff hF).continuous.norm

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]
  [SecondCountableTopology (LowerSpace E)]

omit [SecondCountableTopology E] [MeasurableSpace (LowerSpace E)]
  [BorelSpace (LowerSpace E)] [SecondCountableTopology (LowerSpace E)] in
theorem innerOriginalLoss_measurable (P : Parameters (E:=E) n) :
    Measurable (innerOriginalLoss P) := (innerOriginalLoss_continuous P).measurable

omit [SecondCountableTopology E] in
theorem innerOriginalReply_measurable (P : Parameters (E:=E) n) (p : ℝ) :
    Measurable (fun qb : InnerQuery E × Bool => innerOriginalReply P p qb.1 qb.2) := by
  have hupper : Continuous (fun y : LowerSpace E => P.data.upperY 0 y) := by
    have he : (fun y : LowerSpace E => P.data.upperY 0 y)=gradient (P.data.upper 0) :=
      funext (fun y => (P.data.upper_hasGradientY 0 y).gradient.symm)
    rw [he]
    exact (GradientJetBounds.gradient_contDiff (P.data.upper_contDiff 0)).continuous
  have hfy : Measurable (fun qb : InnerQuery E × Bool => P.data.upperY qb.1.1 qb.1.2) :=
    hupper.measurable.comp (measurable_snd.comp measurable_fst)
  have hfx : Measurable (fun qb : InnerQuery E × Bool => P.data.upperX qb.1.1 qb.1.2) :=
    measurable_const
  have hgx : Measurable (fun qb : InnerQuery E × Bool => P.sampleLowerX p qb.1.1 qb.1.2 qb.2) := by
    have hu : Measurable (fun qb : InnerQuery E × Bool => uProj E qb.1.2) :=
      (uProj E).continuous.measurable.comp (measurable_snd.comp measurable_fst)
    have h := hu.const_smul (-P.L)
    exact h
  have hgy := P.sampleLowerY_measurable p
  exact (hfx.prodMk hfy).prodMk (hgx.prodMk hgy)

end Bilevel.MultiscaleMean
