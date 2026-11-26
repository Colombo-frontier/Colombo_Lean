import Bilevel.MultiscaleInnerCertificate

/-! Canonical witnesses retain exactly the Primitive selected by the
analytic certificate, with both original full-gradient oracles. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 250000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} {P : Parameters (E:=E) n} {μ L ρ Δ C κ ε : ℝ}

namespace InnerPrimitiveCertificate
variable (H : InnerPrimitiveCertificate P μ L ρ Δ C κ ε)

def primitive : Model.Primitive (X:=E) (Y:=LowerSpace E) μ L L L ρ := Classical.choose H

def response : H.primitive.Response := Classical.choose (Classical.choose_spec H)

theorem primitive_f : H.primitive.f=P.data.upper :=
  (Classical.choose_spec (Classical.choose_spec H)).1

theorem primitive_g : H.primitive.g=P.data.lower :=
  (Classical.choose_spec (Classical.choose_spec H)).2.1

theorem response_y : H.response.y=P.data.response :=
  (Classical.choose_spec (Classical.choose_spec H)).2.2.1

theorem mean_eq : H.primitive.hyperobjective H.response=P.realized :=
  (Classical.choose_spec (Classical.choose_spec H)).2.2.2.1

theorem origin : H.response.y 0=0 :=
  (Classical.choose_spec (Classical.choose_spec H)).2.2.2.2.1

theorem gap : Nonempty (H.primitive.GapCertificate H.response 0 Δ) :=
  (Classical.choose_spec (Classical.choose_spec H)).2.2.2.2.2.1

theorem curvature (x z : E) :
    ‖gradient (H.primitive.hyperobjective H.response) x-gradient (H.primitive.hyperobjective H.response) z‖≤
      (C*L*κ^2)*‖x-z‖ :=
  (Classical.choose_spec (Classical.choose_spec H)).2.2.2.2.2.2.2.1 x z

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]
  [MeasurableSpace (Joint E (LowerSpace E))] [BorelSpace (Joint E (LowerSpace E))]

theorem full_oracles (σf σg : ℝ) (hscale : P.β*P.θ≤1) :
    ∃ Of : FreshOracle.Oracle (Query:=InnerQuery E) (E:=Joint E (LowerSpace E))
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg)) σf,
    ∃ Og : FreshOracle.Oracle (Query:=InnerQuery E) (E:=Joint E (LowerSpace E))
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg)) σg,
      (∀ q,Of.truth q=pack (H.primitive.fx q.1 q.2) (H.primitive.fy q.1 q.2)) ∧
      (∀ q,Og.truth q=pack (H.primitive.gx q.1 q.2) (H.primitive.gy q.1 q.2)) ∧
      (∀ q coin,Of.sample q coin=pack (innerOriginalReply P (P.activationProbability σg) q coin).1.1
        (innerOriginalReply P (P.activationProbability σg) q coin).1.2) ∧
      (∀ q coin,Og.sample q coin=pack (innerOriginalReply P (P.activationProbability σg) q coin).2.1
        (innerOriginalReply P (P.activationProbability σg) q coin).2.2) ∧
      (∀ q coin,Og.sample q coin=pack (gradient (fun x => P.sampleLower (P.activationProbability σg) x q.2 coin) q.1)
        (gradient (fun y => P.sampleLower (P.activationProbability σg) q.1 y coin) q.2)) ∧
      (∀ coin,ContDiff ℝ 3 (fun q : InnerQuery E => P.sampleLower (P.activationProbability σg) q.1 q.2 coin)) :=
  inner_full_oracles P H.primitive H.primitive_f H.primitive_g σf σg hscale

end InnerPrimitiveCertificate
end Bilevel.MultiscaleMean
