import Bilevel.MultiscaleFullOracle

/-! Both complete original responses belong to the same retained
Primitive. Each lower sample remains the gradient of its fixed scalar. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 250000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)]
  [MeasurableSpace (Joint E (LowerSpace E))] [BorelSpace (Joint E (LowerSpace E))]
  {n : ℕ} (P : Parameters (E:=E) n)

theorem inner_full_oracles {μ Lf Lg Cf ρ : ℝ}
    (Q : Model.Primitive (X:=E) (Y:=LowerSpace E) μ Lf Lg Cf ρ)
    (hf : Q.f=P.data.upper) (hg : Q.g=P.data.lower)
    (σf σg : ℝ) (hscale : P.β*P.θ≤1) :
    ∃ Of : FreshOracle.Oracle (Query:=InnerQuery E) (E:=Joint E (LowerSpace E))
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg)) σf,
    ∃ Og : FreshOracle.Oracle (Query:=InnerQuery E) (E:=Joint E (LowerSpace E))
      (BernoulliOracle.law (P.activationProbability σg) (P.activationProbability_le_one σg)) σg,
      (∀ q,Of.truth q=pack (Q.fx q.1 q.2) (Q.fy q.1 q.2)) ∧
      (∀ q,Og.truth q=pack (Q.gx q.1 q.2) (Q.gy q.1 q.2)) ∧
      (∀ q coin,Of.sample q coin=pack (innerOriginalReply P (P.activationProbability σg) q coin).1.1
        (innerOriginalReply P (P.activationProbability σg) q coin).1.2) ∧
      (∀ q coin,Og.sample q coin=pack (innerOriginalReply P (P.activationProbability σg) q coin).2.1
        (innerOriginalReply P (P.activationProbability σg) q coin).2.2) ∧
      (∀ q coin,Og.sample q coin=pack (gradient (fun x => P.sampleLower (P.activationProbability σg) x q.2 coin) q.1)
        (gradient (fun y => P.sampleLower (P.activationProbability σg) q.1 y coin) q.2)) ∧
      (∀ coin,ContDiff ℝ 3 (fun q : InnerQuery E => P.sampleLower (P.activationProbability σg) q.1 q.2 coin)) := by
  refine ⟨innerUpperFullOracle P σf σg,innerLowerFullOracle P σg hscale,?_,?_,?_,?_,?_,?_⟩
  · intro q
    have hx := (Q.has_fx q.1 q.2).gradient
    have hy := (Q.has_fy q.1 q.2).gradient
    rw [hf] at hx hy
    have hpx := (P.data.upper_hasGradientX q.1 q.2).gradient
    have hpy := (P.data.upper_hasGradientY q.1 q.2).gradient
    change pack (P.data.upperX q.1 q.2) (P.data.upperY q.1 q.2)=_
    rw [←hpx,←hpy,hx,hy]
  · intro q
    have hx := (Q.has_gx q.1 q.2).gradient
    have hy := (Q.has_gy q.1 q.2).gradient
    rw [hg] at hx hy
    have hpx := (P.data.lower_hasGradientX q.1 q.2).gradient
    have hpy := (P.data.lower_hasGradientY q.1 q.2).gradient
    change pack (P.data.lowerX q.1 q.2) (P.data.lowerY q.1 q.2)=_
    rw [←hpx,←hpy,hx,hy]
  · intro q coin;rfl
  · intro q coin;rfl
  · intro q coin
    exact congrArg₂ pack
      (P.sampleLower_hasGradientX (P.activationProbability σg) q.1 q.2 coin).gradient.symm
      (P.sampleLower_hasGradientY (P.activationProbability σg) q.1 q.2 coin).gradient.symm
  · exact P.sampleLower_joint_contDiff _

end Bilevel.MultiscaleMean
