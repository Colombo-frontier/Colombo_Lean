import Bilevel.PolishedFrozenCode
import Bilevel.PolishedCachedOuterCalls

/-! Exact call counts and state support of the literal reuse branch. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedOracleCode
variable {X Y Seed : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  (response : (X×Y) → Seed → FullResponse X Y)

def reuseCalls (μ Lg σg D r δ : ℝ) (q : ℕ) : ℕ :=
  q*StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)+
    (q*FreshBatchKernel.count σg (δ/12)+q*FreshBatchKernel.count σg (δ/12))

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reusePair_exactCalls (μ Lg σg t D r : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (reusePair μ Lg σg t D r q)
      (q*StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)) :=
  ((tilted_exactCalls response μ Lg σg t D r q).reparam _ _).map _ _

omit [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseFirst_exactCalls (σg δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (reuseFirst σg δ q) (q*FreshBatchKernel.count σg (δ/12)) :=
  (firstGradient_exactCalls response σg δ q).reparam _ _

omit [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseLast_exactCalls (σg δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (reuseLast σg δ q) (q*FreshBatchKernel.count σg (δ/12)) :=
  (lastGradient_exactCalls response σg δ q).reparam _ _

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseEstimator_exactCalls (μ Lg σg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    ExactCalls response (reuseEstimator μ Lg σg t D r δ q) (reuseCalls μ Lg σg D r δ q) := by
  have hh := (((reusePair_exactCalls response μ Lg σg t D r q).bind
    (reuseFirst_exactCalls response σg δ q)).bind (reuseLast_exactCalls response σg δ q)).map
    (C:=of X) (fun z : (CachedEstimatorProcedure.Input X Y×Y)×CachedEstimatorProcedure.Transcript X Y =>
      CachedEstimatorProcedure.estimate t z.1.1 z.2) (by unfold CachedEstimatorProcedure.estimate;fun_prop)
  convert hh using 1
  simp only [reuseCalls]
  omega

theorem reuseCalls_le_estimatorCalls (μ Lg σg D r δ : ℝ) (q : ℕ) :
    reuseCalls μ Lg σg D r δ q≤estimatorCalls μ Lg σg D r δ q := by
  unfold reuseCalls estimatorCalls
  omega

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseEstimateStep_exactCalls (μ Lg Cf σg t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    ExactCalls response (reuseEstimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n)
      (reuseCalls μ Lg σg D r δ q) :=
  ((reuseEstimator_exactCalls response μ Lg σg t D r δ q).reparam _ _).map _ _

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseEstimateStep_support (μ Lg Cf σg t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (reuseEstimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n) (s,stream)
    w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2=s.2 := by
  constructor
  · simp only [reuseEstimateStep,OracleCode.map,eval,Procedure.combine,put,ite_true]
  · rfl

theorem refreshIteration_exactCalls (μ Lg Cf σf σg t D r rA δ η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    ExactCalls response (refreshIteration μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n)
      (anchorCalls μ Lg σf σg D rA η q+reuseCalls μ Lg σg D r δ q) :=
  (refreshAt_exactCalls response μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n).bind
    ((reuseEstimateStep_exactCalls response μ Lg Cf σg t D r δ Λ cap q x₀ yinit n).reparam _ _)

theorem refreshIteration_support (μ Lg Cf σf σg t D r rA δ η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (refreshIteration μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n) (s,stream)
    w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2.1=current Λ cap x₀ n s := by
  let z := eval response (CachedOracleCode.refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n) (s,stream)
  let w := eval response (reuseEstimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n) (z.1.1,z.2)
  have hz := refreshAt_support_pointwise response μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n s stream
  have hw := reuseEstimateStep_support response μ Lg Cf σg t D r δ Λ cap q x₀ yinit n z.1.1 z.2
  change w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2.1=current Λ cap x₀ n s
  change z.1.1.1=s.1 ∧ z.1.1.2.1=current Λ cap x₀ n s at hz
  change w.1.1.1=put z.1.1.1 n (w.1.1.1 n) ∧ w.1.1.2=z.1.1.2 at hw
  exact ⟨hw.1.trans (congrArg (fun G => put G n (w.1.1.1 n)) hz.1),by rw [hw.2];exact hz.2⟩

/-- Exactly five amplified primitive groups occur on a refresh: the anchor
lower solve and upper batch, one tilted solve, and two lower-x batches. -/
theorem refreshIteration_five_groups (μ Lg Cf σf σg t D r rA δ η Λ cap : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    (eval response (refreshIteration μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n) (s,stream)).1.2.2=
      q*StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (rA/12)+
      q*FreshBatchKernel.count σf (η/12)+
      q*StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12)+
      q*FreshBatchKernel.count σg (δ/12)+q*FreshBatchKernel.count σg (δ/12) := by
  have hh := refreshIteration_exactCalls response μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n (s,stream)
  simpa only [anchorCalls,reuseCalls,Nat.add_assoc] using hh

end Bilevel.PolishedFrozenCode
