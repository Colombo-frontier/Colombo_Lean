import Bilevel.PolishedLiteralObserverProbability
import Bilevel.PolishedLiteralRawBorel

/-! The public Borel channel used by the two selected views is the
literal original full-gradient reply formula. Its scalar data are fixed;
its only frame inputs are the disclosed raw column arrays. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev QuerySpace {dx du : ℕ} := PolishedLiteral.FullMeanSpace (X:=Space dx) (U:=Space du)

def blockColumns {S M : ℕ} {U : Type*} (V : Fin (S*M) → U) : Fin S → Fin M → U :=
  fun i j => V (finProdFinEquiv (i,j))

theorem blockColumns_measurable {S M : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockColumns (U:=U) (S:=S) (M:=M)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply _

/-- The source quotient and remainder are evaluated BEFORE this call's
Bernoulli activation. Capping applies only to disclosed column counts. -/
def sourceCounts (S M a : ℕ) (i : Fin S) : ℕ :=
  let b := min a (S*M)
  let r := b/M
  if i.val<r then M else if i.val=r then b%M else 0

variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : PolishedLiteral.Parameters (X:=X) (U:=U))

abbrev RawQuerySpace := PolishedLiteral.FullMeanSpace (X:=X) (U:=U)

@[irreducible] def rawCounterReply (τ p : ℝ) (a : P.MacroColumns)
    (b : Fin ((P.macroNode.n+1)*(P.n+1)) → U)
    (q : RawQuerySpace (X:=X) (U:=U)) (counter : ℕ) (coin : Bool) :
    RawQuerySpace (X:=X) (U:=U) × RawQuerySpace (X:=X) (U:=U) :=
  P.rawReply ((macroSchedule (P.macroNode.n+1) (P.n+1)).count counter)
    (sourceCounts (P.macroNode.n+1) (P.n+1) counter) a (blockColumns (S:=P.macroNode.n+1) (M:=P.n+1) b) τ p coin q

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (RawQuerySpace (X:=X) (U:=U))]
  [BorelSpace (RawQuerySpace (X:=X) (U:=U))]

attribute [local irreducible] PolishedLiteral.Parameters.rawReply

theorem rawCounterReply_fixed_measurable (τ p : ℝ) (a : ℕ) (coin : Bool) :
    Measurable (fun z : (P.MacroColumns × (Fin ((P.macroNode.n+1)*(P.n+1)) → U)) ×
      RawQuerySpace (X:=X) (U:=U) => rawCounterReply P τ p z.1.1 z.1.2 z.2 a coin) := by
  unfold rawCounterReply
  have ht : Measurable (fun z : (P.MacroColumns × (Fin ((P.macroNode.n+1)*(P.n+1)) → U)) ×
      RawQuerySpace (X:=X) (U:=U) => ((z.1.1,blockColumns (S:=P.macroNode.n+1) (M:=P.n+1) z.1.2),z.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk
      ((blockColumns_measurable (S:=P.macroNode.n+1) (M:=P.n+1)).comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  exact (P.rawReply_measurable ((macroSchedule (P.macroNode.n+1) (P.n+1)).count a)
    (sourceCounts (P.macroNode.n+1) (P.n+1) a) τ p coin).comp ht

theorem rawCounterReply_measurable (τ p : ℝ) :
    Measurable (fun z : (P.MacroColumns × (Fin ((P.macroNode.n+1)*(P.n+1)) → U)) ×
      (RawQuerySpace (X:=X) (U:=U) × (ℕ × Bool)) => rawCounterReply P τ p z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2) := by
  have hm : Measurable (fun z : ((P.MacroColumns × (Fin ((P.macroNode.n+1)*(P.n+1)) → U)) ×
      RawQuerySpace (X:=X) (U:=U)) × (ℕ × Bool) => rawCounterReply P τ p z.1.1.1 z.1.1.2 z.1.2 z.2.1 z.2.2) :=
    measurable_from_prod_countable (fun b => rawCounterReply_fixed_measurable P τ p b.1 b.2)
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd))

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (RawQuerySpace (X:=X) (U:=U))]
  [BorelSpace (RawQuerySpace (X:=X) (U:=U))] in
/-- Reframing the actual instance leaves the public evaluator unchanged:
no hidden future column is captured by this reply channel. -/
theorem rawCounterReply_reframe (τ p : ℝ)
    (fx : ChiBoundedChain.Space P.macroNode.n →ₗᵢ[ℝ] X)
    (fu : Fin (P.macroNode.n+1) → ChiBoundedChain.Space P.n →ₗᵢ[ℝ] U) :
    rawCounterReply (P.reframe fx fu) τ p=rawCounterReply P τ p := by
  unfold rawCounterReply
  funext a b q counter coin
  exact congrFun (P.rawReply_reframe fx fu _ _ a
    (blockColumns (S:=P.macroNode.n+1) (M:=P.n+1) b) τ p coin) q

end Bilevel.PolishedLiteralActualObserver
