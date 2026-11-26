import Bilevel.PolishedLiteralObserverChannel
import Bilevel.PolishedLiteralObserverKnown

/-! Actual literal reply implementation of the two source observers.
The algorithm is arbitrary and may return an arbitrary measurable outer
point. Its full primitive query contributes one macro and two micro raw
vectors before the fresh activation, and its output is inserted at the end. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry SourceFrameActions PolishedProjectionDimension
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {dx du : ℕ}
  [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))]
  [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))]
  [BorelSpace (Joint (Space dx) (Space du))]

abbrev sourceXQuery (q : QuerySpace (dx:=dx) (du:=du)) : Space dx := q.fst.fst
abbrev sourceOuterUQuery (q : QuerySpace (dx:=dx) (du:=du)) : Space du := q.fst.snd
abbrev sourceInnerUQuery (q : QuerySpace (dx:=dx) (du:=du)) : Space du := q.snd.fst
abbrev sourceXOutput (q : Joint (Space dx) (Space du)) : Space dx := q.fst
abbrev sourceUOutput (q : Joint (Space dx) (Space du)) : Space du := q.snd

omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem sourceXQuery_measurable : Measurable (sourceXQuery (dx:=dx) (du:=du)) :=
  ((PolishedLiteral.fstMap (X:=Space dx) (U:=Space du)).continuous.comp
    (PolishedLiteral.fstMap (X:=Joint (Space dx) (Space du)) (U:=Joint (Space du) ℝ)).continuous).measurable
omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem sourceOuterUQuery_measurable : Measurable (sourceOuterUQuery (dx:=dx) (du:=du)) :=
  ((PolishedLiteral.sndMap (X:=Space dx) (U:=Space du)).continuous.comp
    (PolishedLiteral.fstMap (X:=Joint (Space dx) (Space du)) (U:=Joint (Space du) ℝ)).continuous).measurable
omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem sourceInnerUQuery_measurable : Measurable (sourceInnerUQuery (dx:=dx) (du:=du)) :=
  ((PolishedLiteral.fstMap (X:=Space du) (U:=ℝ)).continuous.comp
    (PolishedLiteral.sndMap (X:=Joint (Space dx) (Space du)) (U:=Joint (Space du) ℝ)).continuous).measurable
omit [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))] in
theorem sourceXOutput_measurable : Measurable (sourceXOutput (dx:=dx) (du:=du)) :=
  (PolishedLiteral.fstMap (X:=Space dx) (U:=Space du)).continuous.measurable
omit [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))] in
theorem sourceUOutput_measurable : Measurable (sourceUOutput (dx:=dx) (du:=du)) :=
  (PolishedLiteral.sndMap (X:=Space dx) (U:=Space du)).continuous.measurable

variable {St C : Type} [MeasurableSpace St] [MeasurableSpace C]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (τ p : ℝ)

abbrev literalMacroRules := sourceMacroRules A (rawCounterReply P τ p) (rawCounterReply_measurable P τ p)
  (Nat.succ_pos _) sourceXQuery sourceXQuery_measurable sourceXOutput sourceXOutput_measurable
abbrev literalMicroRules := sourceMicroRules A (rawCounterReply P τ p) (rawCounterReply_measurable P τ p)
  (Nat.succ_pos _) (Nat.succ_pos _) sourceOuterUQuery sourceInnerUQuery
  sourceOuterUQuery_measurable sourceInnerUQuery_measurable sourceUOutput sourceUOutput_measurable

/-- The single raw virtual run computed by both selected-frame observers. -/
abbrev literalRun (draws : ℕ → Bool) (U : Frame dx (P.macroNode.n+1))
    (V : Frame du ((P.macroNode.n+1)*(P.n+1))) :=
  masterRun (macroSchedule (P.macroNode.n+1) (P.n+1)) (microSchedule ((P.macroNode.n+1)*(P.n+1)))
    A (rawCounterReply P τ p) draws U V

/-- The complete macro observer's memory is precisely a selected-prefix
view of the literal virtual run, for every frame and draw stream. -/
theorem literal_macro_run (draws : ℕ → Bool) (U : Frame dx (P.macroNode.n+1))
    (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (n t : ℕ) (s : St × ℕ) :
    run (literalMacroRules P A τ p) n t
      (lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V draws s U) U=
      lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V draws (literalRun P A τ p draws U V n t s) U :=
  macro_run_same _ _ A (rawCounterReply P τ p) (rawCounterReply_measurable P τ p) (Nat.succ_pos _)
    sourceXQuery sourceXQuery_measurable sourceXOutput sourceXOutput_measurable draws U V n t s

/-- The micro observer is a second view of exactly the same run; its
other-frame context contains the complete macro frame. -/
theorem literal_micro_run (draws : ℕ → Bool) (U : Frame dx (P.macroNode.n+1))
    (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (n t : ℕ) (s : St × ℕ) :
    run (literalMicroRules P A τ p) n t
      (lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U draws s V) V=
      lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U draws (literalRun P A τ p draws U V n t s) V :=
  micro_run_same _ _ A (rawCounterReply P τ p) (rawCounterReply_measurable P τ p)
    (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) sourceOuterUQuery sourceInnerUQuery
    sourceOuterUQuery_measurable sourceInnerUQuery_measurable sourceUOutput sourceUOutput_measurable draws U V n t s

/-- The C=128 source dimension inequalities control the actual literal
virtual execution under exactly two independent global Haar frames. The
private seed and activation stream may have any joint law, independent
of the frames. -/
theorem literal_two_frame_observed (initial : C → St) (hi : Measurable initial)
    (draws : C → ℕ → Bool) (hdraws : Measurable draws)
    (ρ : Measure C) [IsProbabilityMeasure ρ] (N : ℕ)
    (Rx Ru τx τu δ : ℝ) (hRx : 0<Rx) (hRu : 0<Ru) (hτx : 0<τx) (hτu : 0<τu)
    (hδ : 0<δ) (hδ1 : δ≤1)
    (hdx : sourceDimension (N+1) (P.macroNode.n+1) Rx τx δ≤dx)
    (hdu : sourceDimension (2*N+1) ((P.macroNode.n+1)*(P.n+1)) Ru τu δ≤du) :
    ∃ hx : P.macroNode.n+1≤dx, ∃ hu : (P.macroNode.n+1)*(P.n+1)≤du,
      (ρ.prod ((HaarFrame.frameLaw dx (P.macroNode.n+1) hx).prod
        (HaarFrame.frameLaw du ((P.macroNode.n+1)*(P.n+1)) hu)))
        {z | ¬SourceObserved (literalMacroRules P A τ p) (τx^2/(4*Rx^2)) N 0
          (macroInitial initial draws (z.1,z.2.2),(⊥,∅)) z.2.1 ∨
          ¬SourceObserved (literalMicroRules P A τ p) (τu^2/(4*Ru^2)) N 0
          (microInitial initial draws (z.1,z.2.1),(⊥,∅)) z.2.2}≤ENNReal.ofReal δ :=
  actual_two_frame_observed A (rawCounterReply P τ p) (rawCounterReply_measurable P τ p)
    (Nat.succ_pos _) (Nat.succ_pos _) sourceXQuery sourceXQuery_measurable sourceOuterUQuery sourceInnerUQuery
    sourceOuterUQuery_measurable sourceInnerUQuery_measurable sourceXOutput sourceXOutput_measurable
    sourceUOutput sourceUOutput_measurable initial hi draws hdraws ρ N Rx Ru τx τu δ
    hRx hRu hτx hτu hδ hδ1 hdx hdu

end Bilevel.PolishedLiteralActualObserver
