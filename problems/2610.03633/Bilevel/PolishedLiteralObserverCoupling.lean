import Bilevel.PolishedLiteralSourceObserver
import Bilevel.PolishedLiteralObserverReply

/-! Pathwise coupling with the literal original-gradient oracle. The
activation stream is shared, while private algorithm state is arbitrary.
The only locality premise is the actual source blind box of the virtual
query, not a zero-respecting algorithm restriction. -/
noncomputable section
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ}
  [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St : Type} [MeasurableSpace St]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
  (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V)
  (τ p : ℝ)

def originalReply (coin : Bool) (q : QuerySpace (dx:=dx) (du:=du)) :
    QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du) :=
  (gradient (framedParameters P U hU V hV).upperJoint q,
    ChiConservative.sampleGradient (framedParameters P U hU V hV).sourceLower
      ((framedParameters P U hU V hV).inactiveSourceLower τ (P.w P.J)) p coin q)

def originalStep (draws : ℕ → Bool) (t : ℕ) (s : St × ℕ) : St × ℕ :=
  if A.halt s.1=true then s else
    (A.update (s.1,originalReply P U hU V hV τ p (draws t) (A.query s.1)),advance s.2 (draws t))

def originalRun (draws : ℕ → Bool) : ℕ → ℕ → St × ℕ → St × ℕ
  | 0,_,s => s
  | n+1,t,s => originalRun draws n (t+1) (originalStep P A U hU V hV τ p draws t s)

variable (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
  (hτb : τ≤P.macroNode.width) (hδ : ∀ j,j<P.J → τ≤P.δ j)

omit [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
include hb hβ hτ hτβ hτb hδ in
theorem originalStep_eq_virtual (draws : ℕ → Bool) (t : ℕ) (s : St × ℕ)
    (hq : (framedParameters P U hU V hV).BlindBox
      ((macroSchedule (P.macroNode.n+1) (P.n+1)).count s.2)
      (sourceCounts (P.macroNode.n+1) (P.n+1) s.2) τ (A.query s.1)) :
    originalStep P A U hU V hV τ p draws t s=
      masterStep (macroSchedule (P.macroNode.n+1) (P.n+1))
        (microSchedule ((P.macroNode.n+1)*(P.n+1))) A (rawCounterReply P τ p) draws U V t s := by
  have he := actual_counter_reply P U hU V hV s.2 (draws t) τ p hb hβ hτ hτβ hτb hδ (A.query s.1) hq
  unfold originalStep masterStep originalReply
  split
  · rfl
  · rw [he]

omit [BorelSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (Joint (Space dx) (Space du))] in
include hb hβ hτ hτβ hτb hδ in
/-- On the virtual good event, the complete actual and virtual states
(and therefore every query, stopping decision, and output) coincide. -/
theorem originalRun_eq_virtual (draws : ℕ → Bool) :
    ∀ n t (s : St × ℕ),
      (∀ k,k<n → let z := literalRun P A τ p draws U V k t s
        (framedParameters P U hU V hV).BlindBox
          ((macroSchedule (P.macroNode.n+1) (P.n+1)).count z.2)
          (sourceCounts (P.macroNode.n+1) (P.n+1) z.2) τ (A.query z.1)) →
      originalRun P A U hU V hV τ p draws n t s=literalRun P A τ p draws U V n t s := by
  intro n
  induction n with
  | zero => intros;rfl
  | succ n ih =>
    intro t s hbox
    have hfirst := hbox 0 (by omega)
    change (framedParameters P U hU V hV).BlindBox
      ((macroSchedule (P.macroNode.n+1) (P.n+1)).count s.2)
      (sourceCounts (P.macroNode.n+1) (P.n+1) s.2) τ (A.query s.1) at hfirst
    rw [originalRun,originalStep_eq_virtual P A U hU V hV τ p hb hβ hτ hτβ hτb hδ draws t s hfirst]
    change originalRun P A U hU V hV τ p draws n (t+1)
      (masterStep _ _ A (rawCounterReply P τ p) draws U V t s)=
      literalRun P A τ p draws U V n (t+1) (masterStep _ _ A (rawCounterReply P τ p) draws U V t s)
    apply ih
    intro k hk
    exact hbox (k+1) (by omega)

end Bilevel.PolishedLiteralActualObserver
