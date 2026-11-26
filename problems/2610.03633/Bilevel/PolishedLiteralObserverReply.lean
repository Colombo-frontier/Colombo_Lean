import Bilevel.PolishedLiteralObserverChannel
import Bilevel.PolishedLiteralCounterArithmetic
import Bilevel.PolishedTwoFrameBlocks

/-! Deterministic actual--virtual reply equality for the flat-counter
two-global-frame execution. The current reply uses PRE-activation
quotient/remainder counts even when a successful call crosses a block. -/
noncomputable section
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ}
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
  (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V)

def framedParameters : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du) :=
  P.reframe (PolishedTwoFrameBlocks.ofFrame P.macroNode.n U hU)
    (PolishedTwoFrameBlocks.microBlockFrame V hV)

theorem sourceCounts_eq_flatCounts (S M a : ℕ) : sourceCounts S M a=flatCounts S M a := rfl

/-- All arrays used in the literal source equality contain exactly the
columns that can be supplied before/at the current successful call. -/
theorem disclosed_arrays (a : ℕ) (coin : Bool) :
    let r := (macroSchedule (P.macroNode.n+1) (P.n+1)).count a
    let counts := sourceCounts (P.macroNode.n+1) (P.n+1) a
    let mx := prefixColumns U ((macroSchedule (P.macroNode.n+1) (P.n+1)).count (advance a coin))
    let mu := blockColumns (S:=P.macroNode.n+1) (M:=P.n+1)
      (prefixColumns V ((microSchedule ((P.macroNode.n+1)*(P.n+1))).count (advance a coin)))
    (∀ i : Fin (P.macroNode.n+1),r ≤ i.val → counts i≤P.n) ∧
    (∀ j : Fin (P.macroNode.n+1),j.val<r → mx j=(framedParameters P U hU V hV).macroNode.frame (ChiBoundedChain.basis j)) ∧
    (∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),j.val<counts i → mu i j=(framedParameters P U hU V hV).frames i (ChiBoundedChain.basis j)) ∧
    (coin=true → ∀ (i : Fin (P.macroNode.n+1)) (j : Fin (P.n+1)),
      j.val<(framedParameters P U hU V hV).activeCutCounts r counts i →
      mu i j=(framedParameters P U hU V hV).frames i (ChiBoundedChain.basis j)) := by
  dsimp only
  have ha : a≤advance a coin := by unfold advance;omega
  have hr := macroSchedule_count (P.macroNode.n+1) (P.n+1) a (Nat.succ_pos _)
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    rw [hr] at hi
    simpa only [sourceCounts_eq_flatCounts,Nat.add_sub_cancel] using
      flatCounts_current_bound (Nat.succ_pos P.n) i hi
  · intro j hj
    have hp := (macroSchedule (P.macroNode.n+1) (P.n+1)).monotone ha
    have hj' := hj.trans_le hp
    rw [prefixColumns,if_pos hj']
    exact (PolishedTwoFrameBlocks.ofFrame_basis P.macroNode.n U hU j).symm
  · intro i j hj
    have hj' : j.val<flatCounts (P.macroNode.n+1) (P.n+1) a i := hj
    have hp := (flatCounts_prefix_iff (Nat.succ_pos P.n) i j).mpr hj'
    have hp' := hp.trans_le ((microSchedule ((P.macroNode.n+1)*(P.n+1))).monotone ha)
    change (prefixColumns V ((microSchedule ((P.macroNode.n+1)*(P.n+1))).count (advance a coin)))
      (finProdFinEquiv (i,j))=_
    rw [prefixColumns,if_pos hp']
    exact (PolishedTwoFrameBlocks.microBlockFrame_basis V hV i j).symm
  · intro hc i j hj
    have hj' : j.val<(if i.val≤min a ((P.macroNode.n+1)*(P.n+1))/(P.n+1) then
        flatCounts (P.macroNode.n+1) (P.n+1) a i+1 else 0) := by
      change j.val<(if i.val≤(macroSchedule (P.macroNode.n+1) (P.n+1)).count a then
        sourceCounts (P.macroNode.n+1) (P.n+1) a i+1 else 0) at hj
      rw [hr] at hj
      exact hj
    have hp := flatCounts_active_prefix (Nat.succ_pos P.n) i j hj'
    have hp' : (finProdFinEquiv (i,j)).val<
        (microSchedule ((P.macroNode.n+1)*(P.n+1))).count (advance a coin) := by
      simpa only [advance,hc,if_true,microSchedule] using hp
    change (prefixColumns V ((microSchedule ((P.macroNode.n+1)*(P.n+1))).count (advance a coin)))
      (finProdFinEquiv (i,j))=_
    rw [prefixColumns,if_pos hp']
    exact (PolishedTwoFrameBlocks.microBlockFrame_basis V hV i j).symm

/-- Actual original full replies equal the executable raw-array channel
on the literal source blind box, including both activation outcomes. -/
theorem actual_counter_reply (a : ℕ) (coin : Bool) (τ p : ℝ)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (q : QuerySpace (dx:=dx) (du:=du))
    (hq : (framedParameters P U hU V hV).BlindBox
      ((macroSchedule (P.macroNode.n+1) (P.n+1)).count a)
      (sourceCounts (P.macroNode.n+1) (P.n+1) a) τ q) :
    (gradient (framedParameters P U hU V hV).upperJoint q,
      ChiConservative.sampleGradient (framedParameters P U hU V hV).sourceLower
        ((framedParameters P U hU V hV).inactiveSourceLower τ (P.w P.J)) p coin q)=
      rawCounterReply P τ p
        (prefixColumns U ((macroSchedule (P.macroNode.n+1) (P.n+1)).count (advance a coin)))
        (prefixColumns V ((microSchedule ((P.macroNode.n+1)*(P.n+1))).count (advance a coin))) q a coin := by
  obtain ⟨hcounts,ha,hold,hnew⟩ := disclosed_arrays P U hU V hV a coin
  have he := (framedParameters P U hU V hV).actual_reply_eq_raw
    ((macroSchedule (P.macroNode.n+1) (P.n+1)).count a)
    (sourceCounts (P.macroNode.n+1) (P.n+1) a)
    (prefixColumns U ((macroSchedule (P.macroNode.n+1) (P.n+1)).count (advance a coin)))
    (blockColumns (S:=P.macroNode.n+1) (M:=P.n+1)
      (prefixColumns V ((microSchedule ((P.macroNode.n+1)*(P.n+1))).count (advance a coin))))
    τ p coin hb hβ hτ hτβ hτb hδ hcounts ha hold hnew q hq
  refine he.trans ?_
  unfold rawCounterReply
  exact congrFun (P.rawReply_reframe _ _ _ _ _ _ τ p coin) q

end Bilevel.PolishedLiteralActualObserver
