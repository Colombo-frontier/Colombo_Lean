import Bilevel.PolishedSourceFrameBudget
import Bilevel.PolishedTwoFrameProjection

/-! The macro source observer inserts exactly one raw vector per call,
and one terminal output. It does not inflate m_x=N+1 to 2*N+1. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine RawGenieBorel
variable {H : Memory.{u}} {d T : ℕ}

def oneQueryPolicy (L : Rules H d T) : (n R t : ℕ) → Policy d T H (n+1) R
  | 0,_,_ => .query L.output L.output_measurable Prod.fst measurable_fst .halt
  | n+1,0,t => .query (L.first t) (L.first_measurable t) Prod.fst measurable_fst
      (.adapt (fun h => L.finish t (h,0))
        ((L.finish_measurable t).comp (measurable_id.prodMk measurable_const))
        (oneQueryPolicy L n 0 (t+1)))
  | n+1,R+1,t => .query (L.first t) (L.first_measurable t) Prod.fst measurable_fst
      (.branch {h | L.request t h=true} ((L.request_measurable t) (measurableSet_singleton true))
        (.reveal (L.column t) (L.column_measurable t)
          (fun p => L.finish t (p.1,p.2.1))
          ((L.finish_measurable t).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
          (oneQueryPolicy L n R (t+1)))
        (.adapt (fun h => L.finish t (h,0))
          ((L.finish_measurable t).comp (measurable_id.prodMk measurable_const))
          (oneQueryPolicy L n (R+1) (t+1))))

theorem oneQuery_source_observed (L : Rules H d T) (cap : ℝ)
    (hsecond : ∀ t h,L.second t h=0) (credit : H → ℕ)
    (hrequest : ∀ t h,L.request t h=true → 0<credit h)
    (hyes : ∀ t h U,L.request t h=true → credit (step L t h U)+1≤credit h)
    (hno : ∀ t h U,L.request t h≠true → credit (step L t h U)≤credit h) :
    ∀ n R t (s : State H d T) (U : Frame d T), credit s.1≤R →
      RawGenieProtocol.Safe cap (compile (oneQueryPolicy L n R t) s.1) s.2.1 s.2.2 U →
      SourceObserved L cap n t s U := by
  intro n
  induction n with
  | zero =>
    intro R t s U _ h
    exact h.2
  | succ n ih =>
    intro R t s U hc h
    cases R with
    | zero =>
      have he := RawGenieProtocol.safe_current _ cap _ _ _ h.2
      refine ⟨?_,?_⟩
      · simpa only [querySpace,hsecond,Submodule.span_zero_singleton,sup_bot_eq] using he
      have hr : L.request t s.1≠true := by intro hr;have := hrequest t s.1 hr;omega
      apply ih 0 (t+1) (observeStep L t s U) U
      · rw [observeStep_memory]
        have := hno t s.1 U hr
        omega
      · simpa only [oneQueryPolicy,RawGenieBorel.compile,RawGenieProtocol.Safe,observeStep,step,if_neg hr,
          hsecond,Submodule.span_zero_singleton,sup_bot_eq] using h.2
    | succ R =>
      have he := RawGenieProtocol.safe_current _ cap _ _ _ h.2
      refine ⟨?_,?_⟩
      · simpa only [querySpace,hsecond,Submodule.span_zero_singleton,sup_bot_eq] using he
      by_cases hr : L.request t s.1=true
      · have hn := h.2
        simp only [oneQueryPolicy,RawGenieBorel.compile,Set.mem_setOf_eq,if_pos hr,RawGenieProtocol.Safe] at hn
        apply ih R (t+1) (observeStep L t s U) U
        · rw [observeStep_memory]
          have := hyes t s.1 U hr
          omega
        · simpa only [oneQueryPolicy,RawGenieBorel.compile,RawGenieProtocol.Safe,Set.mem_setOf_eq,if_pos hr,
            observeStep,step,hsecond,Submodule.span_zero_singleton,sup_bot_eq] using hn.2
      · have hn := h.2
        simp only [oneQueryPolicy,RawGenieBorel.compile,Set.mem_setOf_eq,if_neg hr,RawGenieProtocol.Safe] at hn
        apply ih (R+1) (t+1) (observeStep L t s U) U
        · rw [observeStep_memory]
          exact (hno t s.1 U hr).trans hc
        · simpa only [oneQueryPolicy,RawGenieBorel.compile,RawGenieProtocol.Safe,Set.mem_setOf_eq,if_neg hr,
            observeStep,step,hsecond,Submodule.span_zero_singleton,sup_bot_eq] using hn

end Bilevel.SourceFrameActions
