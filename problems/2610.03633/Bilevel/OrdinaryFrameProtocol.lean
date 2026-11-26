import Bilevel.RawGenieBorelProbability

/-! A concrete ordinary-frame observer. Each call first inserts two raw
vectors, including all-column projection updates, and only then decides
whether to reveal a full column. At most R columns may be revealed. A final
arbitrary output vector is inserted once after the last call. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.OrdinaryFrame
open EuclideanGaussian ProjectionPosterior ProjectionGeometry TransportControllerMachine RawGenieBorel

structure Rules (H : Memory.{u}) (d T : ℕ) where
  first : ℕ → H → Space d
  first_measurable : ∀ t,Measurable (first t)
  afterFirst : ℕ → H × Frame d T → H
  afterFirst_measurable : ∀ t,Measurable (afterFirst t)
  second : ℕ → H → Space d
  second_measurable : ∀ t,Measurable (second t)
  afterSecond : ℕ → H × Frame d T → H
  afterSecond_measurable : ∀ t,Measurable (afterSecond t)
  success : ℕ → Set H
  success_measurable : ∀ t,MeasurableSet (success t)
  column : ℕ → H → Fin T
  column_measurable : ∀ t,Measurable (column t)
  afterReveal : ℕ → H × (Space d × Frame d T) → H
  afterReveal_measurable : ∀ t,Measurable (afterReveal t)
  output : H → Space d
  output_measurable : Measurable output

def queryCount : ℕ → ℕ
  | 0 => 1
  | Q+1 => queryCount Q+1+1

theorem queryCount_eq (Q : ℕ) : queryCount Q=2*Q+1 := by
  induction Q with
  | zero => rfl
  | succ Q ih => simp only [queryCount,ih]; omega

def policy {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) :
    (Q R t : ℕ) → Policy d T H (queryCount Q) R
  | 0,_,_ => .query L.output L.output_measurable Prod.fst measurable_fst .halt
  | Q+1,0,t => .query (L.first t) (L.first_measurable t)
      (L.afterFirst t) (L.afterFirst_measurable t)
      (.query (L.second t) (L.second_measurable t) (L.afterSecond t) (L.afterSecond_measurable t)
        (policy L Q 0 (t+1)))
  | Q+1,R+1,t => .query (L.first t) (L.first_measurable t)
      (L.afterFirst t) (L.afterFirst_measurable t)
      (.query (L.second t) (L.second_measurable t) (L.afterSecond t) (L.afterSecond_measurable t)
        (.branch (L.success t) (L.success_measurable t)
          (.reveal (L.column t) (L.column_measurable t)
            (L.afterReveal t) (L.afterReveal_measurable t) (policy L Q R (t+1)))
          (policy L Q (R+1) (t+1))))

abbrev State (H : Memory.{u}) (d T : ℕ) := H × (Submodule ℝ (Space d) × Set (Fin T))

def queryStep {d T : ℕ} {H : Memory.{u}} (q : H → Space d)
    (respond : H × Frame d T → H) (s : State H d T) (U : Frame d T) : State H d T :=
  let V := s.2.1 ⊔ Submodule.span ℝ {q s.1}
  (respond (s.1,RawGenieProtocol.projections d T V U),(V,s.2.2))

def revealStep {d T : ℕ} {H : Memory.{u}} (j : H → Fin T)
    (respond : H × (Space d × Frame d T) → H) (s : State H d T) (U : Frame d T) : State H d T :=
  let V := s.2.1 ⊔ Submodule.span ℝ {U (j s.1)}
  (respond (s.1,(U (j s.1),RawGenieProtocol.projections d T V U)),(V,insert (j s.1) s.2.2))

def precoin {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) (t : ℕ)
    (s : State H d T) (U : Frame d T) : State H d T :=
  queryStep (L.second t) (L.afterSecond t)
    (queryStep (L.first t) (L.afterFirst t) s U) U

open Classical in
def run {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) :
    (Q R t : ℕ) → State H d T → Frame d T → State H d T
  | 0,_,_,s,U => queryStep L.output Prod.fst s U
  | Q+1,0,t,s,U => run L Q 0 (t+1) (precoin L t s U) U
  | Q+1,R+1,t,s,U =>
    let a := precoin L t s U
    if a.1∈L.success t then run L Q R (t+1) (revealStep (L.column t) (L.afterReveal t) a U) U
    else run L Q (R+1) (t+1) a U

theorem safe_run {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) (cap : ℝ) :
    ∀ Q R t (s : State H d T) (U : Frame d T),
    RawGenieProtocol.Safe cap (compile (policy L Q R t) s.1) s.2.1 s.2.2 U →
    GenieProtocol.BoundedEnergy (run L Q R t s U).2.1 (run L Q R t s U).2.2 U cap := by
  classical
  intro Q
  induction Q with
  | zero =>
    intro R t s U h
    exact h.2
  | succ Q ih =>
    intro R t s U h
    cases R with
    | zero => exact ih 0 (t+1) (precoin L t s U) U h.2.2
    | succ R =>
      have hn := h.2.2
      change RawGenieProtocol.Safe cap
        (if (precoin L t s U).1∈L.success t then
          compile (.reveal (L.column t) (L.column_measurable t) (L.afterReveal t)
            (L.afterReveal_measurable t) (policy L Q R (t+1))) (precoin L t s U).1
        else compile (policy L Q (R+1) (t+1)) (precoin L t s U).1)
        (precoin L t s U).2.1 (precoin L t s U).2.2 U at hn
      by_cases ha : (precoin L t s U).1∈L.success t
      · rw [if_pos ha] at hn
        simpa only [run,if_pos ha] using
          ih R (t+1) (revealStep (L.column t) (L.afterReveal t) (precoin L t s U) U) U hn.2
      · rw [if_neg ha] at hn
        simpa only [run,if_neg ha] using ih (R+1) (t+1) (precoin L t s U) U hn

end Bilevel.OrdinaryFrame
