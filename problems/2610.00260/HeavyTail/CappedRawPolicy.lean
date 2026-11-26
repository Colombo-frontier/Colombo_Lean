import HeavyTail.AdaptiveKernelExecution
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! A genuine raw-call-capped policy. Rejected replies leave the query state
unchanged. Accepted replies trigger one public update, and all updates stop
after the requested number of acceptances. No oracle law is used to define
the algorithm. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace HeavyTail.CappedRaw
universe u v w
variable {Seed Reply : Type u} {State : Type v} {Query Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace State]
  [MeasurableSpace Query] [MeasurableSpace Output]

structure Rule (State : Type v) (Query Reply Output : Type*)
    [MeasurableSpace State] [MeasurableSpace Query] [MeasurableSpace Reply] [MeasurableSpace Output] where
  query : State → Query
  query_measurable : Measurable query
  acceptance : Set (State × Reply)
  acceptance_measurable : MeasurableSet acceptance
  update : State × Reply → State
  update_measurable : Measurable update
  readout : State → Output
  readout_measurable : Measurable readout

namespace Rule
variable (M : Rule State Query Reply Output)

def activeAcceptance (n : ℕ) : Set ((ℕ × State) × Reply) :=
  {h | h.1.1 < n ∧ (h.1.2, h.2) ∈ M.acceptance}

theorem activeAcceptance_measurable (n : ℕ) : MeasurableSet (M.activeAcceptance n) :=
  (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const).inter
    (M.acceptance_measurable.preimage ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

def step (n : ℕ) (h : (ℕ × State) × Reply) : ℕ × State :=
  if h ∈ M.activeAcceptance n then (h.1.1 + 1, M.update (h.1.2, h.2)) else h.1

theorem step_measurable (n : ℕ) : Measurable (M.step n) := by
  apply Measurable.ite (M.activeAcceptance_measurable n)
  · exact ((measurable_fst.comp measurable_fst).add_const 1).prodMk
      (M.update_measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  · exact measurable_fst

theorem step_frozen_reject (n : ℕ) (s : ℕ × State) (r : Reply)
    (hr : (s.2, r) ∉ M.acceptance) : M.step n (s, r) = s := by
  simp [step, activeAcceptance, hr]

theorem step_frozen_done (n : ℕ) (s : ℕ × State) (r : Reply)
    (hs : n ≤ s.1) : M.step n (s, r) = s := by
  simp [step, activeAcceptance, not_lt.mpr hs]

theorem step_count_mono (n : ℕ) (h : (ℕ × State) × Reply) : h.1.1 ≤ (M.step n h).1 := by
  unfold step
  split_ifs <;> simp

theorem step_count_le (n : ℕ) (h : (ℕ × State) × Reply) (hh : h.1.1 ≤ n) :
    (M.step n h).1 ≤ n := by
  unfold step
  split_ifs with ha
  · exact Nat.succ_le_of_lt ha.1
  · exact hh

def state (M : Rule State Query Reply Output) (initial : Seed → State) (n : ℕ) :
    (t : ℕ) → AdaptiveKernel.History Seed Reply t → ℕ × State
  | 0 => fun s => (0, initial s)
  | t + 1 => fun h => M.step n (state M initial n t h.1, h.2)

theorem state_measurable {initial : Seed → State} (hi : Measurable initial) (n t : ℕ) :
    Measurable (M.state initial n t) := by
  induction t with
  | zero => exact measurable_const.prodMk hi
  | succ t ih => exact (M.step_measurable n).comp ((ih.comp measurable_fst).prodMk measurable_snd)

theorem state_count_le (initial : Seed → State) (n t : ℕ)
    (h : AdaptiveKernel.History Seed Reply t) : (M.state initial n t h).1 ≤ n := by
  induction t with
  | zero => exact Nat.zero_le n
  | succ t ih => exact M.step_count_le n _ (ih h.1)

def rejection (initial : Seed → State) (n t : ℕ) :
    Set (AdaptiveKernel.History Seed Reply t × Reply) :=
  {h | (M.state initial n t h.1).1 < n ∧ ((M.state initial n t h.1).2, h.2) ∉ M.acceptance}

theorem rejection_measurable {initial : Seed → State} (hi : Measurable initial) (n t : ℕ) :
    MeasurableSet (M.rejection initial n t) := by
  have hs : Measurable (fun h : AdaptiveKernel.History Seed Reply t × Reply =>
      M.state initial n t h.1) := (M.state_measurable hi n t).comp measurable_fst
  exact (measurableSet_lt hs.fst measurable_const).inter
    ((M.acceptance_measurable.preimage (hs.snd.prodMk measurable_snd)).compl)

def rejections (M : Rule State Query Reply Output) (initial : Seed → State) (n : ℕ) :
    (t : ℕ) → AdaptiveKernel.History Seed Reply t → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun h => rejections M initial n t h.1 + if h ∈ M.rejection initial n t then 1 else 0

theorem rejections_measurable {initial : Seed → State} (hi : Measurable initial) (n t : ℕ) :
    Measurable (M.rejections initial n t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).add
        (Measurable.ite (M.rejection_measurable hi n t) measurable_const measurable_const)

theorem incomplete_count_identity (initial : Seed → State) (n t : ℕ)
    (h : AdaptiveKernel.History Seed Reply t) (hi : (M.state initial n t h).1 < n) :
    (M.state initial n t h).1 + M.rejections initial n t h = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hp : (M.state initial n t h.1).1 < n :=
        lt_of_le_of_lt (M.step_count_mono n (M.state initial n t h.1, h.2)) hi
      have hid := ih h.1 hp
      by_cases ha : ((M.state initial n t h.1).2, h.2) ∈ M.acceptance
      · have hac : (M.state initial n t h.1, h.2) ∈ M.activeAcceptance n := ⟨hp, ha⟩
        have hnr : h ∉ M.rejection initial n t := fun hr => hr.2 ha
        simp only [state, step, if_pos hac, rejections, if_neg hnr, Nat.add_zero]
        omega
      · have hna : (M.state initial n t h.1, h.2) ∉ M.activeAcceptance n := by
          simp [activeAcceptance, ha]
        have hr : h ∈ M.rejection initial n t := ⟨hp, ha⟩
        simp only [state, step, if_neg hna, rejections, if_pos hr]
        omega

theorem raw_cap_failure_implies_rejections (initial : Seed → State) (n : ℕ)
    (h : AdaptiveKernel.History Seed Reply (4 * n))
    (hi : (M.state initial n (4 * n) h).1 < n) :
    3 * n ≤ M.rejections initial n (4 * n) h := by
  have hc := M.incomplete_count_identity initial n (4 * n) h hi
  omega

def policy (initial : Seed → State) (hi : Measurable initial) (n T : ℕ) :
    AdaptiveKernel.Policy Seed Query Reply Output T where
  query t h := M.query (M.state initial n t h).2
  query_measurable t := M.query_measurable.comp (M.state_measurable hi n t).snd
  output h := M.readout (M.state initial n T h).2
  output_measurable := M.readout_measurable.comp (M.state_measurable hi n T).snd

end Rule
end HeavyTail.CappedRaw
