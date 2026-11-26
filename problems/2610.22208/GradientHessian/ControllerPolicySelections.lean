import GradientHessian.ControllerPolicyMeasurability
import GradientHessian.ControllerOptionalTrajectory

/-! Measurable selection schedules for the chronological driver. A
presence bit records each policy-selected point exactly once, while all
internal repair phases are absent. Filtering by literal controller visits
then has the already proved sharp subtree visibility bound. -/

noncomputable section
namespace GradientHessian.ControllerPolicyDriver
open Classical FrontierState TaskState ComparisonController ControllerMeasurable
open ComparisonControllerReplay

variable {L M ell : ℕ} {Ω Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Machine.Policy Seed S X Y Z) (stop : State L M ell → Bool)

def selectionBit : Config L M ell S X A → Bool
  | .ready n a s => if stop s then false else if n=0 ∨ P.mode a=0 then true else decide (P.mode a≠1)
  | .pending _ _ _ _ | .finished _ _ => false

def selectionPayload : Config L M ell S X A → Pending X
  | .ready n a _ => if n=0 ∨ P.mode a=0 then ⟨P.output a,.ordinary⟩
    else ⟨P.point a,if P.mode a=2 then .ordinary else .rich⟩
  | .pending _ _ _ phase => (phaseEquiv L M ell X A phase).1
  | .finished a _ => ⟨P.output a,.ordinary⟩

theorem selected_eq_bit_payload (q : Config L M ell S X A) :
    selected P stop q=if selectionBit P stop q then some (selectionPayload P q) else none := by
  cases q with
  | ready n a s =>
    by_cases hs : stop s=true <;> by_cases hn : n=0 <;> by_cases hh : P.mode a=0 <;> by_cases ht : P.mode a=1 <;>
      simp [selected,selectionBit,selectionPayload,hs,hn,hh,ht]
  | pending n a output phase => rfl
  | finished a s => rfl

theorem selectionBit_measurable : Measurable (selectionBit (A := A) P stop) := by
  have h : Measurable (fun q : Unit × Config L M ell S X A => selectionBit P stop q.2) := by
    apply measurable_config_cases (fun _ q => selectionBit P stop q)
    · have hfixed : Measurable (fun q : (Unit × S) × (ℕ × State L M ell) =>
          selectionBit P stop (Config.ready (Action := A) q.2.1 q.1.2 q.2.2)) := by
        apply measurable_from_prod_countable
        rintro ⟨n,s⟩
        exact (measurable_of_countable (fun k : Fin 4 =>
          if stop s then false else if n=0 ∨ k=0 then true else decide (k≠1))).comp
            (P.mode_measurable.comp measurable_snd)
      exact hfixed.comp ((measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    · exact measurable_const
    · exact measurable_const
  exact h.comp ((measurable_const (a := ())).prodMk measurable_id)

theorem selectionPayload_measurable : Measurable (selectionPayload (L := L) (M := M) (ell := ell) (A := A) P) := by
  have h : Measurable (fun q : Unit × Config L M ell S X A => selectionPayload P q.2) := by
    apply measurable_config_cases (fun _ q => selectionPayload P q)
    · have hfixed : Measurable (fun q : (Unit × S) × (ℕ × State L M ell) =>
          selectionPayload P (Config.ready (Action := A) q.2.1 q.1.2 q.2.2)) := by
        apply measurable_from_prod_countable
        rintro ⟨n,s⟩
        have hm : Measurable (fun q : Unit × S => P.mode q.2) := P.mode_measurable.comp measurable_snd
        have hout := measurable_pending_mk (P.output_measurable.comp (measurable_snd (α := Unit)))
          (measurable_const (a := Kind.ordinary))
        have hquery : Measurable (fun q : Unit × S =>
            Pending.mk (P.point q.2) (if P.mode q.2=2 then .ordinary else .rich)) :=
          measurable_pending_mk (P.point_measurable.comp (measurable_snd (α := Unit)))
          (Measurable.ite (hm (measurableSet_singleton 2))
            (measurable_const (a := Kind.ordinary)) (measurable_const (a := Kind.rich)))
        by_cases hn : n=0
        · simpa only [selectionPayload,hn,true_or,if_true] using hout
        · simpa only [selectionPayload,hn,false_or] using
            Measurable.ite (hm (measurableSet_singleton 0)) hout hquery
      exact hfixed.comp ((measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    · exact measurable_fst.comp ((phaseMeasurableEquiv L M ell X A).measurable.comp (by fun_prop))
    · exact measurable_pending_mk (P.output_measurable.comp (by fun_prop)) measurable_const
  exact h.comp ((measurable_const (a := ())).prodMk measurable_id)

def schedule (trajectory : ℕ → Ω → Config L M ell S X A) (fuel : ℕ) :
    ControllerOptionalTrajectory.Schedule Ω X :=
  (List.range fuel).map (fun i =>
    ((fun w => selectionBit P stop (trajectory i w)),fun w => selectionPayload P (trajectory i w)))

theorem schedule_measurable [MeasurableSpace Ω]
    (trajectory : ℕ → Ω → Config L M ell S X A) (ht : ∀ i,Measurable (trajectory i)) (fuel : ℕ) :
    ControllerOptionalTrajectory.IsMeasurable (schedule P stop trajectory fuel) := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  exact ⟨(selectionBit_measurable P stop).comp (ht i),(selectionPayload_measurable P).comp (ht i)⟩

theorem schedule_selected (trajectory : ℕ → Ω → Config L M ell S X A) (fuel : ℕ) (w : Ω) :
    ControllerOptionalTrajectory.selected (schedule P stop trajectory fuel) w=
      (List.range fuel).filterMap (fun i => selected P stop (trajectory i w)) := by
  have h (is : List ℕ) : ControllerOptionalTrajectory.selected
      (is.map (fun i => ((fun w => selectionBit P stop (trajectory i w)),fun w => selectionPayload P (trajectory i w)))) w=
        is.filterMap (fun i => selected P stop (trajectory i w)) := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_cons,ControllerOptionalTrajectory.selected,List.filterMap_cons]
      rw [selected_eq_bit_payload P stop (trajectory i w)]
      cases hb : selectionBit P stop (trajectory i w) <;> simp [hb,ih]
  exact h _

/-- The list uses an atomic continuation of the final selected query even
if the guarded driver stops during its repairs. This preserves the sharp
bound and includes any node already visible before that stopping point. -/
def visiblePoints (R : Rules L M ell X A) (v : Node L)
    (trajectory : ℕ → Ω → Config L M ell S X A) (fuel : ℕ) (w : Ω) (s : State L M ell) : List X :=
  seenPoints R v (ControllerOptionalTrajectory.selected (schedule P stop trajectory fuel) w) s

theorem visiblePoints_length_le (R : Rules L M ell X A) (v : Node L)
    (trajectory : ℕ → Ω → Config L M ell S X A) (fuel : ℕ) (w : Ω)
    {s : State L M ell} (hs : TaskSlots.Ready s) (hell : 0<ell) :
    (visiblePoints P stop R v trajectory fuel w s).length ≤ 8^(L-v.1.val)*M*ell :=
  seenPoints_length_le R v _ hs hell

end GradientHessian.ControllerPolicyDriver
