import GradientHessian.ControllerPolicyMeasurability
import GradientHessian.ControllerDriverMonotonicity

/-! Observable instruction selection for the charged numerical compiler.
Only a genuine open target-leaf ordinary delivery asks for Ay. Pending
points survive repairs, and prior readout requests inspect finite counters
and cache occupancy without consulting the hidden matrix. -/

noncomputable section
namespace GradientHessian.NumericalDriverInstructions
open Classical FrontierState TaskState ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerDriverMonotonicity ControllerMeasurable

variable {L M ell : ℕ} {S X A : Type*}
variable [MeasurableSpace S] [MeasurableSpace X]

def finished : Config L M ell S X A → Bool
  | .finished _ _ => true
  | _ => false

def point [Zero X] : Config L M ell S X A → X
  | .pending _ _ _ phase => (phaseEquiv L M ell X A phase).1.point
  | _ => 0

def product (leaf : Leaf L) (stop : State L M ell → Bool) : Config L M ell S X A → Bool
  | .pending _ _ output (.delivered p before after) =>
      decide (output=false ∧ p.kind=.ordinary ∧ stop before=false ∧ stop after=false ∧
        TaskState.current before=some leaf)
  | _ => false

def readoutIndex (leaf : Leaf L) (j : Fin M) (loaded : Fin M → Bool)
    (s : State L M ell) : Option (Fin M) :=
  if hc : TaskState.current s=some leaf then
    let k : Fin M := ⟨(s.completed leaf).val,current_live s hc⟩
    if k<j ∧ loaded k=false then some k else none
  else none

theorem readoutIndex_lt (leaf : Leaf L) (j : Fin M) (loaded : Fin M → Bool)
    (s : State L M ell) (k : Fin M) (h : readoutIndex leaf j loaded s=some k) : k<j ∧ loaded k=false := by
  by_cases hc : TaskState.current s=some leaf
  · rw [readoutIndex,dif_pos hc] at h
    dsimp only at h
    split_ifs at h with hk
    · cases Option.some.inj h
      exact hk
  · simp only [readoutIndex,dif_neg hc] at h
    cases h

theorem readoutIndex_current (leaf : Leaf L) (j : Fin M) (loaded : Fin M → Bool)
    (s : State L M ell) (k : Fin M) (h : readoutIndex leaf j loaded s=some k) :
    TaskState.current s=some leaf ∧ k.val=(s.completed leaf).val := by
  by_cases hc : TaskState.current s=some leaf
  · rw [readoutIndex,dif_pos hc] at h
    dsimp only at h
    split_ifs at h with hk
    · cases Option.some.inj h
      exact ⟨hc,rfl⟩
  · simp only [readoutIndex,dif_neg hc] at h
    cases h

theorem product_iff (leaf : Leaf L) (stop : State L M ell → Bool) (q : Config L M ell S X A) :
    product leaf stop q=true ↔ ∃ n a p before after,
      q=.pending n a false (.delivered p before after) ∧ p.kind=.ordinary ∧
        stop before=false ∧ stop after=false ∧ TaskState.current before=some leaf := by
  cases q with
  | ready n a s => simp [product]
  | finished a s => simp [product]
  | pending n a output phase =>
    cases phase with
    | repairing p s => simp [product]
    | normal p s => simp [product]
    | frozen p s => simp [product]
    | delivered p before after =>
      simp only [product,decide_eq_true_eq,Config.pending.injEq,Phase.delivered.injEq]
      constructor
      · rintro ⟨ho,hkind,hbefore,hafter,hcur⟩
        exact ⟨n,a,p,before,after,⟨rfl,rfl,ho,rfl,rfl,rfl⟩,hkind,hbefore,hafter,hcur⟩
      · rintro ⟨n',a',p',before',after',⟨hn,ha,ho,hp,hb,he⟩,hk,hstop,hstop',hc⟩
        subst n'; subst a'; subst p'; subst before'; subst after'
        exact ⟨ho,hk,hstop,hstop',hc⟩

theorem stateOf_measurable : Measurable (stateOf (L := L) (M := M) (ell := ell) (S := S) (X := X) (A := A)) := by
  have hh : Measurable (fun q : Unit × Config L M ell S X A => stateOf q.2) := by
    apply measurable_config_cases (fun (_ : Unit) q => stateOf q)
    · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
    · have hp : Measurable (fun q : Unit × PendingData L M ell S X A =>
          phaseEquiv L M ell X A q.2.2.2.2) := (phaseMeasurableEquiv L M ell X A).measurable.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      let f : PhaseData L M ell → State L M ell := fun z => match z with
        | .inl s | .inr (.inl s) | .inr (.inr (.inr s)) => s
        | .inr (.inr (.inl (_,after))) => after
      have h := (measurable_of_countable f).comp (measurable_snd.comp hp)
      convert h using 1
      funext q
      rcases q with ⟨u,n,a,o,phase⟩
      cases phase <;> rfl
    · exact measurable_snd.comp measurable_snd
  exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)

theorem finished_measurable : Measurable (finished (L := L) (M := M) (ell := ell) (S := S) (X := X) (A := A)) := by
  have hh : Measurable (fun q : Unit × Config L M ell S X A => finished q.2) := by
    apply measurable_config_cases (fun (_ : Unit) q => finished q) <;> exact measurable_const
  exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)

theorem point_measurable [Zero X] : Measurable (point (L := L) (M := M) (ell := ell) (S := S) (X := X) (A := A)) := by
  have hh : Measurable (fun q : Unit × Config L M ell S X A => point q.2) := by
    apply measurable_config_cases (fun (_ : Unit) q => point q)
    · exact measurable_const
    · exact measurable_pending_point.comp (measurable_fst.comp
        ((phaseMeasurableEquiv L M ell X A).measurable.comp
          (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
    · exact measurable_const
  exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)

theorem product_measurable (leaf : Leaf L) (stop : State L M ell → Bool) :
    Measurable (product (S := S) (X := X) (A := A) leaf stop) := by
  have hh : Measurable (fun q : Unit × Config L M ell S X A => product leaf stop q.2) := by
    apply measurable_config_cases (fun (_ : Unit) q => product leaf stop q)
    · exact measurable_const
    · have hp : Measurable (fun q : Unit × PendingData L M ell S X A =>
          phaseEquiv L M ell X A q.2.2.2.2) := (phaseMeasurableEquiv L M ell X A).measurable.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      let f : Bool × Kind × PhaseData L M ell → Bool := fun z => match z.2.2 with
        | .inr (.inr (.inl (before,after))) => decide (z.1=false ∧ z.2.1=.ordinary ∧
            stop before=false ∧ stop after=false ∧ TaskState.current before=some leaf)
        | _ => false
      have h := (measurable_of_countable f).comp
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
          ((measurable_pending_kind.comp (measurable_fst.comp hp)).prodMk (measurable_snd.comp hp)))
      convert h using 1
      funext q
      rcases q with ⟨u,n,a,o,phase⟩
      cases phase <;> rfl
    · exact measurable_const
  exact hh.comp ((measurable_const (a := ())).prodMk measurable_id)

end GradientHessian.NumericalDriverInstructions
