import GradientHessian.NumericalDriverInstructions
import GradientHessian.VisibilityTaskWindow

/-! Resource accounting at individual driver transitions, including a saved
pending query. A one-unit pending credit charges delivery without charging
the same ordinary operation twice. -/

noncomputable section
namespace GradientHessian.ControllerDriverResource
open Classical FrontierState TaskState TaskSlots ComparisonController
  ComparisonControllerReplay ControllerPolicyDriver ControllerDriverMonotonicity
  VisibilityWindow VisibilityTaskWindow

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def Good (q : Config L M ell S X A) : Prop := Ready (stateOf q)

variable (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
  (stop : State L M ell → Bool)
  (o : State L M ell → State L M ell → X → Y)
  (v : State L M ell → State L M ell → X → Z)

theorem step_good (hell : 0<ell) (q : Config L M ell S X A) (hq : Good q) :
    Good (step P R stop o v q) := by
  cases q with
  | finished a s => exact hq
  | ready n a s =>
    simp only [step]
    split_ifs <;> exact hq
  | pending n a output phase =>
    cases phase with
    | frozen p s => exact hq
    | delivered p before after =>
      simp only [step,deliver]
      split_ifs <;> try exact hq
      cases p.kind <;> exact hq
    | repairing p s =>
      change Ready s at hq
      cases hs : stop s with
      | true => simpa [step,guardedTick,freeze,hs,tick,Good,stateOf,phaseState] using hq
      | false =>
        cases hc : choose R p s with
        | none => simpa [step,guardedTick,freeze,hs,tick,hc,Good,stateOf,phaseState] using hq
        | some b =>
          have hr := retireSet_ready hq (subtree (R.target b))
          cases ht : stop (retireNode s (R.target b)) <;>
            simpa [step,guardedTick,freeze,hs,tick,hc,ht,Good,stateOf,phaseState] using hr
    | normal p s =>
      change Ready s at hq
      cases hs : stop s with
      | true => simpa [step,guardedTick,freeze,hs,tick,Good,stateOf,phaseState] using hq
      | false =>
        have hr := normal_ready R p hq hell
        cases ht : stop (normal R p s) <;>
          simpa [step,guardedTick,freeze,hs,tick,ht,Good,stateOf,phaseState] using hr

theorem run_good (hell : 0<ell) (q : Config L M ell S X A) (hq : Good q) (N : ℕ) :
    Good (run P R stop o v N q) := by
  induction N generalizing q with
  | zero => exact hq
  | succ N ih => exact ih _ (step_good P R stop o v hell q hq)

def count (test : Config L M ell S X A → ℕ) : ℕ → Config L M ell S X A → ℕ
  | 0,_ => 0
  | N+1,q => test q+count test N (step P R stop o v q)

theorem count_potential (hell : 0<ell)
    (test W : Config L M ell S X A → ℕ)
    (hW : ∀ q,Good q → test q+W q≤W (step P R stop o v q))
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    count P R stop o v test N q+W q≤W (run P R stop o v N q) := by
  induction N generalizing q with
  | zero => simp [count,ControllerPolicyDriver.run]
  | succ N ih =>
    have hh := hW q hq
    have hi := ih _ (step_good P R stop o v hell q hq)
    simp only [count,ControllerPolicyDriver.run]
    omega

theorem count_eq_sum (test : Config L M ell S X A → ℕ)
    (N : ℕ) (q : Config L M ell S X A) :
    count P R stop o v test N q=∑ i∈Finset.range N,test (run P R stop o v i q) := by
  induction N generalizing q with
  | zero => simp [count]
  | succ N ih =>
    rw [count,Finset.sum_range_succ']
    simp only [ControllerPolicyDriver.run,ih]
    omega

def normalBit (qual : State L M ell → Bool) (stop : State L M ell → Bool) :
    Config L M ell S X A → ℕ
  | .pending _ _ _ (.normal p s) =>
      if p.kind=.ordinary ∧ stop s=false ∧ qual s=true then 1 else 0
  | _ => 0

def deliveryBit (qual : State L M ell → Bool) (stop : State L M ell → Bool) :
    Config L M ell S X A → ℕ
  | .pending _ _ output (.delivered p before after) =>
      if output=false ∧ p.kind=.ordinary ∧ stop before=false ∧ stop after=false ∧ qual before=true
      then 1 else 0
  | _ => 0

theorem deliveryBit_le_one (qual : State L M ell → Bool) (q : Config L M ell S X A) :
    deliveryBit qual stop q≤1 := by
  cases q with
  | ready n a s => exact Nat.zero_le _
  | finished a s => exact Nat.zero_le _
  | pending n a output phase =>
    cases phase <;> simp only [deliveryBit]
    all_goals first | omega | (split_ifs <;> omega)

def pendingCredit (qual : State L M ell → Bool) (W : State L M ell → ℕ)
    (q : Config L M ell S X A) : ℕ := W (stateOf q)+(1-deliveryBit qual stop q)

variable (qual : State L M ell → Bool) (W : State L M ell → ℕ)
  (hretire : ∀ s,Ready s → ∀ a,W s≤W (retireNode s (R.target a)))
  (hnormal : ∀ s,Ready s → ∀ p,W s≤W (normal R p s))
  (hprogress : ∀ s,Ready s → ∀ p,p.kind=.ordinary → qual s=true → W s<W (normal R p s))

include hretire hnormal hprogress in
theorem normal_step_credit (q : Config L M ell S X A) (hq : Good q) :
    normalBit qual stop q+W (stateOf q)≤W (stateOf (step P R stop o v q)) := by
  cases q with
  | finished a s => simp [step,normalBit]
  | ready n a s =>
    simp only [step]
    split_ifs <;> simp [normalBit,stateOf,phaseState]
  | pending n a output phase =>
    cases phase with
    | frozen p s => simp [step,normalBit,stateOf,phaseState]
    | delivered p before after =>
      simp only [step,deliver]
      split_ifs <;> try simp [normalBit,stateOf,phaseState]
      cases p.kind <;> simp [normalBit,stateOf,phaseState]
    | repairing p s =>
      change Ready s at hq
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick,normalBit,stateOf,phaseState]
      | false =>
        cases hc : choose R p s with
        | none => simp [step,guardedTick,freeze,hs,tick,hc,normalBit,stateOf,phaseState]
        | some b =>
          have hr := hretire s hq b
          cases ht : stop (retireNode s (R.target b)) <;>
            simpa [step,guardedTick,freeze,hs,tick,hc,ht,normalBit,stateOf,phaseState] using hr
    | normal p s =>
      change Ready s at hq
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick,normalBit,stateOf,phaseState]
      | false =>
        have hr := hnormal s hq p
        have hp : (if p.kind=.ordinary ∧ qual s=true then 1 else 0)+W s≤W (normal R p s) := by
          split_ifs with hh
          · have := hprogress s hq p hh.1 hh.2; omega
          · omega
        cases ht : stop (normal R p s) <;>
          simpa [step,guardedTick,freeze,hs,tick,ht,normalBit,stateOf,phaseState] using hp

include hretire hnormal hprogress in
theorem delivery_step_credit (q : Config L M ell S X A) (hq : Good q) :
    deliveryBit qual stop q+pendingCredit stop qual W q≤
      pendingCredit stop qual W (step P R stop o v q) := by
  cases q with
  | finished a s => simp [step,deliveryBit,pendingCredit]
  | ready n a s =>
    simp only [step]
    split_ifs <;> simp [deliveryBit,pendingCredit,stateOf,phaseState]
  | pending n a output phase =>
    cases phase with
    | frozen p s => simp [step,deliveryBit,pendingCredit,stateOf,phaseState]
    | delivered p before after =>
      have hb := deliveryBit_le_one (A := A) stop qual (Config.pending n a output (.delivered p before after))
      simp only [deliveryBit] at hb
      simp only [step,deliver]
      split_ifs
      all_goals try (simp only [pendingCredit,stateOf,phaseState,deliveryBit,Nat.sub_zero]; omega)
      cases p.kind <;> simp only [pendingCredit,stateOf,phaseState,deliveryBit,Nat.sub_zero] <;> omega
    | repairing p s =>
      change Ready s at hq
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick,deliveryBit,pendingCredit,stateOf,phaseState]
      | false =>
        cases hc : choose R p s with
        | none => simp [step,guardedTick,freeze,hs,tick,hc,deliveryBit,pendingCredit,stateOf,phaseState]
        | some b =>
          have hr := hretire s hq b
          cases ht : stop (retireNode s (R.target b)) <;>
            simpa [step,guardedTick,freeze,hs,tick,hc,ht,deliveryBit,pendingCredit,stateOf,phaseState] using hr
    | normal p s =>
      change Ready s at hq
      cases hs : stop s with
      | true => simp [step,guardedTick,freeze,hs,tick,deliveryBit,pendingCredit,stateOf,phaseState]
      | false =>
        have hr := hnormal s hq p
        cases ht : stop (normal R p s) with
        | true =>
          simpa [step,guardedTick,freeze,hs,tick,ht,deliveryBit,pendingCredit,stateOf,phaseState] using hr
        | false =>
          simp only [step,guardedTick,freeze,hs,ht,Bool.false_eq_true,Bool.or_false,if_false,tick,
            deliveryBit,pendingCredit,stateOf,phaseState]
          split_ifs with hh
          · have hp := hprogress s hq p hh.2.1 hh.2.2.2.2
            omega
          · omega

include hretire hnormal hprogress in
theorem normal_count_bound (hell : 0<ell) (B : ℕ) (hB : ∀ s,Ready s → W s≤B)
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    count P R stop o v (normalBit qual stop) N q≤B := by
  have hc := count_potential P R stop o v hell (normalBit qual stop) (fun z => W (stateOf z))
    (normal_step_credit P R stop o v qual W hretire hnormal hprogress) N q hq
  dsimp only at hc
  have hb := hB _ (run_good P R stop o v hell q hq N)
  omega

include hretire hnormal hprogress in
theorem delivery_count_bound (hell : 0<ell) (B : ℕ) (hB : ∀ s,Ready s → W s≤B)
    (N : ℕ) (q : Config L M ell S X A) (hq : Good q) :
    count P R stop o v (deliveryBit qual stop) N q≤B+1 := by
  have hc := count_potential P R stop o v hell (deliveryBit qual stop) (pendingCredit stop qual W)
    (delivery_step_credit P R stop o v qual W hretire hnormal hprogress) N q hq
  have hb := hB _ (run_good P R stop o v hell q hq N)
  simp only [pendingCredit] at hc
  omega

end GradientHessian.ControllerDriverResource
