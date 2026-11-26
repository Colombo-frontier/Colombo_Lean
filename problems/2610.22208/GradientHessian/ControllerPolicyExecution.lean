import GradientHessian.ControllerPolicyCoupling
import GradientHessian.ControllerPolicyTrace

/-! Exact execution of the original policy by the phase driver. A finite
instruction cutoff appends one ordinary output. Internal repair time is
bounded independently of the raw coefficients and policy replies. -/

noncomputable section
namespace GradientHessian.ControllerPolicyExecution
open Classical TaskState ComparisonController ControllerPolicyDriver

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def advance (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z) : ℕ → S → S
  | 0,a => a
  | n+1,a => advance P o r n (P.step o r a)

def traceFrom (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z) : ℕ → S → List (Pending X)
  | 0,_ => []
  | n+1,a => ControllerPolicyTrace.selected P a ++ traceFrom P o r n (P.step o r a)

def queriesFrom (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z) : ℕ → S → List (Pending X)
  | 0,a => [⟨P.output a,.ordinary⟩]
  | n+1,a => ControllerPolicyTrace.selected P a ++ queriesFrom P o r n (P.step o r a)

theorem advance_succ_end (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (a : S) : advance P o r (n+1) a=P.step o r (advance P o r n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact ih (P.step o r a)

theorem advance_initial (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (seed : Seed) : advance P o r n (P.initial seed)=P.run o r n seed := by
  induction n with
  | zero => rfl
  | succ n ih => rw [advance_succ_end,ih]; rfl

theorem traceFrom_succ_end (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (a : S) : traceFrom P o r (n+1) a=
      traceFrom P o r n a ++ ControllerPolicyTrace.selected P (advance P o r n a) := by
  induction n generalizing a with
  | zero => simp [traceFrom,advance]
  | succ n ih =>
    change ControllerPolicyTrace.selected P a ++ traceFrom P o r (n+1) (P.step o r a)=
      (ControllerPolicyTrace.selected P a ++ traceFrom P o r n (P.step o r a)) ++
        ControllerPolicyTrace.selected P (advance P o r n (P.step o r a))
    rw [ih,List.append_assoc]

theorem traceFrom_initial (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (seed : Seed) : traceFrom P o r n (P.initial seed)=ControllerPolicyTrace.trace P o r n seed := by
  induction n with
  | zero => rfl
  | succ n ih => rw [traceFrom_succ_end,ih,advance_initial]; rfl

theorem queriesFrom_eq (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (a : S) : queriesFrom P o r n a=
      traceFrom P o r n a ++ [⟨P.output (advance P o r n a),.ordinary⟩] := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [queriesFrom,traceFrom,advance,ih,List.append_assoc]

theorem queriesFrom_initial (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (seed : Seed) : queriesFrom P o r n (P.initial seed)=ControllerPolicyTrace.withOutput P o r n seed := by
  rw [queriesFrom_eq,traceFrom_initial,advance_initial]
  rfl

theorem advance_halt (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (a : S) (ha : P.mode a=0) : advance P o r n a=a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [advance,P.step_of_halt o r ha] using ih

theorem queriesFrom_halt (P : Machine.Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (n : ℕ) (a : S) (ha : P.mode a=0) : queriesFrom P o r n a=[⟨P.output a,.ordinary⟩] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [queriesFrom,ControllerPolicyTrace.selected,ha,Machine.Policy.step] using ih

def queryPoint (P : Machine.Policy Seed S X Y Z) (a : S) : Pending X :=
  ⟨P.point a,if P.mode a=2 then .ordinary else .rich⟩

theorem query_execution (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (s : State L M ell) (ha : P.mode a=2 ∨ P.mode a=3)
    (ho : ordinary (serve R (queryPoint P a) s).beforeNormal (serve R (queryPoint P a) s).afterNormal
      (P.point a)=o (P.point a))
    (hr : rich (serve R (queryPoint P a) s).beforeNormal (serve R (queryPoint P a) s).afterNormal
      (P.point a)=r (P.point a)) :
    run P R (fun _ => false) ordinary rich ((serve R (queryPoint P a) s).repairs.length+4)
      (.ready (n+1) a s)=.ready n (P.step o r a) (serve R (queryPoint P a) s).afterNormal := by
  rw [show (serve R (queryPoint P a) s).repairs.length+4=
    1+((serve R (queryPoint P a) s).repairs.length+3) by omega,run_add]
  have hs : run P R (fun _ => false) ordinary rich 1 (.ready (n+1) a s)=
      .pending (n+1) a false (.repairing (queryPoint P a) s) := by
    rcases ha with ha|ha <;> simp [run,step,queryPoint,ha]
  rw [hs,serve_delivery]
  rcases ha with ha|ha <;> simp [queryPoint,ha] at ho hr <;>
    simp [deliver,queryPoint,ha,ho,hr,Machine.Policy.step]

theorem output_execution (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (n : ℕ) (a : S) (s : State L M ell) (ha : n=0 ∨ P.mode a=0) :
    run P R (fun _ => false) ordinary rich ((serve R ⟨P.output a,.ordinary⟩ s).repairs.length+4)
      (.ready n a s)=.finished a (serve R ⟨P.output a,.ordinary⟩ s).afterNormal := by
  rw [show (serve R ⟨P.output a,.ordinary⟩ s).repairs.length+4=
    1+((serve R ⟨P.output a,.ordinary⟩ s).repairs.length+3) by omega,run_add]
  have hs : run P R (fun _ => false) ordinary rich 1 (.ready n a s)=
      .pending n a true (.repairing ⟨P.output a,.ordinary⟩ s) := by simp [run,step,ha]
  rw [hs,serve_delivery]
  rfl

theorem execution_exists (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (Inv : State L M ell → Prop)
    (hInv : ∀ s,Inv s → ∀ p,Inv (serve R p s).afterNormal)
    (ho : ∀ s,Inv s → ∀ p,ordinary (serve R p s).beforeNormal (serve R p s).afterNormal p.point=o p.point)
    (hr : ∀ s,Inv s → ∀ p,rich (serve R p s).beforeNormal (serve R p s).afterNormal p.point=r p.point)
    (N : ℕ) (a : S) (s : State L M ell) (hs : Inv s) :
    ∃ fuel≤(N+1)*(8^L+4),
      run P R (fun _ => false) ordinary rich fuel (.ready N a s)=
        .finished (advance P o r N a) (VisibilityWindow.run R (queriesFrom P o r N a) s) := by
  induction N generalizing a s with
  | zero =>
    refine ⟨(serve R ⟨P.output a,.ordinary⟩ s).repairs.length+4,?_,?_⟩
    · have hb := serve_repairs_length R ⟨P.output a,.ordinary⟩ s
      simpa only [Nat.zero_add,Nat.one_mul] using Nat.add_le_add_right hb 4
    · simpa only [advance,queriesFrom,VisibilityWindow.run] using
        output_execution P R ordinary rich 0 a s (Or.inl rfl)
  | succ N ih =>
    by_cases hhalt : P.mode a=0
    · refine ⟨(serve R ⟨P.output a,.ordinary⟩ s).repairs.length+4,?_,?_⟩
      · have hb := serve_repairs_length R ⟨P.output a,.ordinary⟩ s
        have hmul : 8^L+4≤(N+1+1)*(8^L+4) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      · simpa only [advance_halt P o r _ a hhalt,queriesFrom_halt P o r _ a hhalt,
          VisibilityWindow.run] using output_execution P R ordinary rich (N+1) a s (Or.inr hhalt)
    · by_cases hthink : P.mode a=1
      · obtain ⟨fuel,hfuel,he⟩ := ih (P.think a) s hs
        refine ⟨1+fuel,?_,?_⟩
        · calc
            1+fuel ≤ (8^L+4)+(N+1)*(8^L+4) :=
              Nat.add_le_add ((by decide : 1≤4).trans (Nat.le_add_left 4 (8^L))) hfuel
            _ = (N+1+1)*(8^L+4) := by ring
        · rw [run_add]
          have hfirst : run P R (fun _ => false) ordinary rich 1 (.ready (N+1) a s)=
              .ready N (P.think a) s := by simp [run,step,hthink]
          rw [hfirst,he]
          have h2 : P.mode a≠2 := by omega
          have h3 : P.mode a≠3 := by omega
          have hstep : P.step o r a=P.think a := by simp [Machine.Policy.step,hthink]
          simp only [advance,queriesFrom,ControllerPolicyTrace.selected,if_neg h2,if_neg h3,hstep,List.nil_append]
      · have hquery : P.mode a=2 ∨ P.mode a=3 := by omega
        let p := queryPoint P a
        obtain ⟨fuel,hfuel,he⟩ := ih (P.step o r a) (serve R p s).afterNormal (hInv s hs p)
        refine ⟨(serve R p s).repairs.length+4+fuel,?_,?_⟩
        · have hb := serve_repairs_length R p s
          simp only [Nat.add_mul,Nat.one_mul] at *
          omega
        · rw [run_add,query_execution P R o r ordinary rich N a s hquery (ho s hs p) (hr s hs p),he]
          have hp : ControllerPolicyTrace.selected P a=[p] := by
            rcases hquery with hq|hq <;> simp [p,queryPoint,ControllerPolicyTrace.selected,hq]
          simp only [advance,queriesFrom,hp,List.singleton_append,VisibilityWindow.run]

theorem execution_fixed_fuel (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (Inv : State L M ell → Prop)
    (hInv : ∀ s,Inv s → ∀ p,Inv (serve R p s).afterNormal)
    (ho : ∀ s,Inv s → ∀ p,ordinary (serve R p s).beforeNormal (serve R p s).afterNormal p.point=o p.point)
    (hr : ∀ s,Inv s → ∀ p,rich (serve R p s).beforeNormal (serve R p s).afterNormal p.point=r p.point)
    (N : ℕ) (a : S) (s : State L M ell) (hs : Inv s) :
    run P R (fun _ => false) ordinary rich ((N+1)*(8^L+4)) (.ready N a s)=
      .finished (advance P o r N a) (VisibilityWindow.run R (queriesFrom P o r N a) s) := by
  obtain ⟨fuel,hfuel,he⟩ := execution_exists P R o r ordinary rich Inv hInv ho hr N a s hs
  rw [show (N+1)*(8^L+4)=fuel+((N+1)*(8^L+4)-fuel) by omega,run_add,he,run_finished]

theorem original_policy_execution (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (Inv : State L M ell → Prop)
    (hInv : ∀ s,Inv s → ∀ p,Inv (serve R p s).afterNormal)
    (ho : ∀ s,Inv s → ∀ p,ordinary (serve R p s).beforeNormal (serve R p s).afterNormal p.point=o p.point)
    (hr : ∀ s,Inv s → ∀ p,rich (serve R p s).beforeNormal (serve R p s).afterNormal p.point=r p.point)
    (N : ℕ) (seed : Seed) (s : State L M ell) (hs : Inv s) :
    run P R (fun _ => false) ordinary rich ((N+1)*(8^L+4)) (ControllerPolicyDriver.initial P N seed s)=
      .finished (P.run o r N seed) (VisibilityWindow.run R (ControllerPolicyTrace.withOutput P o r N seed) s) := by
  simpa only [ControllerPolicyDriver.initial,advance_initial,queriesFrom_initial] using
    execution_fixed_fuel P R o r ordinary rich Inv hInv ho hr N (P.initial seed) s hs

end GradientHessian.ControllerPolicyExecution
