import GradientHessian.ControllerRepairRealization

/-! Actual repair events in the original policy trace are realized at a
chosen repairing phase before a fixed coefficient-independent time cap. -/

noncomputable section
namespace GradientHessian.ControllerActionRealization
open Classical TaskState ComparisonController ControllerPolicyDriver
  ControllerPolicyExecution ControllerRepairEvents ControllerRepairRealization

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem action_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (Inv : State L M ell → Prop)
    (hInv : ∀ s,Inv s → ∀ p,Inv (serve R p s).afterNormal)
    (ho : ∀ s,Inv s → ∀ p,ordinary (serve R p s).beforeNormal (serve R p s).afterNormal p.point=o p.point)
    (hr : ∀ s,Inv s → ∀ p,rich (serve R p s).beforeNormal (serve R p s).afterNormal p.point=r p.point)
    (N : ℕ) (algorithm : S) (s : State L M ell) (hs : Inv s) (a : A)
    (ha : a ∈ actions R (queriesFrom P o r N algorithm) s) :
    ∃ i<(N+1)*(8^L+4), ∃ n b output p u,
      run P R (fun _ => false) ordinary rich i (.ready N algorithm s)=
        .pending n b output (.repairing p u) ∧ choose R p u=some a := by
  induction N generalizing algorithm s with
  | zero =>
    have hm : a ∈ pointActions R ⟨P.output algorithm,.ordinary⟩ (8^L) s := by
      simpa only [queriesFrom,actions,List.append_nil] using ha
    obtain ⟨i,hi,u,hu,hchoose⟩ := output_action_realized P R ordinary rich 0 algorithm s a (Or.inl rfl) hm
    refine ⟨i,?_,0,algorithm,true,⟨P.output algorithm,.ordinary⟩,u,hu,hchoose⟩
    simpa only [Nat.zero_add,Nat.one_mul] using hi.trans_le (Nat.add_le_add_left (by decide : 1≤4) _)
  | succ N ih =>
    by_cases hhalt : P.mode algorithm=0
    · have hm : a ∈ pointActions R ⟨P.output algorithm,.ordinary⟩ (8^L) s := by
        simpa only [queriesFrom_halt P o r _ algorithm hhalt,actions,List.append_nil] using ha
      obtain ⟨i,hi,u,hu,hchoose⟩ := output_action_realized P R ordinary rich (N+1) algorithm s a (Or.inr hhalt) hm
      refine ⟨i,?_,N+1,algorithm,true,⟨P.output algorithm,.ordinary⟩,u,hu,hchoose⟩
      exact (hi.trans_le (Nat.add_le_add_left (by decide : 1≤4) _)).trans_le
        (Nat.le_mul_of_pos_left _ (by omega))
    · by_cases hthink : P.mode algorithm=1
      · have h2 : P.mode algorithm≠2 := by omega
        have h3 : P.mode algorithm≠3 := by omega
        have hstep : P.step o r algorithm=P.think algorithm := by simp [Machine.Policy.step,hthink]
        have hm : a ∈ actions R (queriesFrom P o r N (P.think algorithm)) s := by
          simpa only [queriesFrom,ControllerPolicyTrace.selected,if_neg h2,if_neg h3,hstep,List.nil_append] using ha
        obtain ⟨i,hi,n,b,output,p,u,hu,hchoose⟩ := ih (P.think algorithm) s hs hm
        refine ⟨1+i,?_,n,b,output,p,u,?_,hchoose⟩
        · calc
            1+i < (8^L+4)+(N+1)*(8^L+4) :=
              Nat.add_lt_add_of_le_of_lt ((by decide : 1≤4).trans (Nat.le_add_left 4 (8^L))) hi
            _ = (N+1+1)*(8^L+4) := by ring
        · rw [run_add]
          have hfirst : run P R (fun _ => false) ordinary rich 1 (.ready (N+1) algorithm s)=
              .ready N (P.think algorithm) s := by simp [run,step,hthink]
          rw [hfirst]
          exact hu
      · have hquery : P.mode algorithm=2 ∨ P.mode algorithm=3 := by omega
        let p₀ := queryPoint P algorithm
        have hp : ControllerPolicyTrace.selected P algorithm=[p₀] := by
          rcases hquery with hq|hq <;> simp [p₀,queryPoint,ControllerPolicyTrace.selected,hq]
        have hm : a ∈ pointActions R p₀ (8^L) s ∨
            a ∈ actions R (queriesFrom P o r N (P.step o r algorithm)) (serve R p₀ s).afterNormal := by
          simpa only [queriesFrom,hp,List.singleton_append,actions,List.mem_append] using ha
        rcases hm with hfirst|htail
        · obtain ⟨i,hi,u,hu,hchoose⟩ := query_action_realized P R ordinary rich N algorithm s a hquery hfirst
          refine ⟨i,?_,N+1,algorithm,false,p₀,u,hu,hchoose⟩
          exact (hi.trans_le (Nat.add_le_add_left (by decide : 1≤4) _)).trans_le
            (Nat.le_mul_of_pos_left _ (by omega))
        · obtain ⟨i,hi,n,b,output,p,u,hu,hchoose⟩ := ih (P.step o r algorithm)
            (serve R p₀ s).afterNormal (hInv s hs p₀) htail
          refine ⟨(serve R p₀ s).repairs.length+4+i,?_,n,b,output,p,u,?_,hchoose⟩
          · calc
              (serve R p₀ s).repairs.length+4+i < (8^L+4)+(N+1)*(8^L+4) :=
                Nat.add_lt_add_of_le_of_lt (Nat.add_le_add_right (serve_repairs_length R p₀ s) 4) hi
              _ = (N+1+1)*(8^L+4) := by ring
          · rw [run_add,query_execution P R o r ordinary rich N algorithm s hquery
              (ho s hs p₀) (hr s hs p₀)]
            exact hu

theorem original_action_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (o : X → Y) (r : X → Z)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (Inv : State L M ell → Prop)
    (hInv : ∀ s,Inv s → ∀ p,Inv (serve R p s).afterNormal)
    (ho : ∀ s,Inv s → ∀ p,ordinary (serve R p s).beforeNormal (serve R p s).afterNormal p.point=o p.point)
    (hr : ∀ s,Inv s → ∀ p,rich (serve R p s).beforeNormal (serve R p s).afterNormal p.point=r p.point)
    (N : ℕ) (seed : Seed) (s : State L M ell) (hs : Inv s) (a : A)
    (ha : a ∈ actions R (ControllerPolicyTrace.withOutput P o r N seed) s) :
    ∃ i<(N+1)*(8^L+4), ∃ n b output p u,
      run P R (fun _ => false) ordinary rich i (ControllerPolicyDriver.initial P N seed s)=
        .pending n b output (.repairing p u) ∧ choose R p u=some a := by
  apply action_realized P R o r ordinary rich Inv hInv ho hr N (P.initial seed) s hs a
  simpa only [queriesFrom_initial] using ha

end GradientHessian.ControllerActionRealization
