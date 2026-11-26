import GradientHessian.ControllerStoppedAction

/-! Chronological execution for arbitrary receipt-dependent replies.
Unlike a fixed oracle, these replies may contain raw disclosures from the
public controller state. Every selected output is processed exactly once. -/

noncomputable section
namespace GradientHessian.ControllerAdaptiveExecution
open Classical TaskState TaskSlots ComparisonController ComparisonControllerReplay
  ControllerPolicyDriver ControllerRepairEvents ControllerRepairRealization ControllerDriverMonotonicity

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

def replyNext (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) (a : S) (s : State L M ell) : S :=
  let c := serve R (ControllerPolicyExecution.queryPoint P a) s
  if P.mode a=2 then P.ordinaryNext (a,ordinary c.beforeNormal c.afterNormal (P.point a))
  else P.richNext (a,rich c.beforeNormal c.afterNormal (P.point a))

def queries (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z) : ℕ → S → State L M ell → List (Pending X)
  | 0,a,_ => [⟨P.output a,.ordinary⟩]
  | N+1,a,s => if P.mode a=0 then [⟨P.output a,.ordinary⟩]
    else if P.mode a=1 then queries P R ordinary rich N (P.think a) s
    else ControllerPolicyExecution.queryPoint P a ::
      queries P R ordinary rich N (replyNext P R ordinary rich a s)
        (serve R (ControllerPolicyExecution.queryPoint P a) s).afterNormal

theorem query_execution (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (a : S) (s : State L M ell) (ha : P.mode a=2 ∨ P.mode a=3) :
    run P R (fun _ => false) ordinary rich
      ((serve R (ControllerPolicyExecution.queryPoint P a) s).repairs.length+4) (.ready (N+1) a s)=
      .ready N (replyNext P R ordinary rich a s) (serve R (ControllerPolicyExecution.queryPoint P a) s).afterNormal := by
  rw [show (serve R (ControllerPolicyExecution.queryPoint P a) s).repairs.length+4=
    1+((serve R (ControllerPolicyExecution.queryPoint P a) s).repairs.length+3) by omega,run_add]
  have hs : run P R (fun _ => false) ordinary rich 1 (.ready (N+1) a s)=
      .pending (N+1) a false (.repairing (ControllerPolicyExecution.queryPoint P a) s) := by
    rcases ha with ha|ha <;> simp [run,step,ControllerPolicyExecution.queryPoint,ha]
  rw [hs,serve_delivery]
  rcases ha with ha|ha <;> simp [deliver,ControllerPolicyExecution.queryPoint,ha,replyNext]

theorem action_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (algorithm : S) (s : State L M ell) (a : A)
    (ha : a ∈ actions R (queries P R ordinary rich N algorithm s) s) :
    ∃ i<(N+1)*(8^L+4), ∃ n b output p u,
      run P R (fun _ => false) ordinary rich i (.ready N algorithm s)=
        .pending n b output (.repairing p u) ∧ choose R p u=some a := by
  induction N generalizing algorithm s with
  | zero =>
    have hm : a ∈ pointActions R ⟨P.output algorithm,.ordinary⟩ (8^L) s := by
      simpa only [queries,actions,List.append_nil] using ha
    obtain ⟨i,hi,u,hu,hchoose⟩ := output_action_realized P R ordinary rich 0 algorithm s a (Or.inl rfl) hm
    refine ⟨i,?_,0,algorithm,true,⟨P.output algorithm,.ordinary⟩,u,hu,hchoose⟩
    simpa only [Nat.zero_add,Nat.one_mul] using hi.trans_le (Nat.add_le_add_left (by decide : 1≤4) _)
  | succ N ih =>
    by_cases hhalt : P.mode algorithm=0
    · have hm : a ∈ pointActions R ⟨P.output algorithm,.ordinary⟩ (8^L) s := by
        simpa only [queries,if_pos hhalt,actions,List.append_nil] using ha
      obtain ⟨i,hi,u,hu,hchoose⟩ := output_action_realized P R ordinary rich (N+1) algorithm s a (Or.inr hhalt) hm
      refine ⟨i,?_,N+1,algorithm,true,⟨P.output algorithm,.ordinary⟩,u,hu,hchoose⟩
      exact (hi.trans_le (Nat.add_le_add_left (by decide : 1≤4) _)).trans_le
        (Nat.le_mul_of_pos_left _ (by omega))
    · by_cases hthink : P.mode algorithm=1
      · have hm : a ∈ actions R (queries P R ordinary rich N (P.think algorithm) s) s := by
          simpa only [queries,if_neg hhalt,if_pos hthink] using ha
        obtain ⟨i,hi,n,b,output,p,u,hu,hchoose⟩ := ih (P.think algorithm) s hm
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
        let p₀ := ControllerPolicyExecution.queryPoint P algorithm
        have hm : a ∈ pointActions R p₀ (8^L) s ∨
            a ∈ actions R (queries P R ordinary rich N (replyNext P R ordinary rich algorithm s)
              (serve R p₀ s).afterNormal) (serve R p₀ s).afterNormal := by
          simpa only [queries,if_neg hhalt,if_neg hthink,actions,List.mem_append] using ha
        rcases hm with hfirst|htail
        · obtain ⟨i,hi,u,hu,hchoose⟩ := query_action_realized P R ordinary rich N algorithm s a hquery hfirst
          refine ⟨i,?_,N+1,algorithm,false,p₀,u,hu,hchoose⟩
          exact (hi.trans_le (Nat.add_le_add_left (by decide : 1≤4) _)).trans_le
            (Nat.le_mul_of_pos_left _ (by omega))
        · obtain ⟨i,hi,n,b,output,p,u,hu,hchoose⟩ := ih (replyNext P R ordinary rich algorithm s)
            (serve R p₀ s).afterNormal htail
          refine ⟨(serve R p₀ s).repairs.length+4+i,?_,n,b,output,p,u,?_,hchoose⟩
          · calc
              (serve R p₀ s).repairs.length+4+i < (8^L+4)+(N+1)*(8^L+4) :=
                Nat.add_lt_add_of_le_of_lt (Nat.add_le_add_right (serve_repairs_length R p₀ s) 4) hi
              _ = (N+1+1)*(8^L+4) := by ring
          · rw [run_add,query_execution P R ordinary rich N algorithm s hquery]
            exact hu

theorem action_has_shadow_hit (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (a : A) (blocked : A → Bool) (hb : blocked a=true) (stop : State L M ell → Bool)
    (hretire : ∀ s,Ready s → ∀ b,stop s=true → stop (retireNode s (R.target b))=true)
    (hnormal : ∀ s,Ready s → ∀ p,stop s=true → stop (normal R p s)=true)
    (hchosen : ∀ p s,choose R p s=some a → stop s=false)
    (hell : 0<ell) (N : ℕ) (algorithm : S) (s : State L M ell) (hs : Ready s)
    (ha : a ∈ actions R (queries P R ordinary rich N algorithm s) s) :
    ∃ j<(N+1)*(8^L+4), ControllerPolicyCoupling.BlockedHit R blocked stop
      (run P (suppress R blocked) stop ordinary rich j (.ready N algorithm s)) := by
  obtain ⟨i,hi,n,b,output,p,u,hu,hchoose⟩ := action_realized P R ordinary rich N algorithm s a ha
  have hphase : run P R stop ordinary rich i (.ready N algorithm s)=.pending n b output (.repairing p u) := by
    have he := guarded_eq_at_open_endpoint P R stop ordinary rich hell hretire hnormal
      (.ready N algorithm s) hs i
      (show stop (stateOf (run P R (fun _ => false) ordinary rich i (.ready N algorithm s)))=false from by
        rw [hu]
        exact hchosen p u hchoose)
    exact he.trans hu
  obtain ⟨j,hj,hjhit⟩ := ControllerPolicyCoupling.chosen_blocked_has_shadow_hit P R blocked stop ordinary rich
    (.ready N algorithm s) i n b output p u a hphase (hchosen p u hchoose) hchoose hb
  exact ⟨j,hj.trans_lt hi,hjhit⟩

end GradientHessian.ControllerAdaptiveExecution
