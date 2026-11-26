import GradientHessian.ControllerAdaptiveExecution
import GradientHessian.ControllerNormalRealization

/-! Every early retirement in a receipt-adaptive trajectory reaches its
literal normal phase before hit feedback or a reply is returned. -/

noncomputable section
namespace GradientHessian.ControllerAdaptiveEarly
open Classical TaskState ComparisonController ControllerPolicyDriver ControllerPolicyExecution
  ControllerNormalRealization ControllerEarlyEvents ComparisonControllerLedger
open ControllerAdaptiveExecution (queries replyNext)

variable {L M ell : ℕ} {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]

theorem early_realized (P : Machine.Policy Seed S X Y Z) (R : Rules L M ell X A)
    (ordinary : State L M ell → State L M ell → X → Y)
    (rich : State L M ell → State L M ell → X → Z)
    (N : ℕ) (algorithm : S) (s : State L M ell) (q : Task L M)
    (he : 0<count R (queries P R ordinary rich N algorithm s) s q) :
    ∃ i<(N+1)*(8^L+4),∃ n b output p u,
      run P R (fun _ => false) ordinary rich i (.ready N algorithm s)=
        .pending n b output (.normal p u) ∧ IsEarlyFor R p u q := by
  induction N generalizing algorithm s with
  | zero =>
      have hp : earlyFor R ⟨P.output algorithm,.ordinary⟩ s q=1 := by
        have hb := earlyFor_le_one R ⟨P.output algorithm,.ordinary⟩ s q
        simp only [queries,count,tally,Nat.add_zero] at he
        omega
      refine ⟨(serve R ⟨P.output algorithm,.ordinary⟩ s).repairs.length+2,?_,
        0,algorithm,true,⟨P.output algorithm,.ordinary⟩,_,
        output_before_normal P R ordinary rich 0 algorithm s (Or.inl rfl),
        earlyFor_one_before R _ s q hp⟩
      have hb := serve_repairs_length R ⟨P.output algorithm,.ordinary⟩ s
      simpa only [Nat.zero_add,Nat.one_mul] using (by omega :
        (serve R ⟨P.output algorithm,.ordinary⟩ s).repairs.length+2<8^L+4)
  | succ N ih =>
      by_cases hhalt : P.mode algorithm=0
      · have hp : earlyFor R ⟨P.output algorithm,.ordinary⟩ s q=1 := by
          have hb := earlyFor_le_one R ⟨P.output algorithm,.ordinary⟩ s q
          simp only [queries,if_pos hhalt,count,tally,Nat.add_zero] at he
          omega
        refine ⟨(serve R ⟨P.output algorithm,.ordinary⟩ s).repairs.length+2,?_,
          N+1,algorithm,true,⟨P.output algorithm,.ordinary⟩,_,
          output_before_normal P R ordinary rich (N+1) algorithm s (Or.inr hhalt),
          earlyFor_one_before R _ s q hp⟩
        have hb := serve_repairs_length R ⟨P.output algorithm,.ordinary⟩ s
        exact (show (serve R ⟨P.output algorithm,.ordinary⟩ s).repairs.length+2<8^L+4 by omega).trans_le
          (Nat.le_mul_of_pos_left _ (by omega))
      · by_cases hthink : P.mode algorithm=1
        · have hm : 0<count R (queries P R ordinary rich N (P.think algorithm) s) s q := by
            simpa only [queries,if_neg hhalt,if_pos hthink] using he
          obtain ⟨i,hi,n,b,output,p,u,hu,hcost⟩ := ih (P.think algorithm) s hm
          refine ⟨1+i,?_,n,b,output,p,u,?_,hcost⟩
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
          have hm : 0<earlyFor R p₀ s q ∨
              0<count R (queries P R ordinary rich N (replyNext P R ordinary rich algorithm s)
                (serve R p₀ s).afterNormal) (serve R p₀ s).afterNormal q := by
            simp only [queries,if_neg hhalt,if_neg hthink,count,tally] at he
            change 0<earlyFor R p₀ s q ∨
              0<tally R (fun p s => earlyFor R p s q)
                (queries P R ordinary rich N (replyNext P R ordinary rich algorithm s)
                  (serve R p₀ s).afterNormal) (serve R p₀ s).afterNormal
            dsimp only [p₀]
            omega
          rcases hm with hfirst|htail
          · have hone : earlyFor R p₀ s q=1 := by have hb := earlyFor_le_one R p₀ s q; omega
            refine ⟨(serve R p₀ s).repairs.length+2,?_,N+1,algorithm,false,p₀,_,
              query_before_normal P R ordinary rich N algorithm s hquery,
              earlyFor_one_before R p₀ s q hone⟩
            have hb := serve_repairs_length R p₀ s
            exact (show (serve R p₀ s).repairs.length+2<8^L+4 by omega).trans_le
              (Nat.le_mul_of_pos_left _ (by omega))
          · obtain ⟨i,hi,n,b,output,p,u,hu,hcost⟩ := ih (replyNext P R ordinary rich algorithm s)
              (serve R p₀ s).afterNormal htail
            refine ⟨(serve R p₀ s).repairs.length+4+i,?_,n,b,output,p,u,?_,hcost⟩
            · calc
                (serve R p₀ s).repairs.length+4+i < (8^L+4)+(N+1)*(8^L+4) :=
                  Nat.add_lt_add_of_le_of_lt (Nat.add_le_add_right (serve_repairs_length R p₀ s) 4) hi
                _ = (N+1+1)*(8^L+4) := by ring
            · rw [run_add,ControllerAdaptiveExecution.query_execution P R ordinary rich N algorithm s hquery]
              exact hu

end GradientHessian.ControllerAdaptiveEarly
