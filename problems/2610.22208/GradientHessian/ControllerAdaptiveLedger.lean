import GradientHessian.ControllerAdaptiveExecution
import GradientHessian.GeometricPolicyLedger

/-! Exact output and call accounting for receipt-dependent policies.
The initial state may already contain the public packet. The final output
is selected once and appended as one virtual ordinary point. -/

noncomputable section
namespace GradientHessian.ControllerAdaptiveExecution
open Classical TaskState TaskSlots ComparisonController ComparisonControllerLedger
  ControllerPolicyTrace GeometricPolicyLedger HigherHierarchy GeometricRepair GeometricDisclosure

variable {L M ell : ℕ} {Seed S X O V A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace O] [MeasurableSpace V]
variable (P : Machine.Policy Seed S X O V) (R : Rules L M ell X A)
  (ordinary : State L M ell → State L M ell → X → O)
  (rich : State L M ell → State L M ell → X → V)

def finalState : ℕ → S → State L M ell → S
  | 0,a,_ => a
  | N+1,a,s => if P.mode a=0 then a
    else if P.mode a=1 then finalState N (P.think a) s
    else finalState N (replyNext P R ordinary rich a s)
      (serve R (ControllerPolicyExecution.queryPoint P a) s).afterNormal

def trace : ℕ → S → State L M ell → List (Pending X)
  | 0,_,_ => []
  | N+1,a,s => if P.mode a=0 then []
    else if P.mode a=1 then trace N (P.think a) s
    else ControllerPolicyExecution.queryPoint P a :: trace N (replyNext P R ordinary rich a s)
      (serve R (ControllerPolicyExecution.queryPoint P a) s).afterNormal

def output (N : ℕ) (a : S) (s : State L M ell) : X := P.output (finalState P R ordinary rich N a s)
def ordinaryCalls (N : ℕ) (a : S) (s : State L M ell) : ℕ := kindCount .ordinary (trace P R ordinary rich N a s)
def richCalls (N : ℕ) (a : S) (s : State L M ell) : ℕ := kindCount .rich (trace P R ordinary rich N a s)

def HasCaps (a : S) (s : State L M ell) (G H : ℕ) : Prop :=
  ∀ N,ordinaryCalls P R ordinary rich N a s≤G ∧ richCalls P R ordinary rich N a s≤H

theorem queries_eq_trace_output (N : ℕ) (a : S) (s : State L M ell) :
    queries P R ordinary rich N a s=trace P R ordinary rich N a s++
      [⟨output P R ordinary rich N a s,.ordinary⟩] := by
  induction N generalizing a s with
  | zero => rfl
  | succ N ih =>
    by_cases h0 : P.mode a=0
    · simp [queries,trace,output,finalState,h0]
    · by_cases h1 : P.mode a=1
      · simpa only [queries,trace,output,finalState,if_neg h0,if_pos h1] using ih (P.think a) s
      · simp only [queries,trace,output,finalState,if_neg h0,if_neg h1,List.cons_append]
        rw [ih]
        rfl

theorem queries_ordinary_count (N : ℕ) (a : S) (s : State L M ell) :
    kindCount .ordinary (queries P R ordinary rich N a s)=ordinaryCalls P R ordinary rich N a s+1 := by
  rw [queries_eq_trace_output,kindCount_append]
  simp [kindCount,ordinaryCalls]

theorem queries_rich_count (N : ℕ) (a : S) (s : State L M ell) :
    kindCount .rich (queries P R ordinary rich N a s)=richCalls P R ordinary rich N a s := by
  rw [queries_eq_trace_output,kindCount_append]
  simp [kindCount,richCalls]

theorem retired_task_ledger (N : ℕ) (a : S) (hell : 0<ell)
    (hretired : TaskState.retired (VisibilityWindow.run R (queries P R ordinary rich N a initial) initial)=Finset.univ) :
    8^L*M≤richCalls P R ordinary rich N a initial*M+(ordinaryCalls P R ordinary rich N a initial+1)/ell+
      tally R (early R) (queries P R ordinary rich N a initial) initial+
      tally R (repairs R) (queries P R ordinary rich N a initial) initial := by
  have hl := all_retired_task_ledger R (queries P R ordinary rich N a initial) hell hretired
  have ho := ordinary_tally_le R (queries P R ordinary rich N a initial) initial
  have hh := rich_tally_le R (queries P R ordinary rich N a initial) initial
  rw [queries_ordinary_count] at ho
  rw [queries_rich_count] at hh
  exact hl.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_right M hh) (Nat.div_le_div_right ho)) _) _)

section Geometry
variable {Y E : Type} {H : ℕ → Type} {t m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] [∀ h,CompleteSpace (H h)]
variable [MeasurableSpace (Space Y E H m t)]

theorem output_retired {K : ℝ} (hK : 16≤K) (data : Data Y E H m t) (hd : Valid Y E H m t data)
    (P : Machine.Policy Seed S (Space Y E H m t) O V)
    (o : State (t+1) (m+1) ell → State (t+1) (m+1) ell → Space Y E H m t → O)
    (v : State (t+1) (m+1) ell → State (t+1) (m+1) ell → Space Y E H m t → V)
    (N : ℕ) (a : S)
    (hg : ‖gradient (scalar K t data) (output P (rules (ell := ell) K data) o v N a initial)‖≤1) :
    TaskState.retired (VisibilityWindow.run (rules (ell := ell) K data) (queries P (rules (ell := ell) K data) o v N a initial) initial)=Finset.univ := by
  rw [queries_eq_trace_output,controller_run_append]
  apply serve_small_gradient_after_retired hK data hd
  · exact run_lastChildClosed K data _ _ (initial_lastChildClosed (by omega))
  · exact hg

theorem capped_task_ledger {K : ℝ} (hK : 16≤K) (data : Data Y E H m t) (hd : Valid Y E H m t data)
    (P : Machine.Policy Seed S (Space Y E H m t) O V)
    (o : State (t+1) (m+1) ell → State (t+1) (m+1) ell → Space Y E H m t → O)
    (v : State (t+1) (m+1) ell → State (t+1) (m+1) ell → Space Y E H m t → V)
    (N : ℕ) (a : S) (hell : 0<ell) (G Hcap : ℕ)
    (hcaps : HasCaps P (rules (ell := ell) K data) o v a initial G Hcap)
    (hg : ‖gradient (scalar K t data) (output P (rules (ell := ell) K data) o v N a initial)‖≤1) :
    8^(t+1)*(m+1)≤Hcap*(m+1)+(G+1)/ell+
      tally (rules (ell := ell) K data) (early (rules (ell := ell) K data)) (queries P (rules (ell := ell) K data) o v N a initial) initial+
      tally (rules (ell := ell) K data) (repairs (rules (ell := ell) K data)) (queries P (rules (ell := ell) K data) o v N a initial) initial := by
  have hb := retired_task_ledger P (rules (ell := ell) K data) o v N a hell (output_retired hK data hd P o v N a hg)
  have hh := Nat.mul_le_mul_right (m+1) (hcaps N).2
  have ho : (ordinaryCalls P (rules (ell := ell) K data) o v N a initial+1)/ell≤(G+1)/ell :=
    Nat.div_le_div_right (Nat.add_le_add_right (hcaps N).1 1)
  omega

end Geometry
end GradientHessian.ControllerAdaptiveExecution
