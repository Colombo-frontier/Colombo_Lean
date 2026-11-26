import GradientHessian.Machine
import GradientHessian.ComparisonControllerLedger

/-! The chronological selected points of an arbitrary mixed policy, with
one virtual ordinary output. Internal steps and halts add no oracle queries.
Actual controller counters are bounded by the original policy counts. -/

noncomputable section
namespace GradientHessian.ControllerPolicyTrace
open Classical Machine ComparisonController ComparisonControllerLedger

variable {Seed S X Y Z A : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
variable {L M ell : ℕ}

def selected (P : Policy Seed S X Y Z) (s : S) : List (Pending X) :=
  if P.mode s=2 then [⟨P.point s,.ordinary⟩]
  else if P.mode s=3 then [⟨P.point s,.rich⟩] else []

def trace (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z) : ℕ → Seed → List (Pending X)
  | 0,_ => []
  | n+1,seed => trace P o r n seed ++ selected P (P.run o r n seed)

def withOutput (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z) (n : ℕ) (seed : Seed) :
    List (Pending X) := trace P o r n seed ++ [⟨P.output (P.run o r n seed),.ordinary⟩]

def kindCount (k : Kind) : List (Pending X) → ℕ
  | [] => 0
  | p::ps => (if p.kind=k then 1 else 0)+kindCount k ps

omit [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] in
theorem kindCount_append (k : Kind) (ps qs : List (Pending X)) :
    kindCount k (ps++qs)=kindCount k ps+kindCount k qs := by
  induction ps with
  | nil => simp [kindCount]
  | cons p ps ih => simp only [List.cons_append,kindCount,ih,Nat.add_assoc]

theorem selected_ordinary (P : Policy Seed S X Y Z) (s : S) :
    kindCount .ordinary (selected P s)=if P.mode s=2 then 1 else 0 := by
  unfold selected
  split_ifs <;> simp [kindCount]

theorem selected_rich (P : Policy Seed S X Y Z) (s : S) :
    kindCount .rich (selected P s)=if P.mode s=3 then 1 else 0 := by
  unfold selected
  split_ifs with h2 h3 h3 <;> simp_all [kindCount]

theorem trace_ordinary (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z) (n : ℕ) (seed : Seed) :
    kindCount .ordinary (trace P o r n seed)=P.ordinaryCount o r n seed := by
  induction n with
  | zero => simp [trace,kindCount,Policy.ordinaryCount]
  | succ n ih =>
    rw [trace,kindCount_append,ih,selected_ordinary]
    simp only [Policy.ordinaryCount,Finset.sum_range_succ]

theorem trace_rich (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z) (n : ℕ) (seed : Seed) :
    kindCount .rich (trace P o r n seed)=P.richCount o r n seed := by
  induction n with
  | zero => simp [trace,kindCount,Policy.richCount]
  | succ n ih =>
    rw [trace,kindCount_append,ih,selected_rich]
    simp only [Policy.richCount,Finset.sum_range_succ]

theorem withOutput_ordinary (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z) (n : ℕ) (seed : Seed) :
    kindCount .ordinary (withOutput P o r n seed)=P.ordinaryCount o r n seed+1 := by
  simp [withOutput,kindCount_append,trace_ordinary,kindCount]

theorem withOutput_rich (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z) (n : ℕ) (seed : Seed) :
    kindCount .rich (withOutput P o r n seed)=P.richCount o r n seed := by
  simp [withOutput,kindCount_append,trace_rich,kindCount]

omit [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] in
theorem ordinary_tally_le (R : Rules L M ell X A) (ps : List (Pending X)) (s : TaskState.State L M ell) :
    tally R (ordinary R) ps s≤kindCount .ordinary ps := by
  induction ps generalizing s with
  | nil => simp [tally,kindCount]
  | cons p ps ih =>
    have hb : ordinary R p s ≤ (if p.kind=.ordinary then 1 else 0) := by
      unfold ordinary ordinaryCost
      cases p.kind <;> cases TaskState.current (serve R p s).beforeNormal <;> simp
    exact Nat.add_le_add hb (ih _)

omit [MeasurableSpace Seed] [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z] in
theorem rich_tally_le (R : Rules L M ell X A) (ps : List (Pending X)) (s : TaskState.State L M ell) :
    tally R (rich R) ps s≤kindCount .rich ps := by
  induction ps generalizing s with
  | nil => simp [tally,kindCount]
  | cons p ps ih =>
    have hb : rich R p s ≤ (if p.kind=.rich then 1 else 0) := by
      unfold rich richCost
      cases p.kind <;> cases TaskState.current (serve R p s).beforeNormal <;> simp
    exact Nat.add_le_add hb (ih _)

theorem output_task_ledger (P : Policy Seed S X Y Z) (o : X → Y) (r : X → Z)
    (R : Rules L M ell X A) (n : ℕ) (seed : Seed) (hell : 0<ell)
    (hr : TaskState.retired (VisibilityWindow.run R (withOutput P o r n seed) TaskState.initial)=Finset.univ) :
    8^L*M≤P.richCount o r n seed*M+(P.ordinaryCount o r n seed+1)/ell+
      tally R (early R) (withOutput P o r n seed) TaskState.initial+
      tally R (repairs R) (withOutput P o r n seed) TaskState.initial := by
  have hl := all_retired_task_ledger R (withOutput P o r n seed) hell hr
  have ho := ordinary_tally_le R (withOutput P o r n seed) TaskState.initial
  have hh := rich_tally_le R (withOutput P o r n seed) TaskState.initial
  rw [withOutput_ordinary] at ho
  rw [withOutput_rich] at hh
  exact hl.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_right M hh) (Nat.div_le_div_right ho)) _) _)

end GradientHessian.ControllerPolicyTrace
