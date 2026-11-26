import GradientHessian.SelectionCappedProgram

/-! Finite execution and chronological counter transparency below actual budgets. -/

noncomputable section
namespace GradientHessian.SelectionCapTransparency
open Classical Matrix MeasureTheory TestSelectionMachine SelectionCappedProgram
open DisclosureCappedProgram (modeCode)

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

theorem run_succ (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (s : S) :
    P.run A (N+1) s=P.step A (P.run A N s) := Function.iterate_succ_apply' _ _ _

theorem run_add (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (n m : ℕ) (s : S) :
    P.run A (n+m) s=P.run A m (P.run A n s) := by
  change (P.step A)^[n+m] s=(P.step A)^[m] ((P.step A)^[n] s)
  rw [Nat.add_comm,Function.iterate_add_apply]

theorem queryCount_succ (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (s : S) :
    P.queryCount A (N+1) s=P.queryCount A N s+if P.mode (P.run A N s)=2 then 1 else 0 := by
  simp only [Program.queryCount,Finset.sum_range_succ]

theorem queryCount_mono (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    Monotone (fun N => P.queryCount A N s) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [queryCount_succ]
  omega

theorem selections_eq_sum (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (s : S) :
    P.selections A N s=∑ i ∈ Finset.range N,if P.mode (P.run A i s)=3 then 1 else 0 := by
  induction N with
  | zero => simp [Program.selections]
  | succ N ih => simp only [Program.selections,Finset.sum_range_succ,ih]

theorem queryCount_add (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (n m : ℕ) (s : S) :
    P.queryCount A (n+m) s=P.queryCount A n s+P.queryCount A m (P.run A n s) := by
  induction m with
  | zero => simp [Program.queryCount]
  | succ m ih =>
      rw [Nat.add_succ,queryCount_succ,queryCount_succ,ih,run_add]
      omega

theorem selections_add (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (n m : ℕ) (s : S) :
    P.selections A (n+m) s=P.selections A n s+P.selections A m (P.run A n s) := by
  induction m with
  | zero => simp [Program.selections]
  | succ m ih =>
      rw [Nat.add_succ,Program.selections,Program.selections,ih,run_add]
      omega

theorem mode_projects (P : Program d S) (s : S) (q R : ℕ)
    (hq : P.mode s=2 → 0<q) (hR : P.mode s=3 → 0<R) :
    (cap P).mode (s,q,R)=P.mode s := by
  by_cases h0 : P.mode s=0
  · simp [cap,modeCode,h0]
  by_cases h1 : P.mode s=1
  · simp [cap,modeCode,h0,h1]
  by_cases h2 : P.mode s=2
  · simp [cap,modeCode,h0,h1,h2,ne_of_gt (hq h2)]
  have h3 : P.mode s=3 := by omega
  simp [cap,modeCode,h0,h1,h2,h3,ne_of_gt (hR h3)]

theorem step_projects (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) (q R : ℕ)
    (hq : P.mode s=2 → 0<q) (hR : P.mode s=3 → 0<R) :
    (cap P).step A (s,q,R)=
      (P.step A s,q-(if P.mode s=2 then 1 else 0),R-(if P.mode s=3 then 1 else 0)) := by
  have hm := mode_projects P s q R hq hR
  simp only [Program.step,hm]
  by_cases h0 : P.mode s=0
  · simp [h0]
  by_cases h1 : P.mode s=1
  · simp [h0,h1,cap]
  by_cases h2 : P.mode s=2
  · simp [h0,h1,h2,cap]
  have h3 : P.mode s=3 := by omega
  simp [h0,h1,h2,h3,cap]

theorem run_projects (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) (q R N : ℕ)
    (hq : P.queryCount A N s≤q) (hR : P.selections A N s≤R) :
    (cap P).run A N (s,q,R)=
      (P.run A N s,q-P.queryCount A N s,R-P.selections A N s) := by
  induction N with
  | zero => simp [Program.run,Program.queryCount,Program.selections]
  | succ N ih =>
      have hqn := (queryCount_mono P A s (Nat.le_succ N)).trans hq
      have hRn := (P.selections_mono A s (Nat.le_succ N)).trans hR
      have hqp : P.mode (P.run A N s)=2 → 0<q-P.queryCount A N s := by
        intro hm
        rw [queryCount_succ,if_pos hm] at hq
        omega
      have hRp : P.mode (P.run A N s)=3 → 0<R-P.selections A N s := by
        intro hm
        rw [Program.selections,if_pos hm] at hR
        omega
      rw [run_succ,ih hqn hRn,step_projects P A _ _ _ hqp hRp,run_succ,
        queryCount_succ,Program.selections]
      simp only [Nat.sub_sub]

theorem counts_projects (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) (q R N : ℕ)
    (hq : P.queryCount A N s≤q) (hR : P.selections A N s≤R) :
    (cap P).queryCount A N (s,q,R)=P.queryCount A N s ∧
      (cap P).selections A N (s,q,R)=P.selections A N s := by
  have hc := count_conservation P A (s,q,R) N
  rw [run_projects P A s q R N hq hR] at hc
  dsimp only at hc
  constructor <;> omega

theorem selected_endpoint (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ) (s : S) (q R N : ℕ)
    (hq : P.queryCount A N s≤q) (hR : P.selections A (N+1) s≤R)
    (hm : P.mode (P.run A N s)=3) :
    (cap P).mode ((cap P).run A N (s,q,R))=3 ∧
      (cap P).test ((cap P).run A N (s,q,R))=P.test (P.run A N s) := by
  have hRn := (P.selections_mono A s (Nat.le_succ N)).trans hR
  rw [run_projects P A s q R N hq hRn]
  constructor
  · rw [mode_projects]
    · exact hm
    · intro hh; simp [hm] at hh
    · intro _
      rw [Program.selections,if_pos hm] at hR
      omega
  · rfl

end GradientHessian.SelectionCapTransparency
