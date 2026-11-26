import GradientHessian.DisclosureCappedProgram

/-! Resource counters preserve the entire original state through any
finite execution within its actual budgets. Original termination is also
preserved, including a final step that exhausts a resource exactly. -/

noncomputable section
namespace GradientHessian.DisclosureCappedProgram
open Classical Matrix MeasureTheory DisclosureCompiler

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

theorem eval_state (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) (s : S) (q R : ℕ)
    (hq : P.ordinaryCalls A readout N s≤q) (hR : P.disclosures A readout N s≤R) :
    ((cap P).eval A readout N (s,q,R)).2=
      ((P.eval A readout N s).2,q-P.ordinaryCalls A readout N s,R-P.disclosures A readout N s) := by
  induction N generalizing s q R with
  | zero => rfl
  | succ N ih =>
    by_cases h0 : P.mode s=0
    · simp [Program.eval,Program.terminal,Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0]
    by_cases h1 : P.mode s=1
    · have hq' : P.ordinaryCalls A readout N (P.think s)≤q := by simpa [Program.ordinaryCalls,h0,h1] using hq
      have hR' : P.disclosures A readout N (P.think s)≤R := by simpa [Program.disclosures,h0,h1] using hR
      simpa [Program.eval,Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1] using ih _ q R hq' hR'
    by_cases h2 : P.mode s=2
    · have hq' : P.ordinaryCalls A readout N (P.next (s,A*ᵥP.query s))+1≤q := by
        simpa [Program.ordinaryCalls,h0,h1,h2] using hq
      have hR' : P.disclosures A readout N (P.next (s,A*ᵥP.query s))≤R := by
        simpa [Program.disclosures,h0,h1,h2] using hR
      have hq0 : q≠0 := by omega
      have hqq : P.ordinaryCalls A readout N (P.next (s,A*ᵥP.query s))≤q-1 := by omega
      simpa [Program.eval,Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,h2,hq0,
        Nat.sub_sub,Nat.add_comm] using ih _ (q-1) R hqq hR'
    · have hq' : P.ordinaryCalls A readout N (P.disclosed (s,readout (P.mark s)))≤q := by
        simpa [Program.ordinaryCalls,h0,h1,h2] using hq
      have hR' : P.disclosures A readout N (P.disclosed (s,readout (P.mark s)))+1≤R := by
        simpa [Program.disclosures,h0,h1,h2] using hR
      have hR0 : R≠0 := by omega
      have hRR : P.disclosures A readout N (P.disclosed (s,readout (P.mark s)))≤R-1 := by omega
      simpa [Program.eval,Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,h2,hR0,
        Nat.sub_sub,Nat.add_comm] using ih _ q (R-1) hq' hRR

theorem eval_halted (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) (s : S) (q R : ℕ)
    (hq : P.ordinaryCalls A readout N s≤q) (hR : P.disclosures A readout N s≤R)
    (hhalt : (P.eval A readout N s).1=true) : ((cap P).eval A readout N (s,q,R)).1=true := by
  induction N generalizing s q R with
  | zero =>
    have h0 : P.mode s=0 := by simpa [Program.eval,Program.terminal,Program.flag] using hhalt
    simp [Program.eval,Program.terminal,Program.flag,cap,modeCode,h0]
  | succ N ih =>
    by_cases h0 : P.mode s=0
    · simp [Program.eval,Program.terminal,Program.flag,cap,modeCode,h0]
    by_cases h1 : P.mode s=1
    · have hq' : P.ordinaryCalls A readout N (P.think s)≤q := by simpa [Program.ordinaryCalls,h0,h1] using hq
      have hR' : P.disclosures A readout N (P.think s)≤R := by simpa [Program.disclosures,h0,h1] using hR
      have hh : (P.eval A readout N (P.think s)).1=true := by simpa [Program.eval,h0,h1] using hhalt
      simpa [Program.eval,cap,modeCode,h0,h1] using ih _ q R hq' hR' hh
    by_cases h2 : P.mode s=2
    · have hq' : P.ordinaryCalls A readout N (P.next (s,A*ᵥP.query s))+1≤q := by
        simpa [Program.ordinaryCalls,h0,h1,h2] using hq
      have hR' : P.disclosures A readout N (P.next (s,A*ᵥP.query s))≤R := by
        simpa [Program.disclosures,h0,h1,h2] using hR
      have hh : (P.eval A readout N (P.next (s,A*ᵥP.query s))).1=true := by
        simpa [Program.eval,h0,h1,h2] using hhalt
      have hq0 : q≠0 := by omega
      have hqq : P.ordinaryCalls A readout N (P.next (s,A*ᵥP.query s))≤q-1 := by omega
      simpa [Program.eval,cap,modeCode,h0,h1,h2,hq0] using ih _ (q-1) R hqq hR' hh
    · have hq' : P.ordinaryCalls A readout N (P.disclosed (s,readout (P.mark s)))≤q := by
        simpa [Program.ordinaryCalls,h0,h1,h2] using hq
      have hR' : P.disclosures A readout N (P.disclosed (s,readout (P.mark s)))+1≤R := by
        simpa [Program.disclosures,h0,h1,h2] using hR
      have hh : (P.eval A readout N (P.disclosed (s,readout (P.mark s)))).1=true := by
        simpa [Program.eval,h0,h1,h2] using hhalt
      have hR0 : R≠0 := by omega
      have hRR : P.disclosures A readout N (P.disclosed (s,readout (P.mark s)))≤R-1 := by omega
      simpa [Program.eval,cap,modeCode,h0,h1,h2,hR0] using ih _ q (R-1) hq' hRR hh

theorem eval_projects (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) (s : S) (q R : ℕ)
    (hq : P.ordinaryCalls A readout N s≤q) (hR : P.disclosures A readout N s≤R) :
    ((cap P).eval A readout N (s,q,R)).2.1=(P.eval A readout N s).2 :=
  congrArg Prod.fst (eval_state P A readout N s q R hq hR)

theorem eval_projects_of_halted (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (N : ℕ) (s : S) (q R : ℕ)
    (hq : P.ordinaryCalls A readout N s≤q) (hR : P.disclosures A readout N s≤R)
    (hhalt : (P.eval A readout N s).1=true) :
    (((cap P).eval A readout N (s,q,R)).1,((cap P).eval A readout N (s,q,R)).2.1)=P.eval A readout N s := by
  apply Prod.ext
  · rw [hhalt]
    exact eval_halted P A readout N s q R hq hR hhalt
  · exact eval_projects P A readout N s q R hq hR

end GradientHessian.DisclosureCappedProgram
