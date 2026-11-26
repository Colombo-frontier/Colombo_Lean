import GradientHessian.DisclosureCompiler

/-! Literal all-counterfactual caps for an executable preprocessing machine.
Only a genuine product or readout instruction decrements its own counter.
An exhausted requested resource halts before making the oracle call. -/

noncomputable section
namespace GradientHessian.DisclosureCappedProgram
open Classical Matrix MeasureTheory DisclosureCompiler

def modeCode (p : Fin 4 × ℕ × ℕ) : Fin 4 :=
  if p.1=0 then 0 else if p.1=1 then 1 else if p.1=2 then
    (if p.2.1=0 then 0 else 2) else (if p.2.2=0 then 0 else 3)

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

def cap (P : Program d S) : Program d (S × ℕ × ℕ) where
  mode := fun s => modeCode (P.mode s.1,s.2)
  think := fun s => (P.think s.1,s.2)
  query := fun s => P.query s.1
  mark := fun s => P.mark s.1
  next := fun p => (P.next (p.1.1,p.2),p.1.2.1-1,p.1.2.2)
  disclosed := fun p => (P.disclosed (p.1.1,p.2),p.1.2.1,p.1.2.2-1)
  mode_measurable := (measurable_of_countable modeCode).comp ((P.mode_measurable.comp measurable_fst).prodMk measurable_snd)
  think_measurable := (P.think_measurable.comp measurable_fst).prodMk measurable_snd
  query_measurable := P.query_measurable.comp measurable_fst
  mark_measurable := P.mark_measurable.comp measurable_fst
  next_measurable := by
    apply Measurable.prodMk
    · exact P.next_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact (measurable_of_countable (fun q : ℕ × ℕ => (q.1-1,q.2))).comp (measurable_snd.comp measurable_fst)
  disclosed_measurable := by
    apply Measurable.prodMk
    · exact P.disclosed_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact (measurable_of_countable (fun q : ℕ × ℕ => (q.1,q.2-1))).comp (measurable_snd.comp measurable_fst)

theorem calls_le (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) : ∀ N (s : S) (q R : ℕ),
    (cap P).ordinaryCalls A readout N (s,q,R) ≤ q ∧ (cap P).disclosures A readout N (s,q,R) ≤ R := by
  intro N
  induction N with
  | zero => intro s q R; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | succ N ih =>
    intro s q R
    by_cases h0 : P.mode s=0
    · simp [Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0]
    by_cases h1 : P.mode s=1
    · simpa only [Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,if_false,if_true,
        one_ne_zero,Fin.isValue] using ih (P.think s) q R
    by_cases h2 : P.mode s=2
    · by_cases hq : q=0
      · simp [Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,h2,hq]
      · have hh := ih (P.next (s,A*ᵥP.query s)) (q-1) R
        simpa only [Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,h2,hq,
          if_false,if_true,Fin.isValue,reduceCtorEq] using (show
            (cap P).ordinaryCalls A readout N (P.next (s,A*ᵥP.query s),q-1,R)+1 ≤ q ∧
              (cap P).disclosures A readout N (P.next (s,A*ᵥP.query s),q-1,R) ≤ R from ⟨by omega,hh.2⟩)
    · by_cases hR : R=0
      · simp [Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,h2,hR]
      · have hh := ih (P.disclosed (s,readout (P.mark s))) q (R-1)
        simpa only [Program.ordinaryCalls,Program.disclosures,cap,modeCode,h0,h1,h2,hR,
          if_false,if_true,Fin.isValue,reduceCtorEq] using (show
            (cap P).ordinaryCalls A readout N (P.disclosed (s,readout (P.mark s)),q,R-1) ≤ q ∧
              (cap P).disclosures A readout N (P.disclosed (s,readout (P.mark s)),q,R-1)+1 ≤ R from ⟨hh.1,by omega⟩)

end GradientHessian.DisclosureCappedProgram
