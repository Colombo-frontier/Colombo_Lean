import GradientHessian.TestSelectionMachine
import GradientHessian.DisclosureCappedProgram

/-! Hard product and selected-test caps for an arbitrary chronological
selection machine. Counters are charged only by the corresponding instruction. -/

noncomputable section
namespace GradientHessian.SelectionCappedProgram
open Classical Matrix MeasureTheory TestSelectionMachine DisclosureCappedProgram

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

def cap (P : Program d S) : Program d (S × ℕ × ℕ) where
  mode := fun s => modeCode (P.mode s.1,s.2)
  think := fun s => (P.think s.1,s.2)
  query := fun s => P.query s.1
  next := fun p => (P.next (p.1.1,p.2),p.1.2.1-1,p.1.2.2)
  test := fun s => P.test s.1
  selected := fun s => (P.selected s.1,s.2.1,s.2.2-1)
  mode_measurable := (measurable_of_countable modeCode).comp
    ((P.mode_measurable.comp measurable_fst).prodMk measurable_snd)
  think_measurable := (P.think_measurable.comp measurable_fst).prodMk measurable_snd
  query_measurable := P.query_measurable.comp measurable_fst
  next_measurable := (P.next_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    ((measurable_of_countable (fun q : ℕ × ℕ => (q.1-1,q.2))).comp
      (measurable_snd.comp measurable_fst))
  test_measurable := P.test_measurable.comp measurable_fst
  selected_measurable := (P.selected_measurable.comp measurable_fst).prodMk
    ((measurable_of_countable (fun q : ℕ × ℕ => (q.1,q.2-1))).comp measurable_snd)

theorem step_counters (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : S × ℕ × ℕ) :
    ((cap P).step A s).2.1 + (if (cap P).mode s=2 then 1 else 0) = s.2.1 ∧
    ((cap P).step A s).2.2 + (if (cap P).mode s=3 then 1 else 0) = s.2.2 := by
  rcases s with ⟨s,q,R⟩
  by_cases h0 : P.mode s=0
  · simp [cap,modeCode,Program.step,h0]
  by_cases h1 : P.mode s=1
  · simp [cap,modeCode,Program.step,h0,h1]
  by_cases h2 : P.mode s=2
  · by_cases hq : q=0
    · simp [cap,modeCode,Program.step,h0,h1,h2,hq]
    · simp [cap,modeCode,Program.step,h0,h1,h2,hq]; omega
  · by_cases hR : R=0
    · simp [cap,modeCode,Program.step,h0,h1,h2,hR]
    · simp [cap,modeCode,Program.step,h0,h1,h2,hR]; omega

theorem count_conservation (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : S × ℕ × ℕ) (N : ℕ) :
    (cap P).queryCount A N s + ((cap P).run A N s).2.1 = s.2.1 ∧
    (cap P).selections A N s + ((cap P).run A N s).2.2 = s.2.2 := by
  induction N with
  | zero => simp [Program.queryCount,Program.selections,Program.run]
  | succ N ih =>
      have hs := step_counters P A ((cap P).run A N s)
      have hr : (cap P).run A (N+1) s=(cap P).step A ((cap P).run A N s) :=
        Function.iterate_succ_apply' _ _ _
      have hq : (cap P).queryCount A (N+1) s=(cap P).queryCount A N s+
          if (cap P).mode ((cap P).run A N s)=2 then 1 else 0 := by
        simp only [Program.queryCount,Finset.sum_range_succ]
      rw [hq,Program.selections,hr]
      constructor <;> omega

theorem calls_le (P : Program d S) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : S) (q R N : ℕ) :
    (cap P).queryCount A N (s,q,R) ≤ q ∧ (cap P).selections A N (s,q,R) ≤ R := by
  have h := count_conservation P A (s,q,R) N
  dsimp only at h
  constructor <;> omega

end GradientHessian.SelectionCappedProgram
