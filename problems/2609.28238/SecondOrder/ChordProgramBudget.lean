import SecondOrder.ChordProgram

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace SecondOrder
noncomputable section

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem chordProgramRequest_eq_card (P : Parameters) (x y : ℕ → S → Point d) (ρ δ : ℝ) (n : ℕ) (s : S) :
    chordProgramRequest P x y ρ δ n s = Fintype.card (AdaptiveChordSlot P (x n) (y n) ρ δ s) :=
  (adaptiveChordCall_count P (x n) (y n) ρ δ s).symm

/-- A deterministic expression for the expected work, with each chord
evaluated along the actual state trajectory of the fresh-sample program. -/
def chordProgramBound (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters)
    (f : Ω → Point d → ℝ) (initial : S) (x y : ℕ → S → Point d)
    (ρ δ : ℝ) (next : ℕ → S → Point d → S) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (36*(P.hessianNoise^2+P.gradientLip^2)*
      (∫ w, ‖y n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w)-
        x n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w)‖^2
        ∂drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) n)/ρ^2+2)*(8*Real.log (1/δ)+2)

theorem CommonLoss.chordProgram_cost (h : CommonLoss μ P ν F f)
    (initial : S) (x y : ℕ → S → Point d) (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (next : ℕ → S → Point d → S)
    (hm : ∀ n, Measurable (fun w : S × Point d => next n w.1 w.2))
    (hE : ∀ n, Integrable (fun w =>
      ‖y n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w)-
        x n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w)‖^2)
      (drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) n)) (N : ℕ) :
    let costs := callCost initial (chordProgramRequest P x y ρ δ) (chordProgramUpdate P f x y ρ δ next) N
    let law := drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) N
    Integrable (fun w => (costs w : ℝ)) law ∧
      (∫ w, (costs w : ℝ) ∂law) ≤ chordProgramBound μ P f initial x y ρ δ next N := by
  have hr := callRun_measurable initial _ (h.chordProgramUpdate_measurable x y hx hy ρ δ next hm)
  exact adaptive_chord_calls_cost hδ hδ1 P
    (fun n w => x n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w))
    (fun n w => y n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w))
    (fun n => (hx n).comp (hr n)) (fun n => (hy n).comp (hr n)) hE N

/-- The permitted HVP program with a real preflight budget check: it uses
at most Q calls on every path, and its invariant fails or its budget aborts
with probability at most Nδ+1/24. The energy assumptions are explicit. -/
theorem CommonLoss.chordProgram_budget_invariant (h : CommonLoss μ P ν F f)
    (initial : S) (x y : ℕ → S → Point d) (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (next : ℕ → S → Point d → S)
    (hm : ∀ n, Measurable (fun w : S × Point d => next n w.1 w.2))
    (hE : ∀ n, Integrable (fun w =>
      ‖y n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w)-
        x n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w)‖^2)
      (drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) n))
    (Inv : S → Prop) (hi : Inv initial)
    (hn : ∀ n s v, Inv s → ‖v-(gradient F (y n s)-gradient F (x n s))‖ ≤ ρ → Inv (next n s v)) (N : ℕ) :
    let Q := queryCap (chordProgramBound μ P f initial x y ρ δ next N)
    let run := queryBudgetRun Q initial (chordProgramRequest P x y ρ δ) (chordProgramUpdate P f x y ρ δ next) N
    (∀ w, (run w).2.1 ≤ Q) ∧
    drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) N
      {w | (run w).2.2 = true ∨ ¬Inv (run w).1} ≤ ENNReal.ofReal ((N : ℝ)*δ+1/24) := by
  dsimp only
  have hc := h.chordProgram_cost initial x y hx hy hδ hδ1 next hm hE N
  have hB : 0 ≤ chordProgramBound μ P f initial x y ρ δ next N :=
    (integral_nonneg (fun w => Nat.cast_nonneg _)).trans hc.2
  refine ⟨queryBudgetRun_spent_le _ _ _ _ N, ?_⟩
  have hf := h.chordProgram_invariant_failure initial x y hx hy hρ hδ next hm Inv hi hn N
  have hb := queryBudget_failure_bound (queryCap_pos hB) initial (chordProgramRequest P x y ρ δ)
    (chordProgramUpdate P f x y ρ δ next) N Inv hc.1 hB (mul_nonneg (Nat.cast_nonneg N) hδ.le) hc.2 hf
  exact hb.trans (ENNReal.ofReal_le_ofReal (add_le_add_left (queryCap_ratio hB) _))

end
end SecondOrder
