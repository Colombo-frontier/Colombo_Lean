import SecondOrder.QueryCapping

open MeasureTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] {d : ℕ}

def chordProgramRequest (P : Parameters) (x y : ℕ → S → Point d) (ρ δ : ℝ) : ℕ → S → ℕ :=
  fun n => adaptiveChordCost P (x n) (y n) ρ δ

/-- State updates receive the actual robust HVP estimate. All queries of
the local routine are fixed by its state and its fresh line samples. -/
def chordProgramUpdate (P : Parameters) (f : Ω → Point d → ℝ) (x y : ℕ → S → Point d)
    (ρ δ : ℝ) (next : ℕ → S → Point d → S) :
    ℕ → S → BatchTape (ℝ × Ω) (confidenceRepeats δ) → S :=
  fun n s w => next n s (adaptiveChord P f (x n) (y n) ρ δ (s,w))

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.chordProgramUpdate_measurable (h : CommonLoss μ P ν F f)
    (x y : ℕ → S → Point d) (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    (ρ δ : ℝ) (next : ℕ → S → Point d → S)
    (hn : ∀ n, Measurable (fun w : S × Point d => next n w.1 w.2)) (n : ℕ) :
    Measurable (fun w : S × BatchTape (ℝ × Ω) (confidenceRepeats δ) =>
      chordProgramUpdate P f x y ρ δ next n w.1 w.2) :=
  (hn n).comp (measurable_fst.prodMk (h.adaptiveChord_measurable (hx n) (hy n) ρ δ))

theorem chordProgramRequest_measurable (P : Parameters) (x y : ℕ → S → Point d)
    (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n)) (ρ δ : ℝ) (n : ℕ) :
    Measurable (chordProgramRequest P x y ρ δ n) := adaptiveChordCost_measurable P (hx n) (hy n) ρ δ

def chordProgramFailures (P : Parameters) (f : Ω → Point d → ℝ) (F : Point d → ℝ)
    (initial : S) (x y : ℕ → S → Point d) (ρ δ : ℝ) (next : ℕ → S → Point d → S) :
    FreshCallFailure (BatchTape (ℝ × Ω) (confidenceRepeats δ)) :=
  chordCallFailure P f F ρ δ
    (fun n w => x n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w))
    (fun n w => y n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w))

/-- Any invariant preserved by accurate local replies is preserved along
the actual program whenever its fresh estimates all succeed. -/
theorem chordProgram_invariant_on_good_history (P : Parameters) (f : Ω → Point d → ℝ) (F : Point d → ℝ)
    (initial : S) (x y : ℕ → S → Point d) (ρ δ : ℝ) (next : ℕ → S → Point d → S)
    (Inv : S → Prop) (hi : Inv initial)
    (hn : ∀ n s v, Inv s → ‖v-(gradient F (y n s)-gradient F (x n s))‖ ≤ ρ → Inv (next n s v))
    (N : ℕ) (w : Draws (BatchTape (ℝ × Ω) (confidenceRepeats δ)) N)
    (hg : freshHistoryGood (chordProgramFailures P f F initial x y ρ δ next) N w) :
    Inv (callRun initial (chordProgramUpdate P f x y ρ δ next) N w) := by
  induction N with
  | zero => exact hi
  | succ n ih =>
    apply hn n _ _ (ih w.1 hg.1)
    exact le_of_not_gt hg.2

theorem CommonLoss.chordProgram_invariant_failure (h : CommonLoss μ P ν F f)
    (initial : S) (x y : ℕ → S → Point d) (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (next : ℕ → S → Point d → S)
    (hm : ∀ n, Measurable (fun w : S × Point d => next n w.1 w.2))
    (Inv : S → Prop) (hi : Inv initial)
    (hn : ∀ n s v, Inv s → ‖v-(gradient F (y n s)-gradient F (x n s))‖ ≤ ρ → Inv (next n s v))
    (N : ℕ) :
    drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) N
      {w | ¬Inv (callRun initial (chordProgramUpdate P f x y ρ δ next) N w)} ≤
      ENNReal.ofReal ((N : ℝ)*δ) := by
  have hr := callRun_measurable initial _ (h.chordProgramUpdate_measurable x y hx hy ρ δ next hm)
  have hb := h.adaptive_chord_calls_failure hρ hδ
    (fun n w => x n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w))
    (fun n w => y n (callRun initial (chordProgramUpdate P f x y ρ δ next) n w))
    (fun n => (hx n).comp (hr n)) (fun n => (hy n).comp (hr n)) N
  refine (measure_mono ?_).trans hb
  intro w hw hg
  exact hw (chordProgram_invariant_on_good_history P f F initial x y ρ δ next Inv hi hn N w hg)

end
end SecondOrder
