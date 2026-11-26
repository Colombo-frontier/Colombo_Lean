import SecondOrder.ChordQueries
import SecondOrder.ChordCost
import SecondOrder.FreshCallUnion

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace SecondOrder
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

abbrev ChordEndpointHistory (Ω : Type*) (d : ℕ) (δ : ℝ) :=
  (n : ℕ) → Draws (BatchTape (ℝ × Ω) (confidenceRepeats δ)) n → Point d

def chordCallFailure (P : Parameters) (f : Ω → Point d → ℝ) (F : Point d → ℝ)
    (ρ δ : ℝ) (x y : ChordEndpointHistory Ω d δ) :
    FreshCallFailure (BatchTape (ℝ × Ω) (confidenceRepeats δ)) :=
  fun n a z => ρ < ‖adaptiveChord P f (x n) (y n) ρ δ (a,z)-(gradient F (y n a)-gradient F (x n a))‖

/-- Success of all calls in an actual recursive fresh-sample experiment.
Each endpoint may depend on every sample and reply seen at earlier calls. -/
theorem CommonLoss.adaptive_chord_calls_failure (h : CommonLoss μ P ν F f)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (x y : ChordEndpointHistory Ω d δ) (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    (N : ℕ) :
    drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) N
      {w | ¬freshHistoryGood (chordCallFailure P f F ρ δ x y) N w} ≤ ENNReal.ofReal ((N : ℝ)*δ) := by
  apply fresh_calls_constant_bound _ hδ.le
  · intro n
    have hg := (contDiff_gradient_one h.population_smooth).continuous.measurable
    exact measurableSet_lt measurable_const ((h.adaptiveChord_measurable (hx n) (hy n) ρ δ).sub
      (((hg.comp (hy n)).sub (hg.comp (hx n))).comp measurable_fst)).norm
  · intro n a
    exact variableFreshEstimate_slice_confidence (h.randomLine_adaptive_measurable (hx n) (hy n)) ρ δ
      (fun a => h.chord_confidence (x n a) (y n a) hρ hδ) a

/-- Accumulate costs chosen from the past before drawing the next batch. -/
def freshHistoryCost {S : Type*} (c : (n : ℕ) → Draws S n → ℕ) : (n : ℕ) → Draws S n → ℕ
  | 0, _ => 0
  | n+1, w => freshHistoryCost c n w.1+c n w.1

theorem freshHistoryCost_integral {S : Type*} [MeasurableSpace S] {κ : Measure S}
    [IsProbabilityMeasure κ] (c : (n : ℕ) → Draws S n → ℕ)
    (hc : ∀ n, Integrable (fun w => (c n w : ℝ)) (drawsLaw κ n)) (N : ℕ) :
    Integrable (fun w => (freshHistoryCost c N w : ℝ)) (drawsLaw κ N) ∧
    (∫ w, (freshHistoryCost c N w : ℝ) ∂drawsLaw κ N) =
      ∑ n ∈ Finset.range N, ∫ w, (c n w : ℝ) ∂drawsLaw κ n := by
  induction N with
  | zero => simp [freshHistoryCost, integrable_const]
  | succ n ih =>
    have hi := integrable_product_fst (η := κ) (ih.1.add (hc n))
    refine ⟨?_, ?_⟩
    · simpa only [freshHistoryCost, Nat.cast_add] using hi
    · change (∫ w : Draws S n × S, ((freshHistoryCost c n w.1+c n w.1 : ℕ) : ℝ)
        ∂(drawsLaw κ n).prod κ) = _
      simp only [Nat.cast_add]
      rw [integral_fun_fst (fun a => (freshHistoryCost c n a : ℝ)+(c n a : ℝ))]
      simp only [measureReal_univ_eq_one, one_smul]
      rw [integral_add ih.1 (hc n), ih.2, Finset.sum_range_succ]

/-- The expected total number of actual HVP queries preserves the sum of
expected squared chord lengths, including adaptive choices of batch sizes. -/
theorem adaptive_chord_calls_cost {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (P : Parameters) (x y : ChordEndpointHistory Ω d δ)
    (hx : ∀ n, Measurable (x n)) (hy : ∀ n, Measurable (y n))
    (hE : ∀ n, Integrable (fun a => ‖y n a-x n a‖^2)
      (drawsLaw (batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)) n)) (N : ℕ) :
    let law := batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)
    let costs := fun n => adaptiveChordCost P (x n) (y n) ρ δ
    Integrable (fun w => (freshHistoryCost costs N w : ℝ)) (drawsLaw law N) ∧
    (∫ w, (freshHistoryCost costs N w : ℝ) ∂drawsLaw law N) ≤
      ∑ n ∈ Finset.range N,
        (36*(P.hessianNoise^2+P.gradientLip^2)*
          (∫ a, ‖y n a-x n a‖^2 ∂drawsLaw law n)/ρ^2+2)*(8*Real.log (1/δ)+2) := by
  dsimp only
  have hi := freshHistoryCost_integral (fun n => adaptiveChordCost P (x n) (y n) ρ δ)
    (fun n => (adaptiveChordCost_integral P (hx n) (hy n) hδ hδ1 (hE n)).1) N
  refine ⟨hi.1, ?_⟩
  rw [hi.2]
  exact Finset.sum_le_sum (fun n _ => (adaptiveChordCost_integral P (hx n) (hy n) hδ hδ1 (hE n)).2)

end
end SecondOrder
