import NCBall.CountablePolicy

/-! # Uniform finite-pool bounds extend to an unbounded sample pool

No deterministic bound on the labels selected by the strategy is assumed.
For each realized finite history there is a sufficiently large prefix, and
continuity of measure from below transfers the uniform bound.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

theorem countable_outcome_bound {S U Z : Type*} [MeasurableSpace S]
    [MeasurableSpace U] [MeasurableSpace Z] {n N : ℕ}
    (μ : Measure U) (ν : Measure S) (τ : Measure Z)
    [SFinite μ] [SFinite ν] [IsProbabilityMeasure τ]
    (p : CountableRoomPolicy S n) (F : U → Z → Space n → ℝ)
    (hF : Measurable (fun w : U × (Z × Space n) => F w.1 w.2.1 w.2.2))
    (out : LinearHistory S N → Space n) (hout : Measurable out)
    (target : Set (U × Space n)) (htarget : MeasurableSet target) (b : ℝ≥0∞)
    (hfinite : ∀ K : ℕ, (μ.prod (ν.prod (Measure.pi (fun _ : Fin (K + 1) => τ))))
      {w | (w.1, out (sampleTranscript (prefixPolicy p K).point (prefixPolicy p K).handle F N w))
        ∈ target} ≤ b) :
    (μ.prod (ν.prod (Measure.infinitePi (fun _ : ℕ => τ))))
      {w | (w.1, out (sampleTranscript p.point p.handle F N w)) ∈ target} ≤ b := by
  let A : ℕ → Set (U × (S × (ℕ → Z))) := fun K =>
    {w | (w.1, out (sampleTranscript p.point p.handle F N w)) ∈ target ∧
      ∀ t < N, p.handle t (sampleTranscript p.point p.handle F t w) < K + 1}
  have hmono : Monotone A := by
    intro j k hjk w hw
    exact ⟨hw.1, fun t ht => lt_of_lt_of_le (hw.2 t ht) (Nat.add_le_add_right hjk 1)⟩
  have hunion : (⋃ K, A K) =
      {w | (w.1, out (sampleTranscript p.point p.handle F N w)) ∈ target} := by
    ext w
    constructor
    · intro hw
      obtain ⟨K, hK⟩ := mem_iUnion.mp hw
      exact hK.1
    · intro hw
      let q : ℕ → ℕ := fun t => p.handle t (sampleTranscript p.point p.handle F t w)
      refine mem_iUnion.mpr ⟨(Finset.range N).sup q, hw, ?_⟩
      intro t ht
      exact Nat.lt_succ_of_le (Finset.le_sup (f := q) (Finset.mem_range.mpr ht))
  rw [← hunion, hmono.measure_iUnion]
  refine iSup_le (fun K => ?_)
  let B : Set (U × (S × (Fin (K + 1) → Z))) :=
    {w | (w.1, out (sampleTranscript (prefixPolicy p K).point (prefixPolicy p K).handle F N w))
      ∈ target}
  have hB : MeasurableSet B :=
    (measurable_fst.prodMk (hout.comp (sampleTranscript_measurable _ _ F
      (prefixPolicy p K).measurable_point (prefixPolicy p K).measurable_handle hF N))) htarget
  have hsub : A K ⊆ prefixExperiment (K + 1) ⁻¹' B := by
    intro w hw
    change (w.1, out (sampleTranscript (prefixPolicy p K).point (prefixPolicy p K).handle F N
      (prefixExperiment (K + 1) w))) ∈ target
    rw [prefix_transcript_eq p F K N w hw.2]
    exact hw.1
  have hl := prefixExperiment_law μ ν τ (K + 1)
  calc
    _ ≤ (μ.prod (ν.prod (Measure.infinitePi (fun _ : ℕ => τ))))
        (prefixExperiment (K + 1) ⁻¹' B) := measure_mono hsub
    _ = (μ.prod (ν.prod (Measure.pi (fun _ : Fin (K + 1) => τ)))) B := by
      rw [← Measure.map_apply hl.measurable hB, hl.map_eq]
    _ ≤ b := hfinite K

end NCBall
