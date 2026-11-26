import NCBall.CanonicalOracle
import NCBall.CountableReduction
import NCBall.SmoothLower

/-! # The smooth lower bound for arbitrary reusable sample labels -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

def fixedPopulationValue {n M : ℕ} (ρ γ lam : ℝ) (u : HiddenTable n M) : Space n → ℝ :=
  let U := fixedDirections (Real.sqrt (n : ℝ))⁻¹ u
  chainValue M ρ γ lam (roomCenter ρ U) U

def countableGradientSuccess {S : Type*} [MeasurableSpace S] {n M : ℕ}
    (p : CountableRoomPolicy S n) (ρ η σ : ℝ) (N : ℕ)
    (out : LinearHistory S N → Space n) : Set (HiddenTable n M × (S × (ℕ → SampleNoise n M))) :=
  {w | ‖gradient (fixedPopulationValue ρ (4 * η) (calibratedLam (4 * η)) w.1)
    (out (sampleTranscript p.point p.handle
      (fixedSampleValue ρ (4 * η) (calibratedLam (4 * η)) σ) N w))‖ ≤ η}

theorem countable_terminal_quarter {S : Type*} [MeasurableSpace S]
    {n M q₀ N : ℕ} (ν : Measure S) [IsProbabilityMeasure ν]
    (p : CountableRoomPolicy S n) (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (out : LinearHistory S N → Space n) (hout : Measurable out) :
    ((hiddenTableLaw n M).prod (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n M))))
      {w | (w.1, out (sampleTranscript p.point p.handle (fixedSampleValue ρ γ lam σ) N w))
        ∈ fixedTerminalTarget ρ} ≤ 1 / 4 :=
  countable_outcome_bound (hiddenTableLaw n M) ν (gaussianRooms n M) p _
    (fixedSampleValue_measurable ρ γ lam σ) out hout _ (fixedTerminalTarget_measurable ρ) _
    (fun K => finite_sample_terminal_quarter ν (prefixPolicy p K) hq hN hn hρ hσ γ lam
      hqcap hlog out hout)

theorem exists_countable_hard_gradient {S : Type*} [MeasurableSpace S]
    {n M q₀ N : ℕ} (ν : Measure S) [IsProbabilityMeasure ν]
    (p : CountableRoomPolicy S n) (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ η : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hη : 0 < η)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (hgoodlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n)
    (out : LinearHistory S N → Space n) (hout : Measurable out) :
    ∃ u ∈ fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹,
      (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n M)))
        {rz | (u, rz) ∈ countableGradientSuccess p ρ η σ N out} < 1 / 2 := by
  let F := fixedSampleValue (n := n) (M := M) ρ (4 * η) (calibratedLam (4 * η)) σ
  let B : Set (HiddenTable n M × (S × (ℕ → SampleNoise n M))) :=
    {w | (w.1, out (sampleTranscript p.point p.handle F N w)) ∈ fixedTerminalTarget ρ}
  have hB : MeasurableSet B :=
    (measurable_fst.prodMk (hout.comp (sampleTranscript_measurable _ _ F
      p.measurable_point p.measurable_handle (fixedSampleValue_measurable _ _ _ _) N)))
      (fixedTerminalTarget_measurable ρ)
  have hb : ((hiddenTableLaw n M).prod
      (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n M)))) B ≤ 1 / 4 :=
    countable_terminal_quarter ν p hq hN hn hρ hσ (4 * η) (calibratedLam (4 * η))
      hqcap hlog out hout
  obtain ⟨u, hu, hbad⟩ := exists_good_hard_fiber (hiddenTableLaw n M)
    (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n M)))
    (fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹) (fixedGoodEvent_measurable _) B hB
    (fixed_good_event_probability hn hgoodlog) hb
  refine ⟨u, hu, lt_of_le_of_lt (measure_mono ?_) hbad⟩
  intro rz hs
  exact stationary_point_in_terminal_room hρ hη (fixedDirections (Real.sqrt (n : ℝ))⁻¹ u)
    (fixedDirections_clock _ u) hu _ hs

theorem countable_smooth_evaluation_lower_bound {S : Type*} [MeasurableSpace S]
    {n N : ℕ} (ν : Measure S) [IsProbabilityMeasure ν]
    (p : CountableRoomPolicy S n) (hn : 0 < n) {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (hscale : (4 * η) * (bumpConstant + 2) ≤ L / 4)
    (hlog : 12800 * Real.log (2 + H * Δ * L ^ 2 / η ^ 4) ≤ n)
    (out : LinearHistory S N → Space n) (hout : Measurable out)
    (hsuccess : ∀ u ∈ fixedGoodEvent (n := n)
      (M := calibratedDepth (4 * η) H Δ) (Real.sqrt (n : ℝ))⁻¹,
      (1 / 2 : ℝ≥0∞) ≤
        (ν.prod (Measure.infinitePi (fun _ : ℕ => gaussianRooms n (calibratedDepth (4 * η) H Δ))))
        {rz | (u, rz) ∈ countableGradientSuccess p (calibratedRho (4 * η) H)
          η (L / (4 * η)) N out}) :
    ((n : ℝ) + 1) * L ^ 2 * H * Δ / (3276800 * bumpConstant * η ^ 4) ≤ N := by
  have hγ : 0 < 4 * η := by positivity
  have hq := calibratedCharges_pos hn hγ hscale
  have hdim := calibrated_dimension_condition hη hH hΔ hlog
  have hgood := dimension_good_log hq hdim
  have hbudget : calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L ≤ N := by
    by_contra h
    have hN : N < calibratedDepth (4 * η) H Δ * calibratedCharges n (4 * η) L := by omega
    obtain ⟨u, hu, hb⟩ := exists_countable_hard_gradient ν p hq hN hn
      (calibratedRho_pos hγ hH) (by positivity : 0 < L / (4 * η)) hη
      (calibratedCharges_cap n (4 * η) L) hdim hgood out hout
    exact (not_lt_of_ge (hsuccess u hu)) hb
  exact (calibrated_smooth_complexity_lower hn hη hH hΔ hregime hscale).trans
    (by exact_mod_cast hbudget)

end NCBall
