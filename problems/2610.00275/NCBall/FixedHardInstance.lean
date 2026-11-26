import NCBall.FixedExperiment

/-! # A fixed good instance defeats the actual reusable-handle algorithm -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

theorem exists_fixed_hard_gradient {R : Type*} [MeasurableSpace R]
    {n H M q₀ N : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ η : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hη : 0 < η)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (hgoodlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out) :
    ∃ u ∈ fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹,
      (ν.prod (sampleTableLaw n H M))
        {rz | experimentFromSplit (u, rz) ∈
          fullGradientSuccess p ρ η σ (Real.sqrt (n : ℝ))⁻¹ N out} < 1 / 2 := by
  obtain ⟨u, hgood, hu⟩ := exists_fixed_hard_terminal ν p hq hN hn hρ hσ (4 * η)
    (calibratedLam (4 * η)) hqcap hlog hgoodlog out hout
  refine ⟨u, hgood, lt_of_le_of_lt (measure_mono ?_) hu⟩
  intro rz hs
  apply full_success_on_good_subset_terminal p hρ hη σ _ N out
  refine ⟨hs, ?_⟩
  change ∀ j < M, ‖latentDirections (Real.sqrt (n : ℝ))⁻¹
    ((splitRoomEquiv n H M).symm (u, rz.2)) j‖ ≤ 2
  rw [combined_latentDirections]
  exact hgood

theorem fixedDirections_clock {n M : ℕ} (scale : ℝ) (u : HiddenTable n M) (j : ℕ) :
    fixedDirections scale u j 0 = 0 := by
  unfold fixedDirections finiteRoomExtension
  split_ifs <;> simp [transverseEmbed_clock]

/-- Explicit-parameter lower-bound core. The fixed good hidden directions
are chosen after the algorithm; all seed and sample randomness remains random.
The analytic function-class theorem applies to the same fixed directions. -/
theorem fixed_hard_instance_core {R : Type*} [MeasurableSpace R]
    {n K q₀ N : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n K) (hn : 0 < n) {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hregime : 200 * bumpConstant * (4 * η) ^ 2 ≤ H * Δ)
    (hscale : (4 * η) * (bumpConstant + 2) ≤ L / 4)
    (hq : 0 < q₀) (hqcap : (q₀ : ℝ) ≤ n * (L / (4 * η)) ^ 2 / 16)
    (hN : N < calibratedDepth (4 * η) H Δ * q₀)
    (hlog : 40 * Real.log (2 + (calibratedDepth (4 * η) H Δ * q₀ : ℕ)) ≤ n)
    (hgoodlog : 2 * Real.log (8 * ((calibratedDepth (4 * η) H Δ : ℝ) + 1)) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out) :
    ∃ u ∈ fixedGoodEvent (n := n) (M := calibratedDepth (4 * η) H Δ) (Real.sqrt (n : ℝ))⁻¹,
      let U := fixedDirections (Real.sqrt (n : ℝ))⁻¹ u
      let M := calibratedDepth (4 * η) H Δ
      let ρ := calibratedRho (4 * η) H
      let f := chainValue M ρ (4 * η) (calibratedLam (4 * η)) (roomCenter ρ U) U
      LipschitzWith ⟨H, hH.le⟩ (gradient f) ∧
      f 0 - sInf (f '' Metric.closedBall 0 (37 * M * ρ)) ≤ Δ ∧
      (ν.prod (sampleTableLaw n K M))
        {rz | experimentFromSplit (u, rz) ∈ fullGradientSuccess p ρ η (L / (4 * η))
          (Real.sqrt (n : ℝ))⁻¹ N out} < 1 / 2 := by
  have hρ := calibratedRho_pos (by positivity : 0 < 4 * η) hH
  obtain ⟨u, hu, hb⟩ := exists_fixed_hard_gradient ν p hq hN hn hρ
    (by positivity : 0 < L / (4 * η)) hη hqcap hlog hgoodlog out hout
  refine ⟨u, hu, ?_⟩
  dsimp only
  have hc := function_class_verification hn hη hH hΔ hL.le hregime hscale hgoodlog
    (fixedDirections (Real.sqrt (n : ℝ))⁻¹ u) (fixedDirections_clock _ u) hu
  exact ⟨hc.2.2.2.1, hc.2.2.2.2.1, hb⟩

end NCBall
