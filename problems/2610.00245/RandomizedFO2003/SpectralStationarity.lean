import RandomizedFO2003.SpectralCascade

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates Cascade

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- All hypotheses of the deterministic stationarity theorem are proved for
the constructed spectral cascade on the original good-weight event. -/
theorem cascade_stationarityBounds (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hH : 512 * ε ≤ h)
    (hu : ∀ i, ‖u i‖ = 1)
    (hweight : ∀ i j, |SpectralCoordinates.weight K (u i) j - S.weight j| ≤ (1 / 32) * S.weight j) :
    (S.cascade K N U u h).StationarityBounds (S.cascadeInverse K N U) h γ ε := by
  have hm (i : Fin (N + 1)) := S.continuous_rotated_normalized_moments hγ K (U i) (u i) (hu i)
    h (1 / 32) hh (by norm_num) le_rfl (hweight i)
  refine {
    selfAdjoint := S.cascade_operator_selfAdjoint K N U u h
    inverse_selfAdjoint := S.cascadeInverse_selfAdjoint K N U
    inverse_left := S.cascadeInverse_left hγ K N U u h
    positive_D := by change 0 < h ^ 2 / γ; positivity
    positive_α := by change 0 < h / (64 * γ); positivity
    positive_B := by change 0 < radiusCoefficient * h / γ; exact div_pos (mul_pos radiusCoefficient_pos hh) hγ
    positive_γ := hγ
    saturation_large := by norm_num [cascade, saturationThreshold]
    offset_large := by norm_num [cascade, saturationThreshold, forcingOffset]
    coercive := S.cascade_coercive K N U u h
    rhs_norm := fun i => (hm i).2.1.le
    direction_norm := fun i => (hm i).1.le
    radius_large := parameter_radius_bound hh hγ hH
    s_bounds := fun i => (hm i).2.2.1
    k_bounds := fun i => (hm i).2.2.2.1
    r_bounds := fun i => (hm i).2.2.2.2
    a_error := ?_
    b_error := ?_ }
  · intro i
    change (‖U i (direction K (u i) S.residual)‖ * ‖S.cascadeInverse K N U i‖ * ε) / (h / (64 * γ)) ≤ 1 / 8
    rw [(hm i).1, one_mul]
    apply le_trans _ (parameter_a_error hh hγ hH)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (S.cascadeInverse_norm_le hγ K N U i) hε
  · intro i
    change (‖U i (h • u i)‖ * ‖S.cascadeInverse K N U i‖ * ε) / (h ^ 2 / γ) ≤ 1
    rw [(hm i).2.1]
    apply le_trans _ (parameter_b_error hh hγ hH)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (S.cascadeInverse_norm_le hγ K N U i) hh.le) hε

/-- Near-stationarity forces complete activation for the actual spectral
cascade. The only random-realization assumptions are unit right-hand-side
directions and the good spectral weights. -/
theorem cascade_stationarity (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    (U : Fin (N + 1) → BlockSpace K ≃ₗᵢ[ℝ] BlockSpace K)
    (u : Fin (N + 1) → BlockSpace K) {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hH : 512 * ε ≤ h)
    (hu : ∀ i, ‖u i‖ = 1)
    (hweight : ∀ i j, |SpectralCoordinates.weight K (u i) j - S.weight j| ≤ (1 / 32) * S.weight j)
    (z : BlockProduct (N + 1) (BlockSpace K))
    (hz : ‖gradient (S.cascade K N U u h).energy z‖ ≤ ε) :
    let d := S.cascade K N U u h
    (∀ i, ‖z i‖ ≤ d.B) ∧
    (∀ i, |forcingReadout (d.b i) d.D (z i)| ≤ d.K) ∧
    (∀ i, d.gate i (z i) = 1) ∧
    ‖d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N)‖ ≤ ε :=
  (S.cascade K N U u h).stationarity_from_bounds (S.cascadeInverse K N U)
    (S.cascade_stationarityBounds hγ K N U u hh hε hH hu hweight) z hz

end RandomizedFO2003.FiniteSpectralDesign
