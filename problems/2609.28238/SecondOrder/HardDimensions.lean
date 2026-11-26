import SecondOrder.MinimaxEndpointLower

open Filter
open scoped Topology

namespace SecondOrder
noncomputable section

def firstOrderHvpDimension (P : Parameters) (ε : ℝ) : ℕ :=
  FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε)
    (firstOrderEndpointLinks P.gap ε)

def firstOrderRichDimension (P : Parameters) (σ₀ ε : ℝ) : ℕ :=
  FirstOrderDimension (firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε)
    (firstOrderEndpointLinks P.gap ε)

def curvatureHvpDimension (P : Parameters) (γ ν : ℝ) : ℕ :=
  CurvatureDimension (curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)
    (curvatureHolderLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν)

def curvatureRichDimension (P : Parameters) (γ : ℝ) : ℕ :=
  CurvatureDimension (curvatureEndpointHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ)
    (curvatureEndpointLinks P.gap P.hessianHolder (curvatureNoiseBudget P) γ)

theorem firstOrderHvpDimension_pos (P : Parameters) {ε : ℝ} (hε : 0<ε) : 0<firstOrderHvpDimension P ε :=
  Nat.mul_pos (Nat.succ_pos _) (firstOrderEndpointBlockSize_bounds P.gap_pos.le hε).1

theorem firstOrderRichDimension_pos (P : Parameters) (σ₀ : ℝ) {ε : ℝ} (hε : 0<ε) :
    0<firstOrderRichDimension P σ₀ ε :=
  Nat.mul_pos (Nat.succ_pos _) (firstOrderEndpointBlockSize_bounds P.gap_pos.le hε).1

theorem curvatureHvpDimension_pos (P : Parameters) {γ : ℝ} (hγ : 0<γ) (ν : ℝ) :
    0<curvatureHvpDimension P γ ν := by
  have hm := (curvatureEndpointHalfSize_bounds (L := curvatureHolderEffectiveL P.hessianHolder γ ν)
    (σ := curvatureNoiseBudget P) P.gap_pos.le hγ).1
  have hm0 : 0<curvatureHolderHalfSize P.gap P.hessianHolder (curvatureNoiseBudget P) γ ν := by
    unfold curvatureHolderHalfSize
    omega
  exact Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (by norm_num) hm0)

theorem curvatureRichDimension_pos (P : Parameters) {γ : ℝ} (hγ : 0<γ) :
    0<curvatureRichDimension P γ := by
  have hm := (curvatureEndpointHalfSize_bounds (L := P.hessianHolder)
    (σ := curvatureNoiseBudget P) P.gap_pos.le hγ).1
  exact Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (by norm_num) (by omega))

/-- A one-variable normalized dimension bound suffices for the paper's
two-tolerance envelope. The other tolerance only enlarges that envelope. -/
theorem dimension_le_toleranceEnvelope_left {d : ℕ} {κ ε γ : ℝ}
    (hκ : 0≤κ) (hε : 0<ε) (hγ : 0<γ) (hγ1 : γ≤1) (hd : (d:ℝ)*ε^κ≤1) :
    d≤toleranceDimensionEnvelope κ ε γ := by
  have hp := Real.rpow_le_rpow (mul_nonneg hε.le hγ.le)
    (mul_le_of_le_one_right hε.le hγ1) hκ
  have hm := (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg d)).trans hd
  have hh : (d:ℝ)≤(ε*γ)^(-κ) := by
    rw [Real.rpow_neg (mul_nonneg hε.le hγ.le),←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (mul_pos hε hγ) κ)).2 (by simpa only [mul_one] using hm)
  exact_mod_cast hh.trans (Nat.le_ceil ((ε*γ)^(-κ)))

theorem dimension_le_toleranceEnvelope_right {d : ℕ} {κ ε γ : ℝ}
    (hκ : 0≤κ) (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hd : (d:ℝ)*γ^κ≤1) :
    d≤toleranceDimensionEnvelope κ ε γ := by
  simpa only [toleranceDimensionEnvelope,mul_comm] using
    dimension_le_toleranceEnvelope_left hκ hγ hε hε1 hd

theorem firstOrderHvpDimension_normalized_tendsto (P : Parameters) {ν κ : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (hκ : 1<κ) :
    Tendsto (fun ε : ℝ => (firstOrderHvpDimension P ε:ℝ)*ε^κ) (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun ε : ℝ => P.gap*
      ((firstOrderEndpointBlockSize P.gap (firstOrderHolderNoiseBudget P) ε:ℝ)*ε^(κ-1))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (firstOrderEndpointBlockSize_mul_rpow_tendsto (s := firstOrderHolderNoiseBudget P) P.gap_pos.le
        (sub_pos.mpr hκ)).const_mul P.gap
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (show 0≤ε from le_of_lt hε) _)
  · filter_upwards [self_mem_nhdsWithin,firstOrderHolderConditions_eventually P hν hν1] with ε hε hc
    have hh := mul_le_mul_of_nonneg_right (firstOrderHolderEndpoint_dimension P hc)
      (Real.rpow_nonneg (show 0≤ε from le_of_lt hε) κ)
    change (firstOrderHvpDimension P ε:ℝ)*ε^κ≤_ at hh
    apply hh.trans_eq
    rw [Real.rpow_sub hε,Real.rpow_one]
    ring

theorem firstOrderRichDimension_normalized_tendsto (P : Parameters) {σ₀ κ : ℝ}
    (hσ₀ : 0<σ₀) (hκ : 1<κ) :
    Tendsto (fun ε : ℝ => (firstOrderRichDimension P σ₀ ε:ℝ)*ε^κ) (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun ε : ℝ => P.gap*
      ((firstOrderEndpointBlockSize P.gap (firstOrderNoiseBudget P σ₀) ε:ℝ)*ε^(κ-1))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (firstOrderEndpointBlockSize_mul_rpow_tendsto (s := firstOrderNoiseBudget P σ₀) P.gap_pos.le
        (sub_pos.mpr hκ)).const_mul P.gap
  apply squeeze_zero' _ _ hup
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (show 0≤ε from le_of_lt hε) _)
  · filter_upwards [self_mem_nhdsWithin,firstOrderEndpointConditions_eventually P hσ₀] with ε hε hc
    have hh := mul_le_mul_of_nonneg_right (firstOrderEndpoint_dimension P hc)
      (Real.rpow_nonneg (show 0≤ε from le_of_lt hε) κ)
    change (firstOrderRichDimension P σ₀ ε:ℝ)*ε^κ≤_ at hh
    apply hh.trans_eq
    rw [Real.rpow_sub hε,Real.rpow_one]
    ring

end
end SecondOrder
