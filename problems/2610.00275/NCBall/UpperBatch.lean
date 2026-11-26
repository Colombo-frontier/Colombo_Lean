import NCBall.UpperConvergence

/-! # Batch averaging and the local objective gap -/

noncomputable section
open MeasureTheory Metric
open scoped InnerProductSpace BigOperators unitInterval
namespace NCBall

theorem sum_block_telescope (b : ℕ → ℝ) (m K : ℕ) :
    (∑ k ∈ Finset.range K, (b (k * m + m) - b (k * m))) = b (K * m) - b 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul]
    ring

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {G : E → Ξ → E} {f : E → ℝ} {V : ℝ}

theorem upper_expected_batches (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    {D α Δ : ℝ} (hD : 0 ≤ D) (hα : 0 < α) (x₀ : E) (m K : ℕ)
    (hgap : ∀ w : UpperRandomness Ξ,
      f x₀ - f (upperState D hD α G x₀ w.1 w.2 (K * m)).1 ≤ Δ) :
    D * (∫ w : UpperRandomness Ξ, ∑ k ∈ Finset.range K,
      ‖∑ t ∈ Finset.range m, gradient f (upperLocation D hD α G x₀ w.1 w.2 (k * m + t))‖
        ∂upperPoolLaw μ) ≤
      (K : ℝ) * (2 * D ^ 2 / α + (α / 2) * (m : ℝ) * V ^ 2 + D * (Real.sqrt (m : ℝ) * |V|)) + Δ := by
  let A := fun k (w : UpperRandomness Ξ) =>
    ‖∑ t ∈ Finset.range m, gradient f (upperLocation D hD α G x₀ w.1 w.2 (k * m + t))‖
  let B := fun k (w : UpperRandomness Ξ) =>
    f (upperState D hD α G x₀ w.1 w.2 (k * m + m)).1 - f (upperState D hD α G x₀ w.1 w.2 (k * m)).1
  let C := 2 * D ^ 2 / α + (α / 2) * (m : ℝ) * V ^ 2 + D * (Real.sqrt (m : ℝ) * |V|)
  have hA : ∀ k, Integrable (A k) (upperPoolLaw μ) := fun k =>
    (memLp_finset_sum (Finset.range m) (fun t _ => upperMean_memLp ho D hD α x₀ (k * m + t))).norm.integrable
      (by norm_num)
  have hB : ∀ k, Integrable (B k) (upperPoolLaw μ) := fun k =>
    upper_block_difference_integrable hf ho D hD α x₀ (k * m) m
  have hb (k : ℕ) : D * (∫ w, A k w ∂upperPoolLaw μ) ≤ C - ∫ w, B k w ∂upperPoolLaw μ := by
    have hk := upper_expected_block_gradient hf ho hD hα x₀ (k * m) m
    dsimp only [A, B, C]
    linarith
  have hs := Finset.sum_le_sum (fun k (_hk : k ∈ Finset.range K) => hb k)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  rw [← integral_finset_sum _ (fun k _ => hA k), ← integral_finset_sum _ (fun k _ => hB k)] at hs
  have ht (w : UpperRandomness Ξ) :
      (∑ k ∈ Finset.range K, B k w) = f (upperState D hD α G x₀ w.1 w.2 (K * m)).1 - f x₀ := by
    simpa only [upperState] using sum_block_telescope
      (fun t => f (upperState D hD α G x₀ w.1 w.2 t).1) m K
  simp only [ht] at hs
  have hfinal : Integrable (fun w : UpperRandomness Ξ =>
      f (upperState D hD α G x₀ w.1 w.2 (K * m)).1 - f x₀) (upperPoolLaw μ) := by
    simpa only [zero_add, upperState] using upper_block_difference_integrable hf ho D hD α x₀ 0 (K * m)
  have hlow : -Δ ≤ ∫ w : UpperRandomness Ξ,
      f (upperState D hD α G x₀ w.1 w.2 (K * m)).1 - f x₀ ∂upperPoolLaw μ := by
    calc
      _ = ∫ _w : UpperRandomness Ξ, -Δ ∂upperPoolLaw μ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hfinal (fun w => by linarith [hgap w])
  exact hs.trans (by dsimp only [C]; linarith)

theorem upper_expected_batches_local (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    {D α Δ R : ℝ} (hD : 0 ≤ D) (hα : 0 < α) (x₀ : E) (m K : ℕ)
    (hpath : (K * m : ℕ) * D ≤ R)
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    D * (∫ w : UpperRandomness Ξ, ∑ k ∈ Finset.range K,
      ‖∑ t ∈ Finset.range m, gradient f (upperLocation D hD α G x₀ w.1 w.2 (k * m + t))‖
        ∂upperPoolLaw μ) ≤
      (K : ℝ) * (2 * D ^ 2 / α + (α / 2) * (m : ℝ) * V ^ 2 + D * (Real.sqrt (m : ℝ) * |V|)) + Δ := by
  apply upper_expected_batches hf ho hD hα x₀ m K
  intro w
  apply hgap
  rw [mem_closedBall, dist_eq_norm]
  exact (upper_state_location_bound D hD α G x₀ w.1 w.2 (K * m)).trans hpath

theorem upper_expected_average_local (hf : ContDiff ℝ 1 f)
    (ho : OracleMoments μ G (gradient f) V)
    {D α Δ R : ℝ} (hD : 0 < D) (hα : 0 < α) (x₀ : E) {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (hpath : (K * m : ℕ) * D ≤ R)
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    (K : ℝ)⁻¹ * (∫ w : UpperRandomness Ξ, ∑ k ∈ Finset.range K,
      ‖(m : ℝ)⁻¹ • ∑ t ∈ Finset.range m,
        gradient f (upperLocation D hD.le α G x₀ w.1 w.2 (k * m + t))‖ ∂upperPoolLaw μ) ≤
      Δ / (D * (m : ℝ) * (K : ℝ)) + 2 * D / (α * (m : ℝ)) + α * V ^ 2 / (2 * D) +
        Real.sqrt (m : ℝ) * |V| / (m : ℝ) := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hK' : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hb := upper_expected_batches_local hf ho hD.le hα x₀ m K hpath hgap
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hm'.le),
    ← Finset.mul_sum, integral_const_mul]
  apply (mul_le_mul_iff_of_pos_left (mul_pos (mul_pos hD hm') hK')).mp
  convert hb using 1 <;> field_simp <;> ring

end NCBall
