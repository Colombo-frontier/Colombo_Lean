import NCBall.UpperRandomOutput
import NCBall.UpperParameters
import NCBall.LocalGoldsteinGap

/-! # A calibrated first-order local Goldstein guarantee

This theorem concerns the explicitly defined iid oracle algorithm. The
zeroth-order estimator and nonsmooth smoothing remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped unitInterval
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]

theorem calibrated_first_order_success {G : E → Ξ → E} {f : E → ℝ} {V Δ ν ε R : ℝ}
    (hf : ContDiff ℝ 1 f) (ho : OracleMoments μ G (gradient f) V)
    (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) (hΔ : ν * ε ≤ Δ)
    (hR : 5 * Δ / ε ≤ R) (x₀ : E) (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    ∃ (D α : ℝ) (hD : 0 ≤ D) (m K : ℕ) (hK : 0 < K),
      0 < D ∧ 0 < α ∧ 0 < m ∧ (m : ℝ) * D = ν ∧
      (K * m : ℕ) ≤ 725 * V ^ 2 * Δ / (ν * ε ^ 3) ∧
      Measurable (upperRandomOutput D hD α G x₀ m (K := K)) ∧
      (∀ w : UpperRandomness Ξ, ∀ t < K * m, upperLocation D hD α G x₀ w.1 w.2 t ∈ closedBall x₀ R) ∧
      (∀ w : UpperRandomness Ξ × Fin K, upperRandomOutput D hD α G x₀ m w ∈ closedBall x₀ R) ∧
      ∃ S : Set (UpperRandomness Ξ × Fin K), MeasurableSet S ∧ (1 / 2 : ℝ) ≤ (upperOutputLaw μ K hK).real S ∧
        ∀ w ∈ S, clarkeGoldsteinResidual f ν (upperRandomOutput D hD α G x₀ m w) ≤ ε := by
  let D := upperClipRadius V ν ε
  let α := upperLearningRate V ν ε
  let m := upperBlockLength V ε
  let K := upperBlockCount Δ ν ε
  have hD : 0 < D := upperClipRadius_pos hν hε hV
  have hα : 0 < α := upperLearningRate_pos hν hε hV
  have hm : 0 < m := upperBlockLength_pos hε hV
  have hK : 0 < K := upperBlockCount_pos hν hε hΔ
  have hradius : (m : ℝ) * D = ν := upper_block_radius_eq hε hV
  have hpath : (K * m : ℕ) * D ≤ R := (upper_total_path_bound hν hε hV hΔ).trans hR
  refine ⟨D, α, hD.le, m, K, hK, hD, hα, hm, hradius, upper_total_steps_bound hν hε hV hΔ,
    upperRandomOutput_measurable D hD.le α G ho.measurable x₀ m K, ?_, ?_, ?_⟩
  · intro w t ht
    rw [mem_closedBall, dist_eq_norm]
    exact (upper_sample_location_bound D hD.le α G x₀ w.1 w.2 t).trans
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast (show t + 1 ≤ K * m by omega)) hD.le).trans hpath)
  · intro w
    exact (closedBall_subset_closedBall hpath) (upperRandomOutput_in_ball D hD.le α G x₀ hm w)
  · obtain ⟨S, hS, hmass, hsuccess⟩ := upperRandomOutput_success hf ho hD hα hε x₀ hm hK hpath hgap
      (upper_parameter_accuracy hν hε hV hΔ)
    refine ⟨S, hS, hmass, ?_⟩
    intro w hw
    simpa only [hradius] using (hsuccess w hw).2

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
theorem upperRandomOutput_one (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (w : UpperRandomness Ξ × Fin 1) : upperRandomOutput D hD α G x₀ 1 w = x₀ := by
  have hk : w.2.val = 0 := by omega
  simp [upperRandomOutput, upperOutput, hk, upperLocation, upperState]

theorem first_order_local_success {G : E → Ξ → E} {f : E → ℝ} {V Δ ν ε R : ℝ}
    (hf : ContDiff ℝ 1 f) (ho : OracleMoments μ G (gradient f) V)
    (hν : 0 < ν) (hε : 0 < ε) (hV : ε ≤ V) (hΔ : 0 ≤ Δ) (hRpos : 0 < R)
    (hR : 5 * Δ / ε ≤ R) (x₀ : E) (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    ∃ (D α : ℝ) (hD : 0 ≤ D) (m K : ℕ) (hK : 0 < K),
      0 < α ∧ 0 < m ∧ (m : ℝ) * D ≤ ν ∧
      (K * m : ℕ) ≤ 725 * (1 + V ^ 2 * Δ / (ν * ε ^ 3)) ∧
      Measurable (upperRandomOutput D hD α G x₀ m (K := K)) ∧
      (∀ w : UpperRandomness Ξ, ∀ t < K * m, upperLocation D hD α G x₀ w.1 w.2 t ∈ closedBall x₀ R) ∧
      (∀ w : UpperRandomness Ξ × Fin K, upperRandomOutput D hD α G x₀ m w ∈ closedBall x₀ R) ∧
      ∃ S : Set (UpperRandomness Ξ × Fin K), MeasurableSet S ∧ (1 / 2 : ℝ) ≤ (upperOutputLaw μ K hK).real S ∧
        ∀ w ∈ S, clarkeGoldsteinResidual f ν (upperRandomOutput D hD α G x₀ m w) ≤ ε := by
  by_cases hdeep : ν * ε ≤ Δ
  · obtain ⟨D, α, hD, m, K, hK, hDpos, hα, hm, hradius, hsteps, hmeas, hqueries, houtputs, hsuccess⟩ :=
      calibrated_first_order_success hf ho hν hε hV hdeep hR x₀ hgap
    refine ⟨D, α, hD, m, K, hK, hα, hm, hradius.le, ?_, hmeas, hqueries, houtputs, hsuccess⟩
    calc
      _ ≤ 725 * V ^ 2 * Δ / (ν * ε ^ 3) := hsteps
      _ ≤ _ := by ring_nf; linarith
  · have hstationary : clarkeGoldsteinResidual f ν x₀ ≤ ε := by
      by_cases hd : Δ = 0
      · have hz := zero_gap_start_stationary hf x₀ hν hRpos (by simpa only [hd] using hgap)
        exact hz.trans hε.le
      · have hdpos : 0 < Δ := lt_of_le_of_ne hΔ (Ne.symm hd)
        apply large_radius_start_stationary hf x₀ hdpos hε
        · exact (div_le_iff₀ hε).2 (by linarith)
        · have hnonneg : 0 ≤ Δ / ε := div_nonneg hΔ hε.le
          calc
            _ ≤ 5 * Δ / ε := by ring_nf at hnonneg ⊢; linarith
            _ ≤ R := hR
        · exact hgap
    refine ⟨0, 1, le_rfl, 1, 1, by norm_num, by norm_num, by norm_num, by simpa using hν.le,
      ?_, upperRandomOutput_measurable 0 le_rfl 1 G ho.measurable x₀ 1 1, ?_, ?_, ?_⟩
    · have hp : 0 ≤ V ^ 2 * Δ / (ν * ε ^ 3) := by positivity
      norm_num
      nlinarith
    · intro w t ht
      have ht0 : t = 0 := by omega
      simpa only [ht0, upperLocation, upperState, smul_zero, add_zero] using mem_closedBall_self hRpos.le (x := x₀)
    · intro w
      rw [upperRandomOutput_one]
      exact mem_closedBall_self hRpos.le
    · refine ⟨univ, MeasurableSet.univ, by norm_num, ?_⟩
      intro w _
      rw [upperRandomOutput_one]
      exact hstationary

end NCBall
