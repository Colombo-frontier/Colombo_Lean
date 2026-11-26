import UpperProgramBlockMeasurable
import HaarRebalancingUpperMarginal

/-! The analysis-only regularization has the same actual adaptive execution.
The resulting expected risk is exactly the risk under the proved iid block law. -/

open MeasureTheory MeasureTheory.Measure Metric
open scoped BigOperators

namespace Task006.Full

theorem upperBlock_point_mem {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ))
    (block : UpperSampleBlock d Ω) (i : Fin d) (sign : ℝ) (hs : |sign| = 1) :
    x + (sign * P.δ) • Task006.HaarRebalancing.column block.1.1 i + P.ρ • (block.1.2 i).val ∈
      queryDomain d P.R := by
  have hu : ‖(block.1.2 i).val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (block.1.2 i).property
  have hq := (Task006.HaarRebalancing.orthonormal_column block.1.1).norm_eq_one i
  have hd : ‖(sign * P.δ) • Task006.HaarRebalancing.column block.1.1 i‖ = P.δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, hs, abs_of_pos P.delta_pos, hq]
    ring
  have hr : ‖P.ρ • (block.1.2 i).val‖ ≤ P.ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg P.rho_nonneg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu P.rho_nonneg
  have hn := norm_add_le (x + (sign * P.δ) • Task006.HaarRebalancing.column block.1.1 i)
    (P.ρ • (block.1.2 i).val)
  have hnx := norm_add_le x ((sign * P.δ) • Task006.HaarRebalancing.column block.1.1 i)
  rw [hd] at hnx
  change dist _ 0 ≤ 2 * P.R
  rw [dist_zero_right]
  linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]

theorem upperBlockDirection_congr {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F F' : Space d → Ω → ℝ) {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ))
    (block : UpperSampleBlock d Ω)
    (hF : ∀ i y, y ∈ queryDomain d P.R → F y (block.2 i) = F' y (block.2 i)) :
    upperBlockDirection P F x block = upperBlockDirection P F' x block := by
  unfold upperBlockDirection orthogonalReconstruct
  apply Finset.sum_congr rfl
  intro i _
  have hp := hF i _ (upperBlock_point_mem P hx block i 1 (by norm_num))
  have hm := hF i _ (upperBlock_point_mem P hx block i (-1) (by norm_num))
  simp only [one_mul, neg_one_mul, neg_smul, sub_eq_add_neg] at hp hm ⊢
  rw [hp, hm]

theorem upperBlockIterate_congr {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F F' : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω)
    (hF : ∀ t i y, y ∈ queryDomain d P.R → F y ((blocks t).2 i) = F' y ((blocks t).2 i))
    (t : ℕ) : upperBlockIterate P F blocks t = upperBlockIterate P F' blocks t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [upperBlockIterate, upperBlockIterate]
    split_ifs with ht
    · rw [ih, upperBlockDirection_congr P F F'
        (upperBlockIterate_norm_le P F' blocks t) (blocks ⟨t, ht⟩) (hF ⟨t, ht⟩)]
    · exact ih

noncomputable def upperBlockOutput {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω) : Space d :=
  iterateAverage (upperBlockIterate P F blocks) T

theorem upperBlockOutput_measurable {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (@upperBlockOutput d T Ω P F) := by
  unfold upperBlockOutput iterateAverage
  exact (Finset.measurable_sum _ (fun t _ => upperBlockIterate_measurable P hF t)).const_smul ((T : ℝ)⁻¹)

theorem upperBlockOutput_norm_le {d T : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (hT : 0 < T) (F : Space d → Ω → ℝ) (blocks : Fin T → UpperSampleBlock d Ω) :
    ‖upperBlockOutput P F blocks‖ ≤ P.R - (P.ρ + P.δ) := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  unfold upperBlockOutput iterateAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ)⁻¹)]
  calc
    (T : ℝ)⁻¹ * ‖∑ t ∈ Finset.range T, upperBlockIterate P F blocks t‖ ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ‖upperBlockIterate P F blocks t‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (T : ℝ)⁻¹ * ∑ _t ∈ Finset.range T, (P.R - (P.ρ + P.δ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => upperBlockIterate_norm_le P F blocks t))
        (by positivity)
    _ = P.R - (P.ρ + P.δ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hTreal.ne']

namespace SampleInstance

theorem upperProgram_output_eq_blockOutput_ae {d T : ℕ} (P : UpperProgramParameters)
    (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L : ℝ} (I : SampleInstance d L P.R Ω μ) (hR : 0 ≤ P.R) :
    (upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample =ᵐ[
      (upperSeedLaw d T).prod (iidHandleLaw μ)]
        fun w => upperBlockOutput P (I.rebalancedSample hR) (upperBlockPath w) := by
  have hTape := iid_all_handles_property μ (I.jointLipschitzSample_spec hR).2.2
  have hPair := (quasiMeasurePreserving_snd (μ := upperSeedLaw d T)).ae hTape
  filter_upwards [hPair] with w hw
  change iterateAverage (upperIterate P w.1
      ((upperPairedProgram P hd).toAlgorithm.finalTranscript I.sample w.2 w.1)) T = _
  unfold upperBlockOutput
  congr 1
  funext t
  rw [upperIterate_eq_blockIterate P hd I w.2 w.1 t]
  exact upperBlockIterate_congr P I.sample (I.rebalancedSample hR) (upperBlockPath w)
    (fun t i y hy => (hw (t.val * d + i.val) y hy).symm) t

theorem upperProgram_risk_eq_block_risk {d T : ℕ} (P : UpperProgramParameters)
    (hd : 0 < d) (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : ℝ} (hL : 0 ≤ L)
    (I : SampleInstance d L P.R Ω μ) (hR : 0 ≤ P.R) :
    (∫ w, (upperPairedProgram P hd).toAlgorithm.realizedGap I w
      ∂(upperSeedLaw d T).prod (iidHandleLaw μ)) =
      ∫ blocks, I.objective (upperBlockOutput P (I.rebalancedSample hR) blocks) - optimalValue I
        ∂Measure.pi (fun _ : Fin T => upperSampleBlockLaw d μ) := by
  let H : (Fin T → UpperSampleBlock d Ω) → ℝ := fun blocks =>
    I.objectiveExtension hL hR (upperBlockOutput P (I.rebalancedSample hR) blocks) - optimalValue I
  have hH : Measurable H :=
    ((I.objectiveExtension_lipschitz hL hR).continuous.measurable.comp
      (upperBlockOutput_measurable P (I.rebalancedSample_measurable hR))).sub measurable_const
  have hext (blocks : Fin T → UpperSampleBlock d Ω) : H blocks =
      I.objective (upperBlockOutput P (I.rebalancedSample hR) blocks) - optimalValue I := by
    have hn := upperBlockOutput_norm_le P hT (I.rebalancedSample hR) blocks
    have hx : upperBlockOutput P (I.rebalancedSample hR) blocks ∈ queryDomain d P.R := by
      change dist _ 0 ≤ 2 * P.R
      rw [dist_zero_right]
      linarith [P.rho_nonneg, P.delta_pos]
    exact congrArg (fun a => a - optimalValue I) (I.objectiveExtension_eq hL hR hx).symm
  calc
    _ = ∫ w, H (upperBlockPath w) ∂(upperSeedLaw d T).prod (iidHandleLaw μ) := by
      apply integral_congr_ae
      filter_upwards [I.upperProgram_output_eq_blockOutput_ae P hd hR] with w hw
      change I.objective ((upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample w) - optimalValue I = _
      rw [hw, hext]
    _ = ∫ blocks, H blocks ∂Measure.pi (fun _ : Fin T => upperSampleBlockLaw d μ) := by
      rw [← upperBlockPath_map hd μ]
      exact (integral_map upperBlockPath_measurable.aemeasurable hH.aestronglyMeasurable).symm
    _ = _ := integral_congr_ae (ae_of_all _ hext)

end SampleInstance

#print axioms SampleInstance.upperProgram_risk_eq_block_risk

end Task006.Full
