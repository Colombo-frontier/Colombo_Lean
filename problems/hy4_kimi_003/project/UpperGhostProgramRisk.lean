import UpperGhostFeasible

/-! The paper's actual-to-ghost risk correction for the original algorithm,
not merely a conditional statement about abstract agreeing random variables. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set
namespace Task006.Full.SampleInstance

variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : Task006.Full.SampleInstance d L P.R Ω μ)

noncomputable def upperGhostLoss (hL : 0 ≤ L) (hR : 0 ≤ P.R) (T : ℕ)
    (state : UpperGhostState d) : ℝ :=
  I.objectiveExtension hL hR (ballProj P.R hR ((T : ℝ)⁻¹ • state.2)) - optimalValue I

theorem upperGhostLoss_measurable (hL : 0 ≤ L) (hR : 0 ≤ P.R) (T : ℕ) :
    Measurable (I.upperGhostLoss P hL hR T) := by
  exact ((I.objectiveExtension_lipschitz hL hR).continuous.measurable.comp
    ((ballProj_lipschitz (E := Space d) hR).continuous.measurable.comp
      (measurable_snd.const_smul ((T : ℝ)⁻¹)))).sub measurable_const

theorem upperGhostLoss_bounds (hL : 0 ≤ L) (hR : 0 ≤ P.R) (T : ℕ) (state : UpperGhostState d) :
    0 ≤ I.upperGhostLoss P hL hR T state ∧ I.upperGhostLoss P hL hR T state ≤ 2 * L * P.R := by
  have hp := ballProj_mem P.R hR ((T : ℝ)⁻¹ • state.2)
  have hpq : ballProj P.R hR ((T : ℝ)⁻¹ • state.2) ∈ queryDomain d P.R := by
    have hn : ‖ballProj P.R hR ((T : ℝ)⁻¹ • state.2)‖ ≤ P.R := by simpa using hp
    change dist _ 0 ≤ 2 * P.R
    rw [dist_zero_right]
    linarith
  unfold upperGhostLoss
  rw [← I.objectiveExtension_eq hL hR hpq]
  exact I.objective_gap_bounds hL hR hp

theorem upperGhostLoss_eq (hL : 0 ≤ L) (hR : 0 ≤ P.R) (T : ℕ) (state : UpperGhostState d)
    (hs : ‖(T : ℝ)⁻¹ • state.2‖ ≤ P.R) :
    I.upperGhostLoss P hL hR T state = I.objective ((T : ℝ)⁻¹ • state.2) - optimalValue I := by
  unfold upperGhostLoss
  rw [ballProj_eq_self hR hs]
  have hq : (T : ℝ)⁻¹ • state.2 ∈ queryDomain d P.R := by
    change dist _ 0 ≤ 2 * P.R
    rw [dist_zero_right]
    linarith
  rw [← I.objectiveExtension_eq hL hR hq]

set_option maxHeartbeats 1000000 in
theorem upperGhost_actual_risk_transfer {T : ℕ} (hd : 0 < d) (hT : 0 < T)
    (hR : 0 ≤ P.R) (hL : 0 < L) (s : ℝ) (hs : 1 ≤ s) (hq : (d : ℝ) * Real.exp (-s) < 1) :
    (∫ w, (upperPairedProgram P hd).toAlgorithm.realizedGap I w
      ∂(upperSeedLaw d T).prod (iidHandleLaw μ)) ≤
        (∫ j, I.objective ((T : ℝ)⁻¹ • j.1.2.2) - optimalValue I
          ∂I.upperGhostLaw P hR hL hd s hs hq T) + 2 * L * P.R * (T * ((d : ℝ) * Real.exp (-s))) := by
  let F := I.rebalancedSample hR
  let G := I.upperGhostGood P hR s
  let ν := upperSampleBlockLaw d μ
  let step := upperGhostStep (d := d) (Ω := Ω) P F
  have hF : Measurable (Function.uncurry F) := I.rebalancedSample_measurable hR
  have hstep : Measurable step := upperGhostStep_measurable P hF
  have hG := I.upperGhostGood_measurable P hR s
  have hpos := I.upperGhostGood_pos P hR hL hd hs hq
  let π := I.upperGhostLaw P hR hL hd s hs hq T
  have hbad (x : UpperGhostState d) : ν (G x)ᶜ ≤ ENNReal.ofReal ((d : ℝ) * Real.exp (-s)) := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    exact I.upperGhostGood_bad_probability P hR hL hd hs x
  have ht := ghostProcess_risk_transfer ν G hG hpos step hstep (0, 0)
    (by positivity : 0 ≤ (d : ℝ) * Real.exp (-s)) (by positivity : 0 ≤ 2 * L * P.R) hbad
    (I.upperGhostLoss P hL.le hR T) (I.upperGhostLoss_measurable P hL.le hR T)
    (I.upperGhostLoss_bounds P hL.le hR T) T
  have hmap : π.map (fun j => j.1.1) =
      (Measure.pi (fun _ : Fin T => ν)).map (fun blocks => iidState step (0, 0) blocks T) :=
    ghostProcess_actual_iid ν G hG hpos step hstep (0, 0)
  have hloss := I.upperGhostLoss_measurable P hL.le hR T
  have hact : Measurable (fun j : GhostState (UpperGhostState d) => j.1.1) := measurable_fst.comp measurable_fst
  have hiid : Measurable (fun blocks : Fin T → UpperSampleBlock d Ω => iidState step (0, 0) blocks T) :=
    iidState_measurable step hstep (0, 0) T
  have hleft : (∫ j, I.upperGhostLoss P hL.le hR T j.1.1 ∂π) =
      ∫ w, (upperPairedProgram P hd).toAlgorithm.realizedGap I w
        ∂(upperSeedLaw d T).prod (iidHandleLaw μ) := by
    calc
      _ = ∫ x, I.upperGhostLoss P hL.le hR T x ∂π.map (fun j => j.1.1) :=
        (integral_map hact.aemeasurable hloss.aestronglyMeasurable).symm
      _ = ∫ blocks, I.upperGhostLoss P hL.le hR T (iidState step (0, 0) blocks T)
          ∂Measure.pi (fun _ : Fin T => ν) := by
        rw [hmap, integral_map hiid.aemeasurable hloss.aestronglyMeasurable]
      _ = ∫ blocks, I.objective (upperBlockOutput (d := d) (T := T) (Ω := Ω) P F blocks) - optimalValue I
          ∂Measure.pi (fun _ : Fin T => ν) := by
        apply integral_congr_ae
        filter_upwards [] with blocks
        have hout : (T : ℝ)⁻¹ • (iidState step (0, 0) blocks T).2 = upperBlockOutput P F blocks := by
          rw [upperGhost_iid_sum P F blocks T le_rfl]
          rfl
        have hn := upperBlockOutput_norm_le P hT F blocks
        have hR' : P.R - (P.ρ + P.δ) ≤ P.R := by linarith [P.rho_nonneg, P.delta_pos]
        have heq := I.upperGhostLoss_eq P hL.le hR T (iidState step (0, 0) blocks T)
          (by rw [hout]; exact hn.trans hR')
        rw [heq, hout]
      _ = _ := (I.upperProgram_risk_eq_block_risk P hd hT hL.le hR).symm
  have hfeas : ∀ᵐ j ∂π, upperGhostFeasible P T j :=
    ghostProcess_upperStep_feasible P F hF ν G hG hpos T
  have hright : (∫ j, I.upperGhostLoss P hL.le hR T j.1.2 ∂π) =
      ∫ j, I.objective ((T : ℝ)⁻¹ • j.1.2.2) - optimalValue I ∂π := by
    apply integral_congr_ae
    filter_upwards [hfeas] with j hj
    apply I.upperGhostLoss_eq P hL.le hR T j.1.2
    exact (upperGhost_average_norm_le P hT hj.2.2.2).trans
      (by linarith [P.rho_nonneg, P.delta_pos] : P.R - (P.ρ + P.δ) ≤ P.R)
  change (∫ j, I.upperGhostLoss P hL.le hR T j.1.1 ∂π) ≤
    (∫ j, I.upperGhostLoss P hL.le hR T j.1.2 ∂π) + 2 * L * P.R * (T * ((d : ℝ) * Real.exp (-s))) at ht
  rwa [hleft, hright] at ht

#print axioms upperGhost_actual_risk_transfer
end Task006.Full.SampleInstance
