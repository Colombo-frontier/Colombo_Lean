import MatchingBounds1005.ChainSmoothness
import MatchingBounds1005.ParameterThreshold
import MatchingBounds1005.Model

/-! The source calibration proposition, with explicit positive thresholds.
The positive parameter is `t` and the accuracy is exactly `ε=t³`. -/
noncomputable section
open scoped InnerProductSpace BigOperators ContDiff

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen

def accuracyParameter (ε : ℝ) : ℝ := ε ^ (1 / 3 : ℝ)

theorem accuracyParameter_pos {ε : ℝ} (hε : 0 < ε) : 0 < accuracyParameter ε :=
  Real.rpow_pos_of_pos hε _

theorem accuracyParameter_cube {ε : ℝ} (hε : 0 ≤ ε) : accuracyParameter ε ^ 3 = ε := by
  simpa only [accuracyParameter, one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (n := 3) hε (by norm_num)

theorem accuracyParameter_small {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hsmall : ε ≤ δ ^ 3) : accuracyParameter ε ≤ δ := by
  have h := Real.rpow_le_rpow hε hsmall (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have heq : (δ ^ 3) ^ (1 / 3 : ℝ) = δ := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (n := 3) hδ (by norm_num)
  rwa [heq] at h

theorem cube_rate {t : ℝ} (ht : 0 < t) : Model.rate (t ^ 3) = 1 / t ^ 5 := by
  unfold Model.rate
  rw [← Real.rpow_natCast_mul ht.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg ht.le, show t ^ (5 : ℝ) = t ^ (5 : ℕ) from Real.rpow_natCast t 5]
  simp only [one_div]

theorem threshold_path_small {a L t : ℝ} (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)
    (htδ : t ≤ smallThreshold a L) : pathScale a L t ≤ 1 / 4 :=
  (smallThreshold_requirements ha hL ht htδ).2.1.trans (by norm_num)

/-- A fixed amplitude constant and a fixed positive threshold give genuine
uniform derivative, gap, gradient, and horizon bounds for every smaller t.
The actual finite path matrix, smooth primitive, objective, and gradient all
occur in the conclusion; no hard-instance regularity is assumed. -/
theorem exists_uniform_calibration (p : ℕ) (L : ℝ) (hL : 0 < L) :
    ∃ (a : ℝ) (ha : 0 < a), 0 < smallThreshold a L ∧
      ∀ (t : ℝ) (ht : 0 < t) (htδ : t ≤ smallThreshold a L),
        let G := geometry a L t ha hL ht (threshold_path_small ha hL ht htδ)
        let N := phaseCount a t
        let X := BlockGeometry.BlockSpace
          (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) (N - 1)
        1 ≤ N ∧ 1 ≤ amplitude a t ∧
        (∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ z : X,
          ‖iteratedFDeriv ℝ (q + 1) (G.euclideanObjective (amplitude a t) (N - 1)) z‖ ≤ 16 * L) ∧
        (∀ z : X, G.euclideanObjective (amplitude a t) (N - 1) 0 -
          G.euclideanObjective (amplitude a t) (N - 1) z ≤ 1 / 4) ∧
        (∀ z : X, ⟪G.a, z (Fin.last (N - 1))⟫_ℝ = 0 →
          32 * t ^ 3 ≤ ‖gradient (G.euclideanObjective (amplitude a t) (N - 1)) z‖) ∧
        (a / (2880 * 8192 * Real.sqrt (8192 * a / L)) ≤
            ((N * pathSize (pathScale a L t) : ℕ) : ℝ) * t ^ 5 ∧
          ((N * pathSize (pathScale a L t) : ℕ) : ℝ) * t ^ 5 ≤
            a / (720 * 8192 * Real.sqrt (8192 * a / L))) := by
  obtain ⟨C, hC, hprim⟩ := Primitive.finite_order_bounds p
  let a := coreAmplitude L C
  have ha : 0 < a := coreAmplitude_pos hL C
  have hb : 18 * 8192 * C * a ^ 3 ≤ 4 * L :=
    (coreAmplitude_budget hL hC).trans (by linarith)
  refine ⟨a, ha, smallThreshold_pos ha hL, fun t ht htδ => ?_⟩
  obtain ⟨hr, hpath, hgap⟩ := smallThreshold_requirements ha hL ht htδ
  have hphase : 1440 * 8192 * t ^ 4 ≤ a := by
    nlinarith only [hgap, (by positivity : 0 ≤ t ^ 4)]
  have hphase' : 2880 * 8192 * t ^ 4 ≤ a := by
    nlinarith only [hgap, (by positivity : 0 ≤ t ^ 4)]
  have hN := phaseCount_pos a t ht hphase
  let hs := threshold_path_small ha hL ht htδ
  refine ⟨hN, amplitude_ge_one a t ht hr, ?_, ?_, ?_, ?_⟩
  · intro q hq hqp z
    exact calibrated_jet_bound a L t ha hL ht hs p C hC hprim hb hr hpath q hq hqp _ z
  · intro z
    exact calibrated_actual_gap a L t ha hL ht hs hr hN hgap z
  · intro z htail
    exact calibrated_gradient a L t ha hL ht hs hr _ z htail
  · exact horizon_power_bounds a L t ha hL ht hphase' (hpath.trans (by norm_num))

end MatchingBounds1005.EpsilonCalibration
