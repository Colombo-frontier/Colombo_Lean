import MatchingBounds1005.SourcePowerGeometry
import MatchingBounds1005.SignalCalibration
import MatchingBounds1005.PowerInformation

/-! The actual two physical Gaussian channels have a good-event plus
exceptional-event information budget O_p(t³)=O_p(ε). The connection from
this scalar budget to transcript KL is supplied by the Gaussian oracle module. -/
noncomputable section

namespace MatchingBounds1005.TensorGeometry

def tensorEnergyBudget (k : ℕ) (N w θ σ : ℝ) : ℝ :=
  k * N ^ 2 * w ^ 2 * θ ^ (2 * (k - 1)) / (2 * σ ^ 2)

theorem tensorEnergyBudget_nonneg (k : ℕ) (N w θ σ : ℝ) (hθ : 0 ≤ θ) :
    0 ≤ tensorEnergyBudget k N w θ σ := by
  unfold tensorEnergyBudget
  positivity

theorem cubic_tensorEnergyBudget {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) (N w θ : ℝ) :
    tensorEnergyBudget 3 N w θ (maskSigma d 3 ((t ^ 3) ^ 3 / 8)) =
      (96 * sourceGaussianConstant 3 ^ 2) * d * N ^ 2 * w ^ 2 * θ ^ 4 / t ^ 18 := by
  have hs := source_cubic_sigma_inv_sq hd ht
  unfold tensorEnergyBudget
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceMul]
  calc
    _ = (3 / 2 : ℝ) * N ^ 2 * w ^ 2 * θ ^ 4 *
        (1 / maskSigma d 3 ((t ^ 3) ^ 3 / 8) ^ 2) := by ring
    _ = _ := by rw [hs]; ring

theorem quartic_tensorEnergyBudget {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) (N w θ : ℝ) :
    tensorEnergyBudget 4 N w θ (maskSigma d 4 ((t ^ 3) ^ 4 / 8)) =
      (128 * sourceGaussianConstant 4 ^ 2) * d * N ^ 2 * w ^ 2 * θ ^ 6 / t ^ 24 := by
  have hs := source_quartic_sigma_inv_sq hd ht
  unfold tensorEnergyBudget
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceMul]
  calc
    _ = (4 / 2 : ℝ) * N ^ 2 * w ^ 2 * θ ^ 6 *
        (1 / maskSigma d 4 ((t ^ 3) ^ 4 / 8) ^ 2) := by ring
    _ = _ := by rw [hs]; ring

end MatchingBounds1005.TensorGeometry

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry

def informationConstant (p : ℕ) : ℝ :=
  (96 * sourceGaussianConstant 3 ^ 2) * (3 * horizonUpper p) * phaseConstant p ^ 2 *
    cubicWeightConstant p ^ 2 * ((4 * angleConstant (horizonUpper p)) ^ 2 + 1) +
  (128 * sourceGaussianConstant 4 ^ 2) * (3 * horizonUpper p) * phaseConstant p ^ 2 *
    quarticWeightConstant p ^ 2 * ((4 * angleConstant (horizonUpper p)) ^ 3 + 1)

def sourceInformationBudget (p : ℕ) (t : ℝ) (ht : 0 < t) (hp : t ≤ parameterThreshold p) : ℝ :=
  let N : ℝ := phaseCount (amplitudeConstant p) t
  let d := dimension p t (powerCopies t)
  let G := canonicalGeometry p t ht hp
  let A := amplitude (amplitudeConstant p) t
  let w₃ := -120 * G.tau * A ^ 3
  let w₄ := 120 * G.tau * A ^ 4
  let σ₃ := maskSigma d 3 ((t ^ 3) ^ 3 / 8)
  let σ₄ := maskSigma d 4 ((t ^ 3) ^ 4 / 8)
  tensorEnergyBudget 3 N w₃ (2 * sourceAngle p t) σ₃ +
    tensorEnergyBudget 4 N w₄ (2 * sourceAngle p t) σ₄ +
    (1 / (powerCopies t : ℝ) ^ 4) *
      (tensorEnergyBudget 3 N w₃ 1 σ₃ + tensorEnergyBudget 4 N w₄ 1 σ₄)

theorem sourceInformationBudget_nonneg (p : ℕ) (t : ℝ) (ht : 0 < t) (hp : t ≤ parameterThreshold p) :
    0 ≤ sourceInformationBudget p t ht hp := by
  have hθ : 0 ≤ 2 * sourceAngle p t := mul_nonneg (by norm_num) (geometricAngle_nonneg _ _ _)
  dsimp only [sourceInformationBudget]
  exact add_nonneg (add_nonneg (tensorEnergyBudget_nonneg _ _ _ _ _ hθ)
    (tensorEnergyBudget_nonneg _ _ _ _ _ hθ))
      (mul_nonneg (by positivity) (add_nonneg (tensorEnergyBudget_nonneg _ _ _ _ _ (by norm_num))
        (tensorEnergyBudget_nonneg _ _ _ _ _ (by norm_num))))

theorem informationConstant_pos (p : ℕ) : 0 < informationConstant p := by
  have h3 := sourceGaussianConstant_pos (by norm_num : 1 ≤ 3)
  have h4 := sourceGaussianConstant_pos (by norm_num : 1 ≤ 4)
  have hD := horizonUpper_pos p
  have hN := phaseConstant_pos p
  have hW3 := cubicWeightConstant_pos p
  have hW4 := quarticWeightConstant_pos p
  have hB := angleConstant_pos hD
  unfold informationConstant
  positivity

/-- The scalar budget for the concrete sampled family, including the
K^-4 exceptional event, with no remaining asymptotic assumptions. -/
theorem sourceInformationBudget_bound (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ geometryThreshold p) :
    sourceInformationBudget p t ht (hsmall.trans (geometryThreshold_le_parameter p)) ≤
      informationConstant p * t ^ 3 := by
  let hp := hsmall.trans (geometryThreshold_le_parameter p)
  let G := canonicalGeometry p t ht hp
  let A := amplitude (amplitudeConstant p) t
  let d := dimension p t (powerCopies t)
  let N : ℝ := phaseCount (amplitudeConstant p) t
  have hd : 0 < d := dimension_pos p t ht hp _
  have ht1 := hp.trans (parameterThreshold_le_one p)
  have hD := horizonUpper_pos p
  have hN := phaseConstant_pos p
  have hW3 := cubicWeightConstant_pos p
  have hW4 := quarticWeightConstant_pos p
  have hB := angleConstant_pos hD
  have hw3 : |-120 * G.tau * A ^ 3| ≤ cubicWeightConstant p * t :=
    calibrated_cubic_weight _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht (path_small p ht hp)
  have hw4 : |120 * G.tau * A ^ 4| ≤ quarticWeightConstant p :=
    calibrated_quartic_weight _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht (path_small p ht hp)
  have hθ : (2 * sourceAngle p t) ^ 2 ≤ (4 * angleConstant (horizonUpper p)) * t ^ 37 := by
    nlinarith only [sourceAngle_bound p t ht hsmall]
  have hζ := PowerInformation.inverse_fourth_bound ht (powerCopies_lower (t := t))
  have h := PowerInformation.source_budget_bound ht ht1 (Nat.cast_nonneg d)
    (show 0 ≤ N from Nat.cast_nonneg _) (by positivity : 0 ≤ 3 * horizonUpper p)
    hN.le hW3.le hW4.le (by positivity : 0 ≤ 4 * angleConstant (horizonUpper p))
    (by positivity : 0 ≤ 96 * sourceGaussianConstant 3 ^ 2)
    (by positivity : 0 ≤ 128 * sourceGaussianConstant 4 ^ 2)
    (by positivity : 0 ≤ 1 / (powerCopies t : ℝ) ^ 4)
    (power_dimension_upper p t ht hp) (phaseCount_upper p t ht) hw3 hw4 hθ hζ
  dsimp only [sourceInformationBudget]
  rw [cubic_tensorEnergyBudget hd ht, quartic_tensorEnergyBudget hd ht,
    cubic_tensorEnergyBudget hd ht, quartic_tensorEnergyBudget hd ht]
  simp only [one_pow, mul_one]
  exact h

end MatchingBounds1005.AnalyticFamily
