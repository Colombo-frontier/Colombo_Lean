import GradientHessian.FirstHeightLemma
import GradientHessian.Reliability

/-! Exact higher-height scale and energy arithmetic. Index zero is height
one for energy, and the first localized parent at height two for width/radius. -/

noncomputable section
namespace GradientHessian.HigherHierarchy

def width (m t : ℕ) : ℝ := FirstHeight.baseRadius (m+1) * 3^t
def radius (m : ℕ) (K : ℝ) (t : ℕ) : ℝ := K * FirstHeight.baseRadius (m+1) * 6^t
def energy (m : ℕ) (K : ℝ) (t : ℕ) : ℝ :=
  Reliability.energy (FirstHeight.firstAmplitude m) (FirstHeight.baseRadius (m+1)) K t
def spacing (m : ℕ) (K : ℝ) (t : ℕ) : ℝ := energy m K t + 768 * radius m K t
def childScale (m : ℕ) : ℕ → ℝ
  | 0 => FirstHeight.outerRadius (m+1)
  | t+1 => width m t
def energyConstant (K : ℝ) : ℝ := FirstHeight.firstAmplitudeCoefficient + 6144*K + 3328/5

theorem baseRadius_pos (m : ℕ) : 0 < FirstHeight.baseRadius (m+1) := by
  unfold FirstHeight.baseRadius
  positivity

theorem width_pos (m t : ℕ) : 0 < width m t := mul_pos (baseRadius_pos m) (by positivity)

theorem width_ge_tasks (m t : ℕ) : (m+1:ℕ) ≤ width m t := by
  have hr := (FirstHeight.baseRadius_range (M := m+1) (by omega)).1
  have hp : (1:ℝ) ≤ 3^t := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (baseRadius_pos m).le
  unfold width
  linarith

theorem width_succ (m t : ℕ) : width m (t+1) = 3 * width m t := by
  simp only [width, pow_succ]
  ring

theorem radius_succ (m : ℕ) (K : ℝ) (t : ℕ) : radius m K (t+1) = 6 * radius m K t := by
  simp only [radius, pow_succ]
  ring

theorem radius_eq_width (m : ℕ) (K : ℝ) (t : ℕ) : radius m K t = K * 2^t * width m t := by
  have h : (6:ℝ)^t = 2^t*3^t := by rw [← mul_pow]; norm_num
  simp only [radius, width, h]
  ring

theorem radius_pos (m : ℕ) {K : ℝ} (hK : 0<K) (t : ℕ) : 0 < radius m K t := by
  rw [radius_eq_width]
  exact mul_pos (mul_pos hK (by positivity)) (width_pos m t)

theorem scale_separation (m : ℕ) {K : ℝ} (hK : 16≤K) (t : ℕ) :
    16 * width m t ≤ radius m K t := by
  rw [radius_eq_width]
  have hp : (1:ℝ) ≤ 2^t := one_le_pow₀ (by norm_num)
  have hk0 : 0 ≤ K := by linarith
  have hk := mul_le_mul_of_nonneg_left hp hk0
  apply mul_le_mul_of_nonneg_right _ (width_pos m t).le
  linarith

theorem childScale_pos (m t : ℕ) : 0 < childScale m t := by
  cases t with
  | zero =>
    rw [childScale, FirstHeight.outerRadius_eq]
    exact mul_pos (by norm_num) (baseRadius_pos m)
  | succ t => exact width_pos m t

theorem childScale_comparable (m t : ℕ) :
    width m t / 3 ≤ childScale m t ∧ childScale m t ≤ 4 * width m t := by
  cases t with
  | zero =>
    simp only [childScale, FirstHeight.outerRadius_eq, width, pow_zero, mul_one]
    have h := (baseRadius_pos m).le
    constructor <;> linarith
  | succ t =>
    rw [childScale, width_succ]
    have h := (width_pos m t).le
    constructor <;> linarith

theorem energy_zero (m : ℕ) (K : ℝ) : energy m K 0 = FirstHeight.firstAmplitude m := rfl

theorem energy_succ (m : ℕ) (K : ℝ) (t : ℕ) :
    energy m K (t+1) = 8 * spacing m K t + 8 * 208 * width m t := rfl

theorem firstAmplitude_pos (m : ℕ) : 0 < FirstHeight.firstAmplitude m := by
  unfold FirstHeight.firstAmplitude FirstHeight.amplitude
  have hs := FirstHeight.spacing_ge m
  have hr := (FirstHeight.outerRadius_range (M := m+1) (by omega)).1
  norm_num only [Nat.cast_ofNat]
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  push_cast at hr
  nlinarith

theorem energy_pos (m : ℕ) {K : ℝ} (hK : 0≤K) (t : ℕ) : 0 < energy m K t := by
  induction t with
  | zero => exact firstAmplitude_pos m
  | succ t ih =>
    rw [energy_succ]
    have hr : 0 ≤ radius m K t :=
      mul_nonneg (mul_nonneg hK (baseRadius_pos m).le) (by positivity)
    have hw := (width_pos m t).le
    unfold spacing
    linarith

theorem spacing_pos (m : ℕ) {K : ℝ} (hK : 0≤K) (t : ℕ) : 0 < spacing m K t := by
  have he := energy_pos m hK t
  have hr : 0 ≤ radius m K t :=
    mul_nonneg (mul_nonneg hK (baseRadius_pos m).le) (by positivity)
  unfold spacing
  linarith

theorem energyConstant_pos {K : ℝ} (hK : 0≤K) : 0 < energyConstant K := by
  unfold energyConstant
  linarith [FirstHeight.firstAmplitudeCoefficient_pos]

theorem energy_le (m : ℕ) {K : ℝ} (hK : 0≤K) (t : ℕ) :
    energy m K t ≤ energyConstant K * 8^t * (m+1) := by
  have hb := Reliability.energy_upper_bound (A₁ := FirstHeight.firstAmplitude m)
    (baseRadius_pos m).le hK t
  have ha := FirstHeight.firstAmplitude_linear m
  have hr := (FirstHeight.baseRadius_range (M := m+1) (by omega)).2.le
  push_cast at hr
  have hk := mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ 3072*K by positivity)
  have hc := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 1664/5)
  have hs : FirstHeight.firstAmplitude m + 3072*K*FirstHeight.baseRadius (m+1) +
      (1664/5:ℝ)*FirstHeight.baseRadius (m+1) ≤ energyConstant K * (m+1) := by
    unfold energyConstant
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 8^t)
  change energy m K t ≤ _ at hb
  calc
    _ ≤ 8^t * (energyConstant K * (m+1)) := hb.trans hp
    _ = _ := by ring

theorem energy_le_source_height (m : ℕ) {K : ℝ} (hK : 0≤K) (t : ℕ) :
    energy m K t ≤ energyConstant K * 8^(t+1) * (m+1) := by
  have he := energy_le m hK t
  have hp : (8:ℝ)^t ≤ 8^(t+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (energyConstant_pos hK).le) (by positivity))

end GradientHessian.HigherHierarchy
