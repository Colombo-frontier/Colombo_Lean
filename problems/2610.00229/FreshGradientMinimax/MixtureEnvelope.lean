import FreshGradientMinimax.RandomInput

/-! A guarantee for all input distributions with bounded mean energy implies
an affine pointwise envelope. The auxiliary mixture is used only in the proof;
the algorithm does not need to know a zero-energy point. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]

theorem kernel_affine_envelope_of_mean_guarantee (K : Kernel X Y)
    (E : X → ℝ) (hE : ∀ x, 0 ≤ E x) (x₀ : X) (hx₀ : E x₀ = 0)
    (V : Y → ℝ) (hV : ∀ y, 0 ≤ V y) {B η : ℝ} (hB : 0 < B)
    (hguarantee : ∀ (ν : Measure X) (_ : IsProbabilityMeasure ν),
      Integrable E ν → (∫ x, E x ∂ν) ≤ B →
        Integrable V (K ∘ₘ ν) ∧ (∫ y, V y ∂K ∘ₘ ν) ≤ η) (x : X) :
    Integrable V (K x) ∧ (∫ y, V y ∂K x) ≤ η * (1 + E x / B) := by
  let p : ℝ := B / (B + E x)
  let q : ℝ := E x / (B + E x)
  have hd : 0 < B + E x := add_pos_of_pos_of_nonneg hB (hE x)
  have hp : 0 < p := div_pos hB hd
  have hq : 0 ≤ q := div_nonneg (hE x) hd.le
  have hpq : p + q = 1 := by
    dsimp [p, q]
    rw [← add_div, div_self hd.ne']
  let ν : Measure X := ENNReal.ofReal p • Measure.dirac x + ENNReal.ofReal q • Measure.dirac x₀
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp.le hq, hpq, ENNReal.ofReal_one]
  have hip : Integrable E (ENNReal.ofReal p • Measure.dirac x) :=
    integrable_dirac.smul_measure ENNReal.ofReal_ne_top
  have hiq : Integrable E (ENNReal.ofReal q • Measure.dirac x₀) :=
    integrable_dirac.smul_measure ENNReal.ofReal_ne_top
  have hmean : (∫ t, E t ∂ν) ≤ B := by
    rw [integral_add_measure hip hiq]
    simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp.le,
      ENNReal.toReal_ofReal hq, hx₀, smul_eq_mul, mul_zero, add_zero]
    dsimp [p]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg B]
  have h := hguarantee ν hν (hip.add_measure hiq) hmean
  have hlaw : K ∘ₘ ν = ENNReal.ofReal p • K x + ENNReal.ofReal q • K x₀ := by
    rw [Measure.comp_add, Measure.comp_smul, Measure.comp_smul,
      Measure.dirac_bind K.measurable, Measure.dirac_bind K.measurable]
  rw [hlaw] at h
  have hi : Integrable V (K x) :=
    (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
      h.1.left_of_add_measure
  have hweighted : p * (∫ y, V y ∂K x) ≤ η := by
    have hm := h.2
    rw [integral_add_measure h.1.left_of_add_measure h.1.right_of_add_measure] at hm
    simp only [integral_smul_measure, ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq,
      smul_eq_mul] at hm
    have hn := mul_nonneg hq (integral_nonneg hV (μ := K x₀))
    linarith
  refine ⟨hi, ?_⟩
  have hratio : (1 + E x / B) * p = 1 := by
    dsimp [p]
    field_simp
  apply (mul_le_mul_right hp).mp
  calc
    (∫ y, V y ∂K x) * p ≤ η := by simpa only [mul_comm] using hweighted
    _ = (η * (1 + E x / B)) * p := by rw [mul_assoc, hratio, mul_one]

end FreshGradientMinimax
