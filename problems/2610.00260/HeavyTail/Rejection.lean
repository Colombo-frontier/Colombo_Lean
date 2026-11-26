import HeavyTail.ProbabilityTools
import HeavyTail.AcceptedMoments

/-! The complete fixed-law rejection lemma, with a common explicit constant.
The probability law is arbitrary, so the theorem can be applied to each frozen
conditional oracle law. Realization by a capped adaptive sampler is separate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace HeavyTail

def rejectionConstant (p : ℝ) : ℝ :=
  max (2 * (2 : ℝ) ^ (p - 1))
    (max (2 * (3 / 2 : ℝ) ^ (2 - p)) (2 * (2 : ℝ) ^ p))

theorem rejectionConstant_pos (p : ℝ) : 0 < rejectionConstant p :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

theorem divide_by_acceptance_le {x a : ℝ} (hx : 0 ≤ x) (ha : a ≤ 1 / 16) :
    x / (1 - a) ≤ 2 * x := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - a)).mpr
  nlinarith

theorem rejection_bias_arithmetic {p q a s L τ : ℝ}
    (hpq : p.HolderConjugate q) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 16)
    (hs : 0 ≤ s) (hL : 0 ≤ L) (hτ : 0 < τ)
    (htail : a ≤ (2 * L / τ) ^ p) :
    s * a ^ (1 / q) / (1 - a) ≤
      rejectionConstant p * s * (L / τ) ^ (p - 1) := by
  have hp : a ^ (1 / q) ≤ (2 * L / τ) ^ (p - 1) := by
    calc
      _ ≤ ((2 * L / τ) ^ p) ^ (1 / q) :=
        Real.rpow_le_rpow ha0 htail hpq.symm.one_div_nonneg
      _ = _ := by
        rw [← Real.rpow_mul (by positivity), mul_one_div, hpq.div_conj_eq_sub_one]
  have hfactor : (2 * L / τ) ^ (p - 1) =
      (2 : ℝ) ^ (p - 1) * (L / τ) ^ (p - 1) := by
    rw [mul_div_assoc, Real.mul_rpow (by norm_num) (by positivity)]
  have hC : 2 * (2 : ℝ) ^ (p - 1) ≤ rejectionConstant p := le_max_left _ _
  calc
    _ ≤ 2 * (s * a ^ (1 / q)) := divide_by_acceptance_le (by positivity) ha
    _ ≤ 2 * (s * (2 * L / τ) ^ (p - 1)) := by gcongr
    _ = (2 * (2 : ℝ) ^ (p - 1)) * s * (L / τ) ^ (p - 1) := by rw [hfactor]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hs)
      (Real.rpow_nonneg (by positivity) _)

theorem rejection_trace_arithmetic {p a L τ : ℝ}
    (ha : a ≤ 1 / 16) (hL : 0 ≤ L) (hτ : 0 ≤ τ) :
    (3 * τ / 2) ^ (2 - p) * (L ^ p / (1 - a)) ≤
      rejectionConstant p * L ^ p * τ ^ (2 - p) := by
  have hC : 2 * (3 / 2 : ℝ) ^ (2 - p) ≤ rejectionConstant p :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hfactor : (3 * τ / 2) ^ (2 - p) =
      (3 / 2 : ℝ) ^ (2 - p) * τ ^ (2 - p) := by
    rw [show 3 * τ / 2 = (3 / 2) * τ by ring, Real.mul_rpow (by norm_num) hτ]
  calc
    _ ≤ (3 * τ / 2) ^ (2 - p) * (2 * L ^ p) :=
      mul_le_mul_of_nonneg_left (divide_by_acceptance_le (Real.rpow_nonneg hL _) ha)
        (Real.rpow_nonneg (by positivity) _)
    _ = (2 * (3 / 2 : ℝ) ^ (2 - p)) * L ^ p * τ ^ (2 - p) := by rw [hfactor]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL _)) (Real.rpow_nonneg hτ _)

theorem rejection_weak_arithmetic {p a s : ℝ} (ha : a ≤ 1 / 16) (hs : 0 ≤ s) :
    (2 : ℝ) ^ p * s ^ p / (1 - a) ≤ rejectionConstant p * s ^ p := by
  have hC : 2 * (2 : ℝ) ^ p ≤ rejectionConstant p :=
    (le_max_right _ _).trans (le_max_right _ _)
  calc
    _ ≤ 2 * ((2 : ℝ) ^ p * s ^ p) := divide_by_acceptance_le (by positivity) ha
    _ = (2 * (2 : ℝ) ^ p) * s ^ p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hs _)

section AcceptedLaw
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- All four conclusions of the manuscript's rejection lemma for an arbitrary
fixed probability law. `MemLp` states finiteness/measurability of the raw p-moment;
the two numerical moment bounds and centering are explicit below. -/
theorem rejection_lemma {ξ : Ω → E} {b : E} {p G L s τ : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hG : 0 ≤ G) (hL : 0 < L) (hs : 0 ≤ s)
    (hτ : 64 * (4 * G + L) ≤ τ) (hb : ‖b‖ ≤ 4 * G)
    (hξm : Measurable ξ) (hξp : MemLp ξ (ENNReal.ofReal p) P)
    (hzero : ∫ ω, ξ ω ∂P = 0)
    (hstrong : ∫ ω, ‖ξ ω‖ ^ p ∂P ≤ L ^ p)
    (hweak : ∀ v : E, ‖v‖ = 1 → ∫ ω, |⟪v, ξ ω⟫_ℝ| ^ p ∂P ≤ s ^ p) :
    let S := {ω | ‖b + ξ ω‖ ≤ τ}
    let Q := ProbabilityTheory.cond P S
    let b' := ∫ ω, b + ξ ω ∂Q
    P.real Sᶜ ≤ (2 * L / τ) ^ p ∧ P.real Sᶜ ≤ 1 / 16 ∧
    ‖b' - b‖ ≤ rejectionConstant p * s * (L / τ) ^ (p - 1) ∧
    (∫ ω, ‖b + ξ ω - b'‖ ^ 2 ∂Q) ≤ rejectionConstant p * L ^ p * τ ^ (2 - p) ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ ω, |⟪v, b + ξ ω - b'⟫_ℝ| ^ p ∂Q) ≤ rejectionConstant p * s ^ p := by
  let S := {ω | ‖b + ξ ω‖ ≤ τ}
  let Q := ProbabilityTheory.cond P S
  let m := ∫ ω, ξ ω ∂Q
  have hp0 : 0 ≤ p := by linarith
  have ht : 0 < τ := by linarith
  have hbτ : ‖b‖ ≤ τ / 2 := by linarith
  have hmeas : Measurable (fun ω => ‖b + ξ ω‖) :=
    (continuous_const.add continuous_id).norm.measurable.comp hξm
  have hS : MeasurableSet S := measurableSet_le hmeas measurable_const
  have hSc : Sᶜ = {ω | τ < ‖b + ξ ω‖} := by ext ω; simp [S, not_le]
  have hi : Integrable ξ P := hξp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hip : Integrable (fun ω => ‖ξ ω‖ ^ p) P := by
    simpa only [ENNReal.toReal_ofReal hp0] using hξp.integrable_norm_rpow'
  have hrej : P.real Sᶜ ≤ 1 / 16 := by
    rw [hSc]
    exact norm_rejection_probability_sixteenth hp hG hL hτ hb (hSc ▸ hS.compl) hip hstrong
  have htail : P.real Sᶜ ≤ (2 * L / τ) ^ p := by
    rw [hSc]
    exact norm_rejection_probability hp0 ht hL.le hbτ (hSc ▸ hS.compl) hip hstrong
  have hmass : P.real S + P.real Sᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := P) hS
  have hacc : 0 < P.real S := by linarith
  have hSne : P S ≠ 0 := by
    intro hz
    have hz' : P.real S = 0 := by simp [Measure.real, hz]
    linarith
  letI : IsProbabilityMeasure Q := ProbabilityTheory.cond_isProbabilityMeasure hSne
  have hiQ : Integrable ξ Q := hi.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hSne)
  have hmean : (∫ ω, b + ξ ω ∂Q) = b + m := by
    rw [integral_add (integrable_const b) hiQ, integral_const]
    simp [m]
  have hcenter (ω : Ω) : b + ξ ω - (∫ z, b + ξ z ∂Q) = ξ ω - m := by
    rw [hmean]
    abel
  have hm : m = (P.real S)⁻¹ • (∫ ω in S, ξ ω ∂P) := by
    dsimp [m, Q]
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    rfl
  change P.real Sᶜ ≤ (2 * L / τ) ^ p ∧ P.real Sᶜ ≤ 1 / 16 ∧ _
  refine ⟨htail, hrej, ?_, ?_, ?_⟩
  · change ‖(∫ ω, b + ξ ω ∂Q) - b‖ ≤ _
    rw [hmean, add_sub_cancel_left, hm]
    let q := Real.conjExponent p
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
    exact (accepted_vector_bias hpq hS hi hzero hs
      (fun v _ => hξp.const_inner v) hweak hacc).trans
        (rejection_bias_arithmetic hpq measureReal_nonneg hrej hs hL.le ht htail)
  · change (∫ ω, ‖b + ξ ω - (∫ z, b + ξ z ∂Q)‖ ^ 2 ∂Q) ≤ _
    simp_rw [hcenter]
    have ht0 := conditional_truncated_second_moment ht.le hbτ hS hSne hp hp2 hξp.1 hip hstrong
    change (∫ ω, ‖ξ ω - m‖ ^ 2 ∂Q) ≤ (3 * τ / 2) ^ (2 - p) * (L ^ p / P.real S) at ht0
    have hden : P.real S = 1 - P.real Sᶜ := by linarith
    rw [hden] at ht0
    exact ht0.trans (rejection_trace_arithmetic hrej hL.le ht.le)
  · intro v hv
    change (∫ ω, |⟪v, b + ξ ω - (∫ z, b + ξ z ∂Q)⟫_ℝ| ^ p ∂Q) ≤ _
    simp_rw [hcenter]
    have hvp : Integrable (fun ω => |⟪v, ξ ω⟫_ℝ| ^ p) P := by
      simpa only [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using
        (hξp.const_inner (𝕜 := ℝ) v).integrable_norm_rpow'
    have hw := conditional_vector_weak_moment hSne hp.le hi v hvp (hweak v hv)
    have hden : P.real S = 1 - P.real Sᶜ := by linarith
    rw [hden] at hw
    exact hw.trans (rejection_weak_arithmetic hrej hs)

end AcceptedLaw
end HeavyTail
