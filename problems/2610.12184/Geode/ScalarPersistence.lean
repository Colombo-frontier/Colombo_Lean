import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Scalar persistence lemmas for `geode.tex`, Section 5.2.
The functions below are the actual rational/square-root expressions in the
manuscript. No geometric or oracle-completion theorem is assumed or asserted.
-/
namespace Geode

noncomputable section

def tau (μ : ℝ) : ℝ := 2 * μ / (1 + μ ^ 2)
def kappa (μ : ℝ) : ℝ := (1 - μ ^ 2) / (1 + μ ^ 2)
def eta (μ : ℝ) : ℝ := 2 * μ / (1 - μ ^ 2)
def angleA (μ θ : ℝ) : ℝ := 1 + μ ^ 2 - 2 * μ * θ
def angleB (μ θ a : ℝ) : ℝ := (θ - μ) * a + μ / a
def radicand (μ θ a : ℝ) : ℝ := angleA μ θ - μ ^ 2 / a ^ 2
def ratio (μ θ a : ℝ) : ℝ := angleB μ θ a / Real.sqrt (radicand μ θ a)

theorem mu_sq_lt_one {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) : μ ^ 2 < 1 := by
  nlinarith

theorem kappa_pos {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) : 0 < kappa μ := by
  unfold kappa
  exact div_pos (by nlinarith [mu_sq_lt_one hμ hμmax]) (by positivity)

theorem kappa_le_one {μ : ℝ} (hμ : 0 < μ) (_hμmax : μ ≤ 1 / 16) : kappa μ ≤ 1 := by
  unfold kappa
  apply (div_le_one (by positivity : 0 < 1 + μ ^ 2)).2
  nlinarith

theorem eta_pos {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) : 0 < eta μ := by
  unfold eta
  exact div_pos (by positivity) (by nlinarith [mu_sq_lt_one hμ hμmax])

theorem tau_gt_mu {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) : μ < tau μ := by
  unfold tau
  apply (lt_div_iff₀ (by positivity : 0 < 1 + μ ^ 2)).2
  have := mul_pos hμ (show 0 < 1 - μ ^ 2 by nlinarith [mu_sq_lt_one hμ hμmax])
  nlinarith

theorem tau_le_one {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) : tau μ ≤ 1 := by
  unfold tau
  apply (div_le_one (by positivity : 0 < 1 + μ ^ 2)).2
  nlinarith [sq_nonneg (μ - 1)]

theorem radicand_pos {μ θ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hθ : θ ≤ 1) (ha : 1 ≤ a) : 0 < radicand μ θ a := by
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hdiv : μ ^ 2 / a ^ 2 ≤ μ ^ 2 := by
    exact div_le_self (sq_nonneg μ) ha2
  have hprod : μ * θ ≤ μ := mul_le_of_le_one_right hμ.le hθ
  unfold radicand angleA
  nlinarith

theorem angleB_pos {μ θ a : ℝ} (hμ : 0 < μ) (hθ : μ < θ)
    (ha : 1 ≤ a) : 0 < angleB μ θ a := by
  unfold angleB
  exact add_pos (mul_pos (sub_pos.mpr hθ) (by linarith)) (div_pos hμ (by linarith))

theorem perfect_square {μ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (ha : 1 ≤ a) :
    angleB μ (tau μ) a ^ 2 - eta μ ^ 2 * radicand μ (tau μ) a =
      μ ^ 2 * (kappa μ * a - 1 / (kappa μ * a)) ^ 2 := by
  have hm : 1 - μ ^ 2 ≠ 0 := by nlinarith [mu_sq_lt_one hμ hμmax]
  have hp : 1 + μ ^ 2 ≠ 0 := by positivity
  have ha0 : a ≠ 0 := by linarith
  unfold angleB radicand angleA tau eta kappa
  field_simp
  ring

theorem ratio_ge_iff {μ θ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hθlo : μ < θ) (hθhi : θ ≤ 1) (ha : 1 ≤ a) :
    eta μ ≤ ratio μ θ a ↔
      eta μ ^ 2 * radicand μ θ a ≤ angleB μ θ a ^ 2 := by
  have hr := radicand_pos hμ hμmax hθhi ha
  have hb := angleB_pos hμ hθlo ha
  have he := eta_pos hμ hμmax
  have hs := Real.sqrt_pos.2 hr
  have hsq := Real.sq_sqrt hr.le
  unfold ratio
  rw [le_div_iff₀ hs]
  constructor
  · intro h
    have := mul_self_le_mul_self (by positivity : 0 ≤ eta μ * Real.sqrt (radicand μ θ a)) h
    nlinarith
  · intro h
    have hprod : 0 ≤ eta μ * Real.sqrt (radicand μ θ a) := by positivity
    nlinarith [sq_nonneg (angleB μ θ a - eta μ * Real.sqrt (radicand μ θ a))]

theorem reference_threshold {μ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (ha : 1 ≤ a) : eta μ ≤ ratio μ (tau μ) a := by
  apply (ratio_ge_iff hμ hμmax (tau_gt_mu hμ hμmax) (tau_le_one hμ hμmax) ha).2
  have := perfect_square hμ hμmax ha
  nlinarith [sq_nonneg (kappa μ * a - 1 / (kappa μ * a)), sq_nonneg μ]

theorem reference_argument_ge_one {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    1 ≤ 1 / kappa μ := by
  exact (le_div_iff₀ (kappa_pos hμ hμmax)).2 (by simpa using kappa_le_one hμ hμmax)

theorem reference_residual_zero {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    angleB μ (tau μ) (1 / kappa μ) ^ 2 -
      eta μ ^ 2 * radicand μ (tau μ) (1 / kappa μ) = 0 := by
  rw [perfect_square hμ hμmax (reference_argument_ge_one hμ hμmax)]
  have hk := ne_of_gt (kappa_pos hμ hμmax)
  simp [hk]

theorem angle_threshold {μ θ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hθlo : tau μ ≤ θ) (hθhi : θ ≤ 1) (ha : 1 ≤ a) :
    eta μ ≤ ratio μ θ a := by
  have ht := tau_gt_mu hμ hμmax
  apply (ratio_ge_iff hμ hμmax (lt_of_lt_of_le ht hθlo) hθhi ha).2
  have hbase := (ratio_ge_iff hμ hμmax ht (tau_le_one hμ hμmax) ha).1
    (reference_threshold hμ hμmax ha)
  have hb : angleB μ (tau μ) a ≤ angleB μ θ a := by
    unfold angleB
    nlinarith
  have hr : radicand μ θ a ≤ radicand μ (tau μ) a := by
    unfold radicand angleA
    nlinarith
  have hbpos := angleB_pos hμ ht ha
  have he : 0 ≤ eta μ ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hr he
  nlinarith

/-- The threshold equation after multiplication by the positive number `a²`. -/
def thresholdPolynomial (μ θ w : ℝ) : ℝ :=
  (θ - μ) ^ 2 * w ^ 2 + (2 * (θ - μ) * μ - eta μ ^ 2 * angleA μ θ) * w +
    μ ^ 2 * (1 + eta μ ^ 2)

theorem thresholdPolynomial_identity {μ θ a : ℝ} (ha : a ≠ 0) :
    thresholdPolynomial μ θ (a ^ 2) =
      a ^ 2 * (angleB μ θ a ^ 2 - eta μ ^ 2 * radicand μ θ a) := by
  unfold thresholdPolynomial angleB radicand
  field_simp
  ring

theorem ratio_ge_iff_polynomial {μ θ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hθlo : μ < θ) (hθhi : θ ≤ 1) (ha : 1 ≤ a) :
    eta μ ≤ ratio μ θ a ↔ 0 ≤ thresholdPolynomial μ θ (a ^ 2) := by
  rw [ratio_ge_iff hμ hμmax hθlo hθhi ha,
    thresholdPolynomial_identity (by linarith : a ≠ 0)]
  have ha2 : 0 < a ^ 2 := by positivity
  constructor
  · intro h
    exact mul_nonneg ha2.le (sub_nonneg.mpr h)
  · intro h
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha2).1 h)

/-- A positive-leading-coefficient quadratic cannot cross back below zero
    to the right of a known negative point and a later nonnegative point. -/
theorem quadratic_right_persistence {c d e w₀ w w' : ℝ}
    (hc : 0 ≤ c) (h₀ : c * w₀ ^ 2 + d * w₀ + e < 0)
    (hw : w₀ ≤ w) (hq : 0 ≤ c * w ^ 2 + d * w + e) (hw' : w ≤ w') :
    0 ≤ c * w' ^ 2 + d * w' + e := by
  have hgap : 0 < w - w₀ := by
    by_contra hn
    have : w = w₀ := by linarith
    subst w
    linarith
  have hs : 0 < c * (w + w₀) + d := by
    have hp : 0 < (w - w₀) * (c * (w + w₀) + d) := by nlinarith
    exact (mul_pos_iff_of_pos_left hgap).1 hp
  have hs' : 0 ≤ c * (w' + w) + d := by
    have hm := mul_nonneg hc (show 0 ≤ w' - w₀ by linarith)
    nlinarith
  have hp := mul_nonneg (show 0 ≤ w' - w by linarith) hs'
  nlinarith

theorem below_reference_angle {μ θ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (hθlo : μ < θ) (hθhi : θ < tau μ) :
    thresholdPolynomial μ θ ((1 / kappa μ) ^ 2) < 0 := by
  have ha := reference_argument_ge_one hμ hμmax
  have hap : 0 < 1 / kappa μ := by linarith
  have hbpos := angleB_pos hμ hθlo ha
  have hb : angleB μ θ (1 / kappa μ) < angleB μ (tau μ) (1 / kappa μ) := by
    unfold angleB
    have := mul_pos (sub_pos.mpr hθhi) hap
    nlinarith
  have hr : radicand μ (tau μ) (1 / kappa μ) ≤ radicand μ θ (1 / kappa μ) := by
    unfold radicand angleA
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg (eta μ))
  have hz := reference_residual_zero hμ hμmax
  have hneg : angleB μ θ (1 / kappa μ) ^ 2 -
      eta μ ^ 2 * radicand μ θ (1 / kappa μ) < 0 := by nlinarith
  rw [thresholdPolynomial_identity (ne_of_gt hap)]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hap) hneg

/-- Manuscript Lemma `lem:cd-right-branch`, for its exact parameter range. -/
theorem right_branch_persistence {μ θ a a' : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hθlo : μ < θ) (hθhi : θ ≤ 1)
    (ha : 1 / kappa μ ≤ a) (hlevel : eta μ ≤ ratio μ θ a) (ha' : a ≤ a') :
    eta μ ≤ ratio μ θ a' := by
  have ha0 := reference_argument_ge_one hμ hμmax
  have ha1 : 1 ≤ a := le_trans ha0 ha
  have ha'1 : 1 ≤ a' := le_trans ha1 ha'
  by_cases hθ : tau μ ≤ θ
  · exact angle_threshold hμ hμmax hθ hθhi ha'1
  · have hθ' : θ < tau μ := lt_of_not_ge hθ
    have hq₀ := below_reference_angle hμ hμmax hθlo hθ'
    have hq := (ratio_ge_iff_polynomial hμ hμmax hθlo hθhi ha1).1 hlevel
    apply (ratio_ge_iff_polynomial hμ hμmax hθlo hθhi ha'1).2
    have hw : (1 / kappa μ) ^ 2 ≤ a ^ 2 := by nlinarith
    have hw' : a ^ 2 ≤ a' ^ 2 := by nlinarith
    exact quadratic_right_persistence (sq_nonneg (θ - μ)) hq₀ hw hq hw'

/-- The equality case in the manuscript's perfect-square lemma. -/
theorem reference_equality_iff {μ a : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16)
    (ha : 1 ≤ a) : ratio μ (tau μ) a = eta μ ↔ a = 1 / kappa μ := by
  have hr := radicand_pos hμ hμmax (tau_le_one hμ hμmax) ha
  have hs := Real.sqrt_pos.2 hr
  have hsq := Real.sq_sqrt hr.le
  have he := eta_pos hμ hμmax
  have hb := angleB_pos hμ (tau_gt_mu hμ hμmax) ha
  have hk := kappa_pos hμ hμmax
  constructor
  · intro h
    have hbeq : angleB μ (tau μ) a = eta μ * Real.sqrt (radicand μ (tau μ) a) :=
      (div_eq_iff (ne_of_gt hs)).1 h
    have hz : μ ^ 2 * (kappa μ * a - 1 / (kappa μ * a)) ^ 2 = 0 := by
      have hi := perfect_square hμ hμmax ha
      nlinarith
    have hz' : (kappa μ * a - 1 / (kappa μ * a)) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (ne_of_gt hμ))
    have heq : kappa μ * a = 1 / (kappa μ * a) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp hz')
    have hka : 0 < kappa μ * a := mul_pos hk (by linarith)
    have hmul : (kappa μ * a) * (kappa μ * a) = 1 :=
      (eq_div_iff (ne_of_gt hka)).1 heq
    have hka1 : kappa μ * a = 1 := by nlinarith
    exact (eq_div_iff (ne_of_gt hk)).2 (by nlinarith)
  · intro h
    have hz : angleB μ (tau μ) a ^ 2 - eta μ ^ 2 * radicand μ (tau μ) a = 0 := by
      rw [h]
      exact reference_residual_zero hμ hμmax
    apply (div_eq_iff (ne_of_gt hs)).2
    have hprod : 0 < eta μ * Real.sqrt (radicand μ (tau μ) a) := mul_pos he hs
    nlinarith

end
end Geode

