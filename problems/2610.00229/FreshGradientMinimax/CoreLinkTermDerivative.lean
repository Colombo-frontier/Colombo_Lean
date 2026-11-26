import FreshGradientMinimax.SquareLinkDerivatives
import FreshGradientMinimax.PathIncidence

/-! Actual derivatives and sign information for the adjacent-coordinate term
of (22). The incoming derivative is bounded away from zero when its gate is open. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def coreLinkTermD1 (a b : ℝ) : ℝ :=
  -coreGateDeriv (-a) * coreTheta (-b) - coreGateDeriv a * coreTheta b
def coreLinkTermD2 (a b : ℝ) : ℝ :=
  -(coreGate (-a) + coreGate a) * coreDensity b

theorem coreLinkTermD1_nonpos (a b : ℝ) : coreLinkTermD1 a b ≤ 0 := by
  have h1 := mul_nonneg (coreGateDeriv_nonneg (-a)) (coreTheta_pos (-b)).le
  have h2 := mul_nonneg (coreGateDeriv_nonneg a) (coreTheta_pos b).le
  unfold coreLinkTermD1
  nlinarith only [h1, h2]

theorem coreLinkTermD2_nonpos (a b : ℝ) : coreLinkTermD2 a b ≤ 0 := by
  unfold coreLinkTermD2
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg (coreGate_nonneg _) (coreGate_nonneg _)))
    (coreDensity_pos _).le

theorem coreGate_pair_open {a : ℝ} (ha : 1 ≤ |a|) : 1 ≤ coreGate (-a) + coreGate a := by
  rcases le_abs.mp ha with ha | ha
  · linarith [coreGate_one_le ha, coreGate_nonneg (-a)]
  · have hn : 1 ≤ -a := by linarith
    linarith [coreGate_one_le hn, coreGate_nonneg a]

theorem coreLinkTermD2_barrier {a b : ℝ} (ha : 1 ≤ |a|) (hb : |b| ≤ 1) :
    coreLinkTermD2 a b ≤ -Real.exp (-(1 / 2 : ℝ)) := by
  have h := mul_le_mul_of_nonneg_right (coreGate_pair_open ha) (coreDensity_pos b).le
  have hd := coreDensity_lower_on_unit hb
  unfold coreLinkTermD2
  nlinarith only [h, hd]

theorem coreLinkTermD1_bound (a b : ℝ) : |coreLinkTermD1 a b| ≤ 96 := by
  have h1 := mul_le_mul (coreGateDeriv_bound (-a)) (coreTheta_lt_three (-b)).le
    (coreTheta_pos (-b)).le (by norm_num : (0 : ℝ) ≤ 16)
  have h2 := mul_le_mul (coreGateDeriv_bound a) (coreTheta_lt_three b).le
    (coreTheta_pos b).le (by norm_num : (0 : ℝ) ≤ 16)
  have h := abs_sub (-coreGateDeriv (-a) * coreTheta (-b)) (coreGateDeriv a * coreTheta b)
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (coreTheta_pos (-b)), abs_of_pos (coreTheta_pos b)] at h
  unfold coreLinkTermD1
  linarith

theorem coreLinkTermD2_bound (a b : ℝ) : |coreLinkTermD2 a b| ≤ 6 := by
  have hgate : 0 ≤ coreGate (-a) + coreGate a := add_nonneg (coreGate_nonneg _) (coreGate_nonneg _)
  have hg : coreGate (-a) + coreGate a ≤ 6 := by linarith [coreGate_le_three (-a), coreGate_le_three a]
  unfold coreLinkTermD2
  rw [abs_mul, abs_neg, abs_of_nonneg hgate, abs_of_pos (coreDensity_pos b)]
  have h := mul_le_mul hg (coreDensity_le_one b) (coreDensity_pos b).le (by norm_num : (0 : ℝ) ≤ 6)
  linarith

theorem coreLinkTerm_linear_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y => coreLinkTerm (A y) (B y))
      (coreLinkTermD1 (A x) (B x) • A + coreLinkTermD2 (A x) (B x) • B) x := by
  have hga := (coreGate_hasDerivAt (-A x)).comp_hasFDerivAt x A.hasFDerivAt.neg
  have hgb := (coreGate_hasDerivAt (A x)).comp_hasFDerivAt x A.hasFDerivAt
  have hta := (coreTheta_hasDerivAt (-B x)).comp_hasFDerivAt x B.hasFDerivAt.neg
  have htb := (coreTheta_hasDerivAt (B x)).comp_hasFDerivAt x B.hasFDerivAt
  have h := (hga.mul hta).sub (hgb.mul htb)
  apply h.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
    coreLinkTermD1, coreLinkTermD2, coreGateDeriv, coreDensity_neg, Function.comp_def]
  ring

theorem coreLinkTermD_flat {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    coreLinkTermD1 a b = 0 ∧ coreLinkTermD2 a b = 0 := by
  have hp := coreGate_derivatives_flat ((le_abs_self a).trans ha)
  have hm := coreGate_derivatives_flat ((neg_le_abs a).trans ha)
  have hflat := coreGate_flat ha
  simp only [coreLinkTermD1, coreLinkTermD2, hp.1, hm.1, hflat.1, hflat.2,
    neg_zero, zero_mul, zero_add, sub_zero, and_self]

end FreshGradientMinimax
