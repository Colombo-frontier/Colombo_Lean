import FreshGradientMinimax.SquareLinkCore
import FreshGradientMinimax.CoreGateBounds
import FreshGradientMinimax.CoreThetaRootBounds

/-! Complete scalar-link regularity and the dimension-independent component
constants in the first part of Lemma C.1, for both signs of the actual links. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def rootLink (s a b : ℝ) : ℝ := coreGateRoot (s * a) * coreThetaRoot (-b)
def rootLinkD1 (s a b : ℝ) : ℝ := s * coreGateRootDeriv (s * a) * coreThetaRoot (-b)
def rootLinkD2 (s a b : ℝ) : ℝ := -coreGateRoot (s * a) * coreThetaRootDeriv (-b)
def rootLinkD11 (s a b : ℝ) : ℝ := s ^ 2 * coreGateRootSecond (s * a) * coreThetaRoot (-b)
def rootLinkD12 (s a b : ℝ) : ℝ := -s * coreGateRootDeriv (s * a) * coreThetaRootDeriv (-b)
def rootLinkD22 (s a b : ℝ) : ℝ := coreGateRoot (s * a) * coreThetaRootSecond (-b)

theorem coreLinkPlus_rootLink (a b : ℝ) : coreLinkPlus a b = rootLink (-1) a b := by
  rw [coreLinkPlus, Real.sqrt_mul (coreGate_nonneg _), ← coreGateRoot_eq_sqrt]
  simp only [rootLink, neg_one_mul, coreThetaRoot]

theorem coreLinkMinus_rootLink (a b : ℝ) : coreLinkMinus a b = rootLink 1 a b := by
  rw [coreLinkMinus, ← coreTheta_reflection b, Real.sqrt_mul (coreGate_nonneg _), ← coreGateRoot_eq_sqrt]
  simp only [rootLink, one_mul, coreThetaRoot]

theorem rootLink_contDiff (s : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (fun z : ℝ × ℝ => rootLink s z.1 z.2) :=
  (coreGateRoot_contDiff.comp (contDiff_const.mul contDiff_fst)).mul
    (coreThetaRoot_contDiff.comp contDiff_snd.neg)

theorem coreLinkPlus_contDiff {n : ℕ∞} : ContDiff ℝ n (fun z : ℝ × ℝ => coreLinkPlus z.1 z.2) := by
  simp_rw [coreLinkPlus_rootLink]
  exact rootLink_contDiff (-1)

theorem coreLinkMinus_contDiff {n : ℕ∞} : ContDiff ℝ n (fun z : ℝ × ℝ => coreLinkMinus z.1 z.2) := by
  simp_rw [coreLinkMinus_rootLink]
  exact rootLink_contDiff 1

theorem rootLink_hasDerivAt_first (s a b : ℝ) :
    HasDerivAt (fun x => rootLink s x b) (rootLinkD1 s a b) a := by
  convert ((coreGateRoot_hasDerivAt (s * a)).comp a ((hasDerivAt_id a).const_mul s)).mul_const
    (coreThetaRoot (-b)) using 1
  simp only [rootLinkD1, mul_one]
  ring

theorem rootLink_hasDerivAt_second (s a b : ℝ) :
    HasDerivAt (rootLink s a) (rootLinkD2 s a b) b := by
  convert ((coreThetaRoot_hasDerivAt (-b)).comp b (hasDerivAt_neg b)).const_mul
    (coreGateRoot (s * a)) using 1
  unfold rootLinkD2
  ring

theorem rootLinkD1_hasDerivAt_first (s a b : ℝ) :
    HasDerivAt (fun x => rootLinkD1 s x b) (rootLinkD11 s a b) a := by
  convert (((coreGateRootDeriv_hasDerivAt (s * a)).comp a ((hasDerivAt_id a).const_mul s)).const_mul s).mul_const
    (coreThetaRoot (-b)) using 1
  simp only [rootLinkD11, mul_one]
  ring

theorem rootLinkD1_hasDerivAt_second (s a b : ℝ) :
    HasDerivAt (rootLinkD1 s a) (rootLinkD12 s a b) b := by
  convert ((coreThetaRoot_hasDerivAt (-b)).comp b (hasDerivAt_neg b)).const_mul
    (s * coreGateRootDeriv (s * a)) using 1
  unfold rootLinkD12
  ring

theorem rootLinkD2_hasDerivAt_first (s a b : ℝ) :
    HasDerivAt (fun x => rootLinkD2 s x b) (rootLinkD12 s a b) a := by
  convert (((coreGateRoot_hasDerivAt (s * a)).comp a ((hasDerivAt_id a).const_mul s)).neg).mul_const
    (coreThetaRootDeriv (-b)) using 1
  simp only [rootLinkD12, mul_one]
  ring

theorem rootLinkD2_hasDerivAt_second (s a b : ℝ) :
    HasDerivAt (rootLinkD2 s a) (rootLinkD22 s a b) b := by
  convert ((coreThetaRootDeriv_hasDerivAt (-b)).comp b (hasDerivAt_neg b)).const_mul
    (-coreGateRoot (s * a)) using 1
  unfold rootLinkD22
  ring

theorem rootLink_component_bounds {s : ℝ} (hs : |s| = 1) (a b : ℝ) :
    |rootLink s a b| ≤ 4 ∧ |rootLinkD1 s a b| ≤ 20 ∧ |rootLinkD2 s a b| ≤ 20 ∧
      |rootLinkD11 s a b| ≤ 1000 ∧ |rootLinkD12 s a b| ≤ 1000 ∧ |rootLinkD22 s a b| ≤ 1000 := by
  have h0 := mul_le_mul (coreGateRoot_bound (s * a)) (coreThetaRoot_bound (-b))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h1 := mul_le_mul (coreGateRootDeriv_bound (s * a)) (coreThetaRoot_bound (-b))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  have h2 := mul_le_mul (coreGateRoot_bound (s * a)) (coreThetaRootDeriv_bound (-b))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h11 := mul_le_mul (coreGateRootSecond_bound (s * a)) (coreThetaRoot_bound (-b))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 120)
  have h12 := mul_le_mul (coreGateRootDeriv_bound (s * a)) (coreThetaRootDeriv_bound (-b))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  have h22 := mul_le_mul (coreGateRoot_bound (s * a)) (coreThetaRootSecond_bound (-b))
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simp only [rootLink, rootLinkD1, rootLinkD2, rootLinkD11, rootLinkD12, rootLinkD22,
    abs_mul, abs_neg, abs_pow, hs, one_pow, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem rootLink_flat {s a : ℝ} (ha : s * a ≤ 1 / 2) (b : ℝ) :
    rootLink s a b = 0 ∧ rootLinkD1 s a b = 0 ∧ rootLinkD2 s a b = 0 ∧
      rootLinkD11 s a b = 0 ∧ rootLinkD12 s a b = 0 ∧ rootLinkD22 s a b = 0 := by
  simp only [rootLink, rootLinkD1, rootLinkD2, rootLinkD11, rootLinkD12, rootLinkD22,
    coreGateRoot_zero ha, coreGateRootDeriv_flat ha, coreGateRootSecond_flat ha,
    mul_zero, zero_mul, neg_zero, and_self]

end FreshGradientMinimax
