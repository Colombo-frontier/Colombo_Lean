import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! Concrete smooth cutoffs in Section `sec:split`. Product formulas avoid
differentiating absolute value at zero and are proved equal to the source. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Smoothness2601.Cutoffs

abbrev S := Real.smoothTransition
def psi (t : ℝ) : ℝ := S (2*t-1)
def gate (t : ℝ) : ℝ := psi t + psi (-t)
def bump (t : ℝ) : ℝ := t * (1-S (8*t-1)) * (1-S (-8*t-1))
def zeta (t : ℝ) : ℝ := (S (16*t-1)+S (-16*t-1)) * (1-S (t-1)) * (1-S (-t-1))

theorem expGlue_monotone : Monotone expNegInvGlue := by
  intro x y hxy
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact expNegInvGlue.nonneg y
  · have hx' : 0 < x := lt_of_not_ge hx
    have hy : ¬y ≤ 0 := not_le.mpr (hx'.trans_le hxy)
    simp only [expNegInvGlue, hx, hy, ↓reduceIte]
    exact Real.exp_le_exp.mpr (neg_le_neg (inv_anti₀ hx' hxy))

theorem transition_monotone : Monotone S := by
  intro x y hxy
  have ha := expGlue_monotone hxy
  have hb := expGlue_monotone (show 1-y ≤ 1-x by linarith)
  have hm := mul_le_mul ha hb (expNegInvGlue.nonneg (1-y)) (expNegInvGlue.nonneg y)
  change expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1-x)) ≤
    expNegInvGlue y / (expNegInvGlue y + expNegInvGlue (1-y))
  apply (div_le_div_iff₀ (Real.smoothTransition.pos_denom x) (Real.smoothTransition.pos_denom y)).mpr
  nlinarith

theorem psi_contDiff (n : ℕ∞) : ContDiff ℝ n psi :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem gate_contDiff (n : ℕ∞) : ContDiff ℝ n gate :=
  (psi_contDiff n).add ((psi_contDiff n).comp contDiff_id.neg)

theorem bump_contDiff (n : ℕ∞) : ContDiff ℝ n bump := by
  have hp : ContDiff ℝ n (fun t : ℝ => S (8*t-1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hn : ContDiff ℝ n (fun t : ℝ => S (-8*t-1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (contDiff_id.mul (contDiff_const.sub hp)).mul (contDiff_const.sub hn)

theorem zeta_contDiff (n : ℕ∞) : ContDiff ℝ n zeta := by
  have hc (a b : ℝ) : ContDiff ℝ n (fun t : ℝ => S (a*t-b)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (((hc 16 1).add (hc (-16) 1)).mul
    (contDiff_const.sub (by simpa using hc 1 1))).mul
    (contDiff_const.sub (by simpa using hc (-1) 1))

theorem psi_zero {t : ℝ} (ht : t ≤ 1/2) : psi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem psi_one {t : ℝ} (ht : 1 ≤ t) : psi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := Real.smoothTransition.nonneg _
theorem psi_le_one (t : ℝ) : psi t ≤ 1 := Real.smoothTransition.le_one _
theorem psi_monotone : Monotone psi := fun _ _ h => transition_monotone (by linarith)
theorem psi_deriv_nonneg (t : ℝ) : 0 ≤ deriv psi t := by
  have hd := ((psi_contDiff 1).differentiable (by norm_num) t).hasDerivAt
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  exact mul_nonneg (inv_nonneg.mpr hh'.le)
    (sub_nonneg.mpr (psi_monotone (show t ≤ t+h by linarith)))

theorem gate_nonneg (t : ℝ) : 0 ≤ gate t := add_nonneg (psi_nonneg _) (psi_nonneg _)

theorem gate_le_one (t : ℝ) : gate t ≤ 1 := by
  rcases le_total 0 t with ht | ht
  · have hz : psi (-t) = 0 := psi_zero (by linarith)
    simpa only [gate,hz,add_zero] using psi_le_one t
  · have hz : psi t = 0 := psi_zero (by linarith)
    simpa only [gate,hz,zero_add] using psi_le_one (-t)

theorem gate_even (t : ℝ) : gate (-t) = gate t := by simp [gate, add_comm]

theorem gate_zero {t : ℝ} (ht : |t| ≤ 1/2) : gate t = 0 := by
  obtain ⟨hl,hu⟩ := abs_le.mp ht
  simp only [gate,psi_zero hu,psi_zero (show -t ≤ 1/2 by linarith),add_zero]

theorem gate_one {t : ℝ} (ht : 1 ≤ |t|) : gate t = 1 := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    simp only [gate,psi_one ht,psi_zero (show -t ≤ 1/2 by linarith),add_zero]
  · rw [abs_of_nonpos h] at ht
    simp only [gate,psi_one ht,psi_zero (show t ≤ 1/2 by linarith),zero_add]

theorem bump_source (t : ℝ) : bump t = t * (1-S (8*|t|-1)) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have hz : S (-8*t-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [bump,hz,sub_zero,mul_one]
  · rw [abs_of_nonpos ht]
    have hz : S (8*t-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [bump,hz,sub_zero,mul_one]
    congr 2
    ring

theorem bump_zero {t : ℝ} (ht : 1/4 ≤ |t|) : bump t = 0 := by
  rw [bump_source,S,Real.smoothTransition.one_of_one_le (show 1 ≤ 8*|t|-1 by linarith)]
  ring

theorem bump_identity {t : ℝ} (ht : |t| ≤ 1/8) : bump t = t := by
  rw [bump_source,S,Real.smoothTransition.zero_of_nonpos (show 8*|t|-1 ≤ 0 by linarith)]
  ring

theorem bump_abs_le (t : ℝ) : |bump t| ≤ 1/4 := by
  by_cases ht : 1/4 ≤ |t|
  · simp only [bump_zero ht,abs_zero]; norm_num
  · rw [bump_source,abs_mul,abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))]
    have hn := Real.smoothTransition.nonneg (8*|t|-1)
    nlinarith [abs_nonneg t]

theorem zeta_source (t : ℝ) : zeta t = S (16*|t|-1) * (1-S (|t|-1)) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h1 : S (-16*t-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2 : S (-t-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [zeta,h1,h2,add_zero,sub_zero,mul_one]
  · rw [abs_of_nonpos ht]
    have h1 : S (16*t-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have h2 : S (t-1) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [zeta,h1,h2,zero_add,sub_zero,mul_one]
    congr 2
    ring

theorem zeta_even (t : ℝ) : zeta (-t) = zeta t := by rw [zeta_source,zeta_source,abs_neg]

theorem zeta_nonneg (t : ℝ) : 0 ≤ zeta t := by
  rw [zeta_source]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem zeta_le_one (t : ℝ) : zeta t ≤ 1 := by
  rw [zeta_source]
  have ha := Real.smoothTransition.nonneg (16*|t|-1)
  have hb := Real.smoothTransition.nonneg (|t|-1)
  have hc := Real.smoothTransition.le_one (16*|t|-1)
  have hd := Real.smoothTransition.le_one (|t|-1)
  nlinarith

theorem zeta_zero_near {t : ℝ} (ht : |t| ≤ 1/16) : zeta t = 0 := by
  rw [zeta_source,S,Real.smoothTransition.zero_of_nonpos (show 16*|t|-1 ≤ 0 by linarith),zero_mul]

theorem zeta_one {t : ℝ} (hl : 1/8 ≤ |t|) (hu : |t| ≤ 1) : zeta t = 1 := by
  rw [zeta_source,S,Real.smoothTransition.one_of_one_le (show 1 ≤ 16*|t|-1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show |t|-1 ≤ 0 by linarith)]
  ring

theorem zeta_zero_far {t : ℝ} (ht : 2 ≤ |t|) : zeta t = 0 := by
  rw [zeta_source,S,Real.smoothTransition.one_of_one_le (show 1 ≤ |t|-1 by linarith)]
  ring

/-- The separated-support input needed by the bounded-frontier proof. -/
theorem separated_support (t : ℝ) :
    (∀ᶠ u in 𝓝 t, bump u = 0) ∨ (∀ᶠ u in 𝓝 t, gate u = 0) := by
  by_cases ht : |t| < 1/2
  · right
    have he : ∀ᶠ u in 𝓝 t, |u| < 1/2 :=
      (continuous_abs.continuousAt.eventually (gt_mem_nhds ht))
    exact he.mono (fun _ hu => gate_zero hu.le)
  · left
    have ht' : 1/4 < |t| := by linarith
    have he : ∀ᶠ u in 𝓝 t, 1/4 < |u| :=
      (continuous_abs.continuousAt.eventually (lt_mem_nhds ht'))
    exact he.mono (fun _ hu => bump_zero hu.le)

end Smoothness2601.Cutoffs
