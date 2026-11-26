import MatchingBounds1005.Primitive
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform derivative bounds for the two normalized profiles in the scalar
primitive. Compact support is proved for the actual cutoff, not postulated. -/
namespace MatchingBounds1005.Primitive

open Function Set
open scoped ContDiff NNReal

theorem cutoff_compactSupport : HasCompactSupport cutoff := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨Icc (-2 : ℝ) 2, isCompact_Icc, ?_⟩
  intro x hx
  apply cutoff_tail
  have h : ¬ |x| ≤ 2 := by
    simpa only [mem_Icc, ← abs_le] using hx
  exact (lt_of_not_ge h).le

theorem iteratedDeriv_compactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f) (q : ℕ) :
    HasCompactSupport (iteratedDeriv q f) := by
  induction q with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ q ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem smooth_compact_derivatives_bounded {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv q f x| ≤ C := by
  have hcont := hf.continuous_iteratedDeriv q
    (by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    (iteratedDeriv_compactSupport hc q)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (hC x).trans (le_max_left _ _)

noncomputable def coreCorrection (k : ℕ) (x : ℝ) : ℝ :=
  cutoff x * (x ^ k - x ^ (k - 2))

theorem coreCorrection_smooth (k : ℕ) : ContDiff ℝ ∞ (coreCorrection k) :=
  cutoff_smooth.mul ((contDiff_id.pow k).sub (contDiff_id.pow (k - 2)))

theorem coreCorrection_compact (k : ℕ) : HasCompactSupport (coreCorrection k) :=
  cutoff_compactSupport.mul_right

theorem coreCorrection_derivatives_bounded (k q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv q (coreCorrection k) x| ≤ C :=
  smooth_compact_derivatives_bounded (coreCorrection_smooth k) (coreCorrection_compact k) q

theorem normalized_profile_two (x : ℝ) :
    x ^ 2 * weight x = 1 + coreCorrection 2 x := by
  by_cases hx : x = 0
  · subst x
    norm_num [coreCorrection, cutoff_core (show |(0 : ℝ)| ≤ 1 by norm_num)]
  · unfold weight coreCorrection
    norm_num
    field_simp
    ring

theorem normalized_profile_three (x : ℝ) :
    x ^ 3 * weight x = x + coreCorrection 3 x := by
  by_cases hx : x = 0
  · subst x
    simp [coreCorrection]
  · unfold weight coreCorrection
    norm_num
    field_simp
    ring

theorem iteratedDeriv_constant (n : ℕ) (c : ℝ) :
    iteratedDeriv n (fun _ : ℝ => c) = fun _ => if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun _ : ℝ => c) = fun _ => 0 := funext (fun x => deriv_const x c)
    rw [hd, ih]
    simp

theorem iteratedDeriv_id_bound (q : ℕ) (hq : 0 < q) (x : ℝ) :
    |iteratedDeriv q (fun u : ℝ => u) x| ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  rw [iteratedDeriv_succ']
  have hd : deriv (fun u : ℝ => u) = fun _ => 1 := funext (fun u => deriv_id u)
  rw [hd, iteratedDeriv_constant]
  split_ifs <;> norm_num

theorem profile_two_derivatives_bounded (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv q (fun u => u ^ 2 * weight u) x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := coreCorrection_derivatives_bounded 2 q
  refine ⟨C, hC, fun x => ?_⟩
  have heq : (fun u => u ^ 2 * weight u) = fun u => 1 + coreCorrection 2 u :=
    funext normalized_profile_two
  rw [heq, iteratedDeriv_const_add hq]
  exact hbound x

theorem profile_three_derivatives_bounded (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv q (fun u => u ^ 3 * weight u) x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := coreCorrection_derivatives_bounded 3 q
  refine ⟨1 + C, by linarith, fun x => ?_⟩
  have heq : (fun u => u ^ 3 * weight u) = (fun u : ℝ => u) + coreCorrection 3 :=
    funext normalized_profile_three
  have hlevel : (q : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top)
  rw [heq]
  change |iteratedDeriv q (id + coreCorrection 3) x| ≤ 1 + C
  rw [iteratedDeriv_add contDiff_id.contDiffAt
    ((coreCorrection_smooth 3).of_le hlevel).contDiffAt]
  exact (abs_add_le _ _).trans (add_le_add (iteratedDeriv_id_bound q hq x) (hbound x))

theorem slope_normalized {r : ℝ} (hr : 0 < r) :
    slope r = fun u => (120 * r ^ 3) * ((r⁻¹ * u) ^ 3 * weight (r⁻¹ * u)) -
      (120 * r ^ 2) * ((r⁻¹ * u) ^ 2 * weight (r⁻¹ * u)) := by
  funext u
  unfold slope
  rw [div_eq_inv_mul]
  field_simp
  ring

/-- The manuscript's uniform `C_q r^(3-q)` estimate, written as
`C_q r^3 / r^q` to avoid natural-number subtraction in the exponent. -/
theorem potential_derivative_bound (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ u : ℝ,
      |iteratedDeriv (q + 1) (potential r) u| ≤ C * r ^ 3 / r ^ q := by
  obtain ⟨C₃, hC₃, hbound₃⟩ := profile_three_derivatives_bounded q hq
  obtain ⟨C₂, hC₂, hbound₂⟩ := profile_two_derivatives_bounded q hq
  refine ⟨120 * (C₃ + C₂), by positivity, fun r hr u => ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlevel : (q : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top)
  have h₃ : ContDiff ℝ q (fun v : ℝ => v ^ 3 * weight v) :=
    ((contDiff_id.pow 3).mul weight_smooth).of_le hlevel
  have h₂ : ContDiff ℝ q (fun v : ℝ => v ^ 2 * weight v) :=
    ((contDiff_id.pow 2).mul weight_smooth).of_le hlevel
  have hc : ContDiff ℝ q (fun v : ℝ => r⁻¹ * v) := contDiff_const.mul contDiff_id
  have hcomp₃ : ContDiff ℝ q (fun v => (r⁻¹ * v) ^ 3 * weight (r⁻¹ * v)) := h₃.comp hc
  have hcomp₂ : ContDiff ℝ q (fun v => (r⁻¹ * v) ^ 2 * weight (r⁻¹ * v)) := h₂.comp hc
  have hd₃ : ContDiff ℝ q (fun v => (120 * r ^ 3) *
      ((r⁻¹ * v) ^ 3 * weight (r⁻¹ * v))) := contDiff_const.mul hcomp₃
  have hd₂ : ContDiff ℝ q (fun v => (120 * r ^ 2) *
      ((r⁻¹ * v) ^ 2 * weight (r⁻¹ * v))) := contDiff_const.mul hcomp₂
  rw [iteratedDeriv_succ', potential_deriv, slope_normalized hrpos]
  change |iteratedDeriv q
    ((fun v => (120 * r ^ 3) * ((r⁻¹ * v) ^ 3 * weight (r⁻¹ * v))) -
      (fun v => (120 * r ^ 2) * ((r⁻¹ * v) ^ 2 * weight (r⁻¹ * v)))) u| ≤ _
  rw [iteratedDeriv_sub hd₃.contDiffAt hd₂.contDiffAt,
    iteratedDeriv_const_mul hcomp₃.contDiffAt,
    iteratedDeriv_const_mul hcomp₂.contDiffAt,
    iteratedDeriv_comp_const_mul h₃, iteratedDeriv_comp_const_mul h₂]
  have hscale : 0 ≤ r⁻¹ ^ q := pow_nonneg (inv_nonneg.mpr hrpos.le) q
  have hr23 : r ^ 2 ≤ r ^ 3 := by nlinarith [sq_nonneg r]
  calc
    _ ≤ 120 * r ^ 3 * (r⁻¹ ^ q * C₃) + 120 * r ^ 2 * (r⁻¹ ^ q * C₂) := by
      refine (abs_sub _ _).trans ?_
      simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 120 * r ^ 3),
        abs_of_nonneg (by positivity : 0 ≤ 120 * r ^ 2), abs_of_nonneg hscale]
      gcongr
      · exact hbound₃ _
      · exact hbound₂ _
    _ ≤ 120 * r ^ 3 * (r⁻¹ ^ q * C₃) + 120 * r ^ 3 * (r⁻¹ ^ q * C₂) := by
      gcongr
    _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring

/-- Global Lipschitz budgets for every positive derivative order, with the
same uniform dependence on the core width. -/
theorem potential_derivative_lipschitz (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x y : ℝ,
      |iteratedDeriv q (potential r) x - iteratedDeriv q (potential r) y| ≤
        (C * r ^ 3 / r ^ q) * |x - y| := by
  obtain ⟨C, hC, hbound⟩ := potential_derivative_bound q hq
  refine ⟨C, hC, fun r hr x y => ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let L : ℝ≥0 := ⟨C * r ^ 3 / r ^ q, by positivity⟩
  have hlevel : ((q + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (q + 1 : ℕ∞) ≤ ⊤ from le_top)
  have hdiff : Differentiable ℝ (iteratedDeriv q (potential r)) :=
    (contDiff_nat_iff_iteratedDeriv.mp ((potential_smooth r).of_le hlevel)).2 q
      (Nat.lt_succ_self q)
  have hb : ∀ u, ‖deriv (iteratedDeriv q (potential r)) u‖₊ ≤ L := by
    intro u
    apply NNReal.coe_le_coe.mp
    change |deriv (iteratedDeriv q (potential r)) u| ≤ C * r ^ 3 / r ^ q
    rw [← iteratedDeriv_succ]
    exact hbound r hr u
  have hLip := lipschitzWith_of_nnnorm_deriv_le hdiff hb
  simpa only [Real.dist_eq] using hLip.dist_le_mul x y

end MatchingBounds1005.Primitive
