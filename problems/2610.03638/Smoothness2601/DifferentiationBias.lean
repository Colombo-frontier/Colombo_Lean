import Smoothness2601.ChebyshevDifferentiation
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite C^{r,1} Taylor remainder

The highest derivative is Lipschitz; an additional derivative is never assumed.
The proof uses actual iterated derivatives and vector-valued derivative comparison.
-/
noncomputable section
open Set
open scoped Topology BigOperators

namespace Smoothness2601.DifferentiationBias

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def taylorAtZero (f : ℝ → E) (r : ℕ) (t : ℝ) : E :=
  taylorWithinEval f r univ 0 t

theorem taylor_remainder_nonneg (r : ℕ) (f : ℝ → E) (hf : ContDiff ℝ r f)
    {L : ℝ} (_hL : 0 ≤ L)
    (hLip : ∀ u v, ‖iteratedDeriv r f u - iteratedDeriv r f v‖ ≤ L * |u-v|)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖f t - taylorAtZero f r t‖ ≤ L * t ^ (r+1) / ((r+1).factorial : ℝ) := by
  induction r generalizing f t with
  | zero =>
    simpa [taylorAtZero, abs_of_nonneg ht] using hLip t 0
  | succ r ih =>
    have hf' : ContDiff ℝ r (deriv f) :=
      (contDiff_succ_iff_deriv.mp (by simpa using hf)).2.2
    have hd : Differentiable ℝ f :=
      (contDiff_succ_iff_deriv.mp (by simpa using hf)).1
    have hLip' : ∀ u v, ‖iteratedDeriv r (deriv f) u - iteratedDeriv r (deriv f) v‖ ≤
        L * |u-v| := by simpa only [← iteratedDeriv_succ'] using hLip
    let R : ℝ → E := fun x => f x - taylorAtZero f (r+1) x
    let R' : ℝ → E := fun x => deriv f x - taylorAtZero (deriv f) r x
    have hR (x : ℝ) : HasDerivAt R (R' x) x := by
      simpa only [R, R', taylorAtZero, derivWithin_univ] using
        (hd x).hasDerivAt.sub (hasDerivAt_taylorWithinEval_succ (s := univ) (x₀ := 0) f r)
    let B : ℝ → ℝ := fun x => L * x ^ (r+2) / ((r+2).factorial : ℝ)
    let B' : ℝ → ℝ := fun x => L * x ^ (r+1) / ((r+1).factorial : ℝ)
    have hB (x : ℝ) : HasDerivAt B (B' x) x := by
      have hpow := (((hasDerivAt_id x).pow (r+2)).const_mul L).div_const
        ((r+2).factorial : ℝ)
      convert hpow using 1
      dsimp [B']
      have hfact : ((r+2).factorial : ℝ) = (r+2 : ℕ) * ((r+1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_succ (r+1)
      rw [hfact]
      push_cast
      field_simp
      ring
    have hcont : Continuous R := continuous_iff_continuousAt.mpr (fun x => (hR x).continuousAt)
    have hzero : ‖R 0‖ ≤ B 0 := by simp [R, B, taylorAtZero]
    have hbound : ∀ x ∈ Ico 0 t, ‖R' x‖ ≤ B' x := by
      intro x hx
      exact ih (deriv f) hf' hLip' hx.1
    have he := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont.continuousOn
      (fun x _ => (hR x).hasDerivWithinAt) hzero hB hbound ⟨ht, le_rfl⟩
    simpa only [R, B, Nat.succ_eq_add_one, Nat.add_assoc] using he

theorem taylorAtZero_reflect (f : ℝ → E) (r : ℕ) (t : ℝ) :
    taylorAtZero (fun x => f (-x)) r t = taylorAtZero f r (-t) := by
  simp only [taylorAtZero, taylor_within_apply, iteratedDerivWithin_univ,
    iteratedDeriv_comp_neg, neg_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

/-- Sharp Taylor remainder from the finite derivative list, for both signs of t. -/
theorem taylor_remainder (r : ℕ) (f : ℝ → E) (hf : ContDiff ℝ r f)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u v, ‖iteratedDeriv r f u - iteratedDeriv r f v‖ ≤ L * |u-v|)
    (t : ℝ) :
    ‖f t - taylorAtZero f r t‖ ≤ L * |t| ^ (r+1) / ((r+1).factorial : ℝ) := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using taylor_remainder_nonneg r f hf hL hLip ht
  · have ht' : 0 ≤ -t := by linarith
    have hfn : ContDiff ℝ r (fun x => f (-x)) := hf.comp contDiff_neg
    have hLn : ∀ u v, ‖iteratedDeriv r (fun x => f (-x)) u -
        iteratedDeriv r (fun x => f (-x)) v‖ ≤ L * |u-v| := by
      intro u v
      rw [iteratedDeriv_comp_neg, iteratedDeriv_comp_neg, ← smul_sub,
        norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      simpa only [neg_sub_neg, abs_sub_comm] using hLip (-u) (-v)
    have he := taylor_remainder_nonneg r (fun x => f (-x)) hfn hL hLn ht'
    simpa only [neg_neg, taylorAtZero_reflect, abs_of_neg (lt_of_not_ge ht)] using he

open ChebyshevDifferentiation

theorem weighted_monomial (k m : ℕ) {h : ℝ} (hh : 0 < h) (hm : m ≤ 2*k+1) :
    (∑ i, explicitWeight k h i * (h * node (2*k+1) i) ^ m) =
      if m = 1 then 1 else 0 := by
  have he := explicit_differentiation k hh ((Polynomial.X : Polynomial ℝ) ^ m)
    (by simpa using hm)
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at he
  rw [he, Polynomial.derivative_X_pow]
  by_cases hm0 : m = 0
  · simp [hm0]
  by_cases hm1 : m = 1
  · simp [hm1]
  · simp [hm1, show m - 1 ≠ 0 by omega]

/-- The true finite Taylor polynomial differentiates exactly under the explicit
stencil. This works in an arbitrary normed real vector space, with no choice of
coordinates or dimension-dependent norm comparison. -/
theorem weighted_taylor (k r : ℕ) {h : ℝ} (hh : 0 < h) (hr : 1 ≤ r)
    (hrk : r ≤ 2*k+1) (f : ℝ → E) :
    (∑ i, explicitWeight k h i • taylorAtZero f r (h * node (2*k+1) i)) = deriv f 0 := by
  simp only [taylorAtZero, taylor_within_apply, iteratedDerivWithin_univ, sub_zero,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hterm (m : ℕ) (hm : m ∈ Finset.range (r+1)) :
      (∑ i, (explicitWeight k h i * ((m.factorial : ℝ)⁻¹ *
        (h * node (2*k+1) i) ^ m)) • iteratedDeriv m f 0) =
      if m = 1 then deriv f 0 else 0 := by
    rw [← Finset.sum_smul]
    have he : (∑ i, explicitWeight k h i * ((m.factorial : ℝ)⁻¹ *
        (h * node (2*k+1) i) ^ m)) =
        (∑ i, explicitWeight k h i * (h * node (2*k+1) i) ^ m) *
          (m.factorial : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, weighted_monomial k m hh (by have := Finset.mem_range.mp hm; omega)]
    split_ifs with hm1
    · simp [hm1, iteratedDeriv_one]
    · simp
  rw [Finset.sum_congr rfl hterm]
  simp [show 1 < r + 1 by omega]

/-- A generic finite-stencil remainder estimate. -/
theorem stencil_error_bound {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (v : ι → E) (A : ℝ) (hv : ∀ i, ‖v i‖ ≤ A) :
    ‖∑ i, d i • v i‖ ≤ (∑ i, |d i|) * A := by
  calc
    _ ≤ ∑ i, ‖d i • v i‖ := norm_sum_le _ _
    _ = ∑ i, |d i| * ‖v i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |d i| * A := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Equation `eq:Zbias`, with the Taylor constant expressed directly through
the actual Lipschitz bound L of the r-th derivative along the query line. -/
theorem chebyshev_bias (k r : ℕ) {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hr : 1 ≤ r) (hrk : r ≤ 2*k+1) (f : ℝ → E) (hf : ContDiff ℝ r f)
    (hLip : ∀ u v, ‖iteratedDeriv r f u - iteratedDeriv r f v‖ ≤ L * |u-v|) :
    ‖(∑ i, explicitWeight k h i • f (h * node (2*k+1) i)) - deriv f 0‖ ≤
      (2*k+1 : ℕ) * L * h ^ r / ((r+1).factorial : ℝ) := by
  have hremainder (i : Fin (2*k+2)) :
      ‖f (h * node (2*k+1) i) - taylorAtZero f r (h * node (2*k+1) i)‖ ≤
        L * h ^ (r+1) / ((r+1).factorial : ℝ) := by
    have he := taylor_remainder r f hf hL hLip (h * node (2*k+1) i)
    apply he.trans
    have hnode : |node (2*k+1) i| ≤ 1 := abs_le.mpr (node_mem _ i)
    have hprod : |h * node (2*k+1) i| ≤ h := by
      rw [abs_mul, abs_of_pos hh]
      exact (mul_le_mul_of_nonneg_left hnode hh.le).trans_eq (mul_one h)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hprod _) hL)
      (Nat.cast_nonneg _)
  have he : (∑ i, explicitWeight k h i • f (h * node (2*k+1) i)) - deriv f 0 =
      ∑ i, explicitWeight k h i •
        (f (h * node (2*k+1) i) - taylorAtZero f r (h * node (2*k+1) i)) := by
    rw [← weighted_taylor k r hh hr hrk f]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [he]
  have hb := stencil_error_bound (explicitWeight k h)
    (fun i => f (h * node (2*k+1) i) - taylorAtZero f r (h * node (2*k+1) i))
    _ hremainder
  rw [explicit_weights_abs_sum k hh] at hb
  apply hb.trans_eq
  rw [pow_succ]
  field_simp
  ring

section QueryLine

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def directionMap (v : Y) : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight v

@[simp] theorem directionMap_apply (v : Y) (t : ℝ) : directionMap v t = t • v := rfl

/-- The actual r-th scalar-line derivative is the actual r-th Fréchet derivative
applied to r copies of the query direction. -/
theorem iteratedDeriv_queryLine (r : ℕ) (F : Y → E) (hf : ContDiff ℝ r F)
    (y v : Y) (t : ℝ) :
    iteratedDeriv r (fun u : ℝ => F (y + u • v)) t =
      iteratedFDeriv ℝ r F (y + t • v) (fun _ : Fin r => v) := by
  have hg : ContDiff ℝ r (fun z : Y => F (y+z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ r ((fun z : Y => F (y+z)) ∘ directionMap v) t
    (fun _ : Fin r => 1) = _
  rw [(directionMap v).iteratedFDeriv_comp_right hg t le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    directionMap_apply, one_smul, iteratedFDeriv_comp_add_left]

theorem queryLine_lipschitz_top (r : ℕ) (F : Y → E) (hf : ContDiff ℝ r F)
    {L : ℝ}
    (hLip : ∀ u w, ‖iteratedFDeriv ℝ r F u - iteratedFDeriv ℝ r F w‖ ≤ L * ‖u-w‖)
    (y v : Y) (u w : ℝ) :
    ‖iteratedDeriv r (fun t : ℝ => F (y+t • v)) u -
      iteratedDeriv r (fun t : ℝ => F (y+t • v)) w‖ ≤
        (L * ‖v‖ ^ (r+1)) * |u-w| := by
  rw [iteratedDeriv_queryLine r F hf, iteratedDeriv_queryLine r F hf,
    ← ContinuousMultilinearMap.sub_apply]
  calc
    _ ≤ ‖iteratedFDeriv ℝ r F (y+u • v) - iteratedFDeriv ℝ r F (y+w • v)‖ * ‖v‖ ^ r := by
      simpa using (iteratedFDeriv ℝ r F (y+u • v) -
        iteratedFDeriv ℝ r F (y+w • v)).le_opNorm (fun _ : Fin r => v)
    _ ≤ (L * ‖(y+u • v)-(y+w • v)‖) * ‖v‖ ^ r :=
      mul_le_mul_of_nonneg_right (hLip _ _) (pow_nonneg (norm_nonneg v) _)
    _ = _ := by
      rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, pow_succ]
      ring

theorem queryLine_deriv_zero (F : Y → E) {y : Y} (hf : DifferentiableAt ℝ F y) (v : Y) :
    deriv (fun t : ℝ => F (y+t • v)) 0 = fderiv ℝ F y v := by
  have hline : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hf0 : HasFDerivAt F (fderiv ℝ F y) (y+(0:ℝ) • v) := by simpa using hf.hasFDerivAt
  have he := hf0.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero] using he.deriv

/-- Source `eq:Zbias` directly from a finite-order Fréchet derivative Lipschitz
budget on the vector field F. The point and direction are arbitrary. -/
theorem chebyshev_bias_frechet (k r : ℕ) {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hr : 1 ≤ r) (hrk : r ≤ 2*k+1) (F : Y → E) (hf : ContDiff ℝ r F)
    (hLip : ∀ u w, ‖iteratedFDeriv ℝ r F u - iteratedFDeriv ℝ r F w‖ ≤ L * ‖u-w‖)
    (y v : Y) :
    ‖(∑ i, explicitWeight k h i • F (y + (h * node (2*k+1) i) • v)) -
      fderiv ℝ F y v‖ ≤
        (2*k+1 : ℕ) * (L * ‖v‖ ^ (r+1)) * h ^ r / ((r+1).factorial : ℝ) := by
  have hline : ContDiff ℝ r (fun t : ℝ => F (y+t • v)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have he := chebyshev_bias k r hh (mul_nonneg hL (pow_nonneg (norm_nonneg v) _)) hr hrk
    (fun t : ℝ => F (y+t • v)) hline (queryLine_lipschitz_top r F hf hLip y v)
  rw [queryLine_deriv_zero F ((hf.differentiable (by exact_mod_cast hr)) y) v] at he
  exact he

end QueryLine

end Smoothness2601.DifferentiationBias
