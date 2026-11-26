import VIReference.Pilot.Model
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Taylor models under a Lipschitz highest available derivative

The paper deliberately assumes only `C^(p-1)` regularity and a Lipschitz
`(p-1)`st derivative.  Consequently the usual Taylor theorem requiring a
continuous `p`th derivative is not applicable.  This file instead uses the
integral Taylor formula one order lower and subtracts the constant top-order
term inside the integral.
-/

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

namespace VIReference.Pilot

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The order-`p-1` Taylor polynomial used in the article. -/
noncomputable def taylorModel (p : ℕ) (f : E → F) (x y : E) : F :=
  ∑ j ∈ Finset.range p,
    (Nat.factorial j : ℝ)⁻¹ • iteratedFDeriv ℝ j f x (fun _ ↦ y - x)

private lemma integral_one_sub_pow (q : ℕ) :
    (∫ t : ℝ in 0..1, (1 - t) ^ q) = 1 / (q + 1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ t ^ q) 1]
  simp [integral_pow]

private lemma integral_mul_one_sub_pow (q : ℕ) :
    (∫ t : ℝ in 0..1, t * (1 - t) ^ q) =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  have hchange : (∫ t : ℝ in 0..1, t * (1 - t) ^ q) =
      ∫ u : ℝ in 0..1, (1 - u) * u ^ q := by
    simpa [mul_comm] using (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := 1) (fun u : ℝ ↦ (1 - u) * u ^ q) 1)
  rw [hchange]
  have hq : IntervalIntegrable (fun u : ℝ ↦ u ^ q) volume 0 1 :=
    (continuous_id.pow q).intervalIntegrable _ _
  have hq1 : IntervalIntegrable (fun u : ℝ ↦ u ^ (q + 1)) volume 0 1 :=
    (continuous_id.pow (q + 1)).intervalIntegrable _ _
  rw [show (∫ u : ℝ in 0..1, (1 - u) * u ^ q) =
      (∫ u : ℝ in 0..1, u ^ q) - ∫ u : ℝ in 0..1, u ^ (q + 1) by
    rw [← intervalIntegral.integral_sub hq hq1]
    apply intervalIntegral.integral_congr
    intro u _
    ring]
  rw [integral_pow, integral_pow]
  norm_num
  field_simp
  ring

/-- Integral remainder identity obtained by applying mathlib's Taylor formula
one order lower. -/
private lemma taylor_remainder_eq (q : ℕ) (f : E → F) (x s : E)
    (hf : ∀ (t : ℝ), t ∈ Icc 0 1 → ContDiffAt ℝ (q + 1) f (x + t • s)) :
    f (x + s) - taylorModel (q + 2) f x (x + s) =
      (Nat.factorial q : ℝ)⁻¹ • ∫ t : ℝ in 0..1,
        (1 - t)^q • ((iteratedFDeriv ℝ (q + 1) f (x + t • s) -
          iteratedFDeriv ℝ (q + 1) f x) (fun _ ↦ s)) := by
  have hformula := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := q) (f := f) (x := x) (y := s) hf
  have hcont_top : ContinuousOn
      (fun t : ℝ ↦ iteratedFDeriv ℝ (q + 1) f (x + t • s) (fun _ ↦ s))
      (uIcc 0 1) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    have hc := (hf t ht').continuousAt_iteratedFDeriv (k := q + 1) (by norm_num)
    have hcurve : ContinuousAt (fun u : ℝ ↦ x + u • s) t := by fun_prop
    have hmap : ContinuousAt
        (fun u : ℝ ↦ iteratedFDeriv ℝ (q + 1) f (x + u • s)) t := by
      simpa [Function.comp_def] using hc.comp
        (f := fun u : ℝ ↦ x + u • s) (g := iteratedFDeriv ℝ (q + 1) f) hcurve
    simpa [Function.comp_def] using
      ((ContinuousEval.continuous_eval (F := E [×q + 1]→L[ℝ] F)).continuousAt.comp
        (hmap.prodMk (continuousAt_const : ContinuousAt
          (fun _ : ℝ ↦ fun _ : Fin (q + 1) ↦ s) t))).continuousWithinAt
  have hconst_int :
      (∫ t : ℝ in 0..1, (1 - t)^q •
        iteratedFDeriv ℝ (q + 1) f x (fun _ ↦ s)) =
        (1 / (q + 1 : ℝ)) • iteratedFDeriv ℝ (q + 1) f x (fun _ ↦ s) := by
    rw [intervalIntegral.integral_smul_const, integral_one_sub_pow]
  have htop_int : IntervalIntegrable (fun t : ℝ ↦ (1 - t)^q •
      iteratedFDeriv ℝ (q + 1) f (x + t • s) (fun _ ↦ s)) volume 0 1 :=
    (ContinuousOn.smul (by fun_prop) hcont_top).intervalIntegrable
  have hcst_int : IntervalIntegrable (fun t : ℝ ↦ (1 - t)^q •
      iteratedFDeriv ℝ (q + 1) f x (fun _ ↦ s)) volume 0 1 :=
    (Continuous.continuousOn (by fun_prop : Continuous (fun t : ℝ ↦ (1 - t)^q •
      iteratedFDeriv ℝ (q + 1) f x (fun _ ↦ s)))).intervalIntegrable
  have hdiff_int :
      (∫ t : ℝ in 0..1, (1 - t)^q •
        ((iteratedFDeriv ℝ (q + 1) f (x + t • s) -
          iteratedFDeriv ℝ (q + 1) f x) (fun _ ↦ s))) =
      (∫ t : ℝ in 0..1, (1 - t)^q •
        iteratedFDeriv ℝ (q + 1) f (x + t • s) (fun _ ↦ s)) -
      (∫ t : ℝ in 0..1, (1 - t)^q •
        iteratedFDeriv ℝ (q + 1) f x (fun _ ↦ s)) := by
    rw [← intervalIntegral.integral_sub htop_int hcst_int]
    apply intervalIntegral.integral_congr
    intro t _
    simp [smul_sub]
  rw [taylorModel, show x + s - x = s by abel, Finset.sum_range_succ]
  rw [hformula, hdiff_int, hconst_int]
  have hfac : (Nat.factorial (q + 1) : ℝ)⁻¹ =
      (Nat.factorial q : ℝ)⁻¹ * (1 / (q + 1 : ℝ)) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [hfac, mul_smul]
  simp only [sub_eq_add_neg, smul_add]
  module

/-- Sharp norm bound for the preceding integral remainder. -/
private lemma taylor_remainder_norm_le (q : ℕ) (f : E → F) (x s : E) (L : ℝ)
    (hf : ∀ (t : ℝ), t ∈ Icc 0 1 → ContDiffAt ℝ (q + 1) f (x + t • s))
    (hlip : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (q + 1) f (x + t • s) -
        iteratedFDeriv ℝ (q + 1) f x‖ ≤ L * ‖t • s‖) :
    ‖f (x + s) - taylorModel (q + 2) f x (x + s)‖ ≤
      L / (Nat.factorial (q + 2) : ℝ) * ‖s‖ ^ (q + 2) := by
  rw [taylor_remainder_eq q f x s hf, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg (Nat.factorial q))]
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(1 - t)^q • ((iteratedFDeriv ℝ (q + 1) f (x + t • s) -
        iteratedFDeriv ℝ (q + 1) f x) (fun _ ↦ s))‖ ≤
        (L * ‖s‖ ^ (q + 2)) * (t * (1 - t)^q) := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _)]
    calc
      (1 - t)^q * ‖(iteratedFDeriv ℝ (q + 1) f (x + t • s) -
          iteratedFDeriv ℝ (q + 1) f x) (fun _ ↦ s)‖
          ≤ (1 - t)^q * (‖iteratedFDeriv ℝ (q + 1) f (x + t • s) -
            iteratedFDeriv ℝ (q + 1) f x‖ * ‖s‖ ^ (q + 1)) := by
              exact mul_le_mul_of_nonneg_left (by
                simpa using (iteratedFDeriv ℝ (q + 1) f (x + t • s) -
                  iteratedFDeriv ℝ (q + 1) f x).le_opNorm_mul_pow_card_of_le
                    (m := fun _ ↦ s) (b := ‖s‖) (by simp))
                (pow_nonneg (sub_nonneg.mpr ht.2) _)
      _ ≤ (1 - t)^q * ((L * ‖t • s‖) * ‖s‖ ^ (q + 1)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hlip t ⟨ht.1.le, ht.2⟩)
                  (pow_nonneg (norm_nonneg _) _)) (pow_nonneg (sub_nonneg.mpr ht.2) _)
      _ = (L * ‖s‖ ^ (q + 2)) * (t * (1 - t)^q) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
              ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (E := F)
    (f := fun t : ℝ ↦ (1 - t)^q •
      ((iteratedFDeriv ℝ (q + 1) f (x + t • s) -
        iteratedFDeriv ℝ (q + 1) f x) (fun _ ↦ s)))
    (g := fun t : ℝ ↦ (L * ‖s‖ ^ (q + 2)) * (t * (1 - t)^q))
    (a := 0) (b := 1) (μ := volume) zero_le_one
    (by filter_upwards with t; exact fun ht ↦ hpoint t ht)
    ((Continuous.continuousOn (by fun_prop : Continuous (fun t : ℝ ↦
      (L * ‖s‖ ^ (q + 2)) * (t * (1 - t)^q)))).intervalIntegrable)
  calc
    (Nat.factorial q : ℝ)⁻¹ *
        ‖∫ t : ℝ in 0..1, (1 - t) ^ q •
          ((iteratedFDeriv ℝ (q + 1) f (x + t • s) -
            iteratedFDeriv ℝ (q + 1) f x) (fun _ ↦ s))‖
      ≤ (Nat.factorial q : ℝ)⁻¹ *
        (∫ t : ℝ in 0..1, (L * ‖s‖ ^ (q + 2)) * (t * (1 - t)^q)) := by
          gcongr
    _ = L / (Nat.factorial (q + 2) : ℝ) * ‖s‖ ^ (q + 2) := by
      rw [intervalIntegral.integral_const_mul, integral_mul_one_sub_pow]
      rw [show Nat.factorial (q + 2) = (q + 2) * (q + 1) * Nat.factorial q by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
      push_cast
      field_simp

/-- The derivative Taylor model, represented using the canonically curried
successive derivatives of `G`.  This is the derivative of `taylorModel`; the
representation is chosen so its operator norm is definitionally the one used
by the source estimate. -/
noncomputable def taylorModelDerivative (p : ℕ) (G : E → E) (x y : E) : E →L[ℝ] E :=
  taylorModel (p - 1) (fderiv ℝ G) x y

private lemma norm_iteratedFDeriv_fderiv_sub (n : ℕ) (f : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖ =
      ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖ := by
  let e := (continuousMultilinearCurryRightEquiv' ℝ n E F).symm
  rw [← e.norm_map (iteratedFDeriv ℝ n (fderiv ℝ f) x -
    iteratedFDeriv ℝ n (fderiv ℝ f) y)]
  simp only [e]
  have hx := iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (n := n) (f := f) (x := x)
  have hy := iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (n := n) (f := f) (x := y)
  simp only [Function.comp_apply] at hx hy
  rw [hx, hy]
  congr 1

private lemma norm_iteratedFDeriv_zero_sub (f : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- A source-level, directly inspectable statement of both estimates in
`lem:taylor`.  The hypotheses are local to an open neighborhood containing the
convex domain, exactly as in `def:class`; no `p`th derivative occurs. -/
def TaylorRemainderClaim (p : ℕ) (Lp : ℝ) (X U : Set E) (G : E → E) : Prop :=
  2 ≤ p → 0 ≤ Lp → IsOpen U → X ⊆ U → Convex ℝ X →
    ContDiffOn ℝ (p - 1 : ℕ) G U →
    (∀ x ∈ X, ∀ y ∈ X,
      ‖iteratedFDeriv ℝ (p - 1) G x - iteratedFDeriv ℝ (p - 1) G y‖ ≤
        Lp * ‖x - y‖) →
    ∀ x ∈ X, ∀ y ∈ X,
      ‖G y - taylorModel p G x y‖ ≤ Lp / (Nat.factorial p : ℝ) * ‖y - x‖ ^ p ∧
      ‖fderiv ℝ G y - taylorModelDerivative p G x y‖ ≤
        Lp / (Nat.factorial (p - 1) : ℝ) * ‖y - x‖ ^ (p - 1)

/-- `lem:taylor`: both sharp Taylor remainder bounds under exactly the
`C^(p-1)` plus Lipschitz-top-derivative assumptions of the article. -/
theorem taylorRemainderClaim_proof (p : ℕ) (Lp : ℝ) (X U : Set E) (G : E → E) :
    TaylorRemainderClaim p Lp X U G := by
  intro hp hLp hU hXU hconv hreg hlip x hx y hy
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 2 := ⟨p - 2, by omega⟩
  have horder : q + 2 - 1 = q + 1 := by omega
  rw [horder] at hreg hlip ⊢
  let s := y - x
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) : x + t • s ∈ X := by
    have hm := hconv.lineMap_mem hx hy ht
    simpa [s, AffineMap.lineMap_apply, add_comm] using hm
  have hcd (t : ℝ) (ht : t ∈ Icc 0 1) :
      ContDiffAt ℝ (q + 1 : ℕ) G (x + t • s) := by
    exact hreg.contDiffAt (hU.mem_nhds (hXU (hseg t ht)))
  have hsxy : x + s = y := by simp [s]
  constructor
  · have hfirst := taylor_remainder_norm_le q G x s Lp
      (fun t ht ↦ (hcd t ht).of_le (by norm_cast))
      (fun t ht ↦ by
        convert hlip (x + t • s) (hseg t ht) x hx using 1 <;> simp [s])
    simpa [hsxy, s] using hfirst
  · cases q with
    | zero =>
      have h := hlip y hy x hx
      rw [← norm_iteratedFDeriv_fderiv_sub (n := 0) G y x] at h
      rw [norm_iteratedFDeriv_zero_sub] at h
      simpa [taylorModelDerivative, taylorModel,
        continuousMultilinearCurryFin0_symm_apply_apply] using h
    | succ r =>
      have hsecond := taylor_remainder_norm_le r (fderiv ℝ G) x s Lp
        (fun t ht ↦ by
          have hd := (hcd t ht).fderiv_right (m := (r + 1 : ℕ)) (by norm_num)
          exact hd.of_le (by norm_cast))
        (fun t ht ↦ by
          rw [norm_iteratedFDeriv_fderiv_sub]
          convert hlip (x + t • s) (hseg t ht) x hx using 1 <;>
            simp [s, Nat.succ_eq_add_one, add_assoc])
      simpa [taylorModelDerivative, hsxy, s, Nat.succ_eq_add_one, add_assoc] using hsecond

end VIReference.Pilot
