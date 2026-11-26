import FullJet.Radial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

open scoped ContDiff BigOperators
open Set Function

namespace FullJet

private theorem order_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section Linear
variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_linear_le_one (L : E →L[ℝ] F) (x : E)
    (hL : ‖L‖ ≤ 1) (hx : ‖L x‖ ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k L x‖ ≤ 1 := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hx
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ L = fun _ => L := funext (fun y => L.fderiv)
    rw [hfd]
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hL
    | succ k => simp [iteratedFDeriv_succ_const]

end Linear

section Inner
variable [InnerProductSpace ℝ E]

noncomputable def normalizedDenom (b : ℝ) (y : E) : ℝ := b ^ 2 + ‖b • y‖ ^ 2

theorem normalizedDenom_contDiff (b : ℝ) : ContDiff ℝ ∞ (normalizedDenom b : E → ℝ) :=
  contDiff_const.add ((contDiff_norm_sq ℝ).comp (contDiff_const.smul contDiff_id))

theorem normalizedDenom_pos {b : ℝ} (hb : 0 < b) (y : E) : 0 < normalizedDenom b y := by
  unfold normalizedDenom
  positivity

theorem normalizedDenom_factor {b : ℝ} (hb : 0 < b) (y : E) :
    normalizedDenom b y = b ^ 2 * (1 + ‖y‖ ^ 2) := by
  simp only [normalizedDenom, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
  ring

/-- Every derivative of the normalized quadratic has a dimension-free bound.
Using the bilinear Leibniz estimate avoids expanding higher derivative tensors. -/
theorem normalizedDenom_derivative_bound {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (x : E) (hx : ‖b • x‖ ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (normalizedDenom b) x‖ ≤ (2 : ℝ) ^ k := by
  let L : E →L[ℝ] E := b • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos hb, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg y) hb1
  have hLj (j : ℕ) : ‖iteratedFDeriv ℝ j L x‖ ≤ 1 :=
    norm_iteratedFDeriv_linear_le_one L x hL hx j
  have hsq := (innerSL ℝ (E := E)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (L.contDiff : ContDiff ℝ ∞ L) L.contDiff x (order_le_infty k) (norm_innerSL_le ℝ)
  have hsum : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  have hsqbound : ‖iteratedFDeriv ℝ k (fun y : E => ‖b • y‖ ^ 2) x‖ ≤ (2 : ℝ) ^ k := by
    calc
      _ = ‖iteratedFDeriv ℝ k (fun y => (innerSL ℝ) (L y) (L y)) x‖ := by
        congr 2
        funext y
        exact (real_inner_self_eq_norm_sq (b • y)).symm
      _ ≤ _ := hsq
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have ha := mul_le_mul_of_nonneg_left (hLj j) (show (0 : ℝ) ≤ k.choose j by positivity)
        have hb' := mul_le_mul ha (hLj (k - j)) (norm_nonneg _) (by positivity)
        simpa using hb'
      _ = _ := hsum
  unfold normalizedDenom
  have hsqcont : ContDiff ℝ k (fun y : E => ‖b • y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp L.contDiff
  rw [iteratedFDeriv_add_apply' (f := fun _ : E => b ^ 2)
    (g := fun y : E => ‖b • y‖ ^ 2) contDiffAt_const hsqcont.contDiffAt,
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  simpa using hsqbound

end Inner

noncomputable def inverseSqrt (t : ℝ) : ℝ := (Real.sqrt t)⁻¹

theorem inverseSqrt_contDiffOn : ContDiffOn ℝ ∞ inverseSqrt (Ioi 0) :=
  (contDiffOn_id.sqrt (fun t ht => ne_of_gt ht)).inv
    (fun t ht => (Real.sqrt_pos.mpr ht).ne')

/-- A real constant depending only on derivative order, with no space or point parameter. -/
noncomputable def inverseSqrtDerivativeBound (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j inverseSqrt 1‖

theorem inverseSqrtDerivativeBound_nonneg (k : ℕ) : 0 ≤ inverseSqrtDerivativeBound k :=
  Finset.sum_nonneg (fun j hj => norm_nonneg _)

theorem inverseSqrt_derivative_le (k j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j inverseSqrt 1‖ ≤ inverseSqrtDerivativeBound k := by
  unfold inverseSqrtDerivativeBound
  exact Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun r => ‖iteratedFDeriv ℝ r inverseSqrt 1‖)
    (fun r hr => norm_nonneg _) (Finset.mem_range.mpr (by omega : j < k + 1))

section Inner
variable [InnerProductSpace ℝ E]

theorem inverseSqrt_normalizedDenom_contDiff {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ∞ (inverseSqrt ∘ (normalizedDenom b : E → ℝ)) := by
  exact ((normalizedDenom_contDiff b).sqrt
    (fun y => (normalizedDenom_pos hb y).ne')).inv
    (fun y => (Real.sqrt_pos.mpr (normalizedDenom_pos hb y)).ne')

theorem inverseSqrt_normalizedDenom_derivative_bound {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (x : E) (hx : ‖b • x‖ ≤ 1)
    (hval : normalizedDenom b x = 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (inverseSqrt ∘ normalizedDenom b) x‖ ≤
      k.factorial * inverseSqrtDerivativeBound k * (2 : ℝ) ^ k := by
  have h := norm_iteratedFDerivWithin_comp_le inverseSqrt_contDiffOn
    (normalizedDenom_contDiff b).contDiffOn (order_le_infty k)
    isOpen_Ioi.uniqueDiffOn uniqueDiffOn_univ
    (fun y hy => normalizedDenom_pos hb y) (mem_univ x)
    (C := inverseSqrtDerivativeBound k) (D := 2) ?_ ?_
  · simpa only [iteratedFDerivWithin_univ] using h
  · intro j hj
    rw [hval, iteratedFDerivWithin_of_isOpen j isOpen_Ioi (by norm_num : (1 : ℝ) ∈ Ioi 0)]
    exact inverseSqrt_derivative_le k j hj
  · intro j hj hjk
    rw [iteratedFDerivWithin_univ]
    exact normalizedDenom_derivative_bound hb hb1 x hx j hj

theorem normalizedRadial_eq {b : ℝ} (hb : 0 < b) :
    (fun y : E => inverseSqrt (normalizedDenom b y) • (b • y)) = radial := by
  funext y
  rw [inverseSqrt, normalizedDenom_factor hb, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq_eq_abs, abs_of_pos hb, smul_smul]
  unfold radial
  rw [mul_inv_rev]
  simp only [mul_smul, inv_smul_smul₀ hb.ne']

end Inner

/-- Explicit finite constants independent of dimension, point, and hidden data. -/
noncomputable def radialDerivativeBound (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
    ((j.factorial : ℝ) * inverseSqrtDerivativeBound j * (2 : ℝ) ^ j)

theorem radialDerivativeBound_nonneg (k : ℕ) : 0 ≤ radialDerivativeBound k := by
  apply Finset.sum_nonneg
  intro j hj
  have := inverseSqrtDerivativeBound_nonneg j
  positivity

section Inner
variable [InnerProductSpace ℝ E]

/-- The dimension-free all-order radial bound, Lemma `lem:radial` of the paper.
The space may be any real inner product space, even infinite dimensional. -/
theorem radial_derivative_bound (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k radial x‖ ≤ radialDerivativeBound k := by
  let b : ℝ := (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹
  have hc : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr hc
  have hb : 0 < b := inv_pos.mpr hs
  have hb1 : b ≤ 1 := by
    exact (inv_le_one₀ hs).mpr
      (Real.one_le_sqrt.mpr (show 1 ≤ 1 + ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖]))
  have hx : ‖b • x‖ ≤ 1 := radial_norm_le_one x
  have hval : normalizedDenom b x = 1 := by
    rw [normalizedDenom_factor hb]
    dsimp [b]
    rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  let L : E →L[ℝ] E := b • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos hb, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg y) hb1
  have hLj (j : ℕ) : ‖iteratedFDeriv ℝ j L x‖ ≤ 1 :=
    norm_iteratedFDeriv_linear_le_one L x hL hx j
  have hg := inverseSqrt_normalizedDenom_contDiff (E := E) hb
  have hgj (j : ℕ) := inverseSqrt_normalizedDenom_derivative_bound hb hb1 x hx hval j
  rw [← normalizedRadial_eq (E := E) hb]
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (inverseSqrt ∘ normalizedDenom b) x‖ *
        ‖iteratedFDeriv ℝ (k - j) L x‖ :=
      norm_iteratedFDeriv_smul_le hg (L.contDiff : ContDiff ℝ ∞ L) x (order_le_infty k)
    _ ≤ radialDerivativeBound k := by
      apply Finset.sum_le_sum
      intro j hj
      have hC0 := inverseSqrtDerivativeBound_nonneg j
      have ha := mul_le_mul_of_nonneg_left (hgj j) (show (0 : ℝ) ≤ k.choose j by positivity)
      have hb' := mul_le_mul ha (hLj (k - j)) (norm_nonneg _) (by positivity)
      simpa only [mul_one] using hb'

/-- Applying a fixed linear functional scales the radial derivative bound by
exactly its operator norm; this is the single-row `1/ρ` dependence. -/
theorem radial_functional_derivative_bound (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (L ∘ radial) x‖ ≤ ‖L‖ * radialDerivativeBound k := by
  rw [L.iteratedFDeriv_comp_left radial_contDiff.contDiffAt (order_le_infty k)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (radial_derivative_bound k x) (norm_nonneg L))

theorem alignment_derivative_bound (θ x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (alignment θ) x‖ ≤ ‖θ‖ * radialDerivativeBound k := by
  simpa only [innerSL_apply_norm] using
    radial_functional_derivative_bound (innerSL ℝ θ) k x

end Inner

end FullJet
