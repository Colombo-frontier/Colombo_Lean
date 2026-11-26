import RandomizedFO2003.RadialSquash
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

namespace RandomizedFO2003.Primitives

open Set Filter
open scoped Topology BigOperators

/-- A finite jet of the fixed scalar cutoff has a common numerical bound on
the only interval where the radial map can be nonzero. -/
theorem radialCutoff_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ q ∈ Icc (0 : ℝ) 4, |iteratedDeriv i radialCutoff q| ≤ C := by
  induction n with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro i hi q _hq
    have hi0 : i = 0 := by omega
    rw [hi0, iteratedDeriv_zero, abs_of_nonneg (radialCutoff_mem q).1]
    exact (radialCutoff_mem q).2
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (((radialCutoff_contDiff (n + 1)).continuous_iteratedDeriv (n + 1) le_rfl).continuousOn :
        ContinuousOn (iteratedDeriv (n + 1) radialCutoff) (Icc (0 : ℝ) 4))
    refine ⟨max C M, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro i hi q hq
    by_cases hin : i ≤ n
    · exact (hbound i hin q hq).trans (le_max_left _ _)
    · have heq : i = n + 1 := by omega
      subst i
      exact (show |iteratedDeriv (n + 1) radialCutoff q| ≤ M by
        simpa only [Real.norm_eq_abs] using hM q hq).trans (le_max_right _ _)

noncomputable def radialJetBound (n : ℕ) : ℝ := (radialCutoff_jet_bound n).choose

theorem radialJetBound_pos (n : ℕ) : 0 < radialJetBound n :=
  (radialCutoff_jet_bound n).choose_spec.1

theorem radialJetBound_spec (n i : ℕ) (hi : i ≤ n) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 4) :
    ‖iteratedFDeriv ℝ i radialCutoff q‖ ≤ radialJetBound n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (radialCutoff_jet_bound n).choose_spec.2 i hi q hq

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_linear_succ_le (A : E →L[ℝ] F) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (n + 1) A x‖ ≤ ‖A‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hA : fderiv ℝ A = fun _ => A := funext (fun _ => A.fderiv)
  rw [hA]
  cases n with
  | zero => rw [norm_iteratedFDeriv_zero]
  | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; exact norm_nonneg A

theorem norm_iteratedFDeriv_id_le_two (i : ℕ) {x : E} (hx : ‖x‖ ≤ 2) :
    ‖iteratedFDeriv ℝ i (id : E → E) x‖ ≤ 2 := by
  cases i with
  | zero => simpa only [norm_iteratedFDeriv_zero, id_eq] using hx
  | succ i =>
    exact (norm_iteratedFDeriv_linear_succ_le (ContinuousLinearMap.id ℝ E) i x).trans
      (ContinuousLinearMap.norm_id_le.trans (by norm_num))

theorem iteratedFDeriv_eq_of_eventuallyEq {f g : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] g) (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  have hw : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq h.self_of_nhds n

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A deliberately coarse estimate avoids choosing bases and thus holds in
every real inner product space, with the same constants. -/
theorem norm_iteratedFDeriv_inner_self_le {x : E} (hx : ‖x‖ ≤ 2) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y : E => inner (𝕜 := ℝ) y y) x‖ ≤ (8 : ℝ) ^ i := by
  have h := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (show ContDiff ℝ i (id : E → E) from contDiff_id) contDiff_id x le_rfl (norm_innerSL_le ℝ)
  have hsum : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (id : E → E) x‖ * ‖iteratedFDeriv ℝ (i - j) (id : E → E) x‖ := h
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * 2 * 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_id_le_two j hx) (Nat.cast_nonneg _))
        (norm_iteratedFDeriv_id_le_two (i - j) hx) (norm_nonneg _) (by positivity)
    _ = 4 * 2 ^ i := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring
    _ ≤ 4 ^ i * 2 ^ i := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hi
    _ = 8 ^ i := by rw [← mul_pow]; norm_num

theorem radialCutoff_inner_derivative_bound (n i : ℕ) (hi : i ≤ n) {x : E} (hx : ‖x‖ ≤ 2) :
    ‖iteratedFDeriv ℝ i (fun y : E => radialCutoff (inner (𝕜 := ℝ) y y)) x‖ ≤
      i.factorial * radialJetBound n * 8 ^ i := by
  apply norm_iteratedFDeriv_comp_le (radialCutoff_contDiff i)
    (show ContDiff ℝ i (fun y : E => inner (𝕜 := ℝ) y y) from contDiff_id.inner ℝ contDiff_id)
    le_rfl x
  · intro j hj
    apply radialJetBound_spec n j (hj.trans hi)
    rw [real_inner_self_eq_norm_sq]
    constructor
    · positivity
    · nlinarith [norm_nonneg x]
  · intro j hj _hji
    exact norm_iteratedFDeriv_inner_self_le hx j hj

/-- This numerical constant is defined without a dimension or a radius. -/
noncomputable def radialDerivativeConstant (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (i.factorial * radialJetBound n * 8 ^ i) * 2

theorem radialDerivativeConstant_pos (n : ℕ) : 0 < radialDerivativeConstant n := by
  have hC := (radialJetBound_pos n).le
  unfold radialDerivativeConstant
  positivity

theorem unitRadialSquash_derivative_bound (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (unitRadialSquash : E → E) x‖ ≤ radialDerivativeConstant n := by
  by_cases hx : ‖x‖ ≤ 2
  · have hs : ContDiff ℝ n (fun y : E => radialCutoff (inner (𝕜 := ℝ) y y)) :=
      (radialCutoff_contDiff n).comp (contDiff_id.inner ℝ contDiff_id)
    have h := norm_iteratedFDeriv_smul_le hs (show ContDiff ℝ n (id : E → E) from contDiff_id) x le_rfl
    apply h.trans
    apply le_trans (Finset.sum_le_sum ?_)
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
    intro i hi
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (radialCutoff_inner_derivative_bound n i
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hx) (Nat.cast_nonneg _))
      (norm_iteratedFDeriv_id_le_two (n - i) hx) (norm_nonneg _)
      (by have hC := (radialJetBound_pos n).le; positivity)
  · rw [iteratedFDeriv_eq_of_eventuallyEq (unitRadialSquash_eventually_zero (lt_of_not_ge hx)) n,
      iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact (radialDerivativeConstant_pos n).le

/-- The exact radius scaling required by the source. The same numerical
constant works for every radius and every real inner product space. -/
theorem radialSquash_derivative_bound (n : ℕ) {B : ℝ} (hB : 0 < B) (x : E) :
    ‖iteratedFDeriv ℝ n (radialSquash B : E → E) x‖ ≤
      radialDerivativeConstant n * B ^ (1 - (n : ℤ)) := by
  let A : E →L[ℝ] E := B⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ B⁻¹ := by
    dsimp only [A]
    rw [norm_smul B⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hB.le) ContinuousLinearMap.norm_id_le
  change ‖iteratedFDeriv ℝ n (B • ((unitRadialSquash : E → E) ∘ A)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply
      (((unitRadialSquash_contDiff n).comp A.contDiff).contDiffAt),
    norm_smul B (iteratedFDeriv ℝ n ((unitRadialSquash : E → E) ∘ A) x),
    Real.norm_eq_abs, abs_of_pos hB,
    A.iteratedFDeriv_comp_right (unitRadialSquash_contDiff n) x le_rfl]
  calc
    _ ≤ B * (‖iteratedFDeriv ℝ n (unitRadialSquash : E → E) (A x)‖ * ‖A‖ ^ n) := by
      apply mul_le_mul_of_nonneg_left _ hB.le
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (unitRadialSquash : E → E) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ B * (radialDerivativeConstant n * (B⁻¹) ^ n) := by
      apply mul_le_mul_of_nonneg_left _ hB.le
      exact mul_le_mul (unitRadialSquash_derivative_bound n (A x))
        (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity)
        (radialDerivativeConstant_pos n).le
    _ = radialDerivativeConstant n * B ^ (1 - (n : ℤ)) := by
      rw [zpow_sub₀ hB.ne', zpow_one, zpow_natCast, div_eq_mul_inv, ← inv_pow]
      ring

end RandomizedFO2003.Primitives
