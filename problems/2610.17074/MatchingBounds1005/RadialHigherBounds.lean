import MatchingBounds1005.Radial
import MatchingBounds1005.Primitive
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.Nat.Choose.Sum

/-! Dimension-free higher derivative bounds. The proof uses a globally smooth
extension of normalization and later lifts x to (x,1). The on-ball derivative
estimates adapt the independently checked method in the local
GradientHessian/RadialHigherDerivatives.lean, but apply at every finite order. -/
namespace MatchingBounds1005.RadialHigher

open Set Filter
open scoped ContDiff Topology BigOperators InnerProductSpace

noncomputable def coefficient (t : ℝ) : ℝ :=
  1 - Real.smoothTransition (4 * t - 1) + Real.smoothTransition (4 * t - 1) / Real.sqrt t

theorem coefficient_core {t : ℝ} (ht : t ≤ 1 / 4) : coefficient t = 1 := by
  have h := Real.smoothTransition.zero_of_nonpos (show 4 * t - 1 ≤ 0 by linarith)
  simp [coefficient, h]

theorem coefficient_tail {t : ℝ} (ht : 1 / 2 ≤ t) : coefficient t = 1 / Real.sqrt t := by
  have h := Real.smoothTransition.one_of_one_le (show 1 ≤ 4 * t - 1 by linarith)
  simp [coefficient, h]

theorem coefficient_smooth : ContDiff ℝ ∞ coefficient := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < 1 / 4
  · apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with y hy
    exact coefficient_core hy.le
  · have htpos : 0 < t := by linarith
    have hs : ContDiffAt ℝ ∞ (fun y : ℝ => Real.smoothTransition (4 * y - 1)) t :=
      Real.smoothTransition.contDiffAt.comp t
        ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)
    exact (contDiffAt_const.sub hs).add
      (hs.div (Real.contDiffAt_sqrt htpos.ne') (Real.sqrt_pos.mpr htpos).ne')

theorem coefficient_jet_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ t ∈ Icc (0 : ℝ) 16,
      |iteratedDeriv i coefficient t| ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (coefficient_smooth.continuous.continuousOn : ContinuousOn coefficient (Icc (0 : ℝ) 16))
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi t ht
    have hi0 : i = 0 := by omega
    simpa only [hi0, iteratedDeriv_zero, Real.norm_eq_abs] using (hC t ht).trans (le_max_right _ _)
  | succ n ih =>
    obtain ⟨C, hC, hb⟩ := ih
    have hlevel : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
      by exact_mod_cast (show (n + 1 : ℕ∞) ≤ ⊤ from le_top)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((coefficient_smooth.continuous_iteratedDeriv (n + 1) hlevel).continuousOn :
        ContinuousOn (iteratedDeriv (n + 1) coefficient) (Icc (0 : ℝ) 16))
    refine ⟨max C M, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro i hi t ht
    by_cases hin : i ≤ n
    · exact (hb i hin t ht).trans (le_max_left _ _)
    · have heq : i = n + 1 := by omega
      subst i
      exact (hM t ht).trans (le_max_right _ _)

noncomputable def jetBound (n : ℕ) : ℝ := (coefficient_jet_bound n).choose
theorem jetBound_pos (n : ℕ) : 0 < jetBound n := (coefficient_jet_bound n).choose_spec.1
theorem jetBound_spec (n i : ℕ) (hi : i ≤ n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 16) :
    ‖iteratedFDeriv ℝ i coefficient t‖ ≤ jetBound n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (coefficient_jet_bound n).choose_spec.2 i hi t ht

noncomputable def normalizationConstant (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (i.factorial * jetBound n * 32 ^ i) * 4

theorem normalizationConstant_pos (n : ℕ) : 0 < normalizationConstant n := by
  have hC := jetBound_pos n
  unfold normalizationConstant
  positivity

section Space
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalization (x : E) : E := coefficient ⟪x, x⟫_ℝ • x

theorem normalization_smooth : ContDiff ℝ ∞ (normalization : E → E) :=
  (coefficient_smooth.comp (contDiff_id.inner ℝ contDiff_id)).smul contDiff_id

theorem id_derivative_bound (i : ℕ) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ i (id : E → E) x‖ ≤ 4 := by
  cases i with
  | zero => simpa only [norm_iteratedFDeriv_zero, id_eq] using hx
  | succ i =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext (fun _ => fderiv_id)
    rw [hd]
    cases i with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact ContinuousLinearMap.norm_id_le.trans (by norm_num)
    | succ i =>
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      norm_num

theorem square_derivative_bound {x : E} (hx : ‖x‖ ≤ 4) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y : E => ⟪y, y⟫_ℝ) x‖ ≤ (32 : ℝ) ^ i := by
  have h := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (show ContDiff ℝ i (id : E → E) from contDiff_id) contDiff_id x le_rfl (norm_innerSL_le ℝ)
  have hsum : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
    exact_mod_cast Nat.sum_range_choose i
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (id : E → E) x‖ * ‖iteratedFDeriv ℝ (i-j) (id : E → E) x‖ := h
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * 4 * 4 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (id_derivative_bound j hx) (Nat.cast_nonneg _))
        (id_derivative_bound (i-j) hx) (norm_nonneg _) (by positivity)
    _ = 16 * 2 ^ i := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring
    _ ≤ 16 ^ i * 2 ^ i := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hi
    _ = 32 ^ i := by rw [← mul_pow]; norm_num

theorem coefficient_inner_derivative_bound (n i : ℕ) (hi : i ≤ n) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ i (fun y : E => coefficient ⟪y, y⟫_ℝ) x‖ ≤
      i.factorial * jetBound n * 32 ^ i := by
  have hlevel : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  apply norm_iteratedFDeriv_comp_le (coefficient_smooth.of_le hlevel)
    (show ContDiff ℝ n (fun y : E => ⟪y, y⟫_ℝ) from contDiff_id.inner ℝ contDiff_id)
    (by exact_mod_cast hi) x
  · intro j hj
    apply jetBound_spec n j (hj.trans hi)
    rw [real_inner_self_eq_norm_sq]
    exact ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
  · intro j hj _
    exact square_derivative_bound hx j hj

theorem normalization_bound_on_ball (n : ℕ) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ n (normalization : E → E) x‖ ≤ normalizationConstant n := by
  have hs : ContDiff ℝ ∞ (fun y : E => coefficient ⟪y, y⟫_ℝ) :=
    coefficient_smooth.comp (contDiff_id.inner ℝ contDiff_id)
  have hlevel : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  have h := norm_iteratedFDeriv_smul_le hs (show ContDiff ℝ ∞ (id : E → E) from contDiff_id)
    x hlevel
  apply h.trans
  apply le_trans (Finset.sum_le_sum ?_) (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  intro i hi
  exact mul_le_mul (mul_le_mul_of_nonneg_left (coefficient_inner_derivative_bound n i
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hx) (Nat.cast_nonneg _))
    (id_derivative_bound (n-i) hx) (norm_nonneg _) (by have hC := jetBound_pos n; positivity)

theorem normalization_tail {x : E} (hx : (3 / 4 : ℝ) ≤ ‖x‖) :
    normalization x = ‖x‖⁻¹ • x := by
  unfold normalization
  rw [real_inner_self_eq_norm_sq, coefficient_tail (by nlinarith),
    Real.sqrt_sq (norm_nonneg x), one_div]

theorem normalization_tail_smul {a : ℝ} (ha : 0 < a) {x : E}
    (hx : (3 / 4 : ℝ) ≤ ‖x‖) (hax : (3 / 4 : ℝ) ≤ ‖a • x‖) :
    normalization (a • x) = normalization x := by
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt (by linarith : 0 < ‖x‖)
  rw [normalization_tail hax, normalization_tail hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, smul_smul]
  congr 1
  field_simp

theorem derivative_eq_of_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  have hw : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq h.self_of_nhds n

theorem normalization_derivative_bound (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (normalization : E → E) x‖ ≤ normalizationConstant n := by
  by_cases hx : ‖x‖ ≤ 4
  · exact normalization_bound_on_ball n hx
  have hr : 0 < ‖x‖ := by linarith
  let a : ℝ := ‖x‖⁻¹
  have ha : 0 < a := inv_pos.mpr hr
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith : 1 ≤ ‖x‖)
  let A : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ 1 := by
    calc
      ‖A‖ = a * ‖ContinuousLinearMap.id ℝ E‖ := by
        rw [show A = a • ContinuousLinearMap.id ℝ E from rfl,
          norm_smul a (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a := mul_le_of_le_one_right ha.le ContinuousLinearMap.norm_id_le
      _ ≤ 1 := ha1
  have hAx : ‖A x‖ = 1 := by
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact inv_mul_cancel₀ hr.ne'
  have heq : (normalization : E → E) =ᶠ[𝓝 x] (normalization ∘ A) := by
    have hy : ∀ᶠ y : E in 𝓝 x, (3 / 4 : ℝ) < ‖y‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith))
    have hAy : ∀ᶠ y : E in 𝓝 x, (3 / 4 : ℝ) < ‖A y‖ :=
      (continuous_norm.comp A.continuous).continuousAt.eventually
        (lt_mem_nhds (by change (3 / 4 : ℝ) < ‖A x‖; rw [hAx]; norm_num))
    filter_upwards [hy, hAy] with y hy hAy
    exact (normalization_tail_smul ha hy.le hAy.le).symm
  have hlevel : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  rw [derivative_eq_of_eventuallyEq heq n,
    A.iteratedFDeriv_comp_right normalization_smooth x hlevel]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (normalization : E → E) (A x)‖ * ‖A‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (normalization : E → E) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ normalizationConstant n * 1 := mul_le_mul
      (normalization_bound_on_ball n (by rw [hAx]; norm_num))
      (pow_le_one₀ (norm_nonneg A) hA) (by positivity) (normalizationConstant_pos n).le
    _ = _ := mul_one _

abbrev LiftSpace := WithLp 2 (E × ℝ)

noncomputable def liftEmbedding : E →L[ℝ] LiftSpace (E := E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E ℝ)

noncomputable def liftProjection : LiftSpace (E := E) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E ℝ).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap

noncomputable def liftOffset : LiftSpace (E := E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm (0, 1)

@[simp] theorem liftEmbedding_fst (x : E) : (liftEmbedding x).fst = x := rfl
@[simp] theorem liftEmbedding_snd (x : E) : (liftEmbedding x).snd = 0 := rfl
@[simp] theorem liftOffset_fst : (liftOffset (E := E)).fst = 0 := rfl
@[simp] theorem liftOffset_snd : (liftOffset (E := E)).snd = 1 := rfl
@[simp] theorem liftProjection_apply (y : LiftSpace (E := E)) : liftProjection y = y.fst := rfl

theorem liftEmbedding_norm (x : E) : ‖liftEmbedding x‖ = ‖x‖ :=
  WithLp.norm_equiv_symm_fst 2 E ℝ x

theorem liftEmbedding_norm_le_one : ‖liftEmbedding (E := E)‖ ≤ 1 := by
  apply (liftEmbedding (E := E)).opNorm_le_bound (by norm_num)
  intro x
  simp only [liftEmbedding_norm, one_mul, le_refl]

theorem liftProjection_norm_le_one : ‖liftProjection (E := E)‖ ≤ 1 := by
  apply (liftProjection (E := E)).opNorm_le_bound (by norm_num)
  intro y
  simpa only [liftProjection_apply, one_mul] using WithLp.norm_fst_le E y

theorem lift_norm_sq (x : E) : ‖liftEmbedding x + liftOffset‖ ^ 2 = ‖x‖ ^ 2 + 1 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.add_fst, WithLp.add_snd,
    liftEmbedding_fst, liftEmbedding_snd, liftOffset_fst, liftOffset_snd]
  simp

theorem lift_norm (x : E) : ‖liftEmbedding x + liftOffset‖ = Real.sqrt (1 + ‖x‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (liftEmbedding x + liftOffset)), lift_norm_sq, add_comm]

theorem radial_one_lift (x : E) :
    radial 1 x = liftProjection (normalization (liftEmbedding x + liftOffset)) := by
  have hs := lift_norm_sq x
  have hn : (3 / 4 : ℝ) ≤ ‖liftEmbedding x + liftOffset‖ := by
    nlinarith [sq_nonneg ‖x‖, norm_nonneg (liftEmbedding x + liftOffset)]
  rw [normalization_tail hn, map_smul, liftProjection_apply, WithLp.add_fst,
    liftEmbedding_fst, liftOffset_fst, add_zero, lift_norm]
  simp [radial, radialScale]

/-- All derivative orders for the actual rational radial map, with constants
independent of its real inner-product space. -/
theorem radial_one_derivative_bound (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (radial 1 : E → E) x‖ ≤ normalizationConstant n := by
  let e : LiftSpace (E := E) := liftOffset
  let H : LiftSpace (E := E) → LiftSpace (E := E) := fun y => normalization (y + e)
  have hH : ContDiff ℝ ∞ H := normalization_smooth.comp (contDiff_id.add contDiff_const)
  have hcomp : ContDiff ℝ ∞ (H ∘ liftEmbedding (E := E)) :=
    hH.comp (liftEmbedding (E := E)).contDiff
  have hlevel : (n : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)
  have heq : (radial 1 : E → E) = liftProjection ∘ (H ∘ liftEmbedding) :=
    funext radial_one_lift
  rw [heq, liftProjection.iteratedFDeriv_comp_left hcomp.contDiffAt hlevel]
  calc
    _ ≤ ‖liftProjection (E := E)‖ * ‖iteratedFDeriv ℝ n (H ∘ liftEmbedding) x‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (H ∘ liftEmbedding) x‖ := by
      gcongr
      exact liftProjection_norm_le_one
    _ = ‖iteratedFDeriv ℝ n (H ∘ liftEmbedding) x‖ := one_mul _
    _ ≤ normalizationConstant n := by
      rw [liftEmbedding.iteratedFDeriv_comp_right hH x hlevel]
      calc
        _ ≤ ‖iteratedFDeriv ℝ n H (liftEmbedding x)‖ * ‖liftEmbedding (E := E)‖ ^ n := by
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (iteratedFDeriv ℝ n H (liftEmbedding x)).norm_compContinuousLinearMap_le
              (fun _ => liftEmbedding)
        _ ≤ normalizationConstant n * 1 := by
          apply mul_le_mul _
            (pow_le_one₀ (norm_nonneg (liftEmbedding (E := E)))
              (liftEmbedding_norm_le_one (E := E)) (n := n)) (by positivity)
            (normalizationConstant_pos n).le
          change ‖iteratedFDeriv ℝ n (fun y => normalization (y + e)) (liftEmbedding x)‖ ≤ _
          rw [iteratedFDeriv_comp_add_right]
          exact normalization_derivative_bound n _
        _ = _ := mul_one _

theorem radial_radius_scaling {R : ℝ} (hR : 0 < R) (x : E) :
    radial R x = R • radial 1 (R⁻¹ • x) := by
  have hs : 1 + ‖R⁻¹ • x‖ ^ 2 / (1 : ℝ) ^ 2 = 1 + ‖x‖ ^ 2 / R ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    simp only [one_pow, div_one, mul_pow, inv_pow, div_eq_mul_inv]
    ring
  simp only [radial, radialScale, hs, smul_smul]
  congr 1
  field_simp
  ring

/-- Every finite derivative order of the manuscript's actual radial map, with
constants depending only on the order, not the ambient dimension. -/
theorem radial_derivative_bound (n : ℕ) {R : ℝ} (hR : 0 < R) (x : E) :
    ‖iteratedFDeriv ℝ n (radial R : E → E) x‖ ≤
      normalizationConstant n * R ^ (1 - (n : ℤ)) := by
  let A : E →L[ℝ] E := R⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ R⁻¹ := by
    dsimp only [A]
    rw [norm_smul R⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hR.le) ContinuousLinearMap.norm_id_le
  have heq : (radial R : E → E) = R • ((radial 1 : E → E) ∘ A) :=
    funext (radial_radius_scaling hR)
  have hu : ContDiff ℝ n (radial 1 : E → E) :=
    radial_contDiff 1 n
  rw [heq, iteratedFDeriv_const_smul_apply ((hu.comp A.contDiff).contDiffAt),
    norm_smul R (iteratedFDeriv ℝ n ((radial 1 : E → E) ∘ A) x),
    Real.norm_eq_abs, abs_of_pos hR, A.iteratedFDeriv_comp_right hu x le_rfl]
  calc
    _ ≤ R * (‖iteratedFDeriv ℝ n (radial 1 : E → E) (A x)‖ * ‖A‖ ^ n) := by
      apply mul_le_mul_of_nonneg_left _ hR.le
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (radial 1 : E → E) (A x)).norm_compContinuousLinearMap_le
          (fun _ => A)
    _ ≤ R * (normalizationConstant n * (R⁻¹) ^ n) := by
      apply mul_le_mul_of_nonneg_left _ hR.le
      exact mul_le_mul (radial_one_derivative_bound n (A x))
        (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity)
        (normalizationConstant_pos n).le
    _ = normalizationConstant n * R ^ (1 - (n : ℤ)) := by
      rw [zpow_sub₀ hR.ne', zpow_one, zpow_natCast, div_eq_mul_inv, ← inv_pow]
      ring

end Space
end MatchingBounds1005.RadialHigher
