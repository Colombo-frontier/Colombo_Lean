import Bilevel.ChiCurvatureFloors

/-! A uniform numerical threshold for the actual nonuniform schedule.
The depth denominator is bounded by a fixed constant times sqrt(theta),
so the source branch T>=2 follows for all sufficiently large theta. -/
noncomputable section
namespace Bilevel.ChiCurvatureSchedule

def thresholdExponent (CT : ℝ) (p : ℕ) : ℝ :=
  (Real.log 3+(Real.log CT+(p:ℝ))^2)/2+Real.log CT

def threshold (CT : ℝ) (p : ℕ) : ℝ := max 1 (4*Real.exp (2*thresholdExponent CT p))

theorem depth_denominator_bound {θ CT : ℝ} (hθ : 1 ≤ θ) (hC : 1 ≤ CT) (p : ℕ) :
    CT^(ChiIndependentWidths.chosenDepth θ+1)*((ChiIndependentWidths.chosenDepth θ:ℝ)+1)^p ≤
      Real.exp (thresholdExponent CT p)*Real.sqrt θ := by
  let J := ChiIndependentWidths.chosenDepth θ
  have hθp : 0<θ := by linarith
  have hCp : 0<CT := by linarith
  have hJ : 0 ≤ (J:ℝ) := Nat.cast_nonneg _
  have hJ1 : 0<(J:ℝ)+1 := by positivity
  have hlogC : 0 ≤ Real.log CT := Real.log_nonneg hC
  have hlogJ : Real.log ((J:ℝ)+1) ≤ (J:ℝ) := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos hJ1
  have hdepth : (J:ℝ)^2 ≤ Real.log 3+Real.log θ := by
    have hj := (ChiIndependentWidths.depth_sq_le_pow J).trans (ChiIndependentWidths.chosenDepth_bound hθ)
    have hl := Real.log_le_log (show 0<2+θ by linarith) (show 2+θ ≤ 3*θ by linarith)
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hθp.ne'] at hl
    exact hj.trans hl
  let D := CT^(J+1)*((J:ℝ)+1)^p
  have hD : 0<D := by dsimp [D];positivity
  have hlogD : Real.log D ≤ thresholdExponent CT p+Real.log θ/2 := by
    rw [show D=CT^(J+1)*((J:ℝ)+1)^p from rfl,
      Real.log_mul (pow_ne_zero _ hCp.ne') (pow_ne_zero _ hJ1.ne'),Real.log_pow,Real.log_pow]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hlogJ (Nat.cast_nonneg p : (0:ℝ) ≤ p)
    have hs := sq_nonneg ((J:ℝ)-(Real.log CT+(p:ℝ)))
    dsimp [thresholdExponent]
    nlinarith
  have hh := Real.exp_le_exp.mpr hlogD
  rw [Real.exp_log hD,Real.exp_add] at hh
  have he : Real.exp (Real.log θ/2)=Real.sqrt θ := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hθp]
    congr 1
    ring
  rw [he] at hh
  exact hh

theorem scale_sqrt_lower {θ CT : ℝ} (hθ : 1 ≤ θ) (hC : 1 ≤ CT) (p : ℕ) :
    Real.exp (-thresholdExponent CT p)*Real.sqrt θ ≤ scale θ CT p := by
  have hθp : 0<θ := by linarith
  have hCp : 0<CT := by linarith
  have hden := depth_denominator_bound hθ hC p
  have hs : 0<Real.sqrt θ := Real.sqrt_pos.mpr hθp
  have hD : 0<CT^(ChiIndependentWidths.chosenDepth θ+1)*
      ((ChiIndependentWidths.chosenDepth θ:ℝ)+1)^p := by positivity
  have hh := div_le_div_of_nonneg_left hθp.le hD hden
  apply le_trans _ hh
  rw [Real.exp_neg]
  apply le_of_eq
  apply (eq_div_iff (mul_pos (Real.exp_pos _) hs).ne').mpr
  rw [mul_assoc,show Real.sqrt θ*(Real.exp (thresholdExponent CT p)*Real.sqrt θ)=
    Real.exp (thresholdExponent CT p)*(Real.sqrt θ)^2 by ring,Real.sq_sqrt hθp.le]
  field_simp

theorem scale_ge_two_above_threshold {θ CT : ℝ} (hC : 1 ≤ CT) (p : ℕ)
    (hθ : threshold CT p ≤ θ) : 2 ≤ scale θ CT p := by
  have hθ1 : 1 ≤ θ := (le_max_left _ _).trans hθ
  have he : 4*Real.exp (2*thresholdExponent CT p) ≤ θ := (le_max_right _ _).trans hθ
  have hs := scale_sqrt_lower hθ1 hC p
  have hexp : Real.exp (2*thresholdExponent CT p)=(Real.exp (thresholdExponent CT p))^2 := by
    rw [show 2*thresholdExponent CT p=thresholdExponent CT p+thresholdExponent CT p by ring,
      Real.exp_add,pow_two]
  rw [hexp] at he
  have hroot : 2*Real.exp (thresholdExponent CT p) ≤ Real.sqrt θ := by
    have hsq := Real.sq_sqrt (show 0 ≤ θ by linarith)
    nlinarith [Real.sqrt_nonneg θ,Real.exp_pos (thresholdExponent CT p)]
  have hh := mul_le_mul_of_nonneg_left hroot (Real.exp_pos (-thresholdExponent CT p)).le
  have hprod : Real.exp (-thresholdExponent CT p)*(2*Real.exp (thresholdExponent CT p))=2 := by
    rw [Real.exp_neg]
    field_simp
  rw [hprod] at hh
  exact hh.trans hs

end Bilevel.ChiCurvatureSchedule
