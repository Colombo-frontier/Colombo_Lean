import Bilevel.ChiCurvatureSchedule

/-! Actual natural-floor lengths under the nonuniform curvature schedule.
Their weighted cube-root cost is bounded by one common scale T. -/
noncomputable section
namespace Bilevel.ChiCurvatureSchedule

def length (cn η T : ℝ) (j : ℕ) : ℕ :=
  Nat.floor (cn*(curvature T (j+1)/curvature T j)/η^2)

theorem length_upper {cn η T : ℝ} (hcn : 0 ≤ cn) (hT : 0<T) (j : ℕ) :
    (length cn η T j:ℝ) ≤ cn*(curvature T (j+1)/curvature T j)/η^2 :=
  Nat.floor_le (div_nonneg (mul_nonneg hcn
    (div_nonneg (curvature_pos hT _).le (curvature_pos hT _).le)) (sq_nonneg η))

theorem length_large {cn η T : ℝ} (hcn : 0 ≤ cn) (hT : 1 ≤ T)
    (hscale : 128 ≤ cn/η^2) (j : ℕ) : 128 ≤ length cn η T j := by
  have hr := curvature_ratio_ge_one hT j
  have harg : 128 ≤ cn*(curvature T (j+1)/curvature T j)/η^2 := by
    apply hscale.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg η)
    nlinarith [mul_le_mul_of_nonneg_left hr hcn]
  exact (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast harg)

theorem weighted_length_bound {cn η T : ℝ} (hcn : 0 ≤ cn) (hT : 0<T) (j : ℕ) :
    curvature T (j+1)*(length cn η T j:ℝ)^(1/3:ℝ) ≤ (cn/η^2)^(1/3:ℝ)*T := by
  have ha := curvature_pos hT (j+1)
  have hr := div_pos ha (curvature_pos hT j)
  have he : cn*(curvature T (j+1)/curvature T j)/η^2=
      (cn/η^2)*(curvature T (j+1)/curvature T j) := by ring
  have hh := Real.rpow_le_rpow (show (0:ℝ) ≤ (length cn η T j:ℝ) by positivity)
    (length_upper hcn hT j) (by norm_num : (0:ℝ) ≤ 1/3)
  rw [he,Real.mul_rpow (div_nonneg hcn (sq_nonneg η)) hr.le] at hh
  have hm := mul_le_mul_of_nonneg_left hh ha.le
  apply hm.trans_eq
  calc
    _ = (cn/η^2)^(1/3:ℝ)*(curvature T (j+1)*(curvature T (j+1)/curvature T j)^(1/3:ℝ)) := by ring
    _ = _ := by rw [curvature_ratio_identity hT j]

def scale (θ CT : ℝ) (p : ℕ) : ℝ :=
  θ/(CT^(ChiIndependentWidths.chosenDepth θ+1)*((ChiIndependentWidths.chosenDepth θ:ℝ)+1)^p)

theorem scale_pos {θ CT : ℝ} (hθ : 0<θ) (hC : 0<CT) (p : ℕ) : 0<scale θ CT p := by
  unfold scale
  positivity

theorem scale_le_parameter {θ CT : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ CT) (p : ℕ) :
    scale θ CT p ≤ θ := by
  have hCp : 1 ≤ CT^(ChiIndependentWidths.chosenDepth θ+1) := one_le_pow₀ hC
  have hJ : 1 ≤ ((ChiIndependentWidths.chosenDepth θ:ℝ)+1)^p := one_le_pow₀
    (by have := Nat.cast_nonneg (α:=ℝ) (ChiIndependentWidths.chosenDepth θ);linarith)
  have hd : 1 ≤ CT^(ChiIndependentWidths.chosenDepth θ+1)*
      ((ChiIndependentWidths.chosenDepth θ:ℝ)+1)^p := by nlinarith
  exact div_le_self hθ hd

theorem actual_final_curvature {θ CT : ℝ} (hθ : 1 ≤ θ) (hC : 1 ≤ CT)
    (p : ℕ) (hscale : 1 ≤ scale θ CT p) :
    Real.exp (-4)*scale θ CT p ≤ curvature (scale θ CT p) (ChiIndependentWidths.chosenDepth θ) :=
  final_curvature_lower hscale hθ ((scale_le_parameter (by linarith) hC p).trans (by linarith))

end Bilevel.ChiCurvatureSchedule
