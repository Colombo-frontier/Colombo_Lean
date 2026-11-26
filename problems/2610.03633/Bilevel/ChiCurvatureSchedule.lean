import Bilevel.ChiIndependentWidths
import Bilevel.ZeroChainSchedule

/-! The actual nonuniform curvature recurrence from rec:eq:depth.
This is arithmetic for the prescribed levels; hard-instance realization
and extension budgets are separate. -/
noncomputable section
namespace Bilevel.ChiCurvatureSchedule

def curvature (T : ℝ) (j : ℕ) : ℝ := T^(1-1/(4:ℝ)^j)

theorem curvature_zero (T : ℝ) : curvature T 0=1 := by simp [curvature]

theorem curvature_pos {T : ℝ} (hT : 0<T) (j : ℕ) : 0<curvature T j :=
  Real.rpow_pos_of_pos hT _

theorem curvature_bounds {T : ℝ} (hT : 1 ≤ T) (j : ℕ) :
    1 ≤ curvature T j ∧ curvature T j ≤ T := by
  have hp : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
  have he0 : 0 ≤ 1-1/(4:ℝ)^j := by
    have hh := (div_le_one (by positivity : (0:ℝ)<4^j)).mpr hp
    linarith
  have he1 : 1-1/(4:ℝ)^j ≤ 1 := by
    linarith [one_div_nonneg.mpr (pow_nonneg (by norm_num : (0:ℝ) ≤ 4) j)]
  exact ⟨Real.one_le_rpow hT he0,
    by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT he1⟩

theorem quartic_recurrence {T : ℝ} (hT : 0<T) (j : ℕ) :
    curvature T (j+1)^4=T^3*curvature T j := by
  unfold curvature
  calc
    _ = T^((1-1/(4:ℝ)^(j+1))*4) :=
      ((Real.rpow_mul hT.le _ (4:ℝ)).trans (Real.rpow_natCast _ 4)).symm
    _ = T^(3+(1-1/(4:ℝ)^j)) := by
      congr 1
      rw [pow_succ]
      field_simp
      ring
    _ = _ := (Real.rpow_add hT _ _).trans
      (congrArg (fun a => a*T^(1-1/(4:ℝ)^j)) (Real.rpow_natCast T 3))

theorem curvature_ratio_identity {T : ℝ} (hT : 0<T) (j : ℕ) :
    curvature T (j+1)*(curvature T (j+1)/curvature T j)^(1/3:ℝ)=T := by
  unfold curvature
  rw [← Real.rpow_sub hT,← Real.rpow_mul hT.le,← Real.rpow_add hT]
  have he : (1-1/(4:ℝ)^(j+1))+
      ((1-1/(4:ℝ)^(j+1))-(1-1/(4:ℝ)^j))*(1/3)=1 := by
    rw [pow_succ]
    field_simp
    ring
  rw [he,Real.rpow_one]

theorem curvature_ratio_ge_one {T : ℝ} (hT : 1 ≤ T) (j : ℕ) :
    1 ≤ curvature T (j+1)/curvature T j := by
  have hTp : 0<T := by linarith
  apply (one_le_div (curvature_pos hTp j)).mpr
  apply Real.rpow_le_rpow_of_exponent_le hT
  have hp : (4:ℝ)^j ≤ 4^(j+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ)<4^j) hp
  linarith

theorem chosenDepth_upper {θ : ℝ} (hθ : 1 ≤ θ) :
    Real.log (2+θ)<(4:ℝ)^(ChiIndependentWidths.chosenDepth θ+1) := by
  have harg : 0<2+θ := by linarith
  have hl : 0<Real.log (2+θ) := Real.log_pos (by linarith)
  have h4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hf := Nat.lt_floor_add_one (Real.log (Real.log (2+θ))/Real.log 4)
  have hh : Real.log (Real.log (2+θ))<
      ((ChiIndependentWidths.chosenDepth θ:ℝ)+1)*Real.log 4 := (div_lt_iff₀ h4).mp hf
  have he := Real.exp_lt_exp.mpr hh
  rw [Real.exp_log hl] at he
  have hid : ((ChiIndependentWidths.chosenDepth θ:ℝ)+1)*Real.log 4=
      ((ChiIndependentWidths.chosenDepth θ+1:ℕ):ℝ)*Real.log 4 := by push_cast;ring
  rw [hid,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)] at he
  exact he

theorem curvature_exp_formula {T : ℝ} (hT : 0<T) (j : ℕ) :
    curvature T j=T*Real.exp (-Real.log T/(4:ℝ)^j) := by
  rw [curvature,Real.rpow_def_of_pos hT]
  have he : Real.log T*(1-1/(4:ℝ)^j)=Real.log T+(-Real.log T/(4:ℝ)^j) := by ring
  rw [he,Real.exp_add,Real.exp_log hT]

theorem final_curvature_lower {T θ : ℝ} (hT : 1 ≤ T) (hθ : 1 ≤ θ) (hupper : T ≤ 2+θ) :
    Real.exp (-4)*T ≤ curvature T (ChiIndependentWidths.chosenDepth θ) := by
  have hTp : 0<T := by linarith
  have hlog := Real.log_le_log hTp hupper
  have hh := chosenDepth_upper hθ
  rw [pow_succ] at hh
  have hratio : Real.log T/(4:ℝ)^ChiIndependentWidths.chosenDepth θ ≤ 4 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  rw [curvature_exp_formula hTp]
  have he : Real.exp (-4) ≤ Real.exp (-Real.log T/(4:ℝ)^ChiIndependentWidths.chosenDepth θ) :=
    Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hratio)
  nlinarith [mul_le_mul_of_nonneg_left he hTp.le]

end Bilevel.ChiCurvatureSchedule
