import SecondOrder.FirstOrderEncoding
import SecondOrder.ScalarJetAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SecondOrder
noncomputable section

def tanhFirst (x : ℝ) : ℝ := 1-(Real.tanh x)^2
def tanhSecond (x : ℝ) : ℝ := -2*Real.tanh x*tanhFirst x
def tanhThird (x : ℝ) : ℝ := -2*(tanhFirst x)^2+4*(Real.tanh x)^2*tanhFirst x
def logCosh (x : ℝ) : ℝ := Real.log (Real.cosh x)

theorem tanh_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n Real.tanh := by
  rw [show Real.tanh=(fun x => Real.sinh x/Real.cosh x) from funext Real.tanh_eq_sinh_div_cosh]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

theorem tanh_hasDerivAt (x : ℝ) : HasDerivAt Real.tanh (tanhFirst x) x := by
  have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  convert hh using 1
  · funext y; exact Real.tanh_eq_sinh_div_cosh y
  · unfold tanhFirst
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem tanhFirst_hasDerivAt (x : ℝ) : HasDerivAt tanhFirst (tanhSecond x) x := by
  convert (hasDerivAt_const x (1:ℝ)).sub ((tanh_hasDerivAt x).pow 2) using 1
  unfold tanhSecond
  ring

theorem tanhSecond_hasDerivAt (x : ℝ) : HasDerivAt tanhSecond (tanhThird x) x := by
  convert ((tanh_hasDerivAt x).const_mul (-2)).mul (tanhFirst_hasDerivAt x) using 1
  unfold tanhSecond tanhThird
  ring

theorem tanhFirst_mem (x : ℝ) : 0≤tanhFirst x ∧ tanhFirst x≤1 := by
  have hh := tanh_abs_le_one x
  have hs : (Real.tanh x)^2≤1 := by nlinarith [sq_abs (Real.tanh x),abs_nonneg (Real.tanh x)]
  unfold tanhFirst
  constructor <;> nlinarith [sq_nonneg (Real.tanh x)]

theorem tanhSecond_abs_le (x : ℝ) : |tanhSecond x|≤2 := by
  have ht := tanh_abs_le_one x
  have hs := tanhFirst_mem x
  unfold tanhSecond
  rw [abs_mul,abs_mul,abs_of_nonneg hs.1]
  norm_num
  nlinarith [mul_le_mul ht hs.2 hs.1 (by norm_num : (0:ℝ)≤1)]

theorem tanhThird_abs_le (x : ℝ) : |tanhThird x|≤6 := by
  have ht := tanh_abs_le_one x
  have hs := tanhFirst_mem x
  have ht2 : (Real.tanh x)^2≤1 := by nlinarith [sq_abs (Real.tanh x),abs_nonneg (Real.tanh x)]
  have hs2 : (tanhFirst x)^2≤1 := by nlinarith
  have hm := mul_le_mul ht2 hs.2 hs.1 (by norm_num : (0:ℝ)≤1)
  unfold tanhThird
  apply (abs_add _ _).trans
  simp only [abs_mul,abs_pow,sq_abs,abs_of_nonneg hs.1]
  norm_num
  nlinarith only [hs2,hm]

theorem tanhFirst_difference (s t : ℝ) : |tanhFirst t-tanhFirst s|≤2*|t-s| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := (2:ℝ))
      (fun x (_ : x ∈ Set.univ) => (tanhFirst_hasDerivAt x).hasDerivWithinAt)
      (fun x _ => by simpa only [Real.norm_eq_abs] using tanhSecond_abs_le x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ s) (Set.mem_univ t)

theorem tanhSecond_difference (s t : ℝ) : |tanhSecond t-tanhSecond s|≤6*|t-s| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := (6:ℝ))
      (fun x (_ : x ∈ Set.univ) => (tanhSecond_hasDerivAt x).hasDerivWithinAt)
      (fun x _ => by simpa only [Real.norm_eq_abs] using tanhThird_abs_le x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ s) (Set.mem_univ t)

theorem logCosh_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n logCosh :=
  Real.contDiff_cosh.log (fun x => (Real.cosh_pos x).ne')

theorem logCosh_hasDerivAt (x : ℝ) : HasDerivAt logCosh (Real.tanh x) x := by
  simpa only [logCosh,Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'

theorem logCosh_nonneg (x : ℝ) : 0≤logCosh x := Real.log_nonneg (Real.one_le_cosh x)

@[simp] theorem logCosh_zero : logCosh 0=0 := by simp [logCosh]

end
end SecondOrder
