import Problem254
import Audit254
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Paper254

/-- Reducing the exp-concavity coefficient is proved from concavity of
nonnegative real powers, rather than assumed as an external interface. -/
theorem ExpConcaveOn.mono {d : ℕ} {W : Set (Space d)} {f : Loss d}
    {η ν : ℝ} (hf : ExpConcaveOn η W f) (hη : 0 < η)
    (hν : 0 ≤ ν) (hle : ν ≤ η) : ExpConcaveOn ν W f := by
  have hp0 : 0 ≤ ν / η := div_nonneg hν hη.le
  have hp1 : ν / η ≤ 1 := (div_le_one hη).mpr hle
  have he : ∀ z, Real.exp (-ν * f z) = Real.exp (-η * f z) ^ (ν / η) := by
    intro z
    rw [← Real.exp_mul]
    congr 1
    field_simp
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [he x, he y, he (a • x + b • y)]
  have hpow := (Real.concaveOn_rpow hp0 hp1).2
    (show Real.exp (-η * f x) ∈ Ici 0 from (Real.exp_pos _).le)
    (show Real.exp (-η * f y) ∈ Ici 0 from (Real.exp_pos _).le) ha hb hab
  have hbase := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hpow hbase
  exact le_trans hpow (Real.rpow_le_rpow (by positivity) hbase hp0)

/-- A supporting-hyperplane inequality, including boundary points and
lower-dimensional decision sets, obtained by restricting to a line segment. -/
theorem concave_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} {f : E → ℝ} {df : E →L[ℝ] ℝ} {w v : E}
    (hf : ConcaveOn ℝ W f) (hw : w ∈ W) (hv : v ∈ W)
    (hd : HasFDerivWithinAt f df W w) : f v ≤ f w + df (v-w) := by
  have hm := hf.1.mapsTo_lineMap hw hv
  have hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (f ∘ AffineMap.lineMap w v) :=
    (hf.comp_affineMap (AffineMap.lineMap w v)).subset hm (convex_Icc _ _)
  have hl : HasDerivWithinAt (f ∘ AffineMap.lineMap w v) (df (v-w))
      (Icc (0 : ℝ) 1) 0 :=
    hd.comp_hasDerivWithinAt_of_eq 0 AffineMap.hasDerivWithinAt_lineMap hm (by simp)
  have hs := hc.slope_le_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (by norm_num : (0 : ℝ) < 1) hl
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hs
  linarith

def logRemainder (x : ℝ) : ℝ := -Real.log (1-x) - x - x^2/4

theorem logRemainder_derivative (x : ℝ) (hx : x < 1) :
    HasDerivAt logRemainder (x*(1+x)/(2*(1-x))) x := by
  have hn : 1-x ≠ 0 := by linarith
  have hd := (((hasDerivAt_id x).const_sub 1).log hn).neg
  have hh := (hd.sub (hasDerivAt_id x)).sub (((hasDerivAt_id x).pow 2).div_const 4)
  convert hh using 1
  dsimp [logRemainder]
  field_simp
  ring

theorem quadratic_log_lower (x : ℝ) (hx : |x| ≤ 1/2) :
    x + x^2/4 ≤ -Real.log (1-x) := by
  have hb := abs_le.mp hx
  have hc : ContinuousOn logRemainder (Icc (-1/2) (1/2)) := by
    intro z hz
    exact (logRemainder_derivative z (by have := hz.2; linarith)).continuousAt.continuousWithinAt
  have hzero : logRemainder 0 = 0 := by simp [logRemainder]
  by_cases hpos : 0 ≤ x
  · have hm : MonotoneOn logRemainder (Icc 0 (1/2)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (hc.mono (by intro z hz; exact ⟨by linarith [hz.1], hz.2⟩))
        (f' := fun z => z*(1+z)/(2*(1-z)))
      · intro z hz
        have hz' : z ∈ Icc (0 : ℝ) (1/2) := interior_subset hz
        exact (logRemainder_derivative z (by linarith [hz'.2])).hasDerivWithinAt
      · intro z hz
        have hz' : z ∈ Icc (0 : ℝ) (1/2) := interior_subset hz
        exact div_nonneg (mul_nonneg hz'.1 (by linarith [hz'.1])) (by linarith [hz'.2])
    have hh := hm (show (0 : ℝ) ∈ Icc 0 (1/2) by constructor <;> norm_num)
      ⟨hpos, hb.2⟩ hpos
    rw [hzero] at hh
    dsimp [logRemainder] at hh
    linarith
  · have hm : AntitoneOn logRemainder (Icc (-1/2) 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (hc.mono (by intro z hz; exact ⟨hz.1, by linarith [hz.2]⟩))
        (f' := fun z => z*(1+z)/(2*(1-z)))
      · intro z hz
        have hz' : z ∈ Icc (-1/2 : ℝ) 0 := interior_subset hz
        exact (logRemainder_derivative z (by linarith [hz'.2])).hasDerivWithinAt
      · intro z hz
        have hz' : z ∈ Icc (-1/2 : ℝ) 0 := interior_subset hz
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hz'.2 (by linarith [hz'.1])) (by linarith [hz'.2])
    have hh := hm (show x ∈ Icc (-1/2) 0 from ⟨by linarith [hb.1], le_of_not_ge hpos⟩)
      (show (0 : ℝ) ∈ Icc (-1/2) 0 by constructor <;> norm_num) (le_of_not_ge hpos)
    rw [hzero] at hh
    dsimp [logRemainder] at hh
    linarith

end Paper254
#print axioms Paper254.ExpConcaveOn.mono
#print axioms Paper254.concave_support
#print axioms Paper254.quadratic_log_lower
