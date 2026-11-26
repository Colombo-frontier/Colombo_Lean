import Bilevel.NearIdentityRestricted

/-! A compactly supported normal direction turns a global Hessian/Lipschitz
budget into a global gradient bound proportional to that normal width. -/
noncomputable section
open scoped Topology
namespace Bilevel.CompactNormal
open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_zero_outside (f : E → ℝ) (q : E →L[ℝ] ℝ) (W : ℝ)
    (hzero : ∀ z,W≤|q z| → f z=0) (z : E) (hz : W < |q z|) : gradient f z=0 := by
  have he : f=ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_const q.continuous.abs).mem_nhds hz] with y hy
    exact hzero y hy.le
  have hh : HasGradientAt f 0 z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_zero] using (hasFDerivAt_const (0:ℝ) z).congr_of_eventuallyEq he
  exact hh.gradient

theorem gradient_norm_le (f : E → ℝ) (q : E →L[ℝ] ℝ) (e : E) (W : ℝ) (hW : 0<W)
    (hqe : q e=1) (he : ‖e‖≤1) (hzero : ∀ z,W≤|q z| → f z=0)
    (δ : NNReal) (hLip : LipschitzWith δ (gradient f)) (z : E) :
    ‖gradient f z‖≤3*(δ:ℝ)*W := by
  by_cases hz : W < |q z|
  · rw [gradient_zero_outside f q W hzero z hz,norm_zero]
    positivity
  · have hz' : |q z|≤W := le_of_not_gt hz
    let y := z+(2*W-q z) • e
    have hqy : q y=2*W := by simp only [y,map_add,map_smul,hqe,smul_eq_mul,mul_one];ring
    have hgy : gradient f y=0 := gradient_zero_outside f q W hzero y
      (by rw [hqy,abs_of_pos (by positivity)];linarith)
    have hdist : ‖z-y‖≤3*W := by
      have heq : z-y=-(2*W-q z) • e := by dsimp [y];module
      rw [heq,norm_smul,Real.norm_eq_abs,abs_neg]
      apply (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans
      rw [mul_one]
      have ha := abs_add_le (2*W) (-(q z))
      rw [abs_of_pos (by positivity : 0<2*W),abs_neg] at ha
      rw [← sub_eq_add_neg] at ha
      linarith
    have hl := hLip.dist_le_mul z y
    simp only [dist_eq_norm,hgy,sub_zero] at hl
    exact hl.trans ((mul_le_mul_of_nonneg_left hdist δ.coe_nonneg).trans_eq (by ring))

end Bilevel.CompactNormal
