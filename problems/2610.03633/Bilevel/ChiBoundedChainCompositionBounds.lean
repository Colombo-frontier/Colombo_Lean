import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Order-sensitive chain-rule bounds. Keeping the first/second/third outer
derivatives separate is essential for radial compression of a long chain. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiBoundedChain.Composition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_first (f : E → F) (x : E) : ‖iteratedFDeriv ℝ 1 f x‖=‖fderiv ℝ f x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]

theorem first_comp_bound {f : E → F} {g : F → G} (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    ‖iteratedFDeriv ℝ 1 (g ∘ f) x‖≤‖iteratedFDeriv ℝ 1 g (f x)‖*‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [norm_first,norm_first,norm_first,fderiv_comp x hg hf]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem second_comp_bound {f : E → F} {g : F → G}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    ‖iteratedFDeriv ℝ 2 (g ∘ f) x‖≤
      ‖iteratedFDeriv ℝ 2 g (f x)‖*‖iteratedFDeriv ℝ 1 f x‖^2+
        ‖iteratedFDeriv ℝ 1 g (f x)‖*‖iteratedFDeriv ℝ 2 f x‖ := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdg : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have he : fderiv ℝ (g ∘ f)=fun y => ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f y)) (fderiv ℝ f y) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by norm_num) _) (hf.differentiable (by norm_num) _)
  have hb := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (hdg.comp (hf.of_le (by norm_num))) hdf x (n:=1) (by norm_num) (ContinuousLinearMap.norm_compL_le ℝ E F G)
  have hF₁ := first_comp_bound (g:=fderiv ℝ g) x (hf.differentiable (by norm_num) _)
    (hdg.differentiable (by norm_num) _)
  rw [norm_iteratedFDeriv_fderiv] at hF₁
  rw [← norm_iteratedFDeriv_fderiv (n:=1),he]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,Nat.choose_self,
    Nat.cast_one,one_mul,zero_add,Nat.sub_zero,Nat.sub_self,norm_iteratedFDeriv_zero,
    Function.comp_apply,norm_iteratedFDeriv_fderiv] at hb
  rw [← norm_first g (f x)] at hb
  norm_num at hb
  exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_right hF₁ (norm_nonneg (iteratedFDeriv ℝ 1 f x))])

theorem third_comp_bound {f : E → F} {g : F → G}
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : E) :
    ‖iteratedFDeriv ℝ 3 (g ∘ f) x‖≤
      ‖iteratedFDeriv ℝ 3 g (f x)‖*‖iteratedFDeriv ℝ 1 f x‖^3+
        3*‖iteratedFDeriv ℝ 2 g (f x)‖*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 f x‖+
        ‖iteratedFDeriv ℝ 1 g (f x)‖*‖iteratedFDeriv ℝ 3 f x‖ := by
  have hdf : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdg : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have he : fderiv ℝ (g ∘ f)=fun y => ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f y)) (fderiv ℝ f y) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by norm_num) _) (hf.differentiable (by norm_num) _)
  have hb := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (hdg.comp (hf.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega)))) hdf x (n:=2) (by norm_num) (ContinuousLinearMap.norm_compL_le ℝ E F G)
  have hF₁ := first_comp_bound (g:=fderiv ℝ g) x (hf.differentiable (by norm_num) _)
    (hdg.differentiable (by norm_num) _)
  have hF₂ := second_comp_bound (hf.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega))) hdg x
  rw [norm_iteratedFDeriv_fderiv] at hF₁
  simp only [norm_iteratedFDeriv_fderiv] at hF₂
  rw [← norm_iteratedFDeriv_fderiv (n:=2),he]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,Nat.choose_self,
    Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add,Nat.sub_zero,Nat.sub_self,Nat.reduceSub,
    norm_iteratedFDeriv_zero,Function.comp_apply,norm_iteratedFDeriv_fderiv] at hb
  rw [← norm_first g (f x)] at hb
  norm_num at hb
  exact hb.trans (by nlinarith only
    [mul_le_mul_of_nonneg_right hF₂ (norm_nonneg (iteratedFDeriv ℝ 1 f x)),
      mul_le_mul_of_nonneg_right hF₁ (norm_nonneg (iteratedFDeriv ℝ 2 f x))])

end Bilevel.ChiBoundedChain.Composition
