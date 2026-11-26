import NCConcave16991.ConeSmoothScalarBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual quantitative first- and second-derivative calculus -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open Set
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

structure DerivativeBound (f : F → ℝ) (B C : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  first_nonneg : 0 ≤ B
  second_nonneg : 0 ≤ C
  first : ∀ x, ‖fderiv ℝ f x‖ ≤ B
  second : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖

namespace DerivativeBound

variable {f g : F → ℝ} {B C D G : ℝ}

theorem sub_bound (hf : DerivativeBound f B C) (x y : F) :
    |f x - f y| ≤ B * ‖x - y‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := f) (fun z _ ↦ hf.smooth.differentiable (by simp) z)
    (fun z _ ↦ hf.first z) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

theorem add (hf : DerivativeBound f B C) (hg : DerivativeBound g D G) :
    DerivativeBound (fun x ↦ f x + g x) (B + D) (C + G) := by
  have hd (x : F) := fderiv_fun_add (hf.smooth.differentiable (by simp) x)
    (hg.smooth.differentiable (by simp) x)
  refine ⟨hf.smooth.add hg.smooth, add_nonneg hf.first_nonneg hg.first_nonneg,
    add_nonneg hf.second_nonneg hg.second_nonneg, ?_, ?_⟩
  · intro x
    rw [hd]
    exact (norm_add_le _ _).trans (add_le_add (hf.first x) (hg.first x))
  · intro x y
    rw [hd, hd]
    have he : fderiv ℝ f x + fderiv ℝ g x - (fderiv ℝ f y + fderiv ℝ g y) =
        (fderiv ℝ f x - fderiv ℝ f y) + (fderiv ℝ g x - fderiv ℝ g y) := by abel
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add (hf.second x y) (hg.second x y)).trans_eq (by ring))

theorem const_mul (hf : DerivativeBound f B C) (a : ℝ) :
    DerivativeBound (fun x ↦ a * f x) (|a| * B) (|a| * C) := by
  have hd (x : F) : fderiv ℝ (fun x ↦ a * f x) x = a • fderiv ℝ f x :=
    ((hf.smooth.differentiable (by simp) x).hasFDerivAt.const_mul a).fderiv
  refine ⟨contDiff_const.mul hf.smooth, mul_nonneg (abs_nonneg _) hf.first_nonneg,
    mul_nonneg (abs_nonneg _) hf.second_nonneg, ?_, ?_⟩
  · intro x
    rw [hd, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.first x) (abs_nonneg _)
  · intro x y
    rw [hd, hd, ← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf.second x y) (abs_nonneg _)).trans_eq (by ring)

theorem sub (hf : DerivativeBound f B C) (hg : DerivativeBound g D G) :
    DerivativeBound (fun x ↦ f x - g x) (B + D) (C + G) := by
  simpa only [abs_neg, abs_one, one_mul, neg_one_mul, sub_eq_add_neg] using hf.add (hg.const_mul (-1))

theorem linear (P : F →L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B) (hP : ‖P‖ ≤ B) :
    DerivativeBound P B 0 := by
  refine ⟨P.contDiff, hB, le_rfl, ?_, ?_⟩ <;> intro x <;> simp [P.fderiv, hP]

theorem comp_contraction {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (hf : DerivativeBound f B C) (P : H →L[ℝ] F) (hP : ‖P‖ ≤ 1) :
    DerivativeBound (fun x ↦ f (P x)) B C := by
  have hd (x : H) : fderiv ℝ (fun x ↦ f (P x)) x = (fderiv ℝ f (P x)).comp P :=
    ((hf.smooth.differentiable (by simp) (P x)).hasFDerivAt.comp x P.hasFDerivAt).fderiv
  have hnorm (x : H) : ‖P x‖ ≤ ‖x‖ :=
    (P.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))
  refine ⟨hf.smooth.comp P.contDiff, hf.first_nonneg, hf.second_nonneg, ?_, ?_⟩
  · intro x
    rw [hd]
    exact ((fderiv ℝ f (P x)).opNorm_comp_le P).trans
      ((mul_le_mul (hf.first _) hP (norm_nonneg _) hf.first_nonneg).trans_eq (mul_one _))
  · intro x y
    rw [hd, hd, ← ContinuousLinearMap.sub_comp]
    have hh := hf.second (P x) (P y)
    rw [← map_sub] at hh
    have hc := hh.trans (mul_le_mul_of_nonneg_left (hnorm (x - y)) hf.second_nonneg)
    exact ((fderiv ℝ f (P x) - fderiv ℝ f (P y)).opNorm_comp_le P).trans
      ((mul_le_mul hc hP (norm_nonneg _) (mul_nonneg hf.second_nonneg (norm_nonneg _))).trans_eq (mul_one _))

theorem scalar_comp (hf : DerivativeBound f B C) (g g' : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hg' : ∀ t, HasDerivAt g (g' t) t)
    {D G : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hfirst : ∀ t, |g' t| ≤ D)
    (hsecond : ∀ x y, |g' x - g' y| ≤ G * |x - y|) :
    DerivativeBound (fun x ↦ g (f x)) (D * B) (D * C + G * B ^ 2) := by
  have hd (x : F) : fderiv ℝ (fun x ↦ g (f x)) x = g' (f x) • fderiv ℝ f x :=
    ((hg' (f x)).comp_hasFDerivAt x (hf.smooth.differentiable (by simp) x).hasFDerivAt).fderiv
  refine ⟨hg.comp hf.smooth, mul_nonneg hD hf.first_nonneg,
    add_nonneg (mul_nonneg hD hf.second_nonneg) (mul_nonneg hG (sq_nonneg B)), ?_, ?_⟩
  · intro x
    rw [hd, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hfirst _) (hf.first _) (norm_nonneg _) hD
  · intro x y
    rw [hd, hd]
    have he : g' (f x) • fderiv ℝ f x - g' (f y) • fderiv ℝ f y =
        g' (f x) • (fderiv ℝ f x - fderiv ℝ f y) +
          (g' (f x) - g' (f y)) • fderiv ℝ f y := by
      simp only [smul_sub, sub_smul]
      abel
    rw [he]
    have ht := norm_add_le (g' (f x) • (fderiv ℝ f x - fderiv ℝ f y))
      ((g' (f x) - g' (f y)) • fderiv ℝ f y)
    simp only [norm_smul, Real.norm_eq_abs] at ht
    have h11 := mul_le_mul (hfirst (f x)) (hf.second x y) (norm_nonneg _) hD
    have hdiff := (hsecond (f x) (f y)).trans
      (mul_le_mul_of_nonneg_left (hf.sub_bound x y) hG)
    have h12 := mul_le_mul hdiff (hf.first y) (norm_nonneg _)
      (mul_nonneg hG (mul_nonneg hf.first_nonneg (norm_nonneg _)))
    nlinarith

end DerivativeBound

end NCConcave16991.ConeSmooth
