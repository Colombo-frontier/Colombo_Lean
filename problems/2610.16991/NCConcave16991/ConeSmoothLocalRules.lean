import NCConcave16991.ConeSmoothRules
import Mathlib.Tactic.Module

/-! # Quantitative product calculus on the actual constrained dual cylinder -/

noncomputable section

namespace NCConcave16991.ConeSmooth

open Set
open scoped ContDiff Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

structure LocalJetBound (S : Set F) (f : F → ℝ) (A B C : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  C_nonneg : 0 ≤ C
  value : ∀ x ∈ S, |f x| ≤ A
  first : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ B
  second : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖

namespace LocalJetBound

variable {S : Set F} {f g : F → ℝ} {A B C D G H : ℝ}

theorem sub_bound (hf : LocalJetBound S f A B C) (hS : Convex ℝ S) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) : |f x - f y| ≤ B * ‖x - y‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (s := S) (𝕜 := ℝ)
    (f := f) (fun t ht ↦ hf.smooth.differentiable (by simp) t)
    (fun t ht ↦ hf.first t ht) hS hy hx
  simpa only [Real.norm_eq_abs] using hh

theorem weaken (hf : LocalJetBound S f A B C) {A' B' C' : ℝ}
    (hA : A ≤ A') (hB : B ≤ B') (hC : C ≤ C') : LocalJetBound S f A' B' C' :=
  ⟨hf.smooth, hf.A_nonneg.trans hA, hf.B_nonneg.trans hB, hf.C_nonneg.trans hC,
    fun x hx ↦ (hf.value x hx).trans hA, fun x hx ↦ (hf.first x hx).trans hB,
    fun x hx y hy ↦ (hf.second x hx y hy).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))⟩

theorem mul (hf : LocalJetBound S f A B C) (hg : LocalJetBound S g D G H) (hS : Convex ℝ S) :
    LocalJetBound S (fun x ↦ f x * g x) (A * D) (A * G + D * B) (A * H + D * C + 2 * B * G) := by
  have hd (x : F) : fderiv ℝ (fun x ↦ f x * g x) x = f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
    ((hf.smooth.differentiable (by simp) x).hasFDerivAt.mul
      (hg.smooth.differentiable (by simp) x).hasFDerivAt).fderiv
  have smul_estimate (a b : ℝ) (u v : F →L[ℝ] ℝ) :
      ‖a • u - b • v‖ ≤ |a| * ‖u - v‖ + |a - b| * ‖v‖ := by
    have he : a • u - b • v = a • (u - v) + (a - b) • v := by
      module
    rw [he]
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • (u - v)) ((a - b) • v)
  refine ⟨hf.smooth.mul hg.smooth, mul_nonneg hf.A_nonneg hg.A_nonneg,
    add_nonneg (mul_nonneg hf.A_nonneg hg.B_nonneg) (mul_nonneg hg.A_nonneg hf.B_nonneg),
    add_nonneg (add_nonneg (mul_nonneg hf.A_nonneg hg.C_nonneg) (mul_nonneg hg.A_nonneg hf.C_nonneg))
      (mul_nonneg (mul_nonneg (by norm_num) hf.B_nonneg) hg.B_nonneg), ?_, ?_, ?_⟩
  · intro x hx
    rw [abs_mul]
    exact mul_le_mul (hf.value x hx) (hg.value x hx) (abs_nonneg _) hf.A_nonneg
  · intro x hx
    rw [hd]
    have ht := norm_add_le (f x • fderiv ℝ g x) (g x • fderiv ℝ f x)
    simp only [norm_smul, Real.norm_eq_abs] at ht
    exact ht.trans (add_le_add
      (mul_le_mul (hf.value x hx) (hg.first x hx) (norm_nonneg _) hf.A_nonneg)
      (mul_le_mul (hg.value x hx) (hf.first x hx) (norm_nonneg _) hg.A_nonneg))
  · intro x hx y hy
    rw [hd, hd]
    have he : f x • fderiv ℝ g x + g x • fderiv ℝ f x -
        (f y • fderiv ℝ g y + g y • fderiv ℝ f y) =
        (f x • fderiv ℝ g x - f y • fderiv ℝ g y) +
          (g x • fderiv ℝ f x - g y • fderiv ℝ f y) := by abel
    rw [he]
    have h1 := smul_estimate (f x) (f y) (fderiv ℝ g x) (fderiv ℝ g y)
    have h2 := smul_estimate (g x) (g y) (fderiv ℝ f x) (fderiv ℝ f y)
    have h11 := mul_le_mul (hf.value x hx) (hg.second x hx y hy) (norm_nonneg _) hf.A_nonneg
    have h12 := mul_le_mul (hf.sub_bound hS hx hy) (hg.first y hy) (norm_nonneg _)
      (mul_nonneg hf.B_nonneg (norm_nonneg (x - y)))
    have h21 := mul_le_mul (hg.value x hx) (hf.second x hx y hy) (norm_nonneg _) hg.A_nonneg
    have h22 := mul_le_mul (hg.sub_bound hS hx hy) (hf.first y hy) (norm_nonneg _)
      (mul_nonneg hg.B_nonneg (norm_nonneg (x - y)))
    have ht := norm_add_le (f x • fderiv ℝ g x - f y • fderiv ℝ g y)
      (g x • fderiv ℝ f x - g y • fderiv ℝ f y)
    nlinarith

theorem hessian_bound (hf : LocalJetBound S f A B C) {x : F} (hx : x ∈ S) (hS : S ∈ 𝓝 x) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
  apply norm_fderiv_le_of_lip' (𝕜 := ℝ) hf.C_nonneg
  filter_upwards [hS] with y hy
  exact hf.second y hy x hx

end LocalJetBound

end NCConcave16991.ConeSmooth
