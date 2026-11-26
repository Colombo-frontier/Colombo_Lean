import NCConcave16991.GlobalHardStateSmoothness

/-! # Quantitative product calculus for the literal outer terms -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Three actual global zeroth/first/second jet bounds. The second condition
is a bound on differences of the actual Fréchet derivative. -/
structure JetBound (f : E → ℝ) (A B C : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  C_nonneg : 0 ≤ C
  value : ∀ x, |f x| ≤ A
  first : ∀ x, ‖fderiv ℝ f x‖ ≤ B
  second : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖

namespace JetBound

variable {f g : E → ℝ} {A B C D F G : ℝ}

theorem const (a : ℝ) : JetBound (fun _ : E ↦ a) |a| 0 0 := by
  refine ⟨contDiff_const, abs_nonneg _, le_rfl, le_rfl, fun _ ↦ le_rfl, ?_, ?_⟩ <;> simp

theorem weaken (hf : JetBound f A B C) (A' B' C' : ℝ)
    (hA : A ≤ A') (hB : B ≤ B') (hC : C ≤ C') : JetBound f A' B' C' :=
  ⟨hf.smooth, hf.A_nonneg.trans hA, hf.B_nonneg.trans hB, hf.C_nonneg.trans hC,
    fun x ↦ (hf.value x).trans hA, fun x ↦ (hf.first x).trans hB,
    fun x y ↦ (hf.second x y).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))⟩

theorem sub_bound (hf : JetBound f A B C) (x y : E) : |f x - f y| ≤ B * ‖x - y‖ := by
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := f) (fun t _ ↦ hf.smooth.differentiable (by simp) t)
    (fun t _ ↦ hf.first t) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

theorem product_fderiv (hf : JetBound f A B C) (hg : JetBound g D F G) (x : E) :
    fderiv ℝ (fun t ↦ f t * g t) x = f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
  (((hf.smooth.differentiable (by simp) x).hasFDerivAt).mul
    ((hg.smooth.differentiable (by simp) x).hasFDerivAt)).fderiv

theorem smul_sub_estimate {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a b : ℝ) (u v : H) :
    ‖a • u - b • v‖ ≤ |a| * ‖u - v‖ + |a - b| * ‖v‖ := by
  have he : a • u - b • v = a • (u - v) + (a - b) • v := by
    simp only [smul_sub, sub_smul]
    abel
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • (u - v)) ((a - b) • v)

theorem mul (hf : JetBound f A B C) (hg : JetBound g D F G) :
    JetBound (fun x ↦ f x * g x) (A * D) (A * F + D * B) (A * G + D * C + 2 * B * F) := by
  have hA := hf.A_nonneg
  have hB := hf.B_nonneg
  have hC := hf.C_nonneg
  have hD := hg.A_nonneg
  have hF := hg.B_nonneg
  have hG := hg.C_nonneg
  refine ⟨hf.smooth.mul hg.smooth, mul_nonneg hf.A_nonneg hg.A_nonneg,
    add_nonneg (mul_nonneg hf.A_nonneg hg.B_nonneg) (mul_nonneg hg.A_nonneg hf.B_nonneg),
    by positivity, ?_, ?_, ?_⟩
  · intro x
    rw [abs_mul]
    exact mul_le_mul (hf.value x) (hg.value x) (abs_nonneg _) hf.A_nonneg
  · intro x
    rw [product_fderiv hf hg]
    have ht := norm_add_le (f x • fderiv ℝ g x) (g x • fderiv ℝ f x)
    simp only [norm_smul, Real.norm_eq_abs] at ht
    exact ht.trans (add_le_add
      (mul_le_mul (hf.value x) (hg.first x) (norm_nonneg _) hf.A_nonneg)
      (mul_le_mul (hg.value x) (hf.first x) (norm_nonneg _) hg.A_nonneg))
  · intro x y
    rw [product_fderiv hf hg, product_fderiv hf hg]
    have he : f x • fderiv ℝ g x + g x • fderiv ℝ f x -
        (f y • fderiv ℝ g y + g y • fderiv ℝ f y) =
        (f x • fderiv ℝ g x - f y • fderiv ℝ g y) +
          (g x • fderiv ℝ f x - g y • fderiv ℝ f y) := by abel
    rw [he]
    have h1 := smul_sub_estimate (f x) (f y) (fderiv ℝ g x) (fderiv ℝ g y)
    have h2 := smul_sub_estimate (g x) (g y) (fderiv ℝ f x) (fderiv ℝ f y)
    have h11 := mul_le_mul (hf.value x) (hg.second x y) (norm_nonneg _) hf.A_nonneg
    have h12 := mul_le_mul (hf.sub_bound x y) (hg.first y) (norm_nonneg _)
      (mul_nonneg hf.B_nonneg (norm_nonneg (x - y)))
    have h21 := mul_le_mul (hg.value x) (hf.second x y) (norm_nonneg _) hg.A_nonneg
    have h22 := mul_le_mul (hg.sub_bound x y) (hf.first y) (norm_nonneg _)
      (mul_nonneg hg.B_nonneg (norm_nonneg (x - y)))
    have ht := norm_add_le (f x • fderiv ℝ g x - f y • fderiv ℝ g y)
      (g x • fderiv ℝ f x - g y • fderiv ℝ f y)
    nlinarith

theorem one_sub (hf : JetBound f A B C) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ x, |1 - f x| ≤ D) : JetBound (fun x ↦ 1 - f x) D B C := by
  have hd (x : E) : fderiv ℝ (fun x ↦ 1 - f x) x = -fderiv ℝ f x := by
    have hh := ((hf.smooth.differentiable (by simp) x).hasFDerivAt).const_sub 1
    exact hh.fderiv
  refine ⟨contDiff_const.sub hf.smooth, hD, hf.B_nonneg, hf.C_nonneg, hv, ?_, ?_⟩
  · intro x
    simpa only [hd, norm_neg] using hf.first x
  · intro x y
    simpa only [hd, neg_sub_neg, norm_sub_rev] using hf.second x y

theorem const_mul (hf : JetBound f A B C) (a : ℝ) :
    JetBound (fun x ↦ a * f x) (|a| * A) (|a| * B) (|a| * C) := by
  have hA := hf.A_nonneg
  have hB := hf.B_nonneg
  have hC := hf.C_nonneg
  have hd (x : E) : fderiv ℝ (fun x ↦ a * f x) x = a • fderiv ℝ f x :=
    (((hf.smooth.differentiable (by simp) x).hasFDerivAt).const_mul a).fderiv
  refine ⟨contDiff_const.mul hf.smooth, by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.value x) (abs_nonneg _)
  · intro x
    rw [hd, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.first x) (abs_nonneg _)
  · intro x y
    rw [hd, hd, ← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf.second x y) (abs_nonneg _)).trans_eq (by ring)

theorem comp_contraction {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (hf : JetBound f A B C) (P : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) :
    JetBound (fun x ↦ f (P x)) A B C := by
  have hd (x : H) : fderiv ℝ (fun x ↦ f (P x)) x = (fderiv ℝ f (P x)).comp P :=
    (((hf.smooth.differentiable (by simp) (P x)).hasFDerivAt).comp x P.hasFDerivAt).fderiv
  have hnorm (x : H) : ‖P x‖ ≤ ‖x‖ :=
    (P.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg x)).trans_eq (one_mul _))
  refine ⟨hf.smooth.comp P.contDiff, hf.A_nonneg, hf.B_nonneg, hf.C_nonneg,
    fun x ↦ hf.value (P x), ?_, ?_⟩
  · intro x
    rw [hd]
    exact ((fderiv ℝ f (P x)).opNorm_comp_le P).trans
      ((mul_le_mul (hf.first _) hP (norm_nonneg _) hf.B_nonneg).trans_eq (mul_one _))
  · intro x y
    rw [hd, hd, ← ContinuousLinearMap.sub_comp]
    have hh := hf.second (P x) (P y)
    rw [← map_sub] at hh
    have hc := hh.trans (mul_le_mul_of_nonneg_left (hnorm (x - y)) hf.C_nonneg)
    exact ((fderiv ℝ f (P x) - fderiv ℝ f (P y)).opNorm_comp_le P).trans
      ((mul_le_mul hc hP (norm_nonneg _) (mul_nonneg hf.C_nonneg (norm_nonneg _))).trans_eq (mul_one _))

end JetBound

end

end NCConcave16991.GlobalHard
