import NCConcave16991.GlobalHardJet

/-! # Actual bounded vector caps and their public inner-product jet -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set LocalizationRadial LocalizationHessian
open scoped ContDiff InnerProductSpace

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure VectorJetBound (f : H → E) (A B C : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  C_nonneg : 0 ≤ C
  value : ∀ x, ‖f x‖ ≤ A
  first : ∀ x, ‖fderiv ℝ f x‖ ≤ B
  second : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖

namespace VectorJetBound

variable {f g : H → E} {A B C D F G : ℝ}

theorem const (v : E) : VectorJetBound (fun _ : H ↦ v) ‖v‖ 0 0 := by
  refine ⟨contDiff_const, norm_nonneg _, le_rfl, le_rfl, fun _ ↦ le_rfl, ?_, ?_⟩ <;> simp

theorem sub_bound (hf : VectorJetBound f A B C) (x y : H) : ‖f x - f y‖ ≤ B * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (𝕜 := ℝ)
    (f := f) (fun t _ ↦ hf.smooth.differentiable (by simp) t)
    (fun t _ ↦ hf.first t) convex_univ (mem_univ y) (mem_univ x)

theorem inner_fderiv (hf : VectorJetBound f A B C) (hg : VectorJetBound g D F G) (x : H) :
    fderiv ℝ (fun t ↦ ⟪f t, g t⟫_ℝ) x =
      (innerSL ℝ (f x)).comp (fderiv ℝ g x) + (innerSL ℝ (g x)).comp (fderiv ℝ f x) := by
  have hh := ((hf.smooth.differentiable (by simp) x).hasFDerivAt).inner ℝ
    ((hg.smooth.differentiable (by simp) x).hasFDerivAt)
  rw [hh.fderiv]
  ext h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, innerSL_apply_apply]
  rw [real_inner_comm (fderiv ℝ f x h) (g x)]

theorem inner_term_sub_estimate (x y : E) (P Q : H →L[ℝ] E) :
    ‖(innerSL ℝ x).comp P - (innerSL ℝ y).comp Q‖ ≤
      ‖x‖ * ‖P - Q‖ + ‖x - y‖ * ‖Q‖ := by
  have he : (innerSL ℝ x).comp P - (innerSL ℝ y).comp Q =
      (innerSL ℝ x).comp (P - Q) + (innerSL ℝ (x - y)).comp Q := by
    ext h
    simp
  rw [he]
  have hh := (norm_add_le _ _).trans (add_le_add
    ((innerSL ℝ x).opNorm_comp_le (P - Q)) ((innerSL ℝ (x - y)).opNorm_comp_le Q))
  simpa only [innerSL_apply_norm] using hh

theorem inner (hf : VectorJetBound f A B C) (hg : VectorJetBound g D F G) :
    JetBound (fun x ↦ ⟪f x, g x⟫_ℝ) (A * D) (A * F + D * B) (A * G + D * C + 2 * B * F) := by
  have hA := hf.A_nonneg
  have hB := hf.B_nonneg
  have hC := hf.C_nonneg
  have hD := hg.A_nonneg
  have hF := hg.B_nonneg
  have hG := hg.C_nonneg
  refine ⟨hf.smooth.inner ℝ hg.smooth, by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · intro x
    exact (abs_real_inner_le_norm (f x) (g x)).trans
      (mul_le_mul (hf.value x) (hg.value x) (norm_nonneg _) hA)
  · intro x
    rw [inner_fderiv hf hg]
    have ht := (norm_add_le _ _).trans (add_le_add
      ((innerSL ℝ (f x)).opNorm_comp_le (fderiv ℝ g x))
      ((innerSL ℝ (g x)).opNorm_comp_le (fderiv ℝ f x)))
    simp only [innerSL_apply_norm] at ht
    exact ht.trans (add_le_add
      (mul_le_mul (hf.value x) (hg.first x) (norm_nonneg _) hA)
      (mul_le_mul (hg.value x) (hf.first x) (norm_nonneg _) hD))
  · intro x y
    rw [inner_fderiv hf hg, inner_fderiv hf hg]
    have he : (innerSL ℝ (f x)).comp (fderiv ℝ g x) + (innerSL ℝ (g x)).comp (fderiv ℝ f x) -
        ((innerSL ℝ (f y)).comp (fderiv ℝ g y) + (innerSL ℝ (g y)).comp (fderiv ℝ f y)) =
        ((innerSL ℝ (f x)).comp (fderiv ℝ g x) - (innerSL ℝ (f y)).comp (fderiv ℝ g y)) +
          ((innerSL ℝ (g x)).comp (fderiv ℝ f x) - (innerSL ℝ (g y)).comp (fderiv ℝ f y)) := by abel
    rw [he]
    have h1 := inner_term_sub_estimate (f x) (f y) (fderiv ℝ g x) (fderiv ℝ g y)
    have h2 := inner_term_sub_estimate (g x) (g y) (fderiv ℝ f x) (fderiv ℝ f y)
    have h11 := mul_le_mul (hf.value x) (hg.second x y) (norm_nonneg _) hA
    have h12 := mul_le_mul (hf.sub_bound x y) (hg.first y) (norm_nonneg _)
      (mul_nonneg hB (norm_nonneg (x - y)))
    have h21 := mul_le_mul (hg.value x) (hf.second x y) (norm_nonneg _) hD
    have h22 := mul_le_mul (hg.sub_bound x y) (hf.first y) (norm_nonneg _)
      (mul_nonneg hF (norm_nonneg (x - y)))
    have ht := norm_add_le
      ((innerSL ℝ (f x)).comp (fderiv ℝ g x) - (innerSL ℝ (f y)).comp (fderiv ℝ g y))
      ((innerSL ℝ (g x)).comp (fderiv ℝ f x) - (innerSL ℝ (g y)).comp (fderiv ℝ f y))
    nlinarith

end VectorJetBound

theorem cap_contraction_jet (R C : ℝ) (hR : 0 < R) (hC : 14 / R ≤ C)
    (P : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) : VectorJetBound (fun x ↦ radialCap R (P x)) (2 * R) 1 C := by
  have hnorm (x : H) : ‖P x‖ ≤ ‖x‖ :=
    (P.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))
  have hd (x : H) : fderiv ℝ (fun x ↦ radialCap R (P x)) x =
      (fderiv ℝ (radialCap R) (P x)).comp P :=
    (((radialCap_differentiable hR (P x)).hasFDerivAt).comp x P.hasFDerivAt).fderiv
  refine ⟨(radialCap_contDiff hR).comp P.contDiff, by positivity, by norm_num,
    (div_nonneg (by norm_num) hR.le).trans hC, ?_, ?_, ?_⟩
  · intro x
    exact (radialCap_value_bounds hR (P x)).trans (min_le_right _ _)
  · intro x
    rw [hd]
    exact ((fderiv ℝ (radialCap R) (P x)).opNorm_comp_le P).trans
      ((mul_le_mul (radialCap_fderiv_norm_le hR _) hP (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring))
  · intro x y
    rw [hd, hd, ← ContinuousLinearMap.sub_comp]
    have hs := radialCap_fderiv_sub_bound hR (P x) (P y)
    rw [← map_sub] at hs
    have hc := (hs.trans (mul_le_mul_of_nonneg_left (hnorm (x - y)) (by positivity : 0 ≤ 14 / R))).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
    exact ((fderiv ℝ (radialCap R) (P x) - fderiv ℝ (radialCap R) (P y)).opNorm_comp_le P).trans
      ((mul_le_mul hc hP (norm_nonneg _) (mul_nonneg ((div_nonneg (by norm_num) hR.le).trans hC) (norm_nonneg _))).trans_eq (mul_one _))

/-- The public vector exit uses this actual inner product of capped vectors.
It has the paper's dimension-free bounds 840, 62 and 106. -/
theorem capped_inner_jet (P Q : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    JetBound (fun x ↦ ⟪radialCap 10 (P x), radialCap 21 (Q x)⟫_ℝ) 840 62 106 := by
  convert (cap_contraction_jet 10 2 (by norm_num) (by norm_num) P hP).inner
    (cap_contraction_jet 21 1 (by norm_num) (by norm_num) Q hQ) using 1 <;> norm_num

end

end NCConcave16991.GlobalHard
