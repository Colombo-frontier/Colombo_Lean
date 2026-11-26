import GradientHessian.LatchDerivativeSums

/-! The square-root register-count gradient estimate. Each local differential
is charged only to its one or two physical Euclidean coordinates. -/

noncomputable section
namespace GradientHessian.LatchGradient

open EuclideanRegisters LatchChain LatchLocalDerivatives LatchDerivativeSums Profiles
open LocalizedNormDerivatives

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_projection_apply {k : ℕ} (i : Fin k) {f : E → ℝ} (U H : Registers E k)
    (hf : DifferentiableAt ℝ f (U i)) :
    (fderiv ℝ (fun X : Registers E k => f (X i)) U) H = (fderiv ℝ f (U i)) (H i) := by
  have h := hf.hasFDerivAt.comp U
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => E) i).hasFDerivAt (x := U))
  change HasFDerivAt (fun X : Registers E k => f (X i)) _ U at h
  rw [h.fderiv]
  rfl

theorem selfTerm_fderiv_apply_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hr : 0 < r i) (hv : ‖v i‖ = 1) (U H : Registers E (k + 1)) :
    ‖(fderiv ℝ (selfTerm k v r i) U) H‖ ≤ (8 * localConstant 1) * ‖H i‖ := by
  have hb : ‖fderiv ℝ (selfResidual (r i) (v i)) (U i)‖ ≤ 8 * localConstant 1 := by
    simpa only [norm_first_derivative, Nat.cast_one, sub_self, zpow_zero, mul_one] using
      selfResidual_derivative_bound (n := 1) hr (v i) (U i) hv (by norm_num)
  change ‖(fderiv ℝ (fun X : Registers E (k + 1) => selfResidual (r i) (v i) (X i)) U) H‖ ≤ _
  rw [fderiv_projection_apply i U H
    ((selfResidual_contDiff _ _).differentiable (by norm_num) _)]
  exact ((fderiv ℝ (selfResidual (r i) (v i)) (U i)).le_opNorm (H i)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem edgeTerm_fderiv_apply_bound (k : ℕ) (v : Fin (k + 1) → E) (r : Fin (k + 1) → ℝ)
    (i : Fin k) (hr : ∀ j, 0 < r j) (hv : ∀ j, ‖v j‖ = 1)
    (hscale : r i.succ = 2 * r i.castSucc) (U H : Registers E (k + 1)) :
    ‖(fderiv ℝ (edgeTerm k v r i) U) H‖ ≤
      (112 * localConstant 1) * ‖H i.castSucc‖ + (8 * localConstant 1) * ‖H i.succ‖ := by
  let B : E → ℝ := incoming (r i.succ) (v i.succ)
  let a : E → ℝ := fun x => chi (u (r i.castSucc) (v i.castSucc) x)
  have hB : DifferentiableAt ℝ B (U i.succ) := (incoming_contDiff _ _).differentiable (by norm_num) _
  have ha : DifferentiableAt ℝ a (U i.castSucc) :=
    (contDiff_chi.comp (u_contDiff _ _)).differentiable (by norm_num) _
  have hDB : ‖fderiv ℝ B (U i.succ)‖ ≤ 8 * localConstant 1 := by
    simpa only [norm_first_derivative, Nat.cast_one, sub_self, zpow_zero, mul_one] using
      incoming_derivative_bound (n := 1) (hr i.succ) (v i.succ) (U i.succ) (hv i.succ) (by norm_num)
  have hDa : ‖fderiv ℝ a (U i.castSucc)‖ ≤ localConstant 1 / r i.castSucc := by
    simpa [scalarProfile, norm_first_derivative] using
      scaled_composite_derivative_bound 2 (hr i.castSucc) (v i.castSucc) (U i.castSucc)
        (hv i.castSucc) (n := 1) (by norm_num)
  have hbval : ‖B (U i.succ)‖ ≤ 56 * r i.succ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (incoming_bounds (hr i.succ).le _ _).1]
    exact (incoming_bounds (hr i.succ).le _ _).2
  have haval : ‖a (U i.castSucc)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (chi_bounds _).1]
    exact (chi_bounds _).2
  have hDap := ((fderiv ℝ a (U i.castSucc)).le_opNorm (H i.castSucc)).trans
    (mul_le_mul_of_nonneg_right hDa (norm_nonneg _))
  have hDBp := ((fderiv ℝ B (U i.succ)).le_opNorm (H i.succ)).trans
    (mul_le_mul_of_nonneg_right hDB (norm_nonneg _))
  have hfirst : ‖B (U i.succ) * (fderiv ℝ a (U i.castSucc)) (H i.castSucc)‖ ≤
      (112 * localConstant 1) * ‖H i.castSucc‖ := by
    rw [norm_mul]
    calc
      _ ≤ (56 * r i.succ) * ((localConstant 1 / r i.castSucc) * ‖H i.castSucc‖) :=
        mul_le_mul hbval hDap (norm_nonneg _) (by have h := hr i.succ; positivity)
      _ = _ := by rw [hscale]; field_simp [(hr i.castSucc).ne']; ring
  have hsecond : ‖a (U i.castSucc) * (fderiv ℝ B (U i.succ)) (H i.succ)‖ ≤
      (8 * localConstant 1) * ‖H i.succ‖ := by
    rw [norm_mul]
    exact (mul_le_mul haval hDBp (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hBj := hB.hasFDerivAt.comp U
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i.succ).hasFDerivAt (x := U))
  have haj := ha.hasFDerivAt.comp U
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 1) => E) i.castSucc).hasFDerivAt (x := U))
  change HasFDerivAt (fun X : Registers E (k + 1) => B (X i.succ)) _ U at hBj
  change HasFDerivAt (fun X : Registers E (k + 1) => a (X i.castSucc)) _ U at haj
  change ‖(fderiv ℝ (fun X : Registers E (k + 1) => B (X i.succ) * a (X i.castSucc)) U) H‖ ≤ _
  rw [(hBj.mul haj).fderiv]
  change ‖B (U i.succ) * (fderiv ℝ a (U i.castSucc)) (H i.castSucc) +
    a (U i.castSucc) * (fderiv ℝ B (U i.succ)) (H i.succ)‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

omit [InnerProductSpace ℝ E] in
theorem coordinate_norm_sum_le {k : ℕ} (H : Registers E k) :
    (∑ i, ‖H i‖) ≤ Real.sqrt k * ‖H‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1 : ℝ)) (fun i => ‖H i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← PiLp.norm_sq_eq_of_L2] at h
  have hsq : (∑ i, ‖H i‖) ^ 2 ≤ (Real.sqrt k * ‖H‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    exact h
  have hsum : 0 ≤ ∑ i, ‖H i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hp : 0 ≤ Real.sqrt k * ‖H‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith only [hsq, hsum, hp]

omit [InnerProductSpace ℝ E] in
theorem prefix_norm_sum_le {k : ℕ} (H : Registers E (k + 1)) :
    (∑ i : Fin k, ‖H i.castSucc‖) ≤ ∑ i : Fin (k + 1), ‖H i‖ := by
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (norm_nonneg _)

omit [InnerProductSpace ℝ E] in
theorem suffix_norm_sum_le {k : ℕ} (H : Registers E (k + 1)) :
    (∑ i : Fin k, ‖H i.succ‖) ≤ ∑ i : Fin (k + 1), ‖H i‖ := by
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (norm_nonneg _)

theorem fderiv_sum_apply_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (f : Fin k → F → ℝ) (U H : F) (hf : ∀ i, DifferentiableAt ℝ (f i) U) :
    ‖(fderiv ℝ (fun X => ∑ i, f i X) U) H‖ ≤ ∑ i, ‖(fderiv ℝ (f i) U) H‖ := by
  rw [fderiv_sum (fun i _ => hf i)]
  simp only [ContinuousLinearMap.sum_apply]
  exact norm_sum_le _ _

theorem residual_fderiv_apply_bound (k : ℕ) (v : Fin (k + 1) → E) {s : ℝ}
    (hs : 0 < s) (hv : ∀ i, ‖v i‖ = 1) (U H : Registers E (k + 1)) :
    ‖(fderiv ℝ (LatchChain.residual k v (sourceScale s)) U) H‖ ≤
      (128 * localConstant 1) * ∑ i, ‖H i‖ := by
  let r : Fin (k + 1) → ℝ := sourceScale s
  have hr : ∀ i, 0 < r i := sourceScale_pos hs
  have hsd : ∀ i, DifferentiableAt ℝ (selfTerm k v r i) U :=
    fun i => (selfTerm_contDiff k v r i).differentiable (by norm_num) U
  have hed : ∀ i, DifferentiableAt ℝ (edgeTerm k v r i) U :=
    fun i => (edgeTerm_contDiff k v r i).differentiable (by norm_num) U
  have hsfull : DifferentiableAt ℝ (selfSum k v r) U := DifferentiableAt.sum (fun i _ => hsd i)
  have hefull : DifferentiableAt ℝ (edgeSum k v r) U := DifferentiableAt.sum (fun i _ => hed i)
  rw [residual_eq_sums k v r (fun i => (hr i).ne'), (hsfull.hasFDerivAt.sub hefull.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  have hself : ‖(fderiv ℝ (selfSum k v r) U) H‖ ≤ (8 * localConstant 1) * ∑ i, ‖H i‖ := by
    apply (fderiv_sum_apply_bound (selfTerm k v r) U H hsd).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => selfTerm_fderiv_apply_bound k v r i (hr i) (hv i) U H)
  have hedge : ‖(fderiv ℝ (edgeSum k v r) U) H‖ ≤ (120 * localConstant 1) * ∑ i, ‖H i‖ := by
    apply (fderiv_sum_apply_bound (edgeTerm k v r) U H hed).trans
    calc
      _ ≤ ∑ i : Fin k, ((112 * localConstant 1) * ‖H i.castSucc‖ +
          (8 * localConstant 1) * ‖H i.succ‖) := Finset.sum_le_sum (fun i _ =>
        edgeTerm_fderiv_apply_bound k v r i hr hv (sourceScale_adjacent s i) U H)
      _ = (112 * localConstant 1) * (∑ i : Fin k, ‖H i.castSucc‖) +
          (8 * localConstant 1) * (∑ i : Fin k, ‖H i.succ‖) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (112 * localConstant 1) * (∑ i : Fin (k + 1), ‖H i‖) +
          (8 * localConstant 1) * (∑ i : Fin (k + 1), ‖H i‖) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (prefix_norm_sum_le H) (by have h := localConstant_pos 1; positivity)
        · exact mul_le_mul_of_nonneg_left (suffix_norm_sum_le H) (by have h := localConstant_pos 1; positivity)
      _ = _ := by ring
  have h := norm_sub_le ((fderiv ℝ (selfSum k v r) U) H) ((fderiv ℝ (edgeSum k v r) U) H)
  nlinarith only [h, hself, hedge]

theorem residual_first_derivative_bound (k : ℕ) (v : Fin (k + 1) → E) {s : ℝ}
    (hs : 0 < s) (hv : ∀ i, ‖v i‖ = 1) (U : Registers E (k + 1)) :
    ‖iteratedFDeriv ℝ 1 (LatchChain.residual k v (sourceScale s)) U‖ ≤
      (128 * localConstant 1) * Real.sqrt (k + 1) := by
  rw [norm_first_derivative]
  apply ContinuousLinearMap.opNorm_le_bound _ (by have h := localConstant_pos 1; positivity)
  intro H
  apply (residual_fderiv_apply_bound k v hs hv U H).trans
  calc
    _ ≤ (128 * localConstant 1) * (Real.sqrt (k + 1) * ‖H‖) :=
      mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using coordinate_norm_sum_le H)
        (by have h := localConstant_pos 1; positivity)
    _ = _ := by ring

end GradientHessian.LatchGradient
