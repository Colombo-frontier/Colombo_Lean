import GradientHessian.InnerDerivativeTools

/-! Euclidean aggregation of derivatives supported on disjoint physical task
blocks. Higher derivative constants do not grow with the number of tasks. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates LocalizedNormDerivatives

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem task_norm_le (H : Space Y E m (k + 2)) (i : Fin m) :
    ‖tasks Y E m (k + 2) H i‖ ≤ ‖H‖ :=
  (PiLp.norm_apply_le (tasks Y E m (k + 2) H) i).trans (WithLp.norm_snd_le Y H)

theorem task_norm_square_sum_le (H : Space Y E m (k + 2)) :
    (∑ i, ‖tasks Y E m (k + 2) H i‖ ^ 2) ≤ ‖H‖ ^ 2 := by
  rw [← PiLp.norm_sq_eq_of_L2]
  exact pow_le_pow_left₀ (norm_nonneg _) (WithLp.norm_snd_le Y H) 2

theorem task_norm_sum_le (H : Space Y E m (k + 2)) :
    (∑ i, ‖tasks Y E m (k + 2) H i‖) ≤ Real.sqrt m * ‖H‖ :=
  (LatchGradient.coordinate_norm_sum_le (tasks Y E m (k + 2) H)).trans
    (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le Y H) (Real.sqrt_nonneg _))

theorem task_pair_norm_sum_le (H K : Space Y E m (k + 2)) :
    (∑ i, ‖tasks Y E m (k + 2) H i‖ * ‖tasks Y E m (k + 2) K i‖) ≤ ‖H‖ * ‖K‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖tasks Y E m (k + 2) H i‖) (fun i => ‖tasks Y E m (k + 2) K i‖)
  have hprod := mul_le_mul (task_norm_square_sum_le H) (task_norm_square_sum_le K)
    (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg ‖H‖)
  have hs : 0 ≤ ∑ i, ‖tasks Y E m (k + 2) H i‖ * ‖tasks Y E m (k + 2) K i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have ht : 0 ≤ ‖H‖ * ‖K‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith only [hcs, hprod, hs, ht]

theorem task_triple_norm_sum_le (H K L : Space Y E m (k + 2)) :
    (∑ i, ‖tasks Y E m (k + 2) H i‖ * ‖tasks Y E m (k + 2) K i‖ *
      ‖tasks Y E m (k + 2) L i‖) ≤ ‖H‖ * ‖K‖ * ‖L‖ := by
  calc
    _ ≤ ∑ i, ‖tasks Y E m (k + 2) H i‖ * ‖tasks Y E m (k + 2) K i‖ * ‖L‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (task_norm_le L i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ i, ‖tasks Y E m (k + 2) H i‖ * ‖tasks Y E m (k + 2) K i‖) * ‖L‖ := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (task_pair_norm_sum_le H K) (norm_nonneg _)

theorem task_product_norm_sum_le {n : ℕ} (hn2 : 2 ≤ n) (hn3 : n ≤ 3)
    (H : Fin n → Space Y E m (k + 2)) :
    (∑ i : Fin m, ∏ j : Fin n, ‖tasks Y E m (k + 2) (H j) i‖) ≤ ∏ j : Fin n, ‖H j‖ := by
  interval_cases n
  · simpa [Fin.prod_univ_succ] using task_pair_norm_sum_le (H 0) (H 1)
  · simpa [Fin.prod_univ_succ, mul_assoc] using task_triple_norm_sum_le (H 0) (H 1) (H 2)

def disjointSum (f : Fin m → Registers E (k + 2) → ℝ) (Z : Space Y E m (k + 2)) : ℝ :=
  ∑ i, f i (tasks Y E m (k + 2) Z i)

theorem disjointSum_contDiff (f : Fin m → Registers E (k + 2) → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) : ContDiff ℝ 3 (disjointSum (Y := Y) f) := by
  exact ContDiff.sum (fun i _ => (hf i).comp (taskProjection (Y := Y) (E := E) m k i).contDiff)

theorem disjointSum_first_derivative_bound (f : Fin m → Registers E (k + 2) → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ i U, ‖iteratedFDeriv ℝ 1 (f i) U‖ ≤ C) (Z : Space Y E m (k + 2)) :
    ‖iteratedFDeriv ℝ 1 (disjointSum f) Z‖ ≤ C * Real.sqrt m := by
  rw [norm_first_derivative]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Real.sqrt_nonneg _))
  intro H
  have hs := LatchGradient.fderiv_sum_apply_bound
    (fun i => (f i) ∘ taskProjection (Y := Y) (E := E) m k i) Z H
    (fun i => ((hf i).comp (taskProjection (Y := Y) (E := E) m k i).contDiff).differentiable (by norm_num) Z)
  change ‖(fderiv ℝ (disjointSum f) Z) H‖ ≤ _ at hs
  apply hs.trans
  calc
    _ ≤ ∑ i : Fin m, C * ‖tasks Y E m (k + 2) H i‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hd := ((hf i).differentiable (by norm_num) (taskProjection m k i Z)).hasFDerivAt.comp Z
        (taskProjection (Y := Y) (E := E) m k i).hasFDerivAt
      rw [hd.fderiv]
      have hb := hD i (taskProjection m k i Z)
      rw [norm_first_derivative] at hb
      exact ((fderiv ℝ (f i) (taskProjection m k i Z)).le_opNorm (taskProjection m k i H)).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = C * ∑ i : Fin m, ‖tasks Y E m (k + 2) H i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.sqrt m * ‖H‖) := mul_le_mul_of_nonneg_left (task_norm_sum_le H) hC
    _ = _ := by ring

theorem disjointSum_higher_derivative_bound (f : Fin m → Registers E (k + 2) → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (hn2 : 2 ≤ n) (hn3 : n ≤ 3)
    (hD : ∀ i U, ‖iteratedFDeriv ℝ n (f i) U‖ ≤ C) (Z : Space Y E m (k + 2)) :
    ‖iteratedFDeriv ℝ n (disjointSum f) Z‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro H
  have hdiff (i : Fin m) : ContDiff ℝ n ((f i) ∘ taskProjection (Y := Y) (E := E) m k i) :=
    ((hf i).comp (taskProjection (Y := Y) (E := E) m k i).contDiff).of_le (by exact_mod_cast hn3)
  unfold disjointSum
  change ‖(iteratedFDeriv ℝ n (fun W => ∑ i : Fin m,
    ((f i) ∘ taskProjection (Y := Y) (E := E) m k i) W) Z) H‖ ≤ _
  rw [iteratedFDeriv_sum (u := Finset.univ) (fun i _ => hdiff i)]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin m, C * ∏ j : Fin n, ‖tasks Y E m (k + 2) (H j) i‖ := by
      apply Finset.sum_le_sum
      intro i _
      have he := (taskProjection (Y := Y) (E := E) m k i).iteratedFDeriv_comp_right
        (hf i) Z (by exact_mod_cast hn3)
      rw [he]
      exact ((iteratedFDeriv ℝ n (f i) (taskProjection m k i Z)).le_opNorm
        (fun j => taskProjection m k i (H j))).trans
          (mul_le_mul_of_nonneg_right (hD i _) (Finset.prod_nonneg (fun j _ => norm_nonneg _)))
    _ = C * ∑ i : Fin m, ∏ j : Fin n, ‖tasks Y E m (k + 2) (H j) i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (task_product_norm_sum_le hn2 hn3 H) hC

end GradientHessian.Inner
