import GradientHessian.InnerBounds

/-! Derivative restrictions along actual contractive linear coordinates. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates

section Normed
variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem derivative_comp_linear_le (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    {f : G → H} (hf : ContDiff ℝ 3 f) {n : ℕ} (hn : n ≤ 3) (x : F) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hn)]
  have h := (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg L) hL))

theorem norm_iteratedFDeriv_add_le {n : ℕ} {f g : F → G} (hf : ContDiff ℝ 3 f)
    (hg : ContDiff ℝ 3 g) (hn : n ≤ 3) (x : F) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
  rw [iteratedFDeriv_add_apply' (hf.contDiffAt.of_le (by exact_mod_cast hn))
    (hg.contDiffAt.of_le (by exact_mod_cast hn))]
  exact norm_add_le _ _

end Normed

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem numerical_norm_le (m k : ℕ) : ‖numerical Y E m k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro Z
  simpa only [one_mul] using WithLp.norm_fst_le Y Z

theorem tasks_norm_le (m k : ℕ) : ‖tasks Y E m k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro Z
  simpa only [one_mul] using WithLp.norm_snd_le Y Z

theorem taskProjection_norm_le (m k : ℕ) (i : Fin m) :
    ‖taskProjection (Y := Y) (E := E) m k i‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (LatchDerivativeSums.projection_norm_le (E := Registers E (k + 2)) i)
      (tasks_norm_le (Y := Y) (E := E) m (k + 2))
      (norm_nonneg (tasks Y E m (k + 2))) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1))

def firstProjection (m k : ℕ) (i : Fin m) : Space Y E m (k + 2) →L[ℝ] E :=
  (PiLp.proj 2 (fun _ : Fin (k + 2) => E) 0).comp (taskProjection m k i)

theorem firstProjection_norm_le (m k : ℕ) (i : Fin m) :
    ‖firstProjection (Y := Y) (E := E) m k i‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (LatchDerivativeSums.projection_norm_le (E := E) (0 : Fin (k + 2)))
      (taskProjection_norm_le (Y := Y) (E := E) m k i)
      (norm_nonneg (taskProjection (Y := Y) (E := E) m k i)) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1))

end GradientHessian.Inner
