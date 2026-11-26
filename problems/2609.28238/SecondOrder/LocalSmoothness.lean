import SecondOrder.LocalObjective
import Mathlib.Analysis.Calculus.MeanValue

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_lipschitz_of_bound {k : ℕ} {f : E → F}
    (hf : ContDiff ℝ (k+1) f) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ M) (x y : E) :
    ‖iteratedFDeriv ℝ k f y-iteratedFDeriv ℝ k f x‖ ≤ M*‖y-x‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) z)
    (fun z _ => ?_) (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ y)
  rw [norm_fderiv_iteratedFDeriv]
  exact hM z

theorem norm_first_iteratedFDeriv (f : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := by
  simpa only [iteratedFDerivWithin_univ, fderivWithin_univ] using
    norm_iteratedFDerivWithin_one (𝕜 := ℝ) (s := Set.univ) (x := x) f uniqueDiffWithinAt_univ

theorem fderiv_lipschitz_of_second_bound {f : E → F} (hf : ContDiff ℝ 2 f)
    {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) (x y : E) :
    ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ M*‖y-x‖ := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num)
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z)
    (fun z _ => ?_) (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ y)
  have he : ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_first_iteratedFDeriv]
  rw [he]
  exact hM z

end General

variable {J I : Type*} [Fintype J] [Fintype I] (E : J → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (S : I → Finset J) (r : ℕ)
  (hr : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ r)

include hr

theorem localObjective_fderiv_lipschitz
    (φ : ∀ i, LocalBlockSpace E (S i) → F) (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 2 (φ i) y‖ ≤ M)
    (x y : BlockSpace E) :
    ‖fderiv ℝ (localObjective E S φ) y-fderiv ℝ (localObjective E S φ) x‖ ≤ (r:ℝ)*M*‖y-x‖ :=
  fderiv_lipschitz_of_second_bound (localObjective_contDiff E S φ hφ)
    (localObjective_second_bound E S r hr φ hφ hM hbound) x y

theorem localObjective_second_lipschitz
    (φ : ∀ i, LocalBlockSpace E (S i) → F) (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i y, ‖iteratedFDeriv ℝ 3 (φ i) y‖ ≤ M)
    (x y : BlockSpace E) :
    ‖iteratedFDeriv ℝ 2 (localObjective E S φ) y-iteratedFDeriv ℝ 2 (localObjective E S φ) x‖ ≤
      (r:ℝ)*M*‖y-x‖ :=
  iteratedFDeriv_lipschitz_of_bound (localObjective_contDiff E S φ hφ)
    (localObjective_third_bound E S r hr φ hφ hM hbound) x y

end
end SecondOrder
