import Nonsmooth.FirstOrder
import Nonsmooth.ConvexQuadraticGradient

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem convexOn_of_nonnegative_hessian {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → ℝ) (S : E → E →L[ℝ] ℝ) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x, HasFDerivAt U (S x) x) (hds : ∀ x, HasFDerivAt S (H x) x)
    (hH : ∀ x v, 0 ≤ H x v v) : ConvexOn ℝ univ U := by
  have hline (x v : E) : ConvexOn ℝ univ (fun t : ℝ => U (x + t • v)) := by
    have hp (t : ℝ) : HasDerivAt (fun r : ℝ => x + r • v) v t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
    have h1 (t : ℝ) : HasDerivAt (fun r : ℝ => U (x + r • v)) (S (x + t • v) v) t :=
      (hd (x + t • v)).comp_hasDerivAt t (hp t)
    have h2 (t : ℝ) : HasDerivAt (fun r : ℝ => S (x + r • v) v) (H (x + t • v) v v) t :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt t
        ((hds (x + t • v)).comp_hasDerivAt t (hp t))
    exact convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (continuous_iff_continuousAt.mpr (fun t => (h1 t).continuousAt)).continuousOn
      (fun t _ => (h1 t).hasDerivWithinAt) (fun t _ => (h2 t).hasDerivWithinAt)
      (fun t _ => hH (x + t • v) v)
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have he : x + b • (y - x) = a • x + b • y := by
    calc
      _ = (a + b) • x + b • (y - x) := by rw [hab, one_smul]
      _ = _ := by simp only [add_smul, smul_sub]; abel
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero,
    one_smul, add_sub_cancel, he] using
    (hline x (y - x)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab

theorem strongConvexOn_of_hessian_lower {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : E → ℝ) (S : E → E →L[ℝ] ℝ) (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x, HasFDerivAt U (S x) x) (hds : ∀ x, HasFDerivAt S (H x) x)
    (ρ : ℝ) (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ H x v v) : StrongConvexOn univ ρ U := by
  apply strongConvexOn_iff_convex.mpr
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  apply convexOn_of_nonnegative_hessian (fun x => U x - ρ / 2 * ‖x‖ ^ 2)
    (fun x => S x - ρ • B x) (fun x => H x - ρ • B)
  · intro x
    convert! (hd x).sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (ρ / 2)) using 1
    ext v
    simp only [sub_apply, smul_apply, smul_eq_mul]
    ring
  · intro x
    exact (hds x).sub (B.hasFDerivAt.const_smul ρ)
  · intro x v
    change 0 ≤ H x v v - ρ * inner ℝ v v
    rw [real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (hH x v)

end
end Nonsmooth
