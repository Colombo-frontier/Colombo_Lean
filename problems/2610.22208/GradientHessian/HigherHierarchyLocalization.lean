import GradientHessian.HigherHierarchyMixture

/-! Numerical localization of every actual driven recursive scalar,
proved by its exact finite convex mixture of the literal capped leaves. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open InnerCoordinates

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, CompleteSpace (H t)]

theorem driven_localization {K : ℝ} (hK : 0 < K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (l : ℝ) (Z : Space Y E H m t)
    (hg : ‖gradient (driven K t d l) Z‖ ≤ 1) :
    ‖numericalProjection t Z‖ ≤ Leaf.numericalRadius := by
  let z := leafProjection t Z
  let f := fun W : Leaf.Space Y E (m+1) => driven K t d l (replaceLeaf t Z W)
  have hf : ContDiff ℝ 3 f := (driven_contDiff hK t d l).comp (replaceLeaf_contDiff t Z)
  have hfg := (leaf_gradient_norm_le t (driven K t d l) Z
    ((driven_contDiff hK t d l).differentiable (by norm_num) Z)).trans hg
  obtain ⟨c,hc⟩ := driven_numerical_slice K t d l Z
  have hv := leafData_valid t d hd
  rw [numericalProjection_eq]
  exact Leaf.mixture_localization (m := m+1) (by omega)
    (resetWeight K t d Z) (leafWeights K t d Z) (resetWeight_nonneg K t d Z)
    (leafWeights_nonneg K t d Z) (leafWeights_partition K t d Z)
    (fun i => (leafData t d i).A) (fun i => (hv i).1)
    (fun i => by simpa only [Nat.cast_add, Nat.cast_one] using (hv i).2.1)
    (fun i => (hv i).2.2.1)
    (fun i => (leafData t d i).b) (fun i => (leafData t d i).a) (fun i => (leafData t d i).v)
    (fun i => (hv i).2.2.2.1) (fun i => (hv i).2.2.2.2)
    f z (hf.differentiable (by norm_num) z) c hc hfg

end GradientHessian.HigherHierarchy
