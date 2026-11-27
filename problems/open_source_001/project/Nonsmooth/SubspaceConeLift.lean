import Nonsmooth.OrthogonalConeLift
import Mathlib.Analysis.InnerProductSpace.Orthogonal

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def comparisonConeExcluded (G : Set E) (f : E → ℝ) (H : Submodule ℝ E)
    (x e : E) (δ B : ℝ) : Prop :=
  ∀ v ∈ H, x + v ∈ G → δ * ‖v‖ ≤ ⟪v, e⟫_ℝ → B ≤ f (x + v)

theorem orthogonal_residual_mem_section (K : Submodule ℝ E) {n z : E}
    (hnK : n ∈ K) (hn : ‖n‖ = 1) (hz : z ∈ K) :
    z - ⟪z, n⟫_ℝ • n ∈ K ⊓ (ℝ ∙ n)ᗮ := by
  refine ⟨K.sub_mem hz (K.smul_mem _ hnK), ?_⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn,
    one_pow, mul_one, sub_self]

theorem comparisonConeExcluded_lift {G : Set E} {f : E → ℝ} (hf : ConvexOn ℝ G f)
    (K : Submodule ℝ E) (x w n e : E) {B δ ε a : ℝ}
    (hnK : n ∈ K) (hn : ‖n‖ = 1) (he : ‖e‖ = 1)
    (heH : e ∈ K ⊓ (ℝ ∙ n)ᗮ) (hwH : w ∈ K ⊓ (ℝ ∙ n)ᗮ)
    (hδ : 0 ≤ δ) (ha : 0 < a) (hw : ‖w‖ ≤ a * ε)
    (hqminusG : x + w - a • n ∈ G) (hqplusG : x + w + a • n ∈ G)
    (hqminusB : f (x + w - a • n) ≤ B) (hqplusB : f (x + w + a • n) ≤ B)
    (hsection : comparisonConeExcluded G f (K ⊓ (ℝ ∙ n)ᗮ) x e δ B) :
    comparisonConeExcluded G f K x e (Real.sqrt (δ ^ 2 + ((1 + δ) * ε) ^ 2)) B := by
  intro z hzK hzG hslope
  let t := ⟪z, n⟫_ℝ
  let u := z - t • n
  have hu : u ∈ K ⊓ (ℝ ∙ n)ᗮ := orthogonal_residual_mem_section K hnK hn hzK
  have hun : ⟪u, n⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hu.2
  have hne : ⟪n, e⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp heH.2
  have huz : u + t • n = z := by dsimp [u]; module
  have hxuz : x + u + t • n = x + z := by rw [add_assoc, huz]
  have h := convex_cone_lift_orthogonal (t := t) hf (K ⊓ (ℝ ∙ n)ᗮ) x u w n e hu hwH he hn hun hne
    hδ ha hw hqminusG hqplusG hqminusB hqplusB hsection
    (by simpa only [hxuz] using hzG) (by simpa only [huz] using hslope)
  simpa only [hxuz] using h

theorem comparisonConeExcluded_mono_coefficient {G : Set E} {f : E → ℝ}
    {H : Submodule ℝ E} {x e : E} {δ δ' B : ℝ}
    (h : comparisonConeExcluded G f H x e δ B) (hδ : δ ≤ δ') :
    comparisonConeExcluded G f H x e δ' B := by
  intro v hv hvG hslope
  exact h v hv hvG ((mul_le_mul_of_nonneg_right hδ (norm_nonneg v)).trans hslope)

end
end Nonsmooth
