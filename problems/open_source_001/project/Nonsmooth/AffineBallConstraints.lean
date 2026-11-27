import Nonsmooth.SoftInequalityPotential
import Nonsmooth.GaussianProjectionAtoms
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Constant affine constraints are replaced by equivalent nonzero constants,
so redundant zero constraints do not create an artificial boundary. -/
def affineSoftConstraint (a : E) (b : ℝ) (x : E) : ℝ := by
  classical
  exact if a = 0 then (if 0 ≤ b then -1 else 1) else ⟪a, x⟫_ℝ - b

theorem affineSoftConstraint_nonpos (a : E) (b : ℝ) (x : E) :
    affineSoftConstraint a b x ≤ 0 ↔ ⟪a, x⟫_ℝ ≤ b := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : 0 ≤ b <;> simp [affineSoftConstraint, hb]
  · simp only [affineSoftConstraint, if_neg ha, sub_nonpos]

theorem affineSoftConstraint_contDiff (a : E) (b : ℝ) :
    ContDiff ℝ ⊤ (affineSoftConstraint a b) := by
  change ContDiff ℝ ⊤ (fun x => affineSoftConstraint a b x)
  by_cases ha : a = 0
  · simp only [affineSoftConstraint, if_pos ha]
    exact contDiff_const
  · simp only [affineSoftConstraint, if_neg ha]
    exact (contDiff_const.inner ℝ contDiff_id).sub contDiff_const

theorem affineSoftConstraint_convex (a : E) (b : ℝ) :
    ConvexOn ℝ univ (affineSoftConstraint a b) := by
  change ConvexOn ℝ univ (fun x => affineSoftConstraint a b x)
  by_cases ha : a = 0
  · simp only [affineSoftConstraint, if_pos ha]
    exact convexOn_const _ convex_univ
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy s t hs ht hst
    simp only [affineSoftConstraint, if_neg ha, inner_add_right,
      inner_smul_right, smul_eq_mul]
    have he := congrArg (fun r : ℝ => r * b) hst
    simp only [add_mul, one_mul] at he
    linarith

def ballPolytopeConstraint (c : E) (R : ℝ) (a : ι → E) (b : ι → ℝ) : Option ι → E → ℝ
  | none => fun x => ‖x - c‖ ^ 2 - R ^ 2
  | some j => affineSoftConstraint (a j) (b j)

theorem ballPolytopeConstraint_region [Fintype ι] (c : E) {R : ℝ} (hR : 0 ≤ R)
    (a : ι → E) (b : ι → ℝ) :
    softInequalityRegion (ballPolytopeConstraint c R a b) =
      closedBall c R ∩ {x : E | ∀ j, ⟪a j, x⟫_ℝ ≤ b j} := by
  ext x
  simp only [softInequalityRegion, mem_setOf_eq, Option.forall, ballPolytopeConstraint,
    affineSoftConstraint_nonpos, sub_nonpos, mem_inter_iff, mem_closedBall, dist_eq_norm]
  exact and_congr_left (fun _ => sq_le_sq₀ (norm_nonneg _) hR)

theorem ballPolytopeConstraint_contDiff (c : E) (R : ℝ) (a : ι → E) (b : ι → ℝ)
    (j : Option ι) : ContDiff ℝ ⊤ (ballPolytopeConstraint c R a b j) := by
  cases j with
  | none => exact ((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const
  | some j => exact affineSoftConstraint_contDiff (a j) (b j)

theorem ballPolytopeConstraint_convex (c : E) (R : ℝ) (a : ι → E) (b : ι → ℝ)
    (j : Option ι) : ConvexOn ℝ univ (ballPolytopeConstraint c R a b j) := by
  cases j with
  | none =>
    have hn : ConvexOn ℝ univ (fun x : E => ‖x - c‖) := by
      simpa only [dist_eq_norm] using convexOn_univ_dist c
    have hn2 : ConvexOn ℝ univ (fun x : E => ‖x - c‖ ^ 2) := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy s t hs ht hst
      have h1 := hn.2 hx hy hs ht hst
      simp only [smul_eq_mul] at h1
      have h2 := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (mul_nonneg hs (norm_nonneg _)) (mul_nonneg ht (norm_nonneg _)))).mpr h1
      exact h2.trans ((convexOn_pow 2).2 (norm_nonneg (x - c)) (norm_nonneg (y - c)) hs ht hst)
    convert! hn2.add_const (-(R ^ 2)) using 1 <;>
      first | rfl | (funext x; simp only [ballPolytopeConstraint, Pi.add_apply, sub_eq_add_neg])
  | some j => exact affineSoftConstraint_convex (a j) (b j)

end
end Nonsmooth
