import FreshGradientMinimax.CompressedCoordinates
import FreshGradientMinimax.JointGradient

/-! The full objective after primal compression and the nonnegative ridge,
with actual derivatives in both variables and jointly. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  (f : Euclid (n + 1) → Euclid dy → ℝ)

def compressedObjective (r R β : ℝ) (x : Euclid dx) (y : Euclid dy) : ℝ :=
  f (compressedCoordinates U r R x) y + β / 2 * ‖x‖ ^ 2

def compressedGradX (r R β : ℝ) (x : Euclid dx) (y : Euclid dy) : Euclid dx :=
  compressedPullback U r R x (gradient (fun u => f u y) (compressedCoordinates U r R x)) + β • x

def compressedGradY (r R : ℝ) (x : Euclid dx) (y : Euclid dy) : Euclid dy :=
  gradient (f (compressedCoordinates U r R x)) y

theorem compressedObjective_contDiff {r R β : ℝ}
    (hf : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2)) :
    ContDiff ℝ 1 (fun z : Joint dx dy => compressedObjective U f r R β z.1 z.2) :=
  (hf.comp (((compressedCoordinates_contDiff U r R).comp contDiff_fst).prodMk contDiff_snd)).add
    (((contDiff_norm_sq ℝ).comp contDiff_fst).const_smul (β / 2))

theorem compressedObjective_hasFDerivAt_x {r R β : ℝ} (hR : 0 < R)
    (hf : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2))
    (x : Euclid dx) (y : Euclid dy) :
    HasFDerivAt (fun z => compressedObjective U f r R β z y) (innerSL ℝ (compressedGradX U f r R β x y)) x := by
  have hi : ContDiff ℝ 1 (fun u : Euclid (n + 1) => (u, y)) := contDiff_id.prodMk contDiff_const
  have hfu : DifferentiableAt ℝ (fun u => f u y) (compressedCoordinates U r R x) :=
    (hf.comp hi).differentiable (by norm_num) _
  have hd := (hfu.hasGradientAt.hasFDerivAt.comp x (compressedCoordinates_hasFDerivAt U r hR x)).add
    (half_quadratic_hasFDerivAt β x)
  apply hd.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, innerSL_apply,
    compressedGradX, inner_add_left, compressedPullback_inner, InnerProductSpace.toDual_apply]

theorem compressedObjective_hasFDerivAt_y {r R β : ℝ}
    (hf : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2))
    (x : Euclid dx) (y : Euclid dy) :
    HasFDerivAt (compressedObjective U f r R β x) (innerSL ℝ (compressedGradY U f r R x y)) y := by
  have hfy : DifferentiableAt ℝ (f (compressedCoordinates U r R x)) y :=
    ((hf.differentiable (by norm_num)) (compressedCoordinates U r R x, y)).comp _
      ((differentiableAt_const (𝕜 := ℝ) (compressedCoordinates U r R x)).prodMk differentiableAt_id)
  exact hfy.hasGradientAt.hasFDerivAt.add_const _

theorem compressedObjective_gradient_x {r R β : ℝ} (hR : 0 < R)
    (hf : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2))
    (x : Euclid dx) (y : Euclid dy) :
    gradient (fun z => compressedObjective U f r R β z y) x = compressedGradX U f r R β x y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (compressedObjective_hasFDerivAt_x U f hR hf x y)).gradient

theorem compressedObjective_gradient_y {r R β : ℝ}
    (hf : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2))
    (x : Euclid dx) (y : Euclid dy) :
    gradient (compressedObjective U f r R β x) y = compressedGradY U f r R x y :=
  (hasGradientAt_iff_hasFDerivAt.mpr (compressedObjective_hasFDerivAt_y U f hf x y)).gradient

theorem compressedObjective_hasFDerivAt {r R β : ℝ} (hR : 0 < R)
    (hf : ContDiff ℝ 1 (fun z : Euclid (n + 1) × Euclid dy => f z.1 z.2))
    (z : Joint dx dy) :
    HasFDerivAt (fun w : Joint dx dy => compressedObjective U f r R β w.1 w.2)
      ((innerSL ℝ (compressedGradX U f r R β z.1 z.2)).coprod
        (innerSL ℝ (compressedGradY U f r R z.1 z.2))) z := by
  have h := joint_hasFDerivAt_gradient
    ((compressedObjective_contDiff U f (r := r) (R := R) (β := β) hf).differentiable (by norm_num) z)
  simpa only [compressedObjective_gradient_x U f hR hf, compressedObjective_gradient_y U f hf] using h

theorem compressedObjective_strongConcave {r R β μ : ℝ}
    (hf : ∀ u, StrongConcaveGradient (f u) (gradient (f u)) μ) (x : Euclid dx) :
    StrongConcaveGradient (compressedObjective U f r R β x) (compressedGradY U f r R x) μ := by
  intro y z
  have h := hf (compressedCoordinates U r R x) y z
  unfold compressedObjective compressedGradY
  linarith only [h]

end FreshGradientMinimax
