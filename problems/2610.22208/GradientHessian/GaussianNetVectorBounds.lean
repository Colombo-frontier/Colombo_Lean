import GradientHessian.GaussianSphereNets
import GradientHessian.GaussianExtremaAlgebra

/-! Quantitative finite-net bounds for the independent-vector comparison
process, including the sign of its minimizing row term. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ε : ℝ} (U : UnitSphereNet E ε) (V : UnitSphereNet F ε)

def netVectorSum (g : F) (h : E) (p : U.Index × V.Index) : ℝ := ⟪(p.2 : F),g⟫_ℝ + ⟪(p.1 : E),h⟫_ℝ

theorem netVector_maximum (g : F) (h : E) :
    finiteMaximum (netVectorSum U V g h) ≤ ‖g‖+‖h‖ := by
  have he : netVectorSum U V g h = fun p : U.Index × V.Index =>
      ⟪(p.1 : E),h⟫_ℝ + ⟪(p.2 : F),g⟫_ℝ := by funext p; exact add_comm _ _
  rw [he,finiteMaximum_pair_add (fun i : U.Index => ⟪(i : E),h⟫_ℝ)
    (fun j : V.Index => ⟪(j : F),g⟫_ℝ)]
  have hu := U.support_upper h
  have hv := V.support_upper g
  linarith

theorem netVector_minimum (g : F) (h : E) :
    ‖g‖-‖h‖-ε*‖g‖ ≤ finiteMinMax (netVectorSum U V g h) := by
  have he : netVectorSum U V g h = fun p : U.Index × V.Index =>
      ⟪(p.1 : E),h⟫_ℝ + ⟪(p.2 : F),g⟫_ℝ := by funext p; exact add_comm _ _
  rw [he,finiteMinMax_pair_add (fun i : U.Index => ⟪(i : E),h⟫_ℝ)
    (fun j : V.Index => ⟪(j : F),g⟫_ℝ)]
  have hmin : -‖h‖ ≤ finiteMinimum (fun i : U.Index => ⟪(i : E),h⟫_ℝ) := by
    apply le_finiteMinimum
    intro i
    have hi := (abs_le.mp (abs_real_inner_le_norm (i : E) h)).1
    simpa only [U.index_unit i,neg_mul,one_mul] using hi
  have hmax := V.support_lower g
  linarith

end GradientHessian.GaussianConcentration
