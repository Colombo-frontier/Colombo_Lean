import MatchingBounds1005.SourceReferenceProgram
import MatchingBounds1005.IsometricTransfer

/-! Actual Haar-rotation measurability inputs for the reference protocol. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.SourceReferenceProgram
open GaussianVector

def rotationMap (d : ℕ) (ρ : Rotation (Vec d)) : Vec d →L[ℝ] Vec d :=
  (isometry (Vec d) ρ).toContinuousLinearMap

theorem rotationMap_column_measurable {d : ℕ} (b : Vec d) :
    Measurable (fun ρ => rotationMap d ρ b) :=
  ((continuous_action (Vec d)).comp (continuous_id.prodMk continuous_const)).measurable

theorem rotationMap_quadratic_continuous {d : ℕ} (Q : Vec d →L[ℝ] Vec d) :
    Continuous (fun p : Rotation (Vec d) × Vec d =>
      rotationMap d p.1 (Q ((rotationMap d p.1).adjoint p.2))) := by
  have hi : Continuous (fun p : Rotation (Vec d) × Vec d =>
      (rotationMap d p.1).adjoint p.2) := by
    simpa only [rotationMap, LinearIsometryEquiv.adjoint_eq_symm] using
      (IsometricTransfer.continuous_inverse_action (E := Vec d))
  exact (continuous_action (Vec d)).comp (continuous_fst.prodMk (Q.continuous.comp hi))

theorem rotationMap_quadratic_measurable {d : ℕ} (Q : Vec d →L[ℝ] Vec d) :
    Measurable (fun p : Rotation (Vec d) × Vec d =>
      rotationMap d p.1 (Q ((rotationMap d p.1).adjoint p.2))) :=
  (rotationMap_quadratic_continuous Q).measurable

end MatchingBounds1005.SourceReferenceProgram
