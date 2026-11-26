import SecondOrder.ContinuousChord
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Symmetric

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- The derivative of the actual gradient, identified with the bilinear
second derivative of the scalar function by the Riesz isometry. -/
theorem hessian_apply_eq_second_derivative {d : ℕ} {F : Point d → ℝ}
    (hF : ContDiff ℝ 2 F) (x v : Point d) :
    hessian F x v = (InnerProductSpace.toDual ℝ (Point d)).symm
      (fderiv ℝ (fderiv ℝ F) x v) := by
  let R := (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    ((hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
      (by norm_num) x).hasFDerivAt
  have hc := R.hasFDerivAt.comp x hd
  have he : hessian F x = R.comp (fderiv ℝ (fderiv ℝ F) x) := hc.fderiv
  rw [he]
  rfl

/-- Schwarz symmetry for the Hessian defined as the derivative of the
gradient; no symmetry assumption is added to the loss model. -/
theorem hessian_inner_symmetric {d : ℕ} {F : Point d → ℝ}
    (hF : ContDiff ℝ 2 F) (x u v : Point d) :
    ⟪hessian F x u, v⟫_ℝ = ⟪hessian F x v, u⟫_ℝ := by
  rw [hessian_apply_eq_second_derivative hF, hessian_apply_eq_second_derivative hF,
    InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v

theorem hessian_isSymmetric {d : ℕ} {F : Point d → ℝ}
    (hF : ContDiff ℝ 2 F) (x : Point d) :
    (hessian F x).toLinearMap.IsSymmetric := by
  intro u v
  exact (hessian_inner_symmetric hF x u v).trans (real_inner_comm _ _)

/-- The deterministic bound used in the stochastic eigenvalue reduction. -/
def eigenHessianBound (P : Parameters) : ℝ := P.gradientLip + P.hessianBound

theorem eigenHessianBound_pos (P : Parameters) : 0 < eigenHessianBound P :=
  add_pos P.gradientLip_pos P.hessianBound_pos

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.population_hessian_symmetric (h : CommonLoss μ P ν F f)
    (x : Point d) : (hessian F x).toLinearMap.IsSymmetric :=
  hessian_isSymmetric h.population_smooth x

/-- One probability-one set works simultaneously at every query point. -/
theorem CommonLoss.sample_hessian_symmetric_bounded (h : CommonLoss μ P ν F f) :
    ∀ᵐ z ∂μ, ∀ x, (hessian (f z) x).toLinearMap.IsSymmetric ∧
      ‖hessian (f z) x‖ ≤ eigenHessianBound P := by
  filter_upwards [h.sample_regularity, h.global_hessian_bound] with z hz hb
  intro x
  refine ⟨hessian_isSymmetric hz.1 x, ?_⟩
  have hn := norm_add_le (hessian (f z) x - hessian F x) (hessian F x)
  rw [sub_add_cancel] at hn
  have hp := h.population_hessian_norm x
  dsimp [eigenHessianBound]
  linarith [hb x]

end
end SecondOrder
