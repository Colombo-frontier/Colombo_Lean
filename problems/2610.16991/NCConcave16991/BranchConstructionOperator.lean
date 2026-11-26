import NCConcave16991.BranchGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The actual branching path operator and its inverse

The operator is the mass plus the Gram operators of the literal branch
differences. Coercivity constructs its inverse in finite dimensions and
proves the inverse-energy estimate used in the source dual-radius bound.
-/

namespace NCConcave16991.BranchConstruction

noncomputable section

open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)]
  (B : ∀ t : Fin N, BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

abbrev Layers := PiLp 2 V

def edge (t : Fin N) : Layers V →L[ℝ] V t.succ :=
  PiLp.proj 2 V t.succ - (B t).normalizedIsometry.toContinuousLinearMap.comp (PiLp.proj 2 V t.castSucc)

theorem edge_apply (t : Fin N) (w : Layers V) :
    edge V B t w = w t.succ - (B t).normalizedIsometry (w t.castSucc) := rfl

def massOperator (μ : ℝ) : Layers V →L[ℝ] Layers V :=
  μ • ContinuousLinearMap.id ℝ (Layers V) + ∑ t : Fin N, (edge V B t).adjoint.comp (edge V B t)

theorem massOperator_bilinear (μ : ℝ) (x y : Layers V) :
    ⟪x, massOperator V B μ y⟫_ℝ = μ * ⟪x, y⟫_ℝ + ∑ t : Fin N, ⟪edge V B t x, edge V B t y⟫_ℝ := by
  simp [massOperator, inner_add_right, inner_sum, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right]

theorem massOperator_energy (μ : ℝ) (w : Layers V) :
    ⟪w, massOperator V B μ w⟫_ℝ = μ * ‖w‖ ^ 2 + ∑ t : Fin N, ‖edge V B t w‖ ^ 2 := by
  rw [massOperator_bilinear]
  simp only [real_inner_self_eq_norm_sq]

theorem massOperator_energy_literal (μ : ℝ) (w : Layers V) :
    ⟪w, massOperator V B μ w⟫_ℝ = μ * (∑ j, ‖w j‖ ^ 2) +
      ∑ t : Fin N, ‖w t.succ - (B t).normalizedIsometry (w t.castSucc)‖ ^ 2 := by
  rw [massOperator_energy, PiLp.norm_sq_eq_of_L2]
  rfl

theorem massOperator_coercive (μ : ℝ) (w : Layers V) :
    μ * ‖w‖ ^ 2 ≤ ⟪w, massOperator V B μ w⟫_ℝ := by
  rw [massOperator_energy]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem massOperator_symmetric (μ : ℝ) (x y : Layers V) :
    ⟪x, massOperator V B μ y⟫_ℝ = ⟪massOperator V B μ x, y⟫_ℝ := by
  calc
    _ = μ * ⟪x, y⟫_ℝ + ∑ t : Fin N, ⟪edge V B t x, edge V B t y⟫_ℝ := massOperator_bilinear V B μ x y
    _ = μ * ⟪y, x⟫_ℝ + ∑ t : Fin N, ⟪edge V B t y, edge V B t x⟫_ℝ := by simp only [real_inner_comm]
    _ = ⟪y, massOperator V B μ x⟫_ℝ := (massOperator_bilinear V B μ y x).symm
    _ = _ := real_inner_comm _ _

theorem massOperator_injective (μ : ℝ) (hμ : 0 < μ) : Function.Injective (massOperator V B μ) := by
  intro x y hxy
  have hz : massOperator V B μ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hh := massOperator_coercive V B μ (x - y)
  rw [hz, inner_zero_right] at hh
  have hs : ‖x - y‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hμ).mp (by simpa using hh)
  have hn : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable [∀ j, FiniteDimensional ℝ (V j)]

def operatorEquiv (μ : ℝ) (hμ : 0 < μ) : Layers V ≃ₗ[ℝ] Layers V :=
  LinearEquiv.ofInjectiveEndo (massOperator V B μ).toLinearMap (massOperator_injective V B μ hμ)

def inverse (μ : ℝ) (hμ : 0 < μ) : Layers V →L[ℝ] Layers V :=
  (operatorEquiv V B μ hμ).symm.toLinearMap.toContinuousLinearMap

theorem mass_inverse (μ : ℝ) (hμ : 0 < μ) (h : Layers V) :
    massOperator V B μ (inverse V B μ hμ h) = h :=
  (operatorEquiv V B μ hμ).apply_symm_apply h

theorem inverse_mass (μ : ℝ) (hμ : 0 < μ) (h : Layers V) :
    inverse V B μ hμ (massOperator V B μ h) = h :=
  (operatorEquiv V B μ hμ).symm_apply_apply h

/-- The source spectral inequality M^-2 ≤ μ^-1 M^-1, derived directly
from the actual coercive operator and its constructed inverse. -/
theorem inverse_energy_bound (μ : ℝ) (hμ : 0 < μ) (h : Layers V) :
    μ * ‖inverse V B μ hμ h‖ ^ 2 ≤ ⟪h, inverse V B μ hμ h⟫_ℝ := by
  have hh := massOperator_coercive V B μ (inverse V B μ hμ h)
  rw [mass_inverse, real_inner_comm] at hh
  exact hh

theorem inverse_energy_nonneg (μ : ℝ) (hμ : 0 < μ) (h : Layers V) :
    0 ≤ ⟪h, inverse V B μ hμ h⟫_ℝ :=
  (mul_nonneg hμ.le (sq_nonneg _)).trans (inverse_energy_bound V B μ hμ h)

theorem inverse_symmetric (μ : ℝ) (hμ : 0 < μ) (x y : Layers V) :
    ⟪x, inverse V B μ hμ y⟫_ℝ = ⟪inverse V B μ hμ x, y⟫_ℝ := by
  calc
    _ = ⟪massOperator V B μ (inverse V B μ hμ x), inverse V B μ hμ y⟫_ℝ := by rw [mass_inverse]
    _ = ⟪inverse V B μ hμ x, massOperator V B μ (inverse V B μ hμ y)⟫_ℝ :=
      (massOperator_symmetric V B μ _ _).symm
    _ = _ := by rw [mass_inverse]

theorem inverse_norm_bound (μ : ℝ) (hμ : 0 < μ) (h : Layers V) :
    ‖inverse V B μ hμ h‖ ≤ ‖h‖ / μ := by
  apply (le_div_iff₀ hμ).mpr
  by_cases hz : inverse V B μ hμ h = 0
  · simp [hz]
  have hp : 0 < ‖inverse V B μ hμ h‖ := norm_pos_iff.mpr hz
  have hh := (inverse_energy_bound V B μ hμ h).trans (real_inner_le_norm h _)
  nlinarith

end

end NCConcave16991.BranchConstruction
