import GradientHessian.LeafFunctions

/-! A coercive quadratic bound in the genuine norm of all physical blocks. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates
open scoped InnerProductSpace

def coercivityConstant : ℝ := 4/Inner.lastRadius Inner.absoluteDepth

theorem coercivityConstant_pos : 0 < coercivityConstant := by
  norm_num [coercivityConstant, Inner.lastRadius, Inner.absoluteDepth]

theorem coercivityConstant_le_half : coercivityConstant ≤ 1/2 := by
  norm_num [coercivityConstant, Inner.lastRadius, Inner.absoluteDepth]

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem inner_radius_le_last (k : ℕ) (j : Fin (k+2)) : Inner.radius k j ≤ Inner.lastRadius k := by
  simp only [Inner.radius, LatchChain.sourceScale, one_mul, Inner.lastRadius]
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)

theorem public_memory_lower (Z : Space Y E m) :
    coercivityConstant*‖tasks Y E m (Inner.absoluteDepth+2) Z‖^2 ≤
      Inner.publicQuadratic m Inner.absoluteDepth Z := by
  have hcoef (j : Fin (Inner.absoluteDepth+2)) :
      coercivityConstant ≤ 4/Inner.radius Inner.absoluteDepth j :=
    div_le_div_of_nonneg_left (by norm_num) (Inner.radius_pos _ j) (inner_radius_le_last _ j)
  calc
    _ = ∑ i, ∑ j, coercivityConstant*‖tasks Y E m (Inner.absoluteDepth+2) Z i j‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    _ ≤ _ := by
      unfold Inner.publicQuadratic LatchChain.publicQuadratic
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcoef j) (sq_nonneg _)

theorem physical_norm_square (Z : Space Y E m) :
    ‖Z‖^2 = ‖numerical Y E m (Inner.absoluteDepth+2) Z‖^2 +
      ‖tasks Y E m (Inner.absoluteDepth+2) Z‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 Z

theorem objective_coercive_bound (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    coercivityConstant*‖Z‖^2 - Inner.innerConstant*m ≤ objective A b a v Z := by
  have h := objective_energy hm A hA b a v Z
  have hmem := public_memory_lower Z
  have hy := mul_le_mul_of_nonneg_right coercivityConstant_le_half
    (sq_nonneg ‖numerical Y E m (Inner.absoluteDepth+2) Z‖)
  rw [physical_norm_square]
  linarith

end GradientHessian.Leaf
