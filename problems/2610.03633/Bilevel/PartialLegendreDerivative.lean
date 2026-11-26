import Bilevel.PartialLegendreBasic
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Actual inverse derivative of the conjugate gradient. Invertibility of
I+B is constructed from the small norm budget, not supplied as a hypothesis. -/
noncomputable section
open scoped Topology
namespace Bilevel.PartialLegendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {δ : NNReal} (hδ : δ < 1)

def linearPerturbation (B : E →L[ℝ] E) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+B

omit [CompleteSpace E] in
theorem small_linear_lipschitz (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) : LipschitzWith δ B := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

include hδ
theorem linearPerturbation_bijective (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) :
    Function.Bijective (linearPerturbation B) := by
  have hl := small_linear_lipschitz B hB
  constructor
  · intro x y hxy
    have hx := solution_of_equation hδ hl (linearPerturbation B x) x rfl
    have hy := solution_of_equation hδ hl (linearPerturbation B x) y hxy.symm
    exact hx.trans hy.symm
  · intro y
    exact ⟨solution hδ hl y,solution_equation hδ hl y⟩

def linearEquiv (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (linearPerturbation B)
    (LinearMap.ker_eq_bot.mpr (linearPerturbation_bijective hδ B hB).1)
    (LinearMap.range_eq_top.mpr (linearPerturbation_bijective hδ B hB).2)

theorem linearEquiv_apply (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) (z : E) :
    linearEquiv hδ B hB z=z+B z := rfl

theorem linearEquiv_symm_solution (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) (y : E) :
    (linearEquiv hδ B hB).symm y=solution hδ (small_linear_lipschitz B hB) y := by
  apply solution_of_equation
  exact (linearEquiv hδ B hB).apply_symm_apply y

theorem linearEquiv_inverse_bound (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ)) :
    ‖((linearEquiv hδ B hB).symm : E →L[ℝ] E)‖ ≤ 1/(1-(δ:ℝ)) := by
  have hd : 0 < 1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hh := solution_lipschitz_bound hδ (small_linear_lipschitz B hB) y 0
  rw [← linearEquiv_symm_solution hδ B hB y,
    ← linearEquiv_symm_solution hδ B hB 0,map_zero,sub_zero,sub_zero] at hh
  convert hh using 1
  ring

theorem solution_hasFDerivAt {G : E → E} (hG : LipschitzWith δ G) (y : E)
    (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ))
    (hDG : HasFDerivAt G B (solution hδ hG y)) :
    HasFDerivAt (solution hδ hG) ((linearEquiv hδ B hB).symm : E →L[ℝ] E) y := by
  have hf : HasFDerivAt (fun z => z+G z)
      (linearEquiv hδ B hB : E →L[ℝ] E) (solution hδ hG y) := by
    exact (hasFDerivAt_id _).add hDG
  exact HasFDerivAt.of_local_left_inverse (solution_continuous hδ hG).continuousAt hf
    (Filter.Eventually.of_forall (solution_equation hδ hG))

theorem conjugate_gradient_hasFDerivAt {G : E → E} (hG : LipschitzWith δ G)
    (P : E → ℝ) (hP : ∀ z,HasGradientAt P (G z) z) (y : E)
    (B : E →L[ℝ] E) (hB : ‖B‖ ≤ (δ:ℝ))
    (hDG : HasFDerivAt G B (solution hδ hG y)) :
    HasFDerivAt (gradient (conjugate hδ hG P))
      ((linearEquiv hδ B hB).symm : E →L[ℝ] E) y := by
  have he : gradient (conjugate hδ hG P)=solution hδ hG :=
    funext (conjugate_gradient hδ hG P hP)
  rw [he]
  exact solution_hasFDerivAt hδ hG y B hB hDG

end Bilevel.PartialLegendre
