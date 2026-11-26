import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

/-! Exact derivatives of a bounded symmetric quadratic plus a linear term. -/
noncomputable section
open scoped InnerProductSpace ContDiff BigOperators

namespace MatchingBounds1005.SymmetricQuadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Q : E →L[ℝ] E) (c : E →L[ℝ] ℝ)

def energy (x : E) : ℝ := (1 / 2 : ℝ) * ⟪x, Q x⟫_ℝ + c x

def hessian : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp Q

theorem smooth : ContDiff ℝ ∞ (energy Q c) :=
  (contDiff_const.mul (contDiff_id.inner ℝ Q.contDiff)).add c.contDiff

theorem hasFDerivAt (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ) (x : E) :
    HasFDerivAt (energy Q c) (innerSL ℝ (Q x) + c) x := by
  have h := (((hasFDerivAt_id (𝕜 := ℝ) x).inner ℝ Q.hasFDerivAt).const_mul (1 / 2 : ℝ)).add
    c.hasFDerivAt
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, innerSL_apply,
    id_eq, smul_eq_mul]
  rw [hsym x v, real_inner_comm (Q x) v]
  ring

theorem fderiv_eq (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ) :
    fderiv ℝ (energy Q c) = fun x => hessian Q x + c :=
  funext (fun x => (hasFDerivAt Q c hsym x).fderiv)

theorem second_apply (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ)
    (x : E) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (energy Q c) x v = ⟪Q (v 0), v 1⟫_ℝ := by
  rw [iteratedFDeriv_two_apply, fderiv_eq Q c hsym]
  have hH : HasFDerivAt (hessian Q : E → E →L[ℝ] ℝ) (hessian Q) x :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (hessian Q) (x := x)
  have h := hH.add (hasFDerivAt_const (𝕜 := ℝ) c x)
  have hd : fderiv ℝ (fun y => hessian Q y + c) x = hessian Q := by
    simpa only [add_zero] using h.fderiv
  rw [hd]
  rfl

theorem second_bound (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ) (x : E) :
    ‖iteratedFDeriv ℝ 2 (energy Q c) x‖ ≤ ‖Q‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg Q)
  intro v
  rw [second_apply Q c hsym, Real.norm_eq_abs]
  calc
    _ ≤ ‖Q (v 0)‖ * ‖v 1‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖Q‖ * ‖v 0‖) * ‖v 1‖ := mul_le_mul_of_nonneg_right (Q.le_opNorm _) (norm_nonneg _)
    _ = _ := by simp [Fin.prod_univ_succ, mul_assoc]

theorem higher_zero (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ) (k : ℕ) :
    iteratedFDeriv ℝ (k + 3) (energy Q c) = 0 := by
  have hconst : iteratedFDeriv ℝ 2 (energy Q c) =
      fun _ => iteratedFDeriv ℝ 2 (energy Q c) 0 := by
    funext x
    ext v
    rw [second_apply Q c hsym, second_apply Q c hsym]
  induction k with
  | zero =>
    funext x
    ext v
    rw [iteratedFDeriv_succ_apply_left, hconst]
    simp
  | succ k ih =>
    funext x
    ext v
    change iteratedFDeriv ℝ ((k + 3) + 1) (energy Q c) x v = 0
    rw [iteratedFDeriv_succ_apply_left, ih]
    simp

end MatchingBounds1005.SymmetricQuadratic
