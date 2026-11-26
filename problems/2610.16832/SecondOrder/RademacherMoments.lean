import SecondOrder.MixedSigns
import SecondOrder.Model

open MeasureTheory
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

@[simp] theorem signValue_sq (b : Bool) : signValue b ^ 2 = 1 := by
  cases b <;> norm_num [signValue]

theorem uniformMean_bool (f : Bool → ℝ) :
    uniformMean f = (f false + f true) / 2 := by
  simp [uniformMean_eq, Fintype.sum_bool, add_comm, div_eq_mul_inv, mul_comm]

theorem sign_affine_second (a b : ℝ) :
    uniformMean (fun w : Bool => (a + b * signValue w)^2) = a^2 + b^2 := by
  rw [uniformMean_bool]
  norm_num [signValue]
  ring

theorem sign_affine_fourth (a b : ℝ) :
    uniformMean (fun w : Bool => (a + b * signValue w)^4) =
      a^4 + 6 * b^2 * a^2 + b^4 := by
  rw [uniformMean_bool]
  norm_num [signValue]
  ring

def rademacherSum {d : ℕ} (a : Fin d → ℝ) (w : Fin d → Bool) : ℝ :=
  ∑ i, a i * signValue (w i)

theorem rademacherSum_snoc {d : ℕ} (a : Fin (d+1) → ℝ)
    (w : Fin d → Bool) (b : Bool) :
    rademacherSum a (Fin.snoc w b) =
      rademacherSum (fun i => a i.castSucc) w + a (Fin.last d) * signValue b := by
  simp [rademacherSum, Fin.sum_univ_castSucc]

theorem rademacherSum_second {d : ℕ} (a : Fin d → ℝ) :
    uniformMean (fun w => rademacherSum a w ^ 2) = ∑ i, a i ^ 2 := by
  induction d with
  | zero => simp [rademacherSum]
  | succ d ih =>
    rw [uniformMean_snoc d]
    simp_rw [rademacherSum_snoc, sign_affine_second]
    rw [uniformMean_add, ih, uniformMean_const, Fin.sum_univ_castSucc]

/-- Independent fair signs have fourth moment at most three times the square
of the second moment, for every deterministic coefficient vector. -/
theorem rademacherSum_fourth {d : ℕ} (a : Fin d → ℝ) :
    uniformMean (fun w => rademacherSum a w ^ 4) ≤ 3 * (∑ i, a i ^ 2)^2 := by
  induction d with
  | zero => simp [rademacherSum]
  | succ d ih =>
    rw [uniformMean_snoc d]
    simp_rw [rademacherSum_snoc, sign_affine_fourth]
    rw [uniformMean_add, uniformMean_add, uniformMean_mul,
      rademacherSum_second, uniformMean_const, Fin.sum_univ_castSucc]
    have hi := ih (fun i => a i.castSucc)
    nlinarith [sq_nonneg (a (Fin.last d)^2)]

/-- The initialization uses only d independent fair signs; it does not
depend on a Hessian or on an unknown eigenvector. -/
def rademacherVector {d : ℕ} (w : Fin d → Bool) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => signValue (w i))

theorem rademacherVector_norm_sq {d : ℕ} (w : Fin d → Bool) :
    ‖rademacherVector w‖^2 = (d : ℝ) := by
  simp [rademacherVector, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem rademacherVector_inner {d : ℕ} (g : Point d) (w : Fin d → Bool) :
    ⟪g, rademacherVector w⟫_ℝ = rademacherSum g w := by
  simp [rademacherVector, rademacherSum, PiLp.inner_apply, real_inner_comm, mul_comm]

theorem rademacherVector_second {d : ℕ} (g : Point d) :
    uniformMean (fun w => ⟪g, rademacherVector w⟫_ℝ ^ 2) = ‖g‖^2 := by
  simp_rw [rademacherVector_inner]
  rw [rademacherSum_second]
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem rademacherVector_fourth {d : ℕ} (g : Point d) :
    uniformMean (fun w => ⟪g, rademacherVector w⟫_ℝ ^ 4) ≤ 3 * ‖g‖^4 := by
  simp_rw [rademacherVector_inner]
  have h := rademacherSum_fourth (fun i => g i)
  have he : (∑ i, g i ^ 2) = ‖g‖^2 := by
    simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [he] at h
  convert h using 1 <;> ring

end
end SecondOrder
