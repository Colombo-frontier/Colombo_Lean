import FreshGradientMinimax.PathCoordinates
import FreshGradientMinimax.PathHyperbolic

/-! The endpoint column of the actual positive-path inverse. The hyperbolic
vector is checked at every coordinate, including both endpoint equations. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def pathGreenVector (β θ : ℝ) (n : ℕ) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => pathGreenSequence β θ n (i.val + 1))

@[simp]
theorem pathGreenVector_apply (β θ : ℝ) (n : ℕ) (i : Fin n) :
    pathGreenVector β θ n i = pathGreenSequence β θ n (i.val + 1) := rfl

theorem pathGreenVector_prev (β θ : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    Fin.cons (α := fun _ => ℝ) 0 (fun j => pathGreenVector β θ (n + 1) j) i.castSucc =
      pathGreenSequence β θ (n + 1) i.val := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · rw [← Fin.succ_castSucc, Fin.cons_succ]
    rfl

theorem pathGreenVector_next (β θ : ℝ) (n : ℕ) (i : Fin n) :
    Fin.snoc (α := fun _ => ℝ) (fun j => pathGreenVector β θ (n + 1) j) 0 i.castSucc.succ =
      pathGreenSequence β θ (n + 1) (i.val + 2) := by
  rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  rfl

theorem pathGreenVector_root {μ β θ : ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (hc : μ + 2 * β = 2 * β * Real.cosh θ) (n : ℕ) :
    normalOperator (pathIncidence (fun _ : Fin (n + 2) => 1)) μ β
      (pathGreenVector β θ (n + 1)) = EuclideanSpace.single (Fin.last n) 1 := by
  ext i
  rw [normalPath_coordinate, pathGreenVector_prev]
  simp only [one_pow, one_add_one_eq_two, mul_one]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have hr := pathGreenSequence_recurrence hc (n + 1) n
    have hb := pathGreenSequence_boundary hβ hθ (n + 1)
    simp only [Fin.succ_last, Fin.snoc_last, pathGreenVector_apply, Fin.val_last,
      EuclideanSpace.single_apply, if_pos rfl, mul_zero, sub_zero, ↓reduceIte]
    have he : n + 1 + 1 = n + 2 := by omega
    rw [he] at hb
    nlinarith only [hr, hb]
  · rw [pathGreenVector_next]
    simp only [pathGreenVector_apply, Fin.coe_castSucc, EuclideanSpace.single_apply,
      if_neg (Fin.castSucc_ne_last k)]
    convert pathGreenSequence_recurrence hc (n + 1) k.val using 1; ring

theorem positivePath_inverse_last {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) (n : ℕ) :
    normalInverse (pathIncidence (fun _ : Fin (n + 2) => 1)) μ β hμ hβ.le
      (EuclideanSpace.single (Fin.last n) 1) = pathGreenVector β (pathTheta μ β) (n + 1) :=
  normalInverse_eq_of_root _ hμ hβ.le
    (pathGreenVector_root hβ (pathTheta_pos hμ hβ) (pathTheta_coefficient hμ hβ) n)

theorem positivePath_endpoint_entry {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) (n : ℕ) :
    normalInverse (pathIncidence (fun _ : Fin (n + 2) => 1)) μ β hμ hβ.le
      (EuclideanSpace.single (Fin.last n) 1) 0 =
        Real.sinh (pathTheta μ β) / (β * Real.sinh (((n : ℝ) + 2) * pathTheta μ β)) := by
  rw [positivePath_inverse_last hμ hβ]
  simp [pathGreenSequence, Nat.cast_add, Nat.cast_one]
  congr 3
  ring

theorem positivePath_endpoint_positive {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) (n : ℕ) :
    0 < normalInverse (pathIncidence (fun _ : Fin (n + 2) => 1)) μ β hμ hβ.le
      (EuclideanSpace.single (Fin.last n) 1) 0 := by
  rw [positivePath_endpoint_entry hμ hβ]
  have hθ := pathTheta_pos hμ hβ
  exact div_pos (Real.sinh_pos_iff.mpr hθ)
    (mul_pos hβ (Real.sinh_pos_iff.mpr (by positivity)))

end FreshGradientMinimax
