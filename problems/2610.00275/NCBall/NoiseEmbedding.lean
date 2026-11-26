import NCBall.Geometry
import NCBall.GaussianUpperTail

/-! # Embedding transverse Gaussian coordinates in the ambient Euclidean space -/

noncomputable section
open scoped BigOperators
namespace NCBall

def transverseVector {n : ℕ} (z : Fin n → ℝ) : Space n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.cons 0 z)

theorem transverseVector_clock {n : ℕ} (z : Fin n → ℝ) : transverseVector z 0 = 0 := by
  rfl

theorem transverseVector_norm_sq {n : ℕ} (z : Fin n → ℝ) :
    ‖transverseVector z‖ ^ 2 = coordinateNormSq z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [transverseVector, coordinateNormSq, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]

theorem transverseVector_continuous (n : ℕ) : Continuous (@transverseVector n) := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))
  · simpa using continuous_apply j

theorem transverseVector_norm_le_two_iff {n : ℕ} (z : Fin n → ℝ) :
    ‖transverseVector z‖ ≤ 2 ↔ coordinateNormSq z ≤ 4 := by
  have he := transverseVector_norm_sq z
  have hn := norm_nonneg (transverseVector z)
  constructor <;> intro h <;> nlinarith

/-- Extend the finite array by zero; only indices below M enter the objective. -/
def roomNoise {n M : ℕ} (z : Fin M → Fin n → ℝ) (j : ℕ) : Space n :=
  if hj : j < M then transverseVector (z ⟨j, hj⟩) else 0

theorem roomNoise_clock {n M : ℕ} (z : Fin M → Fin n → ℝ) (j : ℕ) : roomNoise z j 0 = 0 := by
  unfold roomNoise
  split <;> simp [transverseVector_clock]

theorem roomNoise_norm_sq {n M : ℕ} (z : Fin M → Fin n → ℝ) {j : ℕ} (hj : j < M) :
    ‖roomNoise z j‖ ^ 2 = coordinateNormSq (z ⟨j, hj⟩) := by
  simp only [roomNoise, dif_pos hj, transverseVector_norm_sq]

theorem roomNoise_continuous (n M j : ℕ) :
    Continuous (fun z : Fin M → Fin n → ℝ => roomNoise z j) := by
  unfold roomNoise
  split
  · exact (transverseVector_continuous n).comp (continuous_apply _)
  · exact continuous_const

end NCBall
