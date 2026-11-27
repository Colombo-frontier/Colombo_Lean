import AdaptiveSphereCoordinateRotations

open MeasureTheory Set
open scoped Matrix RealInnerProductSpace

namespace Task006.AdaptiveSphereCoordinateRotations
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
noncomputable section

def permutationOrthogonal (n : ℕ) (e : Equiv.Perm (Fin n)) : OrthogonalGroup n :=
  orthogonalMatrixOfLinearIsometryEquiv (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)

theorem permutationOrthogonal_action (n : ℕ) (e : Equiv.Perm (Fin n))
    (x : E n) (i : Fin n) : (action (permutationOrthogonal n e) x) i = x (e.symm i) := by
  rw [permutationOrthogonal,action_matrixOfIsometry]
  rfl

def swapOrthogonal {n : ℕ} (i j : Fin n) : OrthogonalGroup n :=
  permutationOrthogonal n (Equiv.swap i j)

theorem swapOrthogonal_action_first {n : ℕ} (i j : Fin n) (x : E n) :
    (action (swapOrthogonal i j) x) i = x j := by
  rw [swapOrthogonal,permutationOrthogonal_action]
  simp

theorem swapOrthogonal_action_second {n : ℕ} (i j : Fin n) (x : E n) :
    (action (swapOrthogonal i j) x) j = x i := by
  rw [swapOrthogonal,permutationOrthogonal_action]
  simp

#print axioms permutationOrthogonal_action
#print axioms swapOrthogonal_action_first
#print axioms swapOrthogonal_action_second
end
end Task006.AdaptiveSphereCoordinateRotations
