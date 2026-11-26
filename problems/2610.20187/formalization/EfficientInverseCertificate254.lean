import EfficientInverseHeight254
import EfficientInverseCost254

open Matrix
namespace Paper254

def generalInverseStageHeight (d b : ℕ) :=
  inverseHeight d (2*b+d)+5*inverseHeight d (inverseHeight d (2*b+d))+2*d+3

/-- A single certificate for the executable inverse: exact value, cubic
arithmetic count, polynomial output encoding, and a uniform polynomial
encoding bound on every recursive intermediate matrix. -/
theorem countedGeneralInverse_certificate {d b : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (hu : IsUnit A) (hheight : MatrixHeight A b) :
    (countedGeneralInverse A).1=A⁻¹ ∧
    (countedGeneralInverse A).2≤12*d^3 ∧
    MatrixHeight (countedGeneralInverse A).1 (inverseHeight d b) ∧
    ∀ {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ),
      SchurDescendant (Aᵀ*A) B→
      SchurStageHeight B (efficientInverse (inverseSchur B)) (generalInverseStageHeight d b) := by
  refine ⟨countedGeneralInverse_correct A hu,countedGeneralInverse_cost A,?_,?_⟩
  · rw [countedGeneralInverse_correct A hu]
    exact hheight.inv hu
  · intro n B hB
    apply (efficientGeneralInverse_all_stages_height A hu hheight B hB).mono
    have hn := hB.dimension_le (rational_normal_positive A hu)
    dsimp [generalInverseStageHeight]
    omega

end Paper254
#print axioms Paper254.countedGeneralInverse_certificate
