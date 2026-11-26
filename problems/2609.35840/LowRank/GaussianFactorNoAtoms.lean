import LowRank.GaussianLinearNoAtoms
import LowRank.FactorRangeConstraint

/-! Conditional on a complete factor state, no nonzero fixed matrix can
annihilate the full input with positive probability while a Gaussian
residual column remains. This avoids a separate Grassmannian construction. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem representedMatrix_annihilator_ne_ae {d t q r s : ℕ} (hs : 0 < s)
    {v : NNReal} (hv : v ≠ 0) (st : FactorData d t q r s)
    (hst : st.Orthogonal) (hA : IsUnit st.1.1)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q ≠ 0) :
    ∀ᵐ D ∂iidMatrixLaw r s v, Q * representedMatrix st D ≠ 0 := by
  by_cases hr : (Q * st.2.1).submatrix id Sum.inr = 0
  · exact Filter.Eventually.of_forall (fun D h => hQ
      (representedMatrix_annihilator_zero_of_residual_coefficient_zero st hst hA Q D h hr))
  · filter_upwards [iidMatrixLaw_mul_ne_ae hs hv ((Q * st.2.1).submatrix id Sum.inr) hr 0] with D hD
    intro h
    exact hD (representedMatrix_annihilator_residual st hst Q D h)

theorem representedMatrix_not_contained_ae {d t q r s : ℕ} (hs : 0 < s)
    {v : NNReal} (hv : v ≠ 0) (st : FactorData d t q r s)
    (hst : st.Orthogonal) (hA : IsUnit st.1.1)
    (P : Matrix (Fin d) (Fin d) ℝ) (hP : P ≠ 1) :
    ∀ᵐ D ∂iidMatrixLaw r s v, (1 - P) * representedMatrix st D ≠ 0 := by
  apply representedMatrix_annihilator_ne_ae hs hv st hst hA (1 - P)
  intro h
  exact hP (sub_eq_zero.mp h).symm

end
end LowRank
