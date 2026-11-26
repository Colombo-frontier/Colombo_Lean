import VIReference.Pilot.Halving
import VIReference.Pilot.ModelExistence
import VIReference.Pilot.UpperInterfaces

open Set
open scoped RealInnerProductSpace BigOperators

namespace VIReference.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Extract the already evaluated operator value from the zeroth jet slot. -/
noncomputable def symmetricJetValue (data : VIPublicData E)
    (jet : SymmetricExactJet E data.p) : E :=
  (jet ⟨0, lt_of_lt_of_le (by omega) data.p_ge_two⟩).1 (fun i => Fin.elim0 i)

/-- Taylor polynomial computed solely from the public center and returned jet. -/
noncomputable def taylorModelFromJet (data : VIPublicData E)
    (x : E) (jet : SymmetricExactJet E data.p) (y : E) : E :=
  ∑ j : Fin data.p, (Nat.factorial j.1 : ℝ)⁻¹ •
    (jet j).1 (fun _ ↦ y - x)

theorem symmetricJetValue_exact (data : VIPublicData E) (F : E → E)
    (oracle : ExactSymmetricJetOracle data F) (x : E) :
    symmetricJetValue data (oracle.answer x) = F x := by
  rw [symmetricJetValue, oracle.exact]
  simp [iteratedFDeriv_zero_eq_comp]

theorem taylorModelFromJet_exact (data : VIPublicData E) (F : E → E)
    (oracle : ExactSymmetricJetOracle data F) (x y : E) :
    taylorModelFromJet data x (oracle.answer x) y =
      taylorModel data.p F x y := by
  rw [taylorModelFromJet, taylorModel]
  simp_rw [oracle.exact]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    (Nat.factorial j : ℝ)⁻¹ • iteratedFDeriv ℝ j F x (fun _ ↦ y - x)) data.p

/-- Checkable model-step predicate expressed entirely through public data and
one oracle answer. -/
def IsKnownModelStep (data : VIPublicData E) (x : data.X)
    (jet : SymmetricExactJet E data.p) (yn : data.X × E) : Prop :=
  yn.2 ∈ normalCone data.X yn.1.1 ∧
    taylorModelFromJet data x.1 jet yn.1.1 +
      (tensorBetaCoefficient data.p * data.Lp * ‖yn.1.1 - x.1‖ ^ (data.p - 1)) •
        (yn.1.1 - x.1) + yn.2 = 0

end
end VIReference.Pilot
