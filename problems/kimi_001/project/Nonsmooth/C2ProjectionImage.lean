import Nonsmooth.C2PotentialPlaneRegularity
import Nonsmooth.RegularVectorNoSpike

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def regularProjectionImageOfC2Plane (μ : Measure E) (u v : E) {U : F → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    (a b : F) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ho : inner ℝ a b = (0 : ℝ))
    (hlaw : μ.map (fun z => (inner ℝ z u, inner ℝ v z)) =
      potentialJointLaw (fun t x => U (planePoint a b t x))) : RegularProjectionImage μ u v :=
  let hp := c2StrongQuadraticPotential_plane_regular_both hU hρ a b ha hb ho
  { potential := fun t x => U (planePoint a b t x)
    forward := Classical.choose hp.1
    backward := Classical.choose hp.2
    moments := Classical.choose_spec hp.1
    law := hlaw }

theorem regularProjectionImage_exists_of_c2_plane (μ : Measure E) (u v : E) {U : F → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    (a b : F) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ho : inner ℝ a b = (0 : ℝ))
    (hlaw : μ.map (fun z => (inner ℝ z u, inner ℝ v z)) =
      potentialJointLaw (fun t x => U (planePoint a b t x))) : Nonempty (RegularProjectionImage μ u v) :=
  ⟨regularProjectionImageOfC2Plane μ u v hU hρ a b ha hb ho hlaw⟩

end
end Nonsmooth
