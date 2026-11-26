import Nonsmooth.QuadraticSliceGrowth
import Nonsmooth.DominatedSliceNoSpike

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {ι : Type} [Fintype ι]

def quadraticSoftSliceRegularFamily {ρ : ℝ} (hρ : 1 < ρ) (A B C D E F : ι → ℝ)
    (h : ∀ i p q, 0 ≤ C i * p ^ 2 + 2 * B i * p * q + A i * q ^ 2) :
    RegularStrongSliceFamily (softSlicePotential ρ (quadraticSliceConstraints A B C D E F)) :=
  softSliceRegularFamily hρ _ (quadraticSliceConstraints_hessian A B C D E F h)
    (quadraticSoftSlice_polynomial_growth ρ A B C D E F)

theorem quadraticSoftSlice_moment_continuity {ρ : ℝ} (hρ : 1 < ρ) (A B C D E F : ι → ℝ)
    (h : ∀ i p q, 0 ≤ C i * p ^ 2 + 2 * B i * p * q + A i * q ^ 2) :
    RegularSliceMomentContinuity (softSlicePotential ρ (quadraticSliceConstraints A B C D E F))
      (quadraticSoftSliceRegularFamily hρ A B C D E F h) :=
  softSlice_regular_moment_continuity hρ _ (quadraticSliceConstraints_hessian A B C D E F h)
    (quadraticSoftSlice_polynomial_growth ρ A B C D E F)

theorem quadraticSoftSlice_potential_swap (ρ : ℝ) (A B C D E F : ι → ℝ) :
    softSlicePotential ρ (quadraticSliceConstraints C B A E D F) =
      fun t x => softSlicePotential ρ (quadraticSliceConstraints A B C D E F) x t := by
  funext t x
  unfold softSlicePotential
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    dsimp only [quadraticSliceConstraints]
    ring

theorem quadraticSoftSlice_conditional_no_spike {ρ : ℝ} (hρ : 1 < ρ) (A B C D E F : ι → ℝ)
    (h : ∀ i p q, 0 ≤ C i * p ^ 2 + 2 * B i * p * q + A i * q ^ 2) :
    let V := softSlicePotential ρ (quadraticSliceConstraints A B C D E F)
    ∀ᵐ y ∂realDensityLaw (potentialPartition V),
      (y - ∫ t : ℝ, t ∂realDensityLaw (potentialPartition V)) ^ 2 +
        ((∫ x : ℝ, x ∂condDistrib Prod.snd Prod.fst (potentialJointLaw V) y) -
          ∫ p : ℝ × ℝ, p.2 ∂potentialJointLaw V) ^ 2 ≤
      72 * (1 + Real.log (1 / min
        (cdf (realDensityLaw (potentialPartition V)) y)
        (1 - cdf (realDensityLaw (potentialPartition V)) y))) := by
  let V := softSlicePotential ρ (quadraticSliceConstraints A B C D E F)
  have hflip : ∀ i p q, 0 ≤ A i * p ^ 2 + 2 * B i * p * q + C i * q ^ 2 := by
    intro i p q
    nlinarith [h i q p]
  have G : RegularStrongSliceFamily (fun t x => V x t) := by
    rw [← quadraticSoftSlice_potential_swap ρ A B C D E F]
    exact quadraticSoftSliceRegularFamily hρ C B A E D F hflip
  exact dominated_conditional_slice_no_spike (quadraticSoftSliceRegularFamily hρ A B C D E F h)
    G (quadraticSoftSlice_moment_continuity hρ A B C D E F h)

end
end Nonsmooth
