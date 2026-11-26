import Nonsmooth.GaussianSlabUpdates
import Nonsmooth.SelectionCovarianceCriterion

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {n : ℕ}

theorem gaussianSlabSelection_row_covariance {u : E} (hu : ‖u‖ = 1)
    (a b : Fin (n + 1) → ℝ) :
    ∀ᵐ h ∂(Measure.pi (fun i => gaussianSlabKernel u (a i, b i))).map (supportSingleObservation u),
      ∀ (v : E) (i : Fin (n + 1)), variance (fun z : E => ⟪v, z⟫_ℝ)
        (supportSelectionRowKernel (fun i => gaussianSlabKernel u (a i, b i)) u i h) ≤
          ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  let μ : Fin (n + 1) → Measure E := fun i => gaussianSlabKernel u (a i, b i)
  let P : Fin (n + 1) → Measure E → Prop := fun _ ν =>
    ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤ ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ)
  have hbase : ∀ i, P i (μ i) := fun i v => gaussianSlabKernel_covariance hu (a i) (b i) v
  have hwinner : ∀ i, ∀ᵐ y ∂(μ i).map (fun z : E => ⟪z, u⟫_ℝ),
      P i (condDistrib id (fun z : E => ⟪z, u⟫_ℝ) (μ i) y) :=
    fun i => gaussianSlabKernel_scalar_covariance hu (a i) (b i)
  have hloser : ∀ (w i : Fin (n + 1)) (y : ℝ), i ≠ w →
      μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) ≠ 0 →
        P i ((μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i]) := by
    intro w i y _ _ v
    have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu
    have hzero (t : ℝ) : μ i {z : E | ⟪z, u⟫_ℝ = t} = 0 :=
      gaussianSlabKernel_hyperplane_zero u (a i) (b i) hu0 t
    have hs := supportLoserRegion_ae_halfspace (μ i) hzero w i y
    have he : (μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i] =
        (μ i)[|{z : E | ⟪z, u⟫_ℝ ≤ y}] := by
      simp only [ProbabilityTheory.cond, measure_congr hs, Measure.restrict_congr_set hs]
    rw [he]
    exact gaussianSlabKernel_upper_condition_covariance hu (a i) (b i) y v
  filter_upwards [supportSelection_row_property μ u P hbase hwinner hloser] with h hh
  exact fun v i => hh i v

/-- Actual regular posterior covariance after a maximum-and-index observation of
independent, individually slab-truncated Gaussian rows. -/
theorem gaussianSlabPosterior_row_covariance {u : E} (hu : ‖u‖ = 1)
    (a b : Fin (n + 1) → ℝ) :
    ∀ᵐ h ∂(Measure.pi (fun i => gaussianSlabKernel u (a i, b i))).map (supportSingleObservation u),
      ∀ (v : E) (i : Fin (n + 1)), variance (fun z : Fin (n + 1) → E => ⟪v, z i⟫_ℝ)
        (condDistrib id (supportSingleObservation u)
          (Measure.pi (fun i => gaussianSlabKernel u (a i, b i))) h) ≤
            ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) :=
  supportPosterior_covariance_of_selection_rows _ u
    (fun _ v => ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ)) (gaussianSlabSelection_row_covariance hu a b)

theorem gaussianSlabPosterior_opposite_row_covariance {u : E} (hu : ‖u‖ = 1)
    (a b : Fin (n + 1) → ℝ) :
    ∀ᵐ h ∂(Measure.pi (fun i => gaussianSlabKernel u (a i, b i))).map (supportSingleObservation (-u)),
      ∀ (v : E) (i : Fin (n + 1)), variance (fun z : Fin (n + 1) → E => ⟪v, z i⟫_ℝ)
        (condDistrib id (supportSingleObservation (-u))
          (Measure.pi (fun i => gaussianSlabKernel u (a i, b i))) h) ≤
            ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hu' : ‖-u‖ = 1 := by simpa only [norm_neg] using hu
  simpa only [gaussianSlabKernel_neg] using
    gaussianSlabPosterior_row_covariance hu' (fun i => -b i) (fun i => -a i)

end
end Nonsmooth
