import Bilevel.TransportEdgePairs
import Bilevel.TransportObserverHaarAngle

/-! Actual paired-history conditional operator-angle probability. The
Frobenius estimate and image support are both derived from the paired history
and its proved residual left isotropy. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportEdgePosterior
open EuclideanGaussian OrthogonalAction ProjectionGeometry TransportObserver
set_option maxHeartbeats 400000

theorem paired_operator_failure {G : Type*} [NormedAddCommGroup G]
    {N : ℕ} (L : Pairs N) (W : Submodule ℝ (Space N))
    (hd : 0 < Module.finrank ℝ (range L)ᗮ)
    (μ : Measure (OrthogonalHaar.Group N)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O)
    (R : Submodule ℝ (Space N)) (hR : R ≤ (domain L)ᗮ)
    (fresh : G → R) (hnorm : ∀ u, ‖fresh u‖ ≤ ‖u‖) :
    μ.real {O | ∃ u, ‖u‖/8 < ‖project W (O • (fresh u : Space N))‖} ≤
      64*((Module.finrank ℝ R : ℝ)*Module.finrank ℝ W/(Module.finrank ℝ (range L)ᗮ : ℝ)) := by
  let b := stdOrthonormalBasis ℝ R
  have hsub : {O : OrthogonalHaar.Group N |
      ∃ u, ‖u‖/8 < ‖project W (O • (fresh u : Space N))‖} ⊆
      {O | (1:ℝ)/64 < frameEnergy W (images (fun i => (b i : Space N)) O) Finset.univ} := by
    intro O hO
    by_contra he
    have he' : frameEnergy W (images (fun i => (b i : Space N)) O) Finset.univ ≤ (1:ℝ)/64 :=
      le_of_not_gt he
    let K : R →ₗᵢ[ℝ] Space N := (isometry N O).toLinearIsometry.comp R.subtypeₗᵢ
    have hh := isometry_fresh_projection_of_frobenius W K b fresh hnorm he'
    obtain ⟨u,hu⟩ := hO
    exact (not_lt_of_ge (hh u)) hu
  exact (measureReal_mono (μ := μ) hsub).trans
    (paired_images_projection_failure L W hd μ hμ hL (fun i => (b i : Space N))
      (fun i => b.orthonormal.norm_eq_one i) (fun i => hR (b i).property))

end Bilevel.TransportEdgePosterior
