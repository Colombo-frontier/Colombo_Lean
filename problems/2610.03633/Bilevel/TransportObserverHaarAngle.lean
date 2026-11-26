import Bilevel.TransportObserverHaarMoment

/-! The actual residual-Haar operator angle event follows from the scalar
Frobenius moment. Conditioning on a transcript is not introduced here. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry EuclideanGaussian OrthogonalAction

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [Fintype ι]

theorem isometry_fresh_projection_of_frobenius (W : Submodule ℝ E)
    (J : F →ₗᵢ[ℝ] E) (b : OrthonormalBasis ι ℝ F) (fresh : G → F)
    (hnorm : ∀ u, ‖fresh u‖ ≤ ‖u‖)
    (henergy : frameEnergy W (fun i => J (b i)) Finset.univ ≤ (1:ℝ)/64) :
    ∀ u, ‖project W (J (fresh u))‖ ≤ ‖u‖/8 := by
  let Q := LinearMap.range J.toLinearMap
  let bb : OrthonormalBasis ι ℝ Q := b.map J.equivRange
  have he : frameEnergy W (fun i => (bb i : E)) Finset.univ ≤ (1:ℝ)/64 := by
    simpa only [bb,OrthonormalBasis.map_apply,LinearIsometry.equivRange_apply_coe] using henergy
  exact fresh_projection_of_frobenius Q W bb (fun u => J (fresh u))
    (fun u => ⟨fresh u,rfl⟩) (fun u => by simpa only [J.norm_map] using hnorm u) he

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- An operator bound for every input of a contraction into a fixed residual
input subspace, using one common Haar isometry. The event probability is
controlled by input rank times destination rank, divided by residual dimension. -/
theorem haar_fresh_operator_failure {κ : Type*} [Fintype κ]
    (d : ℕ) (hd : 0 < d) (J : Space d →ₗᵢ[ℝ] E)
    (W : Submodule ℝ E) (bW : OrthonormalBasis ι ℝ W)
    (R : Submodule ℝ (Space d)) (bR : OrthonormalBasis κ ℝ R)
    (fresh : G → R) (hnorm : ∀ u, ‖fresh u‖ ≤ ‖u‖) :
    (OrthogonalHaar.law d).real
      {A | ∃ u, ‖u‖/8 < ‖project W (J (A • (fresh u : Space d)))‖} ≤
      64*((Fintype.card κ : ℝ)*Fintype.card ι/(d:ℝ)) := by
  have hsub : {A : OrthogonalHaar.Group d |
      ∃ u, ‖u‖/8 < ‖project W (J (A • (fresh u : Space d)))‖} ⊆
      {A | (1:ℝ)/64 < frameEnergy W (fun i => J (A • (bR i : Space d))) Finset.univ} := by
    intro A hA
    by_contra he
    have he' : frameEnergy W (fun i => J (A • (bR i : Space d))) Finset.univ ≤ (1:ℝ)/64 :=
      le_of_not_gt he
    let K : R →ₗᵢ[ℝ] E := J.comp ((isometry d A).toLinearIsometry.comp R.subtypeₗᵢ)
    have hh := isometry_fresh_projection_of_frobenius W K bR fresh hnorm he'
    obtain ⟨u,hu⟩ := hA
    exact (not_lt_of_ge (hh u)) hu
  exact (measureReal_mono (μ := OrthogonalHaar.law d) hsub).trans
    (by simpa only [Finset.card_univ] using
      (haar_frame_projection_failure d hd J W bW (fun i => (bR i : Space d)) Finset.univ
        (fun i _ => bR.orthonormal.norm_eq_one i)))

end Bilevel.TransportObserver
