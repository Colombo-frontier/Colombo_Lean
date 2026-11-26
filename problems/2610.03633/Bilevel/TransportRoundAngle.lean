import Bilevel.TransportRoundFresh

/-! Conditional protected-block angle and energy update, now with the actual
fresh residual subspace and a derived paired-edge probability bound. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior OrthogonalAction
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
set_option maxHeartbeats 600000

theorem paired_protected_failure {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Pairs D) (H S W : Submodule ℝ (Space D)) (b : OrthonormalBasis ι ℝ H) (K I : Finset ι)
    (hIK : I ⊆ Finset.univ\K) (A : F →ₗᵢ[ℝ] Space D) (U : G →ₗᵢ[ℝ] Space D) {e : ℝ}
    (hsource : frameEnergy S (fun i => (b i : Space D)) (Finset.univ\K) ≤ e)
    (hsmall : e ≤ (1:ℝ)/4096)
    (hAS : ∀ x, A x ∈ S) (hUS : ∀ u, U u ∈ S)
    (hAK : ∀ i ∈ K, ∀ x, ⟪(b i : Space D),A x⟫ = 0)
    (hUK : ∀ i ∈ K, ∀ u, ⟪(b i : Space D),U u⟫ = 0)
    (horth : ∀ x u, ⟪A x,U u⟫ = 0)
    (hdom : domain L ≤ H ⊔ LinearMap.range A.toLinearMap)
    (hd : 0 < Module.finrank ℝ (range L)ᗮ)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O) :
    μ.real {O |
      (∃ u, ‖u‖/2 < ‖project W (O • U u)‖) ∨
      (∃ u, ‖innovationMap W ((isometry D O).toLinearIsometry.comp U) u‖ < ‖u‖/2) ∨
      8*(e+frameEnergy W (fun i => O • (b i : Space D)) I) <
        frameEnergy (W ⊔ (LinearMap.range U.toLinearMap).map (isometry D O).toLinearEquiv.toLinearMap)
          (fun i => O • (b i : Space D)) I-frameEnergy W (fun i => O • (b i : Space D)) I} ≤
      64*((Module.finrank ℝ (LinearMap.range U.toLinearMap):ℝ)*Module.finrank ℝ W /
        (Module.finrank ℝ (range L)ᗮ:ℝ)) := by
  apply (measureReal_mono (μ := μ) (s₂ := {O | ∃ u, ‖u‖/8 < ‖project W (O •
    ProjectionGeometry.residual (LinearMap.range (innovationMap H A).toLinearMap) (innovationMap H U u))‖}) ?_).trans
      (paired_fresh_failure L H W A U hdom hd μ hμ hL)
  intro O hbad
  by_contra hf
  have hfr : ∀ u, ‖project W ((isometry D O) (ProjectionGeometry.residual
      (LinearMap.range (innovationMap H A).toLinearMap) (innovationMap H U u)))‖ ≤ ‖u‖/8 := by
    intro u
    exact le_of_not_gt (fun hu => hf ⟨u,hu⟩)
  have ha := protected_source_angle H S W b K (isometry D O) A U
    hsource hsmall hAS hUS hAK hUK horth hfr
  have he := protected_source_energy_update H S W b K I hIK (isometry D O) A U
    hsource hsmall hAS hUS hAK hUK horth hfr
  rcases hbad with ⟨u,hu⟩ | ⟨u,hu⟩ | hu
  · exact (not_lt_of_ge (ha.1 u)) hu
  · exact (not_lt_of_ge (ha.2 u)) hu
  · exact (not_lt_of_ge he) hu

end Bilevel.TransportRound
