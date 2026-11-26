import Bilevel.TransportRoundLocal
import Bilevel.TransportEdgeAngle

/-! The fresh complementary subspace is constructed from actual residual
maps. Its support and norm bounds are proved before applying the paired-edge
conditional operator estimate. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def freshSpace (H A U : Submodule ℝ E) : Submodule ℝ E :=
  residualSpace (residualSpace H A) (residualSpace H U)

theorem freshSpace_perp (H A U : Submodule ℝ E) : freshSpace H A U ≤ (H ⊔ A)ᗮ := by
  rw [← sup_residualSpace H A,← Submodule.inf_orthogonal]
  apply le_inf
  · exact residualSpace_local (residualSpace_perp H A) (residualSpace_perp H U)
  · exact residualSpace_perp _ _

theorem residualSpace_rank (A S : Submodule ℝ E) :
    Module.finrank ℝ (residualSpace A S) ≤ Module.finrank ℝ S := Submodule.finrank_map_le _ _

theorem freshSpace_rank (H A U : Submodule ℝ E) :
    Module.finrank ℝ (freshSpace H A U) ≤ Module.finrank ℝ U :=
  (residualSpace_rank _ _).trans (residualSpace_rank _ _)

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem innovation_range (H : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E) :
    LinearMap.range (innovationMap H A).toLinearMap = residualSpace H (LinearMap.range A.toLinearMap) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨A a,⟨a,rfl⟩,rfl⟩
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩

def freshVector (H : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E) (U : G →ₗᵢ[ℝ] E) (u : G) :
    freshSpace H (LinearMap.range A.toLinearMap) (LinearMap.range U.toLinearMap) :=
  ⟨ProjectionGeometry.residual (residualSpace H (LinearMap.range A.toLinearMap)) (innovationMap H U u),
    ⟨innovationMap H U u,⟨U u,⟨u,rfl⟩,rfl⟩,rfl⟩⟩

theorem freshVector_norm (H : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E) (U : G →ₗᵢ[ℝ] E) (u : G) :
    ‖freshVector H A U u‖ ≤ ‖u‖ := by
  exact (residual_norm_le _ _).trans (by
    simpa only [innovationMap_apply,U.norm_map] using residual_norm_le H (U u))

theorem paired_fresh_failure {D : ℕ} (L : Pairs D) (H W : Submodule ℝ (Space D))
    (A : F →ₗᵢ[ℝ] Space D) (U : G →ₗᵢ[ℝ] Space D)
    (hdom : domain L ≤ H ⊔ LinearMap.range A.toLinearMap)
    (hd : 0 < Module.finrank ℝ (range L)ᗮ)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O) :
    μ.real {O | ∃ u, ‖u‖/8 < ‖project W (O •
      ProjectionGeometry.residual (LinearMap.range (innovationMap H A).toLinearMap) (innovationMap H U u))‖} ≤
      64*((Module.finrank ℝ (LinearMap.range U.toLinearMap):ℝ)*Module.finrank ℝ W /
        (Module.finrank ℝ (range L)ᗮ:ℝ)) := by
  let R := freshSpace H (LinearMap.range A.toLinearMap) (LinearMap.range U.toLinearMap)
  have hR : R ≤ (domain L)ᗮ :=
    (freshSpace_perp H _ _).trans (Submodule.orthogonal_le hdom)
  have hh := paired_operator_failure L W hd μ hμ hL R hR (freshVector H A U) (freshVector_norm H A U)
  simp only [freshVector,innovation_range] at hh ⊢
  apply hh.trans
  have hr : (Module.finrank ℝ R:ℝ) ≤ Module.finrank ℝ (LinearMap.range U.toLinearMap) := by
    exact_mod_cast freshSpace_rank H (LinearMap.range A.toLinearMap) (LinearMap.range U.toLinearMap)
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (by norm_num)

end Bilevel.TransportRound
