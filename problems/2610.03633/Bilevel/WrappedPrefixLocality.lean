import Bilevel.ZeroChainWrappedResidual

/-! Actual coordinate support transported through the radial wrapper.
These statements account for the radial query direction: an ambient gradient
need not lie just in the hidden-column prefix. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.WrappedPrefixLocality
open ZeroChain ZeroChainResidualScaled ZeroChainFlatteningBounds
  ZeroChainFlatteningMap RadialWrapper WrappedChain

theorem flattened_gradient_small (n : ℕ) (a β δ : ℝ) (hδ : 0 < δ)
    (z : Space n) (j : Fin (n+1)) (hj : |z j| ≤ δ) :
    gradient (flattenedResidual n a β δ) z j = 0 := by
  have hd := ((R_contDiff n a β).differentiable (by norm_num) _).hasFDerivAt.comp z
    ((flattenMap_contDiff n δ).differentiable (by norm_num) z).hasFDerivAt
  change gradient (R n a β ∘ flattenMap n δ) z j = 0
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hd,
    ContinuousLinearMap.comp_apply, flattenMap_gradient_kills_small δ hδ z j hj,
    map_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem frame_mem_of_support {n r : ℕ} (U : Space n →ₗᵢ[ℝ] E)
    (V : Submodule ℝ E) (hU : ∀ j : Fin (n+1), j.val < r → U (basis j) ∈ V)
    (v : Space n) (hv : ∀ j : Fin (n+1), r ≤ j.val → v j = 0) : U v ∈ V := by
  classical
  have he : v = ∑ j : Fin (n+1), v j • basis j := by
    ext i
    change v i = EuclideanSpace.proj i (∑ j : Fin (n+1), v j • basis j)
    simp [map_sum, basis, PiLp.smul_apply, EuclideanSpace.single_apply]
  rw [he, map_sum]
  apply V.sum_mem
  intro j _
  rw [map_smul]
  by_cases hj : j.val < r
  · exact V.smul_mem _ (hU j hj)
  · rw [hv j (by omega), zero_smul]
    exact V.zero_mem

theorem carried_gradient (n : ℕ) (R : ℝ) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) (f : Space n → ℝ) (hf : Differentiable ℝ f) (u : E) :
    gradient (f ∘ coordinates n R U) u =
      wrappedGradient 0 R u (U (gradient f (coordinates n R U u))) := by
  have h := wrapped_hasGradientAt 0 R hR f U.toContinuousLinearMap.adjoint u
    (gradient f (coordinates n R U u)) (hf _).hasGradientAt
  have he : wrapped 0 R f U.toContinuousLinearMap.adjoint = f ∘ coordinates n R U := by
    funext v
    simp [wrapped, bowl, coordinates]
  rw [he] at h
  simpa only [ContinuousLinearMap.adjoint_adjoint, LinearIsometry.coe_toContinuousLinearMap]
    using h.gradient

theorem carried_gradient_mem (n r : ℕ) (R : ℝ) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) (f : Space n → ℝ) (hf : Differentiable ℝ f)
    (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → U (basis j) ∈ V)
    (hs : ∀ j : Fin (n+1), r ≤ j.val → gradient f (coordinates n R U u) j = 0) :
    gradient (f ∘ coordinates n R U) u ∈ V := by
  rw [carried_gradient n R hR U f hf u]
  exact V.add_mem (V.smul_mem _ (frame_mem_of_support U V hU _ hs)) (V.smul_mem _ hu)

theorem carried_flat_gradient_mem (n r : ℕ) (a β δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |coordinates n R U u j| ≤ δ) :
    gradient (flattenedResidual n a β δ ∘ coordinates n R U) u ∈ V := by
  exact carried_gradient_mem n r R hR U _
    ((flattenedResidual_contDiff n a β δ).differentiable (by norm_num)) u V hu hU
    (fun j hj => flattened_gradient_small n a β δ hδ _ j (hz j hj))

theorem carried_residual_gradient_mem (n r : ℕ) (a β radius : ℝ)
    (hβ : 0 < β) (hR : 0 < radius)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r+1 → U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val → |coordinates n radius U u j| ≤ β/4) :
    gradient (ZeroChainWrappedResidual.residual n a β radius U) u ∈ V := by
  exact carried_gradient_mem n (r+1) radius hR U _
    ((R_contDiff n a β).differentiable (by norm_num)) u V hu hU
    (fun j hj => R_gradient_support n r a β hβ _ hz j hj)

end Bilevel.WrappedPrefixLocality
