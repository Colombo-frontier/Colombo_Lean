import Bilevel.ChiOuterMacro

/-! Coercivity, attained minimum, and the actual initial gap of the revised
one-sided macro. The negative-side penalty is kept in the construction. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.ChiOuter
open ChiBoundedChain RadialWrapper ZeroChainPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem macro_zero (n : ℕ) (ℓ h ν R : ℝ) (U : Space n →ₗᵢ[ℝ] E) :
    macroValue n ℓ h ν R U 0 = -(ℓ*h^2)*phi 0 := by
  simp [macroValue, wrapped, compress, bowl, chain, ZeroChainResidualScaled.scaled, value_zero]

theorem macro_pointwise_gap (n : ℕ) (ℓ h ν R : ℝ) (hℓ : 0 ≤ ℓ) (hν : 0 ≤ ν)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    macroValue n ℓ h ν R U 0 - macroValue n ℓ h ν R U u ≤
      ((n:ℝ)+1)*gaussianBound*(ℓ*h^2) := by
  rw [macro_zero]
  have hc := chain_lower n ℓ h hℓ (WrappedChain.coordinates n R U u)
  have hb := bowl_nonnegative ν R hν u
  have hp := mul_nonneg (show 0 ≤ ℓ*h^2 by positivity) (phi_nonneg 0)
  change -(ℓ*h^2)*phi 0 - (chain n ℓ h (WrappedChain.coordinates n R U u)+bowl ν R u) ≤ _
  linarith

theorem macro_coercive [FiniteDimensional ℝ E] (n : ℕ) (ℓ h ν R : ℝ)
    (hℓ : 0 ≤ ℓ) (hν : 0 < ν) (hR : 0 < R) (U : Space n →ₗᵢ[ℝ] E) :
    Tendsto (macroValue n ℓ h ν R U) (cocompact E) atTop :=
  wrapped_coercive ν R (-((n:ℝ)+1)*gaussianBound*(ℓ*h^2)) hν hR
    (chain n ℓ h) (chain_lower n ℓ h hℓ) U.toContinuousLinearMap.adjoint

theorem macro_continuous (n : ℕ) (ℓ h ν R : ℝ) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) : Continuous (macroValue n ℓ h ν R U) :=
  continuous_iff_continuousAt.mpr (fun u =>
    (macro_hasGradientAt n ℓ h ν R hR U u).hasFDerivAt.continuousAt)

theorem macro_minimum_attained [FiniteDimensional ℝ E] (n : ℕ) (ℓ h ν R : ℝ)
    (hℓ : 0 ≤ ℓ) (hν : 0 < ν) (hR : 0 < R) (U : Space n →ₗᵢ[ℝ] E) :
    ∃ u, ∀ v, macroValue n ℓ h ν R U u ≤ macroValue n ℓ h ν R U v :=
  (macro_continuous n ℓ h ν R hR U).exists_forall_le (macro_coercive n ℓ h ν R hℓ hν hR U)

theorem macro_gap_to_infimum [FiniteDimensional ℝ E] (n : ℕ) (ℓ h ν R : ℝ)
    (hℓ : 0 ≤ ℓ) (hν : 0 < ν) (hR : 0 < R) (U : Space n →ₗᵢ[ℝ] E) :
    macroValue n ℓ h ν R U 0 - sInf (Set.range (macroValue n ℓ h ν R U)) ≤
      ((n:ℝ)+1)*gaussianBound*(ℓ*h^2) := by
  obtain ⟨u,hu⟩ := macro_minimum_attained n ℓ h ν R hℓ hν hR U
  have hi : sInf (Set.range (macroValue n ℓ h ν R U)) = macroValue n ℓ h ν R U u := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨macroValue n ℓ h ν R U u, by rintro _ ⟨v,rfl⟩; exact hu v⟩
      · exact ⟨u,rfl⟩
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨v,rfl⟩
      exact hu v
  rw [hi]
  exact macro_pointwise_gap n ℓ h ν R hℓ hν.le U u

end Bilevel.ChiOuter
