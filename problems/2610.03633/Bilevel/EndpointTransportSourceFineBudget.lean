import Bilevel.EndpointTransportSourceOuterFine
import Bilevel.EndpointTransportNormalExtension
import Bilevel.ChiFineParameterBudget
import Bilevel.ChiNormalizedExtensionJets

/-! The actual physical fine normal term with its source normalization.
The chosen fine parameter pays the third mixed derivative exactly. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration

theorem source_physical_fine_extension_budget : ∃ B : ℝ,1≤B ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n transport dim : ℕ) (Q : Rotations transport dim) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (Ar K ζ cn CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block dim),
      let M := sourceMacroNode n initial Km U
      let G := sourceGeometry initial r η b Ar K ζ cn CR V
      ∀ (J normals : ℕ) (P : ChiFine.Parameters),P.ℓ=(G J []).ell → P.β=(G J []).width →
      ∀ (index : Fin normals) (ρ m₀ d Cf Mpay : ℝ),0≤ρ → 0<m₀ → 0<d → 1≤Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/P.c^2)*B^2)≤Cf →
      P.θ=fineParameter ρ m₀ P.ℓ d Cf J →
      ∀ z : Full (PhysicalBase E J transport dim) normals,
      let data := physicalHierarchyFine Q M G P J
      ‖iteratedFDeriv ℝ 1 (fun y => fineTerm normals index data y/d) z‖≤
        6*SmallGapLiftSupport.C*B^(J+2)*P.ℓ*P.β^2/d ∧
      ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals index data y/d) z‖≤
        12*SmallGapLiftSupport.C*B^(J+2)*P.ℓ*P.β*Real.sqrt P.θ/P.c/d ∧
      ‖iteratedFDeriv ℝ 3 (fun y => fineTerm normals index data y/d) z‖≤ρ/(Mpay*m₀) := by
  obtain ⟨B,hB,hjets⟩ := source_outer_physical_fine_coupling_jets
  refine ⟨B,hB,?_⟩
  intro E _ _ _ n transport dim Q initial hl hw r η b Ar K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let G := sourceGeometry initial r η b Ar K ζ cn CR V
  intro J normals P hℓ hβ index ρ m₀ d Cf Mpay hρ hm hd hMpay hCf hv z
  let data := physicalHierarchyFine Q M G P J
  have hactual := hjets E (PhysicalBase E J transport dim) transport dim n Q initial hl hw
    r η b Ar K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V J
    (baseMacroProjection J transport dim) (baseOrdinaryProjection J transport dim) (basePhysicalProjection J transport dim)
    (baseMacroProjection_norm_le J transport dim) (baseOrdinaryProjection_norm_le J transport dim)
    (basePhysicalProjection_norm_le J transport dim) J P hβ (normalSlice normals index z)
  have hell : 0<P.ℓ := by
    rw [hℓ]
    exact (parentScale_positive initial r η hl hw hr hη (J+1)).1
  have h1 := fineTerm_normalized_jet index data hd z 1 (by norm_num) hactual.1
  have h2 := fineTerm_normalized_jet index data hd z 2 (by norm_num) hactual.2.1
  have h3 := fineTerm_normalized_jet index data hd z 3 (by norm_num) hactual.2.2
  refine ⟨h1,h2,?_⟩
  apply h3.trans
  have hc := P.c_pos
  have hC := SmallGapLiftSupport.C_pos
  have hp := fine_third_budget hρ hm hell hd (show 0≤24*SmallGapLiftSupport.C/P.c^2 by positivity)
    hB hMpay hCf J
  rw [hv]
  convert hp using 1
  ring

end Bilevel.EndpointTransportResponse
