import Bilevel.ChiOuterCarrierFineCoupling
import Bilevel.ChiNormalizedExtensionJets
import Bilevel.ChiFineParameterBudget

/-! Actual fine normal extension on the full space, with exact source
normal coefficient. Its third-jet budget is paid by the chosen fine
parameter; no desired extension bound is assumed. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension

theorem source_fine_extension_budget : ∃ B : ℝ,1 ≤ B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR Km : ℝ),(∀ j,1 ≤ r j) → (∀ j,0 < η j) → (∀ j,η j ≤ 1) →
      (∀ j,0 < b j) → (∀ j,b j ≤ 1) → 1 ≤ K → 0 < ζ → ζ ≤ 1 → 1 ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (J blocks normals : ℕ) (index : Fin normals) (c ρ m₀ d Cf Mpay : ℝ),
      0 < c → c ≤ 1/128 → 0 ≤ ρ → 0 < m₀ → 0 < d → 1 ≤ Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/c^2)*B^2) ≤ Cf →
      let ell := (D J []).ell
      let h := (D J []).width
      let v := fineParameter ρ m₀ ell d Cf J
      ∀ hv : 1 ≤ v, ∀ hc : 0 < c, ∀ hh : 0 < h,
      let data := outerFineData blocks M D J c v hc hh hv
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 1 (fun y => fineTerm normals index data y/d) z‖ ≤
        6*SmallGapLiftSupport.C*B^(J+2)*ell*h^2/d ∧
      ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals index data y/d) z‖ ≤
        12*SmallGapLiftSupport.C*B^(J+2)*ell*h*Real.sqrt v/c/d ∧
      ‖iteratedFDeriv ℝ 3 (fun y => fineTerm normals index data y/d) z‖ ≤ ρ/(Mpay*m₀) := by
  obtain ⟨B,hB,hjets⟩ := source_outer_coupling_jets
  refine ⟨B,hB,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  have hall := hjets E F n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V
  intro J blocks normals index c ρ m₀ d Cf Mpay hc hcs hρ hm hd hMpay hCf
  intro hv hc' hh z
  let ell := (D J []).ell
  let h := (D J []).width
  let v := fineParameter ρ m₀ ell d Cf J
  let data := outerFineData blocks M D J c v hc' hh hv
  have hactual := hall J blocks c v hc hcs hv (normalSlice normals index z)
  have hpos := parentScale_positive initial r η hl hw hr hη (J+1)
  have hell : 0 < ell := hpos.1
  have h1 := fineTerm_normalized_jet index data hd z 1 (by norm_num) hactual.1
  have h2 := fineTerm_normalized_jet index data hd z 2 (by norm_num) hactual.2.1
  have h3 := fineTerm_normalized_jet index data hd z 3 (by norm_num) hactual.2.2
  refine ⟨h1,h2,?_⟩
  apply h3.trans
  have hC := SmallGapLiftSupport.C_pos
  have hp := fine_third_budget hρ hm hell hd (show 0 ≤ 24*SmallGapLiftSupport.C/c^2 by positivity)
    hB hMpay hCf J
  convert hp using 1
  dsimp only [v]
  ring

end Bilevel.ChiExtensionCalibration
