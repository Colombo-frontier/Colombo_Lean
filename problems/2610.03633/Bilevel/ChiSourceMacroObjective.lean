import Bilevel.ChiSourceMacroCalibration
import Bilevel.ChiSourcePhysicalScales
import Bilevel.ChiOuterSharedCertificate

/-! The same shared source geometry, with the actual floor-selected macro
length, has initial gap at most Delta and an 8*epsilon gradient barrier.
All earlier accuracy conditions survive the single window refinement. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry
universe u

theorem source_macro_objective_certificate : ∃ t η ζ cn CR Km Cgap : ℝ,
    0 < t ∧ t < 1 ∧ 0 < η ∧ η ≤ 1 ∧ 0 < ζ ∧ ζ ≤ 2/15 ∧ 0 < cn ∧ cn ≤ 1 ∧
    128 ≤ cn/η^2 ∧ 1 ≤ CR ∧ ζ*Real.sqrt cn ≤ CR ∧ 1 ≤ Km ∧ 1 ≤ Cgap ∧
    ∀ (η₀ Cb Cold cold : ℝ),0 < η₀ → 32/t ≤ Cb → 1 ≤ Cold → 0 < cold →
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ Cold ≤ Cacc ∧ c ≤ cold ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (J : ℕ) (L κ θ Δ ε T : ℝ),
      0 < L → 1 ≤ κ → 1 ≤ θ → 0 < Δ → 0 < ε → 1 ≤ T → 1/η ≤ κ/6 →
      ε ≤ accuracyWindow c Cacc L κ θ Δ J 6 →
      let b := sourceWidth Cb ε η₀ L t η J
      let initial : Scale := ⟨η₀*L,b⟩
      let n := macroIndex Δ Cgap initial.energy
      ε ≤ accuracyWindow cold Cold L κ θ Δ J 6 ∧ 128 ≤ n ∧
      η₀*L*Δ*(t*η)^(2*J)/(4*Cgap*Cb^2*ε^2) ≤ (n:ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight 3 1 ζ cn CR V
      let R := fun j => (D j []).radius
      let ρ := fun j => weight j*(ζ*(parentScale initial (sourceRatio T) (resolution η (κ/6)) j).curvature)
      let f := jointOuter (J+1) M (initial.curvature/24) D ρ R J (κ/6)
      Tendsto f (cocompact (Joint E (Blocks (J+1) F))) atTop ∧ f 0=0 ∧
      f 0-sInf (Set.range f) ≤ Δ ∧
      ∀ z,M.coordinates z.fst (Fin.last n) < b → 8*ε ≤ ‖gradient f z‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζ1,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hshared⟩ :=
    source_shared_objective_certificate.{u}
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζ1,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,?_⟩
  intro η₀ Cb Cold cold hη₀ hCb32 hCold hcold
  have hCb : 0 < Cb := (div_pos (by norm_num : (0:ℝ) < 32) ht).trans_le hCb32
  obtain ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,hmacro⟩ := exists_macro_accuracy_refinement
    hCb hη₀ ht hη (show 0 < Cgap by linarith) hCold hcold
  refine ⟨Cacc,c,hCacc,hc,hc1,hColdC,hccold,?_⟩
  intro E F _ _ _ _ _ _ _ _ J L κ θ Δ ε T hL hκ hθ hΔ hε hT hK hwindow
  dsimp only
  let b := sourceWidth Cb ε η₀ L t η J
  let initial : Scale := ⟨η₀*L,b⟩
  let n := macroIndex Δ Cgap initial.energy
  have hm := hmacro L κ θ Δ ε J hL hκ hθ hΔ hε hwindow
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have hκp : 0 < κ := by linarith
  refine ⟨hm.1,hm.2.1,hm.2.2.2.1,?_⟩
  intro U V
  have ho := hshared E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (sourceRatio_ge_one hT)
    (κ/6) (by positivity) hK U V J
  refine ⟨ho.1,ho.2.1,ho.2.2.1.trans hm.2.2.1,?_⟩
  intro z hlast
  exact (source_margin_ge_eight hη₀ hL ht hη hCb32 hε.le J).trans (ho.2.2.2 z hlast)

end Bilevel.ChiExtensionCalibration
