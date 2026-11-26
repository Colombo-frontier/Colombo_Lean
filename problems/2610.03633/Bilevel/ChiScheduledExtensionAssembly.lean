import Bilevel.ChiScheduledCoarseExtension
import Bilevel.ChiScheduledFineExtension
import Bilevel.ChiScheduledRadialBudget
import Bilevel.ChiExtensionTotal

/-! The actual hidden-plus-public extension assembled from the scheduled
coarse carriers, fine coupling, and radial terms. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem source_hidden_add_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (blocks normals : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (index : Fin J → Fin normals) (fineIndex : Fin normals)
    (data : CompensatedMean.Data (E:=Joint E (Blocks blocks F))) (d : ℝ)
    (hW : ∀ i : Fin J,0 < coarseWidths D J i)
    (z : Full (Joint E (Blocks blocks F)) normals) (k : ℕ) (hk : k ≤ 3)
    (Bc Bf : ℝ)
    (hc : ‖iteratedFDeriv ℝ k (sourceCoarseExtension blocks normals M D J index d) z‖ ≤ Bc)
    (hf : ‖iteratedFDeriv ℝ k (fun y => fineTerm normals fineIndex data y/d) z‖ ≤ Bf) :
    ‖iteratedFDeriv ℝ k (hidden index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex data (1/d)) z‖ ≤ Bc+Bf := by
  have hcc := (coarseSum_contDiff index (coarseFamily blocks M D J) (coarseWidths D J)
    (coarseFamily_contDiff blocks M D J) hW).div_const d
  change ContDiff ℝ 3 (sourceCoarseExtension blocks normals M D J index d) at hcc
  have hfc := (fineTerm_contDiff normals fineIndex data).div_const d
  have he : hidden index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex data (1/d) =
      fun y => sourceCoarseExtension blocks normals M D J index d y+fineTerm normals fineIndex data y/d := by
    funext y
    dsimp only [ChiExtension.hidden,sourceCoarseExtension]
    ring
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [he,iteratedFDeriv_add_apply' ((hcc.of_le hk').contDiffAt) ((hfc.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hc hf)

theorem scheduled_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0 ≤ A) (hKm : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ C B : ℝ,1 ≤ C ∧ 1 ≤ B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ θ η₀ b η κ T CR Km : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 0 ≤ θ → θ ≤ κ → 0 < η₀ → 0 < b → 0 < η → η ≤ 1 → η^2 ≤ 1/2 → 1 ≤ κ →
      1/η ≤ κ/6 → 1 ≤ T → T ≤ κ → 128 ≤ cn/η^2 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) → 1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J → ∀ (index radialIndex : Fin J → Fin normals)
        (fineIndex : Fin normals) (proj : Fin J → Joint E (Blocks blocks F) →L[ℝ] F)
        (hproj : ∀ i,‖proj i‖ ≤ 1) (c Cf Mpay : ℝ),
      0 < c → c ≤ 1/128 → 1 ≤ Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/c^2)*B^2) ≤ Cf →
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∀ hv : 1 ≤ v, ∀ hc : 0 < c, ∀ hh : 0 < (D J []).width,
      let data := outerFineData blocks M D J c v hc hh hv
      let ν := fun i : Fin J => weight (i.val+1)*(D (i.val+1) []).nu
      let R := fun i : Fin J => (D (i.val+1) []).radius
      let H := hidden index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex data (1/normalCoefficient L J)
      let Ext := total index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex data (1/normalCoefficient L J)
        radialIndex proj hproj ν R (normalCoefficient L J)
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 1 H z‖ ≤
        (16*SmallGapLiftSupport.C*C^(J+2)*cn+24*SmallGapLiftSupport.C*B^(J+2))*
          η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 ∧
      ‖iteratedFDeriv ℝ 2 Ext z‖ ≤
        192*SmallGapLiftSupport.C*C^(J+2)*η₀*b*(cn/η^2)*((J:ℝ)+1)^2+
          48*SmallGapLiftSupport.C*B^(J+2)*b/c+144*CR*η₀*b*((J:ℝ)+1)^2 ∧
      ‖iteratedFDeriv ℝ 3 Ext z‖ ≤
        64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*T+
          2*θ/(3*Mpay)+72*ζ*η₀*((J:ℝ)+1)^2*T := by
  obtain ⟨C,hC,hcoarse⟩ := scheduled_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨B,hB,hfine⟩ := scheduled_fine_extension_jets
  refine ⟨C,B,hC,hB,?_⟩
  intro E F _ _ _ _ _ _ n L μ θ η₀ b η κ T CR Km weight hL hμ hθ hθκ hη₀ hb hη hη1 hηsq hκ hthreshold
    hT hTκ hlen hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  intro J blocks normals hJ index radialIndex fineIndex proj hproj c Cf Mpay hc hcs hMpay hCf hv hc' hh z
  let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
  let data := outerFineData blocks M D J c v hc' hh hv
  let ν := fun i : Fin J => weight (i.val+1)*(D (i.val+1) []).nu
  let R := fun i : Fin J => (D (i.val+1) []).radius
  have hκp : 0 < κ := by linarith
  have hp := parentScale_positive initial (sourceRatio T) (resolution η (κ/6)) (mul_pos hη₀ hL) hb
    (sourceRatio_ge_one hT) (base_resolution_positive hη (show 0 < κ/6 by positivity))
  have hW (i : Fin J) : 0 < coarseWidths D J i := by
    unfold coarseWidths
    have hi : 0 < (D (i.val+1) []).width := (hp (i.val+2)).2
    exact mul_pos hi (Real.rpow_pos_of_pos (by positivity) _)
  have hco := hcoarse E F n L η₀ b η κ T CR Km weight hL hη₀ hb hη hη1 hηsq hκ hthreshold hT hTκ hlen
    hw hw1 hCR hCRcn hKm' U V J blocks normals hJ index z
  have hfi := hfine E F n L μ θ η₀ b η κ T A Kminus ζ cn CR Km weight hL hμ hθ hθκ hη₀ hb hη hη1 hκ
    hthreshold hT hw hw1 hKm hζ hζ1 hCR hKm' U V J blocks normals hJ fineIndex c Cf Mpay hc hcs hMpay hCf hv hc' hh z
  have hra := scheduled_radial_jets hJ radialIndex proj hproj L η₀ b η (κ/6) κ T ζ CR
    (fun i => weight (i.val+1)) hL hη₀ hb hη hη1 hκ rfl hT hTκ hζ (by linarith)
    (fun i => hw (i.val+1)) (fun i => hw1 (i.val+1)) z
  have h1 := source_hidden_add_jet_bound blocks normals M D J index fineIndex data (normalCoefficient L J) hW
    z 1 (by norm_num) _ _ hco.1 hfi.1
  have h2 := source_hidden_add_jet_bound blocks normals M D J index fineIndex data (normalCoefficient L J) hW
    z 2 (by norm_num) _ _ hco.2.1 hfi.2.1
  have h3 := source_hidden_add_jet_bound blocks normals M D J index fineIndex data (normalCoefficient L J) hW
    z 3 (by norm_num) _ _ hco.2.2 hfi.2.2
  refine ⟨h1.trans_eq (by ring),?_,?_⟩
  · exact total_jet_bound index (coarseFamily blocks M D J) (coarseWidths D J)
      (coarseFamily_contDiff blocks M D J) hW fineIndex data (1/normalCoefficient L J)
      radialIndex proj hproj ν R (normalCoefficient L J) z 2 (by norm_num) _ _ h2 hra.1
  · exact total_jet_bound index (coarseFamily blocks M D J) (coarseWidths D J)
      (coarseFamily_contDiff blocks M D J) hW fineIndex data (1/normalCoefficient L J)
      radialIndex proj hproj ν R (normalCoefficient L J) z 3 (by norm_num) _ _ h3 hra.2

end Bilevel.ChiExtensionCalibration
