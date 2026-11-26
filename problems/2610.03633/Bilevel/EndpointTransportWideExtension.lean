import Bilevel.EndpointTransportWideCoarse
import Bilevel.EndpointTransportWideFine
import Bilevel.EndpointTransportWideRadial

/-! Complete actual physical normal extension jets on the full source
window. Coarse, fine and public terms share the same constructed geometry. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration ChiCurvatureSchedule ChiIndependentWidths

theorem normalized_hidden_add_jet_bound
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {J s : ℕ}
    (index : Fin J → Fin s) (f : Fin J → X → ℝ) (W : Fin J → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (hW : ∀ i,0<W i)
    (fineIndex : Fin s) (data : CompensatedMean.Data (E:=X)) (d : ℝ)
    (z : Full X s) (k : ℕ) (hk : k≤3) (Bc Bf : ℝ)
    (hc : ‖iteratedFDeriv ℝ k (fun y => coarseSum index f W y/d) z‖≤Bc)
    (hfine : ‖iteratedFDeriv ℝ k (fun y => fineTerm s fineIndex data y/d) z‖≤Bf) :
    ‖iteratedFDeriv ℝ k (hidden index f W fineIndex data (1/d)) z‖≤Bc+Bf := by
  have hcc := (coarseSum_contDiff index f W hf hW).div_const d
  have hfc := (fineTerm_contDiff s fineIndex data).div_const d
  have he : hidden index f W fineIndex data (1/d)=
      fun y => coarseSum index f W y/d+fineTerm s fineIndex data y/d := by
    funext y
    dsimp only [ChiExtension.hidden]
    ring
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  rw [he,iteratedFDeriv_add_apply' ((hcc.of_le hk').contDiffAt) ((hfc.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hc hfine)

theorem wide_physical_hierarchy_extension_jets (Ar Kminus ζ cn : ℝ)
    (hA : 0≤Ar) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C B : ℝ,1≤C ∧ 1≤B ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n transport dim : ℕ) (Q : Rotations transport dim)
      (L μ θ κ η₀ b η t Cb ε Kg CT CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 0≤θ → θ≤κ^2 → 0<κ → 0<η₀ → 0<b → 0<η → η≤1 →
      0<t → t≤1 → 0≤Cb → 0≤ε → 0<Kg → 1/η≤Kg → 0<CT → (C^2/(t*η))^2≤CT →
      1≤scale θ CT 6 → 1≤chosenDepth θ → 128≤cn/η^2 →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) (chosenDepth θ) →
      (∀ j,0<weight j) → (∀ j,weight j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio (scale θ CT 6) j)
          (resolution η Kg j)) →ₗᵢ[ℝ] Block dim),
      let J := chosenDepth θ
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let G := sourceGeometry initial (sourceRatio (scale θ CT 6)) (resolution η Kg) weight Ar Kminus ζ cn CR V
      ∀ (normals : ℕ) (P : ChiFine.Parameters),P.ℓ=(G J []).ell → P.β=(G J []).width →
      ∀ (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals) (Cf Mpay : ℝ),1≤Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/P.c^2)*B^2)≤Cf → 4*(B^2/t)^2≤Cf →
      P.θ=fineParameter (θ*μ) (3*μ/2) P.ℓ (normalCoefficient L J) Cf J →
      let rad := fun j => weight j*(G j []).nu
      let R := fun j => (G j []).radius
      let Ext := physicalHierarchyExtension Q M G P J normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let H := 192*SmallGapLiftSupport.C*Cb*(cn/η^2)^(2/3:ℝ)+
        576*SmallGapLiftSupport.C*Cb/(P.c*Real.sqrt (6*η₀))+144*CR*Cb
      let Third := 64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*scale θ CT 6+
        2*θ/(3*Mpay)+72*ζ*η₀*((J:ℝ)+1)^2*scale θ CT 6
      ∀ z : Full (PhysicalBase E J transport dim) normals,
      ‖iteratedFDeriv ℝ 2 Ext z‖≤H*(ε/L) ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤Third := by
  obtain ⟨C,hC,hcoarse⟩ := wide_physical_coarse_extension_jets Ar Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨B,hB,hfine⟩ := wide_physical_fine_extension_jets
  refine ⟨C,B,hC,hB,?_⟩
  intro E _ _ _ n transport dim Q L μ θ κ η₀ b η t Cb ε Kg CT CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hCT hpay hT hJ hlen
    hwidthGain hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let G := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight Ar Kminus ζ cn CR V
  intro normals P hℓP hβP index radialIndex fineIndex Cf Mpay hMpay hCf hCfWide hv z
  let data := physicalHierarchyFine Q M G P J
  let rad := fun j => weight j*(G j []).nu
  let R := fun j => (G j []).radius
  let W := fun i : Fin J => coarseWidth G (i.val+1)
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg) (mul_pos hη₀ hL) hb
    (sourceRatio_ge_one hT) (base_resolution_positive hη hK)
  have hW (i : Fin J) : 0<W i := coarseWidth_pos G _ (hp (i.val+2)).2
  have hcar := outerPhysicalCoarseFamily_contDiff J Q M (baseMacroProjection J transport dim) G
    (baseOrdinaryProjection J transport dim) (basePhysicalProjection J transport dim) P J
  have hco := hcoarse E n transport dim Q L η₀ b η t Cb ε κ θ Kg CT CR Km weight
    hL hη₀ hb hη hη1 ht ht1 hCb hε hκ hθ hθκ hK hthreshold hCT hpay hT hJ hlen
    hwidthGain hw hw1 hCR hCRcn hKm' U V normals P hℓP hβP index z
  have hfi := hfine E n J transport dim Q L μ θ κ η₀ b η t Cb ε Kg T Ar Kminus ζ cn CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hT hJ hwidthGain
    hw hw1 hKm hζ hζ1 hCR hKm' U V normals P hℓP hβP fineIndex Cf Mpay hMpay hCf hCfWide hv z
  have hpayr : (1/(t*η))^2≤CT := by
    apply le_trans _ hpay
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (one_le_pow₀ hC) (mul_nonneg ht.le hη.le)
  have hra := wide_physical_radial_jets L η₀ b η t Cb ε κ θ Kg CT ζ CR
    hL hη₀ hb hη hη1 ht ht1 hCb hε hκ hθ hθκ hK hCT hpayr hT hJ hζ (by linarith)
    hwidthGain radialIndex weight hw hw1 z
  have hh2 := normalized_hidden_add_jet_bound index (physicalHierarchyCoarse Q M G P J) W hcar hW
    fineIndex data (normalCoefficient L J) z 2 (by norm_num) _ _ hco.1 hfi.1
  have hh3 := normalized_hidden_add_jet_bound index (physicalHierarchyCoarse Q M G P J) W hcar hW
    fineIndex data (normalCoefficient L J) z 3 (by norm_num) _ _ hco.2 hfi.2
  have ha2 := total_jet_bound index (physicalHierarchyCoarse Q M G P J) W hcar hW fineIndex data (1/normalCoefficient L J)
    radialIndex (publicRadialProjection (E:=E) transport dim) (publicRadialProjection_norm_le (E:=E) transport dim)
    (publicRadialCurvature transport rad) (publicRadialRadius transport R) (normalCoefficient L J)
    z 2 (by norm_num) _ _ hh2 hra.1
  have ha3 := total_jet_bound index (physicalHierarchyCoarse Q M G P J) W hcar hW fineIndex data (1/normalCoefficient L J)
    radialIndex (publicRadialProjection (E:=E) transport dim) (publicRadialProjection_norm_le (E:=E) transport dim)
    (publicRadialCurvature transport rad) (publicRadialRadius transport R) (normalCoefficient L J)
    z 3 (by norm_num) _ _ hh3 hra.2
  exact ⟨ha2.trans_eq (by ring),ha3⟩

end Bilevel.EndpointTransportResponse
