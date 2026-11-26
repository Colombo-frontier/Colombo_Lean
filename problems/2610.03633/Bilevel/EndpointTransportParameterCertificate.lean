import Bilevel.EndpointTransportWideExtension
import Bilevel.EndpointTransportUniformUpperBase
import Bilevel.EndpointTransportParameterScales

/-! One physical source parameter family with the actual transport gain,
full public accuracy window, actual upper base and actual extension jets. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension
  ChiExtensionCalibration ChiCurvatureSchedule ChiIndependentWidths

theorem wide_physical_parameter_certificate
    {A Kminus ζ cn η CR Km Cgap Cb t cms : ℝ}
    (hA : 0≤A) (hKminus : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hcn : 0<cn) (hcn1 : cn≤1) (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) (hCgap : 1≤Cgap)
    (hCb : 0<Cb) (ht : 0<t) (ht1 : t≤1) (hcms : 0<cms) (hcms1 : cms≤1/128) :
    ∃ η₀ bStar : ℝ,0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
    ∀ cold : ℝ,0<cold → ∃ Cf CT c : ℝ,1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ c≤cold ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n transport dim : ℕ) (Q : Rotations transport dim) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 3200≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ → 0<Δ → 0<ε →
      ε≤c*min L (Real.sqrt (L*Δ)) → (∀ j,0<weight j) → (∀ j,weight j≤1) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      ∃ P : ChiFine.Parameters,P.c=cms ∧ P.ℓ=(D J []).ell ∧ P.β=(D J []).width ∧
      P.θ=fineParameter (θ*μ) (3*μ/2) P.ℓ (normalCoefficient L J) Cf J ∧
      (∀ j I,0<(D j I).width ∧ 0<(D j I).radius) ∧
      (∀ (blocks : ℕ) (x : PhysicalBase E blocks transport dim),
        ‖iteratedFDeriv ℝ 2 (physicalUpperBase blocks Q M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius) x‖≤L/4 ∧
        ‖gradient (fun w => physicalUpperBase blocks Q M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius (pack x.fst w)) x.snd‖≤L/4) ∧
      ∀ (normals : ℕ) (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (z : Full (PhysicalBase E J transport dim) normals),
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := physicalHierarchyExtension Q M D P J normals index radialIndex fineIndex rad R (normalCoefficient L J)
      ‖iteratedFDeriv ℝ 2 Ext z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤2*θ/9 := by
  obtain ⟨C,B,hC,hB,hjet⟩ := wide_physical_hierarchy_extension_jets A Kminus ζ cn hA hKminus hζ hζ1 hcn hcn1
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hupper⟩ := uniform_physical_upper_base_certificate
    A Kminus ζ cn CR Km Cgap hA hKminus hζ hζ1 hcn hcn1 hCR hCRcn hKm hCgap
  refine ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,?_⟩
  intro cold hcold
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hCff,hCfw,hCTc,_hCTr,hscales⟩ :=
    physical_parameter_scales hC hB hη₀ hη₀1 hbs hCb hη hη1 ht hcn hlen hζ
      (lt_of_lt_of_le zero_lt_one hCR) hcms hcold
  refine ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,?_⟩
  intro E _ _ _ n transport dim Q L μ κ θ Δ ε weight hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  let e := EndpointTransportNormalization.calibrationAccuracy κ ε
  obtain ⟨hθ,hJ,hT,hbp,_hhp,hKg,hKgη,hgain,hrange,hv0,hHpaid,hTpaid⟩ :=
    hscales L μ κ θ Δ ε hL hμ hκ hθκ hbranch hΔ hε hacc
  have hr := sourceRatio_ge_one hT
  have hres (j) := (hrange j).1
  have hres1 (j) := (hrange j).2.1
  have hreslen (j) := (hrange j).2.2
  have he : 0<e := EndpointTransportNormalization.calibrationAccuracy_pos hκ hε
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg) (mul_pos hη₀ hL) hbp hr hres
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (D j I) :=
    sourceNode_admissible A Kminus ζ cn (resolution η Kg j) CR _ _ (sourceRatio T j) (weight j) (V j I)
      hKminus hζ hζ1 (hres j) (hres1 j) hCR (hp j).1 (hp j).2 (hr j) (hw j) (hw1 j)
  have hwidth (j : ℕ) (I : List ℕ) : 0<(D j I).width := (hp (j+1)).2
  have hell : (D J []).ell=η₀*L*curvature T J := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    rw [hj]
    exact source_high_node_curvature initial (lt_of_lt_of_le zero_lt_one hT) η Kg j
  have hv : 1≤fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J := by
    rw [hell]
    exact hv0
  let P : ChiFine.Parameters := ⟨(D J []).ell,(D J []).width,
    fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J,cms,
    (hp (J+1)).1.le,hwidth J [],hv,hcms,hcms1⟩
  refine ⟨P,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · intro j I
    exact ⟨hwidth j I,(hwidth j I).trans_le (hadm j I).2.2.1⟩
  · intro blocks x
    exact hupper E transport dim n Q L Δ hL hΔ (sourceRatio T) (resolution η Kg) weight hr rfl
      hres hres1 hreslen hw hw1 U V J blocks x
  · intro normals index radialIndex fineIndex z
    have hj := hjet E n transport dim Q L μ θ κ η₀ b η t Cb e Kg CT CR Km weight
      hL hμ (zero_le_one.trans hθ) hθκ (by linarith) hη₀ hbp hη hη1 ht ht1 hCb.le he.le
      hKg hKgη (lt_of_lt_of_le zero_lt_one hCT) hCTc hT hJ hlen hgain hw hw1 hCR hCRcn hKm
      U V normals P rfl rfl index radialIndex fineIndex Cf 6 (by norm_num) hCff hCfw rfl z
    have hCn := SmallGapLiftSupport.C_pos
    have hcoef : 576*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀))≤
        1104*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀)) := by gcongr ; norm_num
    have hH : 192*SmallGapLiftSupport.C*Cb*(cn/η^2)^(2/3:ℝ)+
        576*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀))+144*CR*Cb≤
        wideHessianConstant Cb η₀ η cn CR cms :=
      add_le_add_right (add_le_add_left hcoef _) _
    refine ⟨hj.1.trans ((mul_le_mul_of_nonneg_right hH (div_nonneg he.le hL.le)).trans hHpaid),hj.2.trans ?_⟩
    convert hTpaid using 1 ; dsimp only [wideThirdCoarse,wideThirdRadial] ; ring

end Bilevel.EndpointTransportResponse

