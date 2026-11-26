import Bilevel.ChiFixedDepthAssembly
import Bilevel.ChiOuterSourceUpperBase

/-! Actual fixed-depth source parameter certificate. All scalar constants
are chosen before public budgets, dimensions and frames. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

set_option maxHeartbeats 1600000 in
theorem fixed_parameter_certificate {A Kminus ζ cn η CR Km Cb t cms : ℝ}
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2) (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR)
    (hKm' : 1≤Km) (hCb : 0<Cb) (ht : 0<t) (ht1 : t≤1) (hcms : 0<cms) (hcms1 : cms≤1/128) :
    ∃ η₀ Cf c : ℝ,0<η₀ ∧ η₀≤1 ∧ 1≤Cf ∧ 0<c ∧ c≤1 ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ b ε Kg : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 2≤κ → 0<b → b≤1 → 0≤ε → ε≤c*L → 0<Kg → 1/η≤Kg →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1 →
      (∀ j,0<weight j) → (∀ j,weight j≤1) →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v := fineParameter μ (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
      ∃ hv : 1≤v,(∀ j I,0<(D j I).width) ∧
      (∀ blocks z,‖iteratedFDeriv ℝ 2 (upperBase blocks M (initial.curvature/24) D 1 (rad 0) (R 0)) z‖≤L/4 ∧
        ‖gradient (fun u => upperBase blocks M (initial.curvature/24) D 1 (rad 0) (R 0) (pack z.fst u)) z.snd‖≤L/4) ∧
      ∀ (blocks normals : ℕ) (index radialIndex : Fin 1 → Fin normals) (fineIndex : Fin normals) (hβ : 0<(D 1 []).width),
      let Ext := hierarchyExtension blocks M D 1 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1)
      let Ext₀ := hierarchyInactiveExtension blocks M D 1 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1)
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤(2:ℝ)/9 ∧
      ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤(2:ℝ)/9 := by
  obtain ⟨Cu,hCu,hupper⟩ := source_upper_base_budgets A Kminus ζ cn CR Km hA hKm hζ hζ1 hcn hcn1 hCR hCRcn hKm'
  obtain ⟨C,Ba,Bi,hC,hBa,hBi,hjets⟩ := fixed_hierarchy_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨η₀,Cf,c,hη₀,hη₀1,hηCu,hCf,hCfa,hCfi,hCfa2,hCfi2,hc,hc1,_hcold,hthird,hnum⟩ :=
    exists_fixed_depth_parameters hCu hC hBa hBi hCb ht hη hcn hζ (by linarith only [hCR]) hcms (by norm_num : (0:ℝ)<1)
  refine ⟨η₀,Cf,c,hη₀,hη₀1,hCf,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ b ε Kg weight hL hμ hκ hb hb1 hε hacc hK hthreshold hwidthGain hw hw1 U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let v := fineParameter μ (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
  have hres := base_resolution_positive hη hK
  have hresle := base_resolution_le hK hthreshold hη
  have hres1 (j : ℕ) : resolution η Kg j≤1 := (hresle j).trans hη1
  have hlen' (j : ℕ) : 128≤cn/(resolution η Kg j)^2 := hlen.trans
    (div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j)) (pow_le_pow_left₀ (hres j).le (hresle j) 2))
  have hp := parentScale_positive initial (sourceRatio 1) (resolution η Kg)
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one le_rfl) hres
  have hwidth (j : ℕ) (I : List ℕ) : 0<(D j I).width := (hp (j+1)).2
  have hell : (D 1 []).ell=η₀*L := by
    have hh := source_high_node_curvature initial (by norm_num : (0:ℝ)<1) η Kg 0
    simpa only [curvature,Real.one_rpow,mul_one] using hh
  have hnumeric := hnum L μ ε hL hμ hε hacc
  have hv : 1≤v := by dsimp [v]; rw [hell]; exact hnumeric.1
  have hu := hupper E F n initial (mul_pos hη₀ hL) hb (sourceRatio 1) (resolution η Kg) weight
    (sourceRatio_ge_one le_rfl) rfl hres hres1 hlen' hw hw1 U V
  have hCup : 0<Cu := by linarith only [hCu]
  have hηbound := (le_div_iff₀ (show 0<4*Cu by positivity)).mp hηCu
  have hbase : Cu*(η₀*L)≤L/4 := by
    have hh := mul_le_mul_of_nonneg_right hηbound hL.le
    nlinarith only [hh]
  refine ⟨hv,hwidth,?_,?_⟩
  · intro blocks z
    have hh := hu 1 blocks z
    refine ⟨hh.1.trans hbase,hh.2.trans ?_⟩
    change Cu*((η₀*L)*b)≤L/4
    have hh' := mul_le_mul_of_nonneg_left hb1 (show 0≤Cu*(η₀*L) by positivity)
    nlinarith only [hh',hbase]
  intro blocks normals index radialIndex fineIndex hβ z
  have hnormal := SmallGapLiftSupport.C_pos
  have hCfa' : 6*(max 1 (24*SmallGapLiftSupport.C/cms^2)*Ba^2)≤Cf := by
    apply le_trans _ hCfa
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg Ba)
    apply max_le_max le_rfl
    apply div_le_div_of_nonneg_right _ (sq_nonneg cms)
    linarith only [hnormal]
  have hh := hjets E F n L μ κ η₀ b η t Cb ε Kg CR Km weight hL hμ hκ hη₀ hb hη hη1 ht ht1 hCb.le hε
    hK hthreshold hlen hwidthGain hw hw1 hCR hCRcn hKm' U V blocks normals index radialIndex fineIndex
    cms Cf hcms hcms1 hCfa' hCfa2 hCfi hCfi2 hv hcms hβ z
  exact ⟨hh.1.trans hnumeric.2,hh.2.1.trans hthird,hh.2.2.1.trans hnumeric.2,hh.2.2.2.trans hthird⟩

end Bilevel.ChiExtensionCalibration
