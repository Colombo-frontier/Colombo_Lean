import Bilevel.ChiFixedDepthParameters
import Bilevel.ChiOuterSourceUpperBase
import Bilevel.ChiVirtualSourceIdentity
import Bilevel.ChiVirtualBorelInverse

/-! Actual fixed-depth source parameter certificate. All scalar constants
are chosen before public budgets, dimensions and frames. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation

set_option maxHeartbeats 1600000 in
theorem fixed_virtual_parameter_certificate {A Kminus ζ cn η CR Km Cb t cms : ℝ}
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
      (∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤(2:ℝ)/9 ∧
      ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤(2:ℝ)/9) ∧
      ∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
      let f := statePotential active blocks M D 1 rM r cms v normals index radialIndex fineIndex rad R (normalCoefficient L 1) p
      ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤(2:ℝ)/9 := by
  obtain ⟨η₀,Cf,c,hη₀,hη₀1,hCf,hc,hc1,hpars⟩ := fixed_parameter_certificate
    hA hKm hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm' hCb ht ht1 hcms hcms1
  refine ⟨η₀,Cf,c,hη₀,hη₀1,hCf,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ b ε Kg weight hL hμ hκ hb hb1 hε hacc hKg hKgη hgain hw hw1 U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let v := fineParameter μ (3*μ/2) ((D 1 []).ell) (normalCoefficient L 1) Cf 1
  obtain ⟨hv,hwidth,hupper,hjets⟩ := hpars E F n L μ κ b ε Kg weight
    hL hμ hκ hb hb1 hε hacc hKg hKgη hgain hw hw1 U V
  refine ⟨hv,hwidth,hupper,?_⟩
  intro blocks normals index radialIndex fineIndex hβ
  refine ⟨hjets blocks normals index radialIndex fineIndex hβ,?_⟩
  intro rM r active p hp
  have hparents := parentScale_positive initial (sourceRatio 1) (resolution η Kg)
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one le_rfl) (base_resolution_positive hη hKg)
  have hR (i : Fin 1) : 0<R (i.val+1) := by
    let sc := parentScale initial (sourceRatio 1) (resolution η Kg) (i.val+1)
    change 0<CR*sc.force*Real.sqrt (sourceRatio 1 (i.val+1))/(weight (i.val+1)*(ζ*sc.curvature))
    have hf : 0<sc.force := mul_pos (hparents _).1 (hparents _).2
    have hr : 0<sourceRatio 1 (i.val+1) := lt_of_lt_of_le zero_lt_one (sourceRatio_ge_one le_rfl _)
    exact div_pos (mul_pos (mul_pos (by linarith only [hCR]) hf) (Real.sqrt_pos.mpr hr))
      (mul_pos (hw _) (mul_pos hζ (hparents _).1))
  have hC := statePotential_contDiff active blocks M D 1 rM r cms v hcms hβ hv normals
    index radialIndex fineIndex rad R (normalCoefficient L 1) hR (fun i => hwidth (i.val+1) []) p hp
  refine ⟨hC,?_⟩
  let U' := completionFrame M.n (rM p.1) p.2.1 M.frame hp.1
  let V' := fun j I => completionFrame (D j I).n (r p.1 j I) (p.2.2 j I) (D j I).frame (hp.2 j I)
  obtain ⟨hv',_hwidth',_hu',hj'⟩ := hpars (Joint E E) (Joint F F) n L μ κ b ε Kg weight
    hL hμ hκ hb hb1 hε hacc hKg hKgη hgain hw hw1 U' V'
  have hcompleted := hj' blocks normals index radialIndex fineIndex hβ
  intro z
  have h2 := activePotential_jet_bound blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
    (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L 1) (fun i => hwidth (i.val+1) []) 2 (by norm_num) (1/12)
    (fun q => (hcompleted q).1) z
  have h3 := activePotential_jet_bound blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
    (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L 1) (fun i => hwidth (i.val+1) []) 3 (by norm_num) (2/9)
    (fun q => (hcompleted q).2.1) z
  have h02 := inactivePotential_jet_bound blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
    (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L 1) (fun i => hwidth (i.val+1) []) 2 (by norm_num) (1/12)
    (fun q => (hcompleted q).2.2.1) z
  have h03 := inactivePotential_jet_bound blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
    (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L 1) (fun i => hwidth (i.val+1) []) 3 (by norm_num) (2/9)
    (fun q => (hcompleted q).2.2.2) z
  cases active with
  | false =>
    change ‖iteratedFDeriv ℝ 2 (virtualInactive blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L 1)) z‖≤1/12 ∧ _
    rw [virtualInactive_jet_eq blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1) hR 2 z]
    change _ ∧ ‖iteratedFDeriv ℝ 3 (virtualInactive blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L 1)) z‖≤2/9
    rw [virtualInactive_jet_eq blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1) hR 3 z]
    exact ⟨h02,h03⟩
  | true =>
    change ‖iteratedFDeriv ℝ 2 (virtualActive blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L 1)) z‖≤1/12 ∧ _
    rw [virtualActive_jet_eq blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1) hR 2 z]
    change _ ∧ ‖iteratedFDeriv ℝ 3 (virtualActive blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2
      cms v normals index radialIndex fineIndex rad R (normalCoefficient L 1)) z‖≤2/9
    rw [virtualActive_jet_eq blocks M D 1 (rM p.1) (r p.1) p.2.1 p.2.2 M.frame
      (fun j I => (D j I).frame) hp.1 hp.2 cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L 1) hR 3 z]
    exact ⟨h2,h3⟩

end Bilevel.ChiExtensionCalibration
