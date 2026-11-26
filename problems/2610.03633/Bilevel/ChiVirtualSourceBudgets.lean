import Bilevel.ChiVirtualSourceIdentity

/-! The same source calibration controls actual and finite-prefix virtual
extensions on the full accuracy window. Completion changes only frames,
and the virtual scalar is an isometric restriction of the completed one. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation
universe u v

set_option maxHeartbeats 1800000 in
theorem wide_virtual_parameter_certificate
    {A Kminus ζ cn η CR Km Cgap Cb t cms Braw : ℝ}
    (hA : 0≤A) (hKminus : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hcn : 0<cn) (hcn1 : cn≤1) (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) (hCgap : 1≤Cgap)
    (hCb : 0<Cb) (ht : 0<t) (ht1 : t≤1) (hcms : 0<cms) (hcms1 : cms≤1/128) (hBraw : 0≤Braw) :
    ∃ η₀ bStar : ℝ,0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
    ∀ cold : ℝ,0<cold → ∃ Cf CT c : ℝ,1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ c≤cold ∧
    ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ κ θ Δ ε : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 2≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ → 0<Δ → 0<ε →
      ε≤c*min L (Real.sqrt (L*Δ)) → (∀ j,0<weight j) → (∀ j,weight j≤1) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1≤v,
      (∀ j I,0<(D j I).width) ∧
      2*SmallGapLiftSupport.C*Braw*cms*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v)≤(D J []).width/128 ∧
      (∀ (blocks : ℕ) (x : Joint E (Blocks blocks F)),
        ‖iteratedFDeriv ℝ 2 (upperBase blocks M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius) x‖≤L/4 ∧
        ‖gradient (fun w => upperBase blocks M (initial.curvature/24) D J
          (weight 0*(D 0 []).nu) (D 0 []).radius (pack x.fst w)) x.snd‖≤L/4) ∧
      ∀ (hβ : 0<(D J []).width) (blocks normals : ℕ)
        (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals),
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let Ext := hierarchyExtension blocks M D J cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension blocks M D J cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      (∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext z‖≤2*θ/9 ∧
        ‖iteratedFDeriv ℝ 2 Ext₀ z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Ext₀ z‖≤2*θ/9) ∧
      ∀ (AuxM : Type u) (AuxD : Type v) [NormedAddCommGroup AuxM] [InnerProductSpace ℝ AuxM] [CompleteSpace AuxM]
        [NormedAddCommGroup AuxD] [InnerProductSpace ℝ AuxD] [CompleteSpace AuxD]
        (rM : ℕ) (r : ℕ → List ℕ → ℕ)
        (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
        (VM : Space M.n →ₗᵢ[ℝ] AuxM) (VD : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] AuxD)
        (hmGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
          ⟪macroColumns a,macroColumns b⟫=if a=b then 1 else 0)
        (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
          ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0),
      let Virt := activePotential blocks M D J rM r macroColumns columns VM VD hmGram hGram
        cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      let Virt₀ := inactivePotential blocks M D J rM r macroColumns columns VM VD hmGram hGram
        cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 Virt z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Virt z‖≤2*θ/9 ∧
      ‖iteratedFDeriv ℝ 2 Virt₀ z‖≤1/12 ∧ ‖iteratedFDeriv ℝ 3 Virt₀ z‖≤2*θ/9 := by
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hparameter⟩ := wide_parameter_certificate
    hA hKminus hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCgap hCb ht ht1 hcms hcms1 hBraw
  refine ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,?_⟩
  intro cold hcold
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hpars⟩ := hparameter cold hcold
  refine ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,?_⟩
  intro E F _ _ _ _ _ _ n L μ κ θ Δ ε weight hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let v := fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J
  obtain ⟨hv,hwidth,hforce,hupper,hjets⟩ := hpars E F n L μ κ θ Δ ε weight
    hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1 U V
  refine ⟨hv,hwidth,hforce,hupper,?_⟩
  intro hβ blocks normals index radialIndex fineIndex
  refine ⟨hjets hβ blocks normals index radialIndex fineIndex,?_⟩
  intro AuxM AuxD _ _ _ _ _ _ rM r macroColumns columns VM VD hmGram hGram z
  let U' := completionFrame M.n rM macroColumns VM hmGram
  let V' := fun j I => completionFrame (D j I).n (r j I) (columns j I) (VD j I) (hGram j I)
  obtain ⟨hv',_hw',_hf',_hu',hj'⟩ := hpars (Joint E AuxM) (Joint F AuxD) n L μ κ θ Δ ε weight
    hL hμ hκ hθκ hbranch hΔ hε hacc hw hw1 U' V'
  have hcompleted := hj' hβ blocks normals index radialIndex fineIndex
  have h2 := activePotential_jet_bound blocks M D J rM r macroColumns columns VM VD hmGram hGram
    cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
    (fun i => hwidth (i.val+1) []) 2 (by norm_num) (1/12)
    (fun q => (hcompleted q).1) z
  have h3 := activePotential_jet_bound blocks M D J rM r macroColumns columns VM VD hmGram hGram
    cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
    (fun i => hwidth (i.val+1) []) 3 (by norm_num) (2*θ/9)
    (fun q => (hcompleted q).2.1) z
  have h02 := inactivePotential_jet_bound blocks M D J rM r macroColumns columns VM VD hmGram hGram
    cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
    (fun i => hwidth (i.val+1) []) 2 (by norm_num) (1/12)
    (fun q => (hcompleted q).2.2.1) z
  have h03 := inactivePotential_jet_bound blocks M D J rM r macroColumns columns VM VD hmGram hGram
    cms v hcms hβ hv normals index radialIndex fineIndex rad R (normalCoefficient L J)
    (fun i => hwidth (i.val+1) []) 3 (by norm_num) (2*θ/9)
    (fun q => (hcompleted q).2.2.2) z
  exact ⟨h2,h3,h02,h03⟩

end Bilevel.ChiExtensionCalibration

