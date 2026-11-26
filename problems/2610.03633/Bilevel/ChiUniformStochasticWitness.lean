import Bilevel.ChiUniformDeterministicWitness
import Bilevel.ChiHierarchySignal
import Bilevel.ChiConservativeCertificate

/-! The actual full-window Primitive, gap, unique response and conservative
full-query SFO share all construction constants. The informative envelope
retains the finest normal width. No information lower bound is assumed. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths
universe u

set_option maxHeartbeats 400000 in
theorem wide_stochastic_witness (Braw : ℝ) (hBraw : 0≤Braw) :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf CT c Bs : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧ 1≤Bs ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L μ κ θ Δ ε : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∃ hJ : 1≤J,64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M : Node E := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v : ℝ := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      2*SmallGapLiftSupport.C*Braw*(1/128)*(D J []).ell*((D J []).width)^2/
        (normalCoefficient L J*Real.sqrt v)≤(D J []).width/128 ∧
      let Ext := hierarchyExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
        (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      ∃ P : Model.Primitive (X:=Joint E (Blocks (J+1) F)) (Y:=Joint (Blocks (J+1) F) (Normals (2*J))) μ L L L (θ*μ),
      (∀ x y,P.f x y=hierarchyUpper (J+1) M (initial.curvature/24) D J rad R (2*J) (normalCoefficient L J) x.fst y) ∧
      (∀ x y,P.g x y=extensionLower Ext hExt ⟨1/12,by norm_num⟩ hb
        (by change (1:ℝ)/12<1;norm_num) (3*μ/2) (L/4) x.fst x.snd y) ∧
      ∃ r : P.Response,r.y 0=0 ∧ Nonempty (P.GapCertificate r 0 Δ) ∧
        (∀ x,r.y x=pack ((κ/6) • x.snd) (normalTrace Ext x.fst ((κ/6) • x.snd))) ∧
        (∀ x,P.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) D rad R J (κ/6) x) ∧
        (∀ x y,P.IsLowerSolution x y ↔ y=r.y x) ∧ P.hyperobjective r 0=0 ∧
        (∀ x,M.coordinates x.fst (Fin.last n)<b → 8*ε≤‖gradient (P.hyperobjective r) x‖) ∧
        let W := ZeroChainSchedule.width (1/128) (D J []).width v (ZeroChainSchedule.levels v)
        let ηsig := 2*SmallGapLiftSupport.C*Bs^(J+2)*(D J []).ell*(D J []).width*W/normalCoefficient L J
        let hExt₀ : ContDiff ℝ 3 Ext₀ := hierarchyInactiveExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
          (fun i => hwidth (i.val+1) [])
        ∃ hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/4,
        (∀ z,‖iteratedFDeriv ℝ 1 (fun q => Ext q-Ext₀ q) z‖≤ηsig) ∧
        let g := fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ hb (by change (1:ℝ)/12<1;norm_num) μ L
        let g₀ := fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L
        ChiPrimitive.HasConservativeOracle P g g₀ (4*μ*ηsig) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,hdet⟩ :=
    wide_deterministic_witness.{u} Braw hBraw
  obtain ⟨Bs,hBs,hsignal⟩ := source_hierarchy_signal_envelope
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,hBs,?_⟩
  intro E F _ _ _ _ _ _ _ _ L μ κ θ Δ ε hL hμ hκ hκeq hθκ hbranch hΔ hε hacc
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let n := S-1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  let weight := fun j : ℕ => t^(j+1)
  obtain ⟨hJ,hS,hn,hn₀,hrp,hratio,hcount,hd⟩ := hdet E F L μ κ θ Δ ε hL hμ hκ hκeq hθκ hbranch hΔ hε hacc
  refine ⟨hJ,hS,hn,hn₀,hrp,hratio,hcount,?_⟩
  intro U V
  let M : Node E := sourceMacroNode n initial Km U
  let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
  obtain ⟨hv,hwidth,hforce,hb,hi₁₂,P,hf,hg,r,hrzero,hgap,hr,hm,hu,hzero,hgrad⟩ := hd U V
  have hi := fun z => (hi₁₂ z).trans (by norm_num : (1:ℝ)/12≤1/4)
  have hbranches := wide_branch_conditions hCT hbranch
  have hT : 1≤T := (by norm_num : (1:ℝ)≤2).trans hbranches.2.2
  have hbp : 0<b := macroWidth_pos hbs hΔ (mul_pos hη₀ hL)
  have hK : 0<κ/6 := by linarith only [hκ]
  have hCb : 0<32/t := by positivity
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKgp : 0<Kg := div_pos hbp hhp
  have hKg1 : 1≤Kg := by
    apply (le_div_iff₀ hhp).mpr
    simpa only [one_mul] using (div_le_one hbp).mp (hratio.trans hη1)
  have hres1 : ∀ j,resolution η Kg j≤1 := by
    intro j
    cases j with
    | zero => exact (div_le_one hKgp).mpr hKg1
    | succ j => exact hη1
  have hζ1 : ζ≤1 := by linarith only [hζsmall]
  have hw (j : ℕ) : 0<weight j := pow_pos ht _
  have hw1 (j : ℕ) : weight j≤1 := pow_le_one₀ ht.le ht1.le
  have hdn : 0<normalCoefficient L J := normalCoefficient_pos hL hJ
  have hs := hsignal E F n initial (mul_pos hη₀ hL) hbp (sourceRatio T) (resolution η Kg) weight
    3 1 ζ cn CR Km (sourceRatio_ge_one hT) (base_resolution_positive hη hKgp) hres1 hw hw1
    (by norm_num) hζ hζ1 hCR hKm U V J (J+1) (2*J) (1/128) _ (by norm_num) (by norm_num)
    hv (hwidth J []) (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
    (fun j => weight j*(D j []).nu) (fun j => (D j []).radius) (normalCoefficient L J) hdn
  refine ⟨hv,hwidth,hforce,hb,hi₁₂,P,hf,hg,r,hrzero,hgap,hr,hm,hu,hzero,hgrad,hi,hs,?_⟩
  have hell : 0<(D J []).ell :=
    (parentScale_positive initial (sourceRatio T) (resolution η Kg) (mul_pos hη₀ hL) hbp
      (sourceRatio_ge_one hT) (base_resolution_positive hη hKgp) (J+1)).1
  let v : ℝ := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
  have hW := ZeroChainSchedule.width_pos (1/128) (D J []).width v (by norm_num) (hwidth J []) hv
    (ZeroChainSchedule.levels v)
  have hC := SmallGapLiftSupport.C_pos
  have hβ := hwidth J []
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  let Ext := hierarchyExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
  let Ext₀ := hierarchyInactiveExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
  have hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
    (fun i => hwidth (i.val+1) [])
  have hExt₀ : ContDiff ℝ 3 Ext₀ := hierarchyInactiveExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
    (fun i => hwidth (i.val+1) [])
  have hηsig : 0<2*SmallGapLiftSupport.C*Bs^(J+2)*(D J []).ell*(D J []).width*
      ZeroChainSchedule.width (1/128) (D J []).width v (ZeroChainSchedule.levels v)/normalCoefficient L J := by
    positivity
  intro instM instB instS σ
  exact ChiPrimitive.extension_hasConservativeOracle (X:=E) (U:=Blocks (J+1) F) (V:=Normals (2*J))
    Ext Ext₀ hExt hExt₀ hb hi hμ hηsig hs P hg σ

end Bilevel.ChiExtensionCalibration
