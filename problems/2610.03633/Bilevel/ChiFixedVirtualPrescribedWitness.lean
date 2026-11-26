import Bilevel.ChiFixedVirtualStochasticWitness

/-! The actual fixed-depth Primitive, gap, unique response and conservative
full-query SFO share all construction constants. The informative envelope
retains the finest normal width. No information lower bound is assumed. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths ChiPrefixEvaluation
universe u

set_option maxHeartbeats 400000 in
theorem fixed_virtual_prescribed_variation_witness :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf c Bs : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 0<c ∧ c≤1 ∧ 1≤Bs ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L μ κ Δ ε ρg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → μ≤ρg →
      0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := (1:ℕ)
      let T := (1:ℝ)
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M : Node E := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      let v : ℝ := fineParameter μ (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∃ hv : 1≤v, ∃ hwidth : ∀ j I,0<(D j I).width,
      let Ext := hierarchyExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
      let Ext₀ := hierarchyInactiveExtension (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
      let hExt : ContDiff ℝ 3 Ext := hierarchyExtension_contDiff (J+1) M D J (1/128) v (by norm_num) (hwidth J []) hv (2*J)
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
        (fun i => hwidth (i.val+1) [])
      ∃ hb : ∀ z,‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12,
      (∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/12) ∧
      (∀ (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
        (p : VirtualState M D),ValidState M D rM r p →
        let f := statePotential active (J+1) M D J rM r (1/128) v (2*J)
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J) p
        ContDiff ℝ 3 f ∧ ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(1:ℝ)/12 ∧ ‖iteratedFDeriv ℝ 3 f z‖≤(2:ℝ)/9) ∧
      ∃ P : Model.Primitive (X:=Joint E (Blocks (J+1) F)) (Y:=Joint (Blocks (J+1) F) (Normals (2*J))) μ L L L ρg,
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
          (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J (by norm_num)) rad R (normalCoefficient L J)
          (fun i => hwidth (i.val+1) [])
        ∃ hi : ∀ z,‖iteratedFDeriv ℝ 2 Ext₀ z‖≤(1:ℝ)/4,
        (∀ z,‖iteratedFDeriv ℝ 1 (fun q => Ext q-Ext₀ q) z‖≤ηsig) ∧
        let g := fullExtensionLower Ext hExt ⟨1/12,by norm_num⟩ hb (by change (1:ℝ)/12<1;norm_num) μ L
        let g₀ := fullExtensionLower Ext₀ hExt₀ ⟨1/4,by norm_num⟩ hi (by change (1:ℝ)/4<1;norm_num) μ L
        ChiPrimitive.HasConservativeOracle P g g₀ (4*μ*ηsig) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,hBs,hfixed⟩ :=
    fixed_virtual_stochastic_witness.{u}
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,c,Bs,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hc,hc1,hBs,?_⟩
  intro E F _ _ _ _ _ _ _ _ L μ κ Δ ε ρg hL hμ hκ hκeq hρg hΔ hε hacc
  dsimp only
  obtain ⟨hS,hn,hn₀,hrp,hratio,hcount,hd⟩ := hfixed E F L μ κ Δ ε hL hμ hκ hκeq hΔ hε hacc
  refine ⟨hS,hn,hn₀,hrp,hratio,hcount,?_⟩
  intro U V
  obtain ⟨hv,hwidth,hb,hi₁₂,hvirtual,P₀,hf,hg,r₀,hrzero,hgap,hr,hm,hu,hzero,hgrad,hi,hs,horacle⟩ := hd U V
  let P := ChiPrimitive.enlargeVariation P₀ ρg hρg
  let r := ChiPrimitive.enlargeVariationResponse P₀ ρg hρg r₀
  have hgap' : Nonempty (P.GapCertificate r 0 Δ) := by
    obtain ⟨g⟩ := hgap
    exact ⟨⟨g.floor,g.lower_bound,g.gap⟩⟩
  exact ⟨hv,hwidth,hb,hi₁₂,hvirtual,P,hf,hg,r,hrzero,hgap',hr,hm,hu,hzero,hgrad,hi,hs,horacle⟩

end Bilevel.ChiExtensionCalibration


