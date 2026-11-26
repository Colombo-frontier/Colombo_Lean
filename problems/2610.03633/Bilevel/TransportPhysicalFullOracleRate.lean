import Bilevel.TransportPhysicalExpectedRate
import Bilevel.TransportPhysicalSourceOracle

/-! Same actual physical expected-rate family, now identified with the
complete conservative original pointmass SFO pair of each retained Primitive. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  EndpointTransportResponse ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule
  ChiIndependentWidths ChiPrefixEvaluation ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem physical_full_oracle_rate_witness :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf CT c : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧
      ∃ cRate : ℝ,0<cRate ∧ ∃ q : ℕ,
    ∀ (L κ θ Δ ε : ℝ),0<L → 3200≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let macroN := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      let weight := fun j => t^(j+1)
      let rad := sourcePublicRadialWeight initial (sourceRatio T) (resolution η Kg) weight ζ
      let R := sourcePublicNodeRadius initial (sourceRatio T) (resolution η Kg) weight CR ζ
      let layers := EndpointTransportNormalization.interiors κ
      ∃ hJ : 1≤J,64≤S ∧ macroN+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∃ P : ChiFine.Parameters,P.c=1/128 ∧
      P.ℓ=sourcePublicEll initial (sourceRatio T) (resolution η Kg) J ∧
      P.β=sourcePublicWidth initial (sourceRatio T) (resolution η Kg) J ∧
      P.θ=sourcePublicFineParameter initial (sourceRatio T) (resolution η Kg) J
        (θ*(L/κ)) (L/κ) L Cf ∧
      (∀ (dim : ℕ) (Q : Rotations layers dim) (U : Space macroN →ₗᵢ[ℝ] Block dim)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim),
        let M := sourceMacroNode macroN initial Km U
        let G := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
        let core := physicalHierarchyExtension Q M G P J (2*J) (sourceCoarseNormal J)
          (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
        ContDiff ℝ 3 core ∧ ∀ z,‖iteratedFDeriv ℝ 2 core z‖≤(1:ℝ)/12) ∧
      ∃ (dim : ℕ),
      ∃ (hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤dim),
      ∃ (hAll : ∀ i : FrameIndex (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J,chainSize i+1≤dim),
      ∃ (hT : capacity (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) (J+1) 0≤dim),
      ∃ hF : ∀ a : PhysicalSample (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J layers dim,
        LipschitzWith (⟨1/12,by norm_num⟩ : NNReal) (gradient (physicalOriginalPotential macroN J layers dim (2*J) cn (sourceRatio T) (resolution η Kg) hdim hAll hT initial weight 3 1 ζ CR Km P (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J) a)),
      PhysicalRateProperty macroN J layers dim (2*J) cn (sourceRatio T) (resolution η Kg) hdim hAll hT initial weight 3 1 ζ CR Km (initial.curvature/24) P
        (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
        ((normalCoefficient L J) • normalOnes (2*J)) (3*(L/κ)/2) (L/16)
        (EndpointTransportNormalization.coupling L κ) (L/4) hF (EndpointTransportNormalization.gain κ) ε
        (cRate*ChiRefinementRates.deterministic L θ κ Δ ε/(Real.log (2+θ))^q) ∧
      ∀ a : PhysicalSample (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J layers dim,
      let Q := physicalRotations a.1
      let M := sourcePhysicalMacro macroN J layers dim cn (sourceRatio T) (resolution η Kg) hAll a initial Km
      let G := sourcePhysicalGeometry macroN J layers dim cn (sourceRatio T) (resolution η Kg) hdim hT a initial weight 3 1 ζ CR
      let core := physicalHierarchyExtension Q M G P J (2*J) (sourceCoarseNormal J)
        (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let base := physicalUpperBase J Q M (initial.curvature/24) G J (rad 0) (R 0)
      ∃ Pr : Model.Primitive (X:=HybridOuter (Block dim) (Blocks J (Block dim)) dim)
        (Y:=HybridVariables (Blocks J (Block dim)) (Normals (2*J)) layers dim)
        (L/κ) L L L (θ*(L/κ)),
      (∀ x y,Pr.f x y=base (pack x.fst.fst y.fst)+(normalCoefficient L J)*normalReadout (2*J) y.snd) ∧
      ∃ (hExt : ContDiff ℝ 3 (physicalExtension core))
        (hExt2 : ∀ z,‖iteratedFDeriv ℝ 2 (physicalExtension core) z‖≤(1:ℝ)/12),
      (∀ x y,Pr.g x y=sourceHybridLower L κ Q (physicalExtension core) hExt
        ⟨1/12,by norm_num⟩ hExt2 (by change (1:ℝ)/12<1;norm_num) (pack x y)) ∧
      ∃ r : Pr.Response,Nonempty (Pr.GapCertificate r 0 Δ) ∧ r.y 0=0 ∧
        (∀ x,r.y x=ChiHybrid.responseOfExtension (physicalExtension core) (sourceHybridTangent L κ Q) x) ∧
        (∀ x,Pr.hyperobjective r x=jointOuter (J+1) M (initial.curvature/24) G rad R J
          (EndpointTransportNormalization.gain κ) (sourceCoordinates J dim x)) ∧
        (∀ x y,Pr.IsLowerSolution x y ↔ y=r.y x) ∧ Pr.hyperobjective r 0=0 ∧
        (∀ x,M.coordinates x.fst.fst (Fin.last macroN)<b → 8*ε≤‖gradient (Pr.hyperobjective r) x‖) ∧
        HasPhysicalFullOracle macroN J layers dim (2*J) cn (sourceRatio T) (resolution η Kg) hdim hAll hT
          initial weight 3 1 ζ CR Km (initial.curvature/24) P (sourceCoarseNormal J) (sourceRadialNormal J)
          (sourceFineNormal J hJ) rad R (normalCoefficient L J) (3*(L/κ)/2) (L/16)
          (EndpointTransportNormalization.coupling L κ) (L/4) hF (L/κ) L (θ*(L/κ)) a Pr := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,cRate,hcRate,q,hmain⟩ := physical_expected_rate_witness
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,cRate,hcRate,q,?_⟩
  intro L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  dsimp only
  obtain ⟨hJ,hS,hn,hm,hr,hrη,hcount,P,hPc,hPℓ,hPβ,hPθ,hcore,dim,hdim,hAll,hT,hF,hrate,hfamily⟩ :=
    hmain L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  refine ⟨hJ,hS,hn,hm,hr,hrη,hcount,P,hPc,hPℓ,hPβ,hPθ,hcore,dim,hdim,hAll,hT,hF,hrate,?_⟩
  intro a
  obtain ⟨Pr,hf,hExt,hExt2,hg,r,hgap,hzero,hresponse,hmean,hunique,hmean0,hbarrier⟩ := hfamily a
  refine ⟨Pr,hf,hExt,hExt2,hg,r,hgap,hzero,hresponse,hmean,hunique,hmean0,hbarrier,?_⟩
  exact hasPhysicalSourceFullOracle _ _ dim _ L κ cn _ _ hdim hAll hT _ _ 3 1 ζ CR Km _ P _ _ _ _ _ _ hF
    (θ*(L/κ)) a Pr hExt hExt2 hf hg

end Bilevel.TransportHierarchy
