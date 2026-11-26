import Bilevel.EndpointTransportWideUniformCoreWitness
import Bilevel.TransportHierarchySourceGeometry
import Bilevel.ChiCanonicalPublicData
import Bilevel.ChiSourceAuxiliaryFrame

/-! The positive-depth physical source family with public numerical data.
The fine parameter is chosen before ambient dimension or random frames;
the same parameter has a uniform global core Hessian bound. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
  EndpointTransportResponse ChiHierarchyIndex ChiTreeProgress ChiCurvatureSchedule
  ChiIndependentWidths ChiPrefixEvaluation ChiExtension
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem physical_public_witness :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf CT c : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧
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
      ∀ (dim : ℕ)
        (hdim : ∀ j,sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)+1≤dim)
        (hAll : ∀ i : FrameIndex (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J,chainSize i+1≤dim)
        (hT : capacity (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) (J+1) 0≤dim)
        (a : PhysicalSample (sourceCounts macroN cn (sourceRatio T) (resolution η Kg)) J layers dim),
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
        ∀ x,M.coordinates x.fst.fst (Fin.last macroN)<b → 8*ε≤‖gradient (Pr.hyperobjective r) x‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,hmain⟩ := wide_physical_uniform_core_witness
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,
    hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,?_⟩
  intro L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let macroN := S-1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  let dim₀ := max (macroN+1) (sourceAuxiliaryDimension cn η T Kg)
  have hT₀ : 1≤T := (by norm_num : (1:ℝ)≤2).trans (wide_branch_conditions hCT hbranch).2.2
  let U₀ : Space macroN →ₗᵢ[ℝ] Block dim₀ := auxiliaryFrame macroN dim₀ (Nat.le_max_left _ _)
  let V₀ : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim₀ :=
    fun j _ => auxiliaryFrame _ _ ((source_chain_size_le_auxiliary hcn.le hT₀ η Kg j).trans (Nat.le_max_right _ _))
  let Q₀ : Rotations (EndpointTransportNormalization.interiors κ) dim₀ :=
    fun _ => LinearIsometryEquiv.refl ℝ (Block dim₀)
  obtain ⟨hJ,hS,hn,hm,hr,hrη,hcount,hfamily⟩ :=
    hmain (Block dim₀) dim₀ L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  obtain ⟨P,hPc,hPℓ,hPβ,hPθ,hcore,_hPr⟩ := hfamily Q₀ U₀ V₀
  refine ⟨hJ,hS,hn,hm,hr,hrη,hcount,P,hPc,hPℓ,hPβ,?_,hcore,?_⟩
  · change P.θ=fineParameter (θ*(L/κ)) (3*(L/κ)/2)
      (sourcePublicEll initial (sourceRatio T) (resolution η Kg) J) (normalCoefficient L J) Cf J
    have he : P.ℓ=sourcePublicEll initial (sourceRatio T) (resolution η Kg) J := hPℓ
    rw [← he]
    exact hPθ
  intro dim hdim hAll hT a
  obtain ⟨_hJ,_hS,_hn,_hm,_hr,_hrη,_hcount,hfamily'⟩ :=
    hmain (Block dim) dim L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  obtain ⟨P',hP'c,hP'ℓ,hP'β,hP'θ,_hcore',hPr⟩ :=
    hfamily' (physicalRotations a.1) (physicalMacroFrame hAll a) (physicalFamily hdim hT a)
  have he : P'=P := source_fine_parameters_eq P' P (1/128)
    (sourcePublicEll initial (sourceRatio T) (resolution η Kg) J)
    (sourcePublicWidth initial (sourceRatio T) (resolution η Kg) J)
    (fun ell => fineParameter (θ*(L/κ)) (3*(L/κ)/2) ell (normalCoefficient L J) Cf J)
    hP'c hP'ℓ hP'β hP'θ hPc hPℓ hPβ hPθ
  subst P'
  exact hPr

end Bilevel.TransportHierarchy
