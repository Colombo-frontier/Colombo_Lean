import Bilevel.EndpointTransportWideWitness
import Bilevel.EndpointTransportCoreRestriction


noncomputable section
set_option maxHeartbeats 1800000
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration
  ChiCurvatureSchedule ChiIndependentWidths Filter
open scoped Topology

theorem wide_physical_uniform_core_witness :
    ∃ t η ζ cn CR Km Cgap η₀ bStar Cf CT c : ℝ,
      0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
      128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
      0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
      1≤Cf ∧ 1≤CT ∧ 0<c ∧ c≤1 ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] (dim : ℕ) (L κ θ Δ ε : ℝ),
      0<L → 3200≤κ → θ≤κ^2 → wideBranchThreshold CT≤θ →
      0<Δ → 0<ε → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let T := scale θ CT 6
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∃ hJ : 1≤J,64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∀ (Q : Rotations (EndpointTransportNormalization.interiors κ) dim)
        (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim),
      let M := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let G := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
      let rad := fun j => weight j*(G j []).nu
      let R := fun j => (G j []).radius
      ∃ P : ChiFine.Parameters,P.c=1/128 ∧ P.ℓ=(G J []).ell ∧ P.β=(G J []).width ∧
      P.θ=fineParameter (θ*(L/κ)) (3*(L/κ)/2) P.ℓ (normalCoefficient L J) Cf J ∧
      (∀ (dim' : ℕ) (Q' : Rotations (EndpointTransportNormalization.interiors κ) dim')
        (U' : Space n →ₗᵢ[ℝ] Block dim')
        (V' : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim'),
        let M' := sourceMacroNode n initial Km U'
        let G' := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V'
        let rad' := fun j => weight j*(G' j []).nu
        let R' := fun j => (G' j []).radius
        let core' := physicalHierarchyExtension Q' M' G' P J (2*J) (sourceCoarseNormal J)
          (sourceRadialNormal J) (sourceFineNormal J hJ) rad' R' (normalCoefficient L J)
        ContDiff ℝ 3 core' ∧ ∀ z,‖iteratedFDeriv ℝ 2 core' z‖≤(1:ℝ)/12) ∧
      let core := physicalHierarchyExtension Q M G P J (2*J) (sourceCoarseNormal J)
        (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      let base := physicalUpperBase J Q M (initial.curvature/24) G J (rad 0) (R 0)
      ∃ Pr : Model.Primitive (X:=HybridOuter E (Blocks J (Block dim)) dim)
        (Y:=HybridVariables (Blocks J (Block dim)) (Normals (2*J)) (EndpointTransportNormalization.interiors κ) dim)
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
        ∀ x,M.coordinates x.fst.fst (Fin.last n)<b → 8*ε≤‖gradient (Pr.hyperobjective r) x‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,hmain⟩ :=
    wide_physical_witness
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,?_⟩
  intro E _ _ _ _ dim L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  dsimp only
  obtain ⟨hJ,hS,hn,hm,hr,hrη,hcount,hfamily⟩ :=
    hmain E dim L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  refine ⟨hJ,hS,hn,hm,hr,hrη,hcount,?_⟩
  intro Q U V
  obtain ⟨P,hPc,hPell,hPβ,hPθ,hPr⟩ := hfamily Q U V
  refine ⟨P,hPc,hPell,hPβ,hPθ,?_,hPr⟩
  intro dim' Q' U' V'
  obtain ⟨hJ',_hS',_hn',_hm',_hr',_hrη',_hcount',hfamily'⟩ :=
    hmain (Block dim') dim' L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  obtain ⟨P',hP'c,hP'ell,hP'β,hP'θ,Pr',_hf',hExt',hExt2',_hrest⟩ := hfamily' Q' U' V'
  have he : P'=P := source_fine_parameters_eq P' P (1/128) _ _
    (fun ell => fineParameter (θ*(L/κ)) (3*(L/κ)/2) ell (normalCoefficient L (chosenDepth θ)) Cf (chosenDepth θ))
    hP'c hP'ell hP'β hP'θ hPc hPell hPβ hPθ
  subst P'
  refine ⟨core_contDiff_of_physicalExtension dim' hExt',?_⟩
  intro z
  exact core_jet_bound_of_physicalExtension dim' hExt' 2 (by norm_num) (1/12) hExt2' z

end Bilevel.EndpointTransportResponse
