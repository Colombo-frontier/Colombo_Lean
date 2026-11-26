import Bilevel.EndpointTransportParameterCertificate
import Bilevel.EndpointTransportHierarchyPrimitive
import Bilevel.EndpointTransportMacroObjective
import Bilevel.EndpointTransportHybridGradient
import Bilevel.EndpointTransportHierarchyOrigin
import Bilevel.ChiSourceDeterministicWitness

/-! One actual physical hybrid Primitive on the full large-theta window.
All extension/base budgets are discharged for the same source geometry.
The gap and blind gradient belong to this exact Primitive. The arbitrary
adaptive-query information theorem is a separate obligation. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration
  ChiCurvatureSchedule ChiIndependentWidths Filter
open scoped Topology

theorem wide_physical_witness :
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
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hmacro⟩ :=
    EndpointTransportNormalization.transport_macro_objective_certificate
  have hCb : 0<32/t := by positivity
  have hζ1 : ζ≤1 := by linarith only [hζsmall]
  obtain ⟨η₀,bStar,hη₀,hη₀1,hbs,hbs1,hbsgap,hparameter⟩ :=
    wide_physical_parameter_certificate (A:=3) (Kminus:=1) (Cb:=32/t) (cms:=1/128)
      (by norm_num) (by norm_num) hζ hζ1 hcn hcn1 hη hη1 hlen hCR hCRcn hKm hCgap
      hCb ht ht1.le (by norm_num) (by norm_num)
  obtain ⟨cold,hcold,_hcold1,hobjective⟩ := hmacro η₀ bStar hη₀ hη₀1 hbs hbsgap
  obtain ⟨Cf,CT,c,hCf,hCT,hc,hc1,hccold,hparameter⟩ := hparameter cold hcold
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,η₀,bStar,Cf,CT,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,
    hCR,hCRcn,hKm,hCgap,hη₀,hη₀1,hbs,hbs1,hbsgap,hCf,hCT,hc,hc1,?_⟩
  intro E _ _ _ _ dim L κ θ Δ ε hL hκ hθκ hbranch hΔ hε hacc
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (EndpointTransportNormalization.gain κ) (η₀*L) (t*η) J
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let n := S-1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  let weight := fun j : ℕ => t^(j+1)
  have hbranches := wide_branch_conditions hCT hbranch
  have hJ : 1≤J := hbranches.2.1
  have hT : 1≤T := (by norm_num : (1:ℝ)≤2).trans hbranches.2.2
  have hμ : 0<L/κ := div_pos hL (by linarith)
  have hρg : 0≤θ*(L/κ) := mul_nonneg (zero_le_one.trans hbranches.1) hμ.le
  have haccold : ε≤cold*min L (Real.sqrt (L*Δ)) := hacc.trans
    (mul_le_mul_of_nonneg_right hccold (le_min hL.le (Real.sqrt_nonneg _)))
  have ho := hobjective E (Block dim) L Δ κ θ ε T hL hΔ hκ hbranches.1 hθκ hε hT haccold
  refine ⟨hJ,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2.1,ho.2.2.2.2.2.1,?_⟩
  intro Q U V
  let M := sourceMacroNode n initial Km U
  let G := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight 3 1 ζ cn CR V
  let rad := fun j => weight j*(G j []).nu
  let R := fun j => (G j []).radius
  have hp := hparameter E n (EndpointTransportNormalization.interiors κ) dim Q L (L/κ) κ θ Δ ε weight
    hL hμ hκ hθκ hbranch hΔ hε hacc (fun j => pow_pos ht _) (fun j => pow_le_one₀ ht.le ht1.le) U V
  obtain ⟨P,hPc,hPell,hPwidth,hPθ,hgeo,hupper,hjets⟩ := hp
  refine ⟨P,hPc,hPell,hPwidth,hPθ,?_⟩
  dsimp only
  have hj : J-1+1=J := Nat.sub_add_cancel hJ
  have hassembly := physical_hierarchy_primitive_of_budgets hL hκ hρg (J-1) Q M (initial.curvature/24) G P rad R
  rw [hj] at hassembly
  have hnum : θ*(L/κ)/(3*(3*(L/κ)/2))=2*θ/9 := by
    field_simp
    ring
  obtain ⟨Pr,hf,hExt,hExt2,hg,r,hr,hm,hu⟩ := hassembly
    (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ)
    (fun i => (hgeo (i.val+1) []).1) (fun i => (hgeo (i.val+1) []).2)
    (fun z => (hjets (2*J) (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) z).1)
    (fun z => by rw [hnum];exact (hjets (2*J) (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) z).2)
    (fun z => (hupper J z).1.trans (by linarith only [hL]))
    (fun x v => (hupper J (pack x v)).2.trans (by linarith only [hL]))
  let obj := jointOuter (J+1) M (initial.curvature/24) G rad R J (EndpointTransportNormalization.gain κ)
  have ho' := ho.2.2.2.2.2.2 U V
  have hcont : Continuous obj :=
    (jointOuter_contDiff (J+1) M (initial.curvature/24) G rad R J (EndpointTransportNormalization.gain κ) 0).continuous
  obtain ⟨zmin,hmin⟩ := hcont.exists_forall_le ho'.1
  have hbdd : BddBelow (Set.range obj) := ⟨obj zmin,by rintro _ ⟨z,rfl⟩;exact hmin z⟩
  have hgap := source_hybrid_gap_transfer Pr r obj hm (sInf (Set.range obj)) Δ
    (fun z => csInf_le hbdd ⟨z,rfl⟩) ho'.2.2.1
  refine ⟨Pr,hf,hExt,hExt2,hg,r,hgap,?_,hr,hm,?_,?_,?_⟩
  · rw [hr]
    exact physicalHierarchy_response_origin L κ Q M G P J (2*J)
      (sourceCoarseNormal J) (sourceRadialNormal J) (sourceFineNormal J hJ) rad R (normalCoefficient L J)
      (fun i => (hgeo (i.val+1) []).1) (fun i => (hgeo (i.val+1) []).2)
  · intro x y
    rw [hr]
    exact hu x y
  · rw [hm,map_zero]
    exact ho'.2.1
  · intro x hlast
    rw [source_hybrid_gradient_norm M (initial.curvature/24) G rad R Pr r hm x]
    exact ho'.2.2.2 (sourceCoordinates J dim x) hlast

end Bilevel.EndpointTransportResponse
