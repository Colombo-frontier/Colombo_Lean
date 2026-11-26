import Bilevel.ChiCanonicalSourceTemplateReply
import Bilevel.ChiOriginalSourceResponse
import Bilevel.ChiSourceExpectedQueries
import Bilevel.ChiSourcePointwiseReply
import Bilevel.ChiCanonicalSourceCap

/-! Expected original-call lower bound for the literal canonical source
family. Every query certificate and full upper/lower reply identity is
derived from the source energy event. No transcript, local-reply, or
event-probability hypothesis is a premise of this theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiExtension
  PartialLegendre BorelAdaptive

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)


variable (c v : ℝ) (hc : 0<c) (hβ : 0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width) (hv : 1≤v)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
  (hR : ∀ i : Fin J,0<R (i.val+1)) (hwidth : ∀ i : Fin J,0<((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) (i.val+1) []).width)
  (δ : Bool → NNReal) (hδ : ∀ active,δ active<1)
  (hOriginal : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)),ContDiff ℝ 3 (originalPotential active (J+1) ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn))
  (hOriginal2 : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) z,‖iteratedFDeriv ℝ 2 (originalPotential active (J+1) ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn) z‖≤(δ active:ℝ))
  (hActual : ∀ (active : Bool) (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) z,‖iteratedFDeriv ℝ 2 (originalPotential active (J+1) ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km)
    ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR) J c v hc (sourceOriginal_width_pos macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR hβ a) hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
  (hVirtual : ∀ (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (active : Bool)
    (p : VirtualState ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km) ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR)),
    ValidState ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km) ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR) rM r p → ∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active (J+1) ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km) ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR)
        J rM r c v s index radialIndex fineIndex rad R dn p) z‖≤1/12)


variable [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))] [BorelSpace (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))]
  [MeasurableSpace (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))] [BorelSpace (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))]
  [MeasurableSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s)))]
  [BorelSpace (Joint (EuclideanGaussian.Space dim) (Joint (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s)))]
  [MeasurableSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))] [BorelSpace (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))]

include hActual hVirtual hR hwidth in
theorem sourceCanonical_expected_queries
    (hJ : 0<J) (hl : 0<sc.curvature) (hw : 0<sc.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km) (hcs : c≤1/128)
    (μ L π ν ρ₀ R₀ K ε : ℝ) (normal : Normals s) (hπ : 0<π) (hπ1 : π≤1) (hε : 0<ε)
    (N r : ℕ) (bobs : ℝ) (hmax : (capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/(16*π)≤(N:ℝ))
    (hb : 0<bobs) (hb2 : bobs≤2)
    (hd : (2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1)+
      (N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+(r+1)≤dim)
    (hprod : ((N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)):ℕ):ℝ)*
      (((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1:ℕ):ℝ)*bobs)≤1/2)
    (henergy : 2*((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1:ℕ):ℝ)*bobs≤(sourcePublicCap macroN J sc ratios resolutions weight CR ζ Km (ZeroChainSchedule.width c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v (ZeroChainSchedule.levels v))))
    (hbudget : ((2*(N*batchSize (sourceCounts macroN cn ratios resolutions) J (queryVectorCount (J+1)))+1:ℕ):ℝ≥0∞)*
      GenieProtocol.failurePerQuery (totalColumns (sourceCounts macroN cn ratios resolutions) J) r bobs≤1/8)
    (hbarrier : ∀ (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) (x : (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))),((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km).coordinates x.fst (Fin.last macroN)<sc.width →
      8*ε≤sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
        (J+1) ν rad R J K a x)
    {Private State : Type*} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s)) ((FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s)) × (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))) (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)))) (initial : Private → State) (hinit : Measurable initial)
    (ρseed : Measure Private) [IsProbabilityMeasure ρseed]
    (haccuracy : ∀ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll
        sc weight A Kminus ζ CR Km (J+1) ν rad R J K)
          (seededStopped alg (sourceOriginalJoint macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
            (J+1) c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2
            ν ρ₀ R₀ normal μ L π) initial (a,z)))
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)))≤ENNReal.ofReal ε) :
    ∃ a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim),ENNReal.ofReal ((capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0:ℕ)/(512*π))≤
      ∫⁻ z,seededCalls alg (sourceOriginalJoint macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
        (J+1) c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2
        ν ρ₀ R₀ normal μ L π) initial (a,z)
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)) := by
  let h2 := fun (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) (active : Bool)
      (p : {p : VirtualState ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km) ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR) |
        ValidState ((sourceCanonicalMacro macroN J dim cn ratios resolutions hAll) a sc Km) ((sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim) a sc weight A Kminus ζ CR) (finiteMacroCounter (sourceCounts macroN cn ratios resolutions) J) (canonicalCounter (sourceCounts macroN cn ratios resolutions) J) p}) =>
    hVirtual a (finiteMacroCounter (sourceCounts macroN cn ratios resolutions) J) (canonicalCounter (sourceCounts macroN cn ratios resolutions) J) active p.1 p.2
  let evaluate := virtualJointEvaluate (sourceCounts macroN cn ratios resolutions) J (J+1) (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) rfl (fun _ _ => rfl) c v hc hβ hv s
    index radialIndex fineIndex rad R dn hR hwidth (h2 (fun _ => 1)) μ L π ν ρ₀ R₀ normal
  have he := virtualJointEvaluate_measurable (sourceCounts macroN cn ratios resolutions) J (J+1) (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) rfl (fun _ _ => rfl) c v hc hβ hv s
    index radialIndex fineIndex rad R dn hR hwidth (h2 (fun _ => 1)) μ L π ν ρ₀ R₀ normal
  let original := sourceOriginalJoint macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
    (J+1) c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2 ν ρ₀ R₀ normal μ L π
  have hfull := fun (active : Bool)
      (p : {p : VirtualState (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) | ValidState (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km) (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) (fun _ => (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km).n+1) (fun _ => fullCounts (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR)) p}) =>
    hVirtual (fun _ => 1) (fun _ => (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km).n+1) (fun _ => fullCounts (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR)) active p.1 p.2
  have hOrig := sourceOriginalJoint_measurable macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
    (J+1) c v hc hβ hv s index radialIndex fineIndex rad R dn δ hδ hOriginal hOriginal2 hR hwidth hfull
    ν ρ₀ R₀ normal μ L π
  let reorder : Orientations (sourceCounts macroN cn ratios resolutions) J dim ×
      (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s) × Bool) →
      (Orientations (sourceCounts macroN cn ratios resolutions) J dim ×
        FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s)) × Bool :=
    fun p => ((p.1,p.2.1),p.2.2)
  have hargs : Measurable reorder :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hOrig' := hOrig.comp hargs
  have hτ : 0<(ZeroChainSchedule.width c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v (ZeroChainSchedule.levels v)) := ZeroChainSchedule.width_pos c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v hc hβ hv _
  have hcap := sourceCanonical_cap_certificate macroN J dim cn ratios resolutions hdim hAll (fun _ => 1)
    sc weight A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm (ZeroChainSchedule.width c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v (ZeroChainSchedule.levels v)) hτ
  rw [sourceCanonical_cap_eq_public] at hcap
  let point : (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim))) → (EuclideanGaussian.Space dim) := fun x => x.fst
  have hpoint : Measurable point := (jointFstLinear : (Joint (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim))) →L[ℝ] (EuclideanGaussian.Space dim)).continuous.measurable
  have hreply (a : (Orientations (sourceCounts macroN cn ratios resolutions) J dim)) (q : ℕ) (p : (FullNormalVariables (EuclideanGaussian.Space dim) (Blocks (J+1) (EuclideanGaussian.Space dim)) (Normals s))) (coin : Bool)
      (hE : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,GenieProtocol.BoundedEnergy
        (sharedKnown (sourceCounts macroN cn ratios resolutions) J dim q (columns hAll a) (Submodule.span ℝ (Set.range (originalVectors p))))
        (prefixSet (retained (sourceCounts macroN cn ratios resolutions) J q i)) (columns hAll a i) (sourcePublicCap macroN J sc ratios resolutions weight CR ζ Km (ZeroChainSchedule.width c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v (ZeroChainSchedule.levels v)))) :
      original a p coin=evaluate p (actual (sourceCounts macroN cn ratios resolutions) J q (columns hAll a))
        (actual (sourceCounts macroN cn ratios resolutions) J (q+if coin then 1 else 0) (columns hAll a)) coin := by
    have hh := sourceCanonical_template_reply_from_energy macroN J dim cn ratios resolutions hdim hAll a sc weight
      A Kminus ζ CR Km hJ hl hw hr hη hη1 hweight hζ hCR hKm c v hc hcs hβ hv s index radialIndex fineIndex
      rad R dn hR hwidth (hActual true a) (hActual false a) (h2 a) (fun _ => 1) (h2 (fun _ => 1))
      (δ true) (δ false) (hδ true) (hδ false) (hOriginal2 true a) (hOriginal2 false a) q p hE
      μ L π ν ρ₀ R₀ normal coin
    exact hh.symm
  have hmR : 0<(sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km).radius := by
    change 0<Km*sc.width*Real.sqrt ((macroN:ℝ)+1)
    positivity
  refine expected_queries_of_source_replies (sourceCounts macroN cn ratios resolutions) J dim (queryVectorCount (J+1)) hAll alg evaluate he
    (fun k p => originalVectors p.1 k) (fun k => (originalVectors_measurable k).comp measurable_fst)
    (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km).radius sc.width (sourcePublicCap macroN J sc ratios resolutions weight CR ζ Km (ZeroChainSchedule.width c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v (ZeroChainSchedule.levels v))) hmR hw hcap.1.le hcap.2.2.1 point hpoint initial hinit original hOrig'
    (Function.uncurry (sourceOriginalLoss macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
      (J+1) ν rad R J K))
    (sourceOriginalLoss_measurable macroN J dim cn ratios resolutions hdim hAll sc weight A Kminus ζ CR Km
      (J+1) ν rad R J K) (fun _ => norm_nonneg _) ρseed π ε hπ hπ1 hε N r bobs hmax hb hb2 hd hprod henergy hbudget
    ?_ (fun a x hx => hbarrier a x hx) haccuracy
  intro n _ z hg t ht _ _
  exact sourceGood_reply_from_energy hAll alg evaluate he
    (fun k p => originalVectors p k) (fun k => originalVectors_measurable k)
    (macroTerminal (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km).radius point) (macroTerminal_measurable (sourceTemplateMacro macroN J dim cn ratios resolutions hAll sc Km).radius point hpoint)
    initial original (sourcePublicCap macroN J sc ratios resolutions weight CR ζ Km (ZeroChainSchedule.width c ((sourceTemplateGeometry macroN J dim cn ratios resolutions hdim sc weight A Kminus ζ CR) J []).width v (ZeroChainSchedule.levels v))) hreply n z hg t ht

end Bilevel.ChiHierarchyHaar




