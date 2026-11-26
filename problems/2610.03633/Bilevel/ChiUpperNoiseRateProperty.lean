import Bilevel.ChiUpperNoiseExpectedProperty
import Bilevel.ChiUpperNoiseRate

/-! Explicit numerical expected-query rates for the same actual direct
upper-noise response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry ChiUpperNoise
  PartialLegendre BorelAdaptive ChiCurvatureSchedule

variable (macroN dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤dim)
  (sc : Scale) (weight : ℕ → ℝ) (ζ CR Km : ℝ) (rad R : ℕ → ℝ) (K ε : ℝ)

def UpperNoiseRateProperty (μ L π : ℝ) (hπ1 : π≤1) (cost : ℝ) : Prop :=
  ∀ [MeasurableSpace (UpperNoiseOutput dim)] [BorelSpace (UpperNoiseOutput dim)]
    [MeasurableSpace (UpperNoiseQuery dim)] [BorelSpace (UpperNoiseQuery dim)],
  ∀ {Private : Type u} {State : Type v} [MeasurableSpace Private] [MeasurableSpace State]
    (alg : Program State (UpperNoiseQuery dim) (UpperNoiseQuery dim × UpperNoiseQuery dim) (UpperNoiseOutput dim))
    (initial : Private → State) (_hinit : Measurable initial) (ρseed : Measure Private) [IsProbabilityMeasure ρseed]
    (_haccuracy : ∀ a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim,
      (∫⁻ z,ENNReal.ofReal (Function.uncurry (sourceOriginalLoss macroN 0 dim cn ratios resolutions hdim hAll
        sc weight 3 1 ζ CR Km 1 (sc.curvature/24) rad R 0 K)
          (seededStopped alg (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
            (sc.curvature/24) rad R (publicLower μ L) π) initial (a,z)))
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1)))≤ENNReal.ofReal ε),
    ∃ a : Orientations (sourceCounts macroN cn ratios resolutions) 0 dim,
      ENNReal.ofReal cost≤
      ∫⁻ z,seededCalls alg (sourceUpperNoiseJoint macroN dim cn ratios resolutions hdim hAll sc weight 3 1 ζ CR Km
        (sc.curvature/24) rad R (publicLower μ L) π) initial (a,z)
        ∂ρseed.prod (IndependentStream.law (BernoulliOracle.law π hπ1))

theorem UpperNoiseExpectedProperty.rateProperty (μ L π : ℝ) (hπ1 : π≤1)
    (H : UpperNoiseExpectedProperty.{u,v} macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε μ L π hπ1)
    (cost : ℝ) (hcost : cost≤(capacity (sourceCounts macroN cn ratios resolutions) 1 0:ℕ)/(512*π)) :
    UpperNoiseRateProperty.{u,v} macroN dim cn ratios resolutions hdim hAll sc weight ζ CR Km rad R K ε μ L π hπ1 cost := by
  intro instMO instBO instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  obtain ⟨a,ha⟩ := @H instMO instBO instMQ instBQ Private State instP instS alg initial hinit ρseed instρ haccuracy
  exact ⟨a,(ENNReal.ofReal_le_ofReal hcost).trans ha⟩

end Bilevel.ChiHierarchyHaar

namespace Bilevel.ChiUpperNoise
open ChiHierarchyHaar ChiTreeProgress ChiRecursive ChiBoundedChain ChiCurvatureSchedule

theorem upper_noise_capacity (n : ℕ) (cn η Kg : ℝ)
    (hsize : sourceChainIndex cn 1 (1/Kg)+1=microLength cn Kg) :
    capacity (sourceCounts n cn (fun _ => 1) (resolution η Kg)) 1 0=(n+1)*microLength cn Kg := by
  simp only [capacity,sourceCounts,resolution,if_pos rfl,ite_true,Nat.zero_add]
  rw [hsize]

theorem actual_upper_noise_query_rate {η η₀ L Δ Cgap Cb ε cn C κ σ : ℝ} {n : ℕ}
    (hη : 0<η) (hη₀ : 0<η₀) (hL : 0<L) (hΔ : 0<Δ) (hCg : 0<Cgap)
    (hCb : 1≤Cb) (hε : 0<ε) (hcn : 0<cn) (hC : 1≤C) (hκ : 2≤κ)
    (hlen : 128≤cn/η^2)
    (hn : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(n:ℝ))
    (hsize : sourceChainIndex cn 1 (1/(max (κ/6) (1/η)))+1=microLength cn (max (κ/6) (1/η))) :
    (((cn*η₀/(8*Cgap*Cb^2))/(1296*C^2*Cb^2))/512)*
      (L*κ^2*Δ/ε^2+L*κ^4*σ^2*Δ/ε^4)≤
      (capacity (sourceCounts n cn (fun _ => 1) (resolution η (max (κ/6) (1/η)))) 1 0:ℕ)/
        (512*BernoulliOracle.probability (C*Cb*ε/(κ/6)) σ) := by
  have h := actual_upper_noise_probability_rate hη hη₀ hL hΔ hCg hCb hε hcn hC hκ hlen hn (σ:=σ)
  dsimp only at h
  rw [upper_noise_capacity _ _ _ _ hsize]
  have hh := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤512)
  convert hh using 1 <;> ring

end Bilevel.ChiUpperNoise
