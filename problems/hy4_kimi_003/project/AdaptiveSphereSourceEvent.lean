import AdaptiveSphereObservedHandles
import AdaptiveSphereOriginalEnergy
import AdaptiveSphereGlobalEnergy
import HardFamilyBayes
import LowerEventMass

/-! Literal event E={2 K_original<k} from the manuscript: its exact stopped
history representation, old-past measurability, mass, and original-center energy. -/
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.AdaptiveSphereSourceEvent
open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereStopped Task006.AdaptiveSphereMean
open Task006.AdaptiveSphereGlobal Task006.AdaptiveSphereJoint Task006.PosteriorCenter
open Task006.AdaptiveSphereObservedHandles Task006.AdaptiveSphereOriginalHandleEvent
open Task006.AdaptiveSphereStoppedCoupling Task006.AdaptiveSphereStoppedSpan
open Task006.AdaptiveSphereSpan Task006.RankHandleCount Task006.HardFamilyBayes Task006.StoppedEnergy
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

def sourceHandleEvent (alg : OracleAlgorithm d N S) (j : Fin d) (k : ℕ) :
    Set (Exogenous S × OrthogonalGroup d) := {w | 2*originalK alg j w < k}

def stoppedHandleEvent (alg : OracleAlgorithm d N S) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    Set (Exogenous S × OrthogonalGroup d) :=
  {w | 2*observedStoppedK alg k hkd (jointObservation alg k hkd N j w) < (k:ℝ)}

theorem stoppedHandleEvent_measurable_past (alg : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    MeasurableSet[jointPastSigma alg k hkd N j] (stoppedHandleEvent alg k hkd j) := by
  have hs : MeasurableSet {h : Exogenous S × Transcript N |
      2*observedStoppedK alg k hkd h < (k:ℝ)} :=
    measurableSet_lt ((observedStoppedK_measurable alg k hkd).const_mul 2) measurable_const
  exact ⟨_,hs,rfl⟩

theorem mem_stoppedHandleEvent_iff (alg : OracleAlgorithm d N S)
    (k : ℕ) (hkd : k ≤ d) (j : Fin d) (w : Exogenous S × OrthogonalGroup d) :
    w ∈ stoppedHandleEvent alg k hkd j ↔
      2*((stoppedObserver alg id w.1.2 w.1.1 k hkd).informativeHandles
        (linearSample id (column w.2 j)) w.1.2 ()).card < k := by
  change 2*observedStoppedK alg k hkd (jointObservation alg k hkd N j w) < (k:ℝ) ↔ _
  rw [observedStoppedK_actual_eq]
  constructor <;> intro h <;> exact_mod_cast h

/-- Exact source event, not merely a larger rank event. -/
theorem sourceHandleEvent_eq_stoppedHandleEvent (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    sourceHandleEvent alg j k = stoppedHandleEvent alg k hkd j := by
  ext w
  rw [mem_stoppedHandleEvent_iff]
  exact original_stopped_informative_event_iff alg w.1.2 w.1.1 k hkd (column w.2 j)
    (hlegal (column w.2 j) ((orthonormal_column w.2).norm_eq_one j) w.1.1 w.1.2).2.1

theorem sourceHandleEvent_measurable_past (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d) :
    MeasurableSet[jointPastSigma alg k hkd N j] (sourceHandleEvent alg j k) := by
  rw [sourceHandleEvent_eq_stoppedHandleEvent alg R hlegal k hkd j]
  exact stoppedHandleEvent_measurable_past alg k hkd j

/-- Literal L8, derived from the true informative-handle expectation under the
original independent tape law. -/
theorem sourceHandleEvent_half_mass (alg : OracleAlgorithm d N S)
    (L A : ℝ) (hL : 0<L) (hA : 16≤A) (σ : Measure S) [IsProbabilityMeasure σ]
    (k : ℕ) (hk : 0<k) (hdk : d≤8*k) (j : Fin d)
    (hbudget : (4096/A^3)*(N:ℝ) ≤ (d:ℝ)/32) :
    (1/2:ℝ) ≤ ((σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)).real
      (sourceHandleEvent alg j k) := by
  have hm := Task006.LowerEventMass.rank_lt_threshold_half_mass
    (μ := (σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d))
    (fun w => (originalK alg j w : ℝ)) (fun w => 2*(originalK alg j w : ℝ)) d k
    (originalK_integrable alg j _) (fun _ => Nat.cast_nonneg _) ((originalK_measurable alg j).const_mul 2)
    (by exact_mod_cast hk) (by exact_mod_cast hdk)
    ((originalK_expectation alg j L A hL hA σ).trans hbudget) (fun _ => le_rfl)
  have he : {w : Exogenous S × OrthogonalGroup d | 2*(originalK alg j w:ℝ)<(k:ℝ)} =
      sourceHandleEvent alg j k := by
    ext w
    change 2*(originalK alg j w:ℝ)<(k:ℝ) ↔ 2*originalK alg j w<k
    constructor <;> intro h <;> exact_mod_cast h
  rw [he] at hm
  exact hm

def originalJointCenter (alg : OracleAlgorithm d N S) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) : Space d :=
  actualCenter alg id w.1.2 w.1.1 d le_rfl N j w.2

theorem originalJointCenter_measurable (alg : OracleAlgorithm d N S) (j : Fin d) :
    Measurable (originalJointCenter alg j) := by
  have hF : Measurable (fun p : Space d × (Space d × ℝ) => linearSample id p.1 p.2.1 p.2.2) :=
    measurable_snd.snd.mul (measurable_fst.inner measurable_snd.fst)
  have hh := (alg.runPrefix_parameter_measurable (linearSample id) hF N).comp
    (exogenousHaarInput_measurable j)
  have hc := (centerFromTranscript_joint_measurable alg d le_rfl N).comp
    (measurable_fst.prodMk hh)
  change Measurable (fun w : Exogenous S × OrthogonalGroup d =>
    centerFromTranscript alg id w.1.2 w.1.1 d le_rfl N
      (alg.runPrefix (linearSample id (column w.2 j)) w.1.2 w.1.1 N))
  simpa only [Function.comp_def,exogenousHaarInput] using hc

theorem originalJointCenter_square_integrable (alg : OracleAlgorithm d N S) (j : Fin d)
    (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    Integrable (fun w => ‖originalJointCenter alg j w‖^2) (γ.prod (orthogonalHaarProbability d)) := by
  apply Integrable.of_bound ((originalJointCenter_measurable alg j).norm.pow_const 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  have h := actualCenter_norm_le_one alg id w.1.2 w.1.1 d le_rfl N le_rfl j w.2
  change ‖‖actualCenter alg id w.1.2 w.1.1 d le_rfl N j w.2‖^2‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (actualCenter alg id w.1.2 w.1.1 d le_rfl N j w.2)]

theorem source_event_center_agreement (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (w : Exogenous S × OrthogonalGroup d) (hw : w∈sourceHandleEvent alg j k) :
    originalJointCenter alg j w = jointCenter alg k hkd N j w := by
  have hcap := (hlegal (column w.2 j) ((orthonormal_column w.2).norm_eq_one j) w.1.1 w.1.2).2.1
  have hrank := actual_frame_rank_le_twice_informative_handles alg w.1.2 w.1.1 (column w.2 j) d le_rfl hcap
  have hdim : Module.finrank ℝ (measurementSpanBefore alg id w.1.2 w.1.1 N (column w.2 j)) < k := by
    rw [actual_measurementSpan_finrank alg id w.1.2 w.1.1 N le_rfl]
    exact hrank.trans_lt hw
  rw [jointCenter_eq_fixed]
  exact below_dimension_center_eq alg id w.1.2 w.1.1 k hkd j w.2 hdim

/-- Literal source-event energy for the ORIGINAL posterior center, obtained by
its proved equality with the stopped center on exactly E={2K<k}. -/
theorem source_event_original_center_energy_le_ratio (alg : OracleAlgorithm d N S)
    (R : ℝ) (hlegal : LegalOriginal alg R) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (γ : Measure (Exogenous S)) [IsProbabilityMeasure γ] :
    (∫ w in sourceHandleEvent alg j k, ‖originalJointCenter alg j w‖^2
      ∂γ.prod (orthogonalHaarProbability d)) ≤ (k:ℝ)/((d:ℝ)-k+1) := by
  have he := (jointObservation_measurable alg k hkd N j).comap_le _
    (sourceHandleEvent_measurable_past alg R hlegal k hkd j)
  have ht := event_energy_le_stopped_energy (sourceHandleEvent alg j k) he
    (fun w => ‖originalJointCenter alg j w‖^2) (fun w => ‖jointCenter alg k hkd N j w‖^2)
    (originalJointCenter_square_integrable alg j γ) (joint_center_energy_integrable alg k hkd N le_rfl j γ)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun w hw => congrArg (fun x : Space d => ‖x‖^2)
      (source_event_center_agreement alg R hlegal k hkd j w hw)))
  exact (ht.trans (joint_expected_center_energy_le alg k hkd j γ)).trans (rankPotential_le_ratio d k hkd)

#print axioms sourceHandleEvent_eq_stoppedHandleEvent
#print axioms sourceHandleEvent_measurable_past
#print axioms sourceHandleEvent_half_mass
#print axioms source_event_center_agreement
#print axioms source_event_original_center_energy_le_ratio
end
end Task006.AdaptiveSphereSourceEvent
