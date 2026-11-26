import GradientHessian.PresampledPolicyProbability
import GradientHessian.NormalizedConstruction
import GradientHessian.NormalizationPolicyTransport
import GradientHessian.ModelProbabilityLowerBound

/-! Transport of the actual presampled finite-cutoff probability bound to
the normalized Euclidean objectives used by the minimax model. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory HigherHierarchy JetLocality RepairAllocation

variable (Cp : ℝ) (s : Settings)

local instance physicalMeasurable : ∀ t,MeasurableSpace
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) := fun _ => borel _
local instance physicalBorel : ∀ t,BorelSpace
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) := fun _ => ⟨rfl⟩
local instance allocatedMeasurable (t : ℕ) : MeasurableSpace (PhysicalSpace Cp s t) := borel _
local instance allocatedBorel (t : ℕ) : BorelSpace (PhysicalSpace Cp s t) := ⟨rfl⟩
local instance firstMeasurable (t : ℕ) : MeasurableSpace
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ) := borel _
local instance firstBorel (t : ℕ) : BorelSpace
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ) := ⟨rfl⟩
local instance secondMeasurable (t : ℕ) : MeasurableSpace
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ]
      DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ) := borel _
local instance secondBorel (t : ℕ) : BorelSpace
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ]
      DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ) := ⟨rfl⟩
local instance allocatedFirstMeasurable (t : ℕ) : MeasurableSpace (PhysicalSpace Cp s t →L[ℝ] ℝ) := borel _
local instance allocatedFirstBorel (t : ℕ) : BorelSpace (PhysicalSpace Cp s t →L[ℝ] ℝ) := ⟨rfl⟩
local instance allocatedSecondMeasurable (t : ℕ) :
    MeasurableSpace (PhysicalSpace Cp s t →L[ℝ] PhysicalSpace Cp s t →L[ℝ] ℝ) := borel _
local instance allocatedSecondBorel (t : ℕ) :
    BorelSpace (PhysicalSpace Cp s t →L[ℝ] PhysicalSpace Cp s t →L[ℝ] ℝ) := ⟨rfl⟩
local instance ordinaryMeasurable : ∀ t,MeasurableSpace
    (DirectionPolicyReplay.Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) := fun t =>
  @Prod.instMeasurableSpace ℝ _ inferInstance (firstMeasurable Cp s t)
local instance ordinaryBorel : ∀ t,BorelSpace
    (DirectionPolicyReplay.Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) := fun t => by
  change BorelSpace (ℝ × (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ))
  infer_instance
local instance richMeasurable : ∀ t,MeasurableSpace
    (DirectionPolicyReplay.Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) := fun t =>
  @Prod.instMeasurableSpace ℝ _ inferInstance
    (@Prod.instMeasurableSpace _ _ (firstMeasurable Cp s t) (secondMeasurable Cp s t))
local instance richBorel : ∀ t,BorelSpace
    (DirectionPolicyReplay.Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) := fun t => by
  change BorelSpace (ℝ × (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ) ×
    (DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ]
      DirectionPolicyReplay.Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t →L[ℝ] ℝ))
  infer_instance

def sourceCoordinates (t : ℕ) :
    Model.Point (PhysicalDimension.count Cp s.D s.M (t+1)) ≃ₗᵢ[ℝ] PhysicalSpace Cp s t :=
  (allocatedEuclideanEquiv Cp s.D (4096*s.J^2) t).symm

theorem normalizedObjective_pullback (K : ℝ) (t : ℕ) (w : Sample Cp s t) :
    normalizedObjective Cp K s t w=
      NormalizationPolicy.objective (normalizationScale K) (sourceCoordinates Cp s t) (objective Cp K s t w) := rfl

theorem normalized_ordinary_measurable {K : ℝ} (hK : 0<K) (t : ℕ) :
    Measurable (fun q : Sample Cp s t × Model.Point (PhysicalDimension.count Cp s.D s.M (t+1)) =>
      Model.ordinaryOracle (normalizedObjective Cp K s t q.1) q.2) := by
  let e := sourceCoordinates Cp s t
  let L := NormalizationPolicy.queryMap (normalizationScale K) e
  have hraw : Measurable (fun q : Sample Cp s t × PhysicalSpace Cp s t => ordinaryJet (objective Cp K s t q.1) q.2) :=
    (RawHierarchy.ordinaryJet_joint_measurable (n := s.columnsCount) (J := s.J)
      (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 hK t).mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have h := (JetPullback.ordinary_continuous (normalizationScale K) L).measurable.comp
    (hraw.comp (measurable_fst.prodMk (L.continuous.measurable.comp measurable_snd)))
  convert h using 1
  funext q
  exact JetPullback.ordinary_exact (normalizationScale K) L
    ((objective_contDiff hK Cp s t q.1).differentiable (by norm_num)) q.2

theorem normalized_rich_measurable {K : ℝ} (hK : 0<K) (t : ℕ) :
    Measurable (fun q : Sample Cp s t × Model.Point (PhysicalDimension.count Cp s.D s.M (t+1)) =>
      Model.richOracle (normalizedObjective Cp K s t q.1) q.2) := by
  let e := sourceCoordinates Cp s t
  let L := NormalizationPolicy.queryMap (normalizationScale K) e
  have hraw : Measurable (fun q : Sample Cp s t × PhysicalSpace Cp s t => richJet (objective Cp K s t q.1) q.2) :=
    (RawHierarchy.richJet_joint_measurable (n := s.columnsCount) (J := s.J)
      (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 hK t).mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have h := (JetPullback.rich_continuous (normalizationScale K) L).measurable.comp
    (hraw.comp (measurable_fst.prodMk (L.continuous.measurable.comp measurable_snd)))
  convert h using 1
  funext q
  exact JetPullback.rich_exact (normalizationScale K) L
    ((objective_contDiff hK Cp s t q.1).of_le (by decide : (2 : WithTop ℕ∞)≤3)) q.2

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (σ : Measure Seed) [IsProbabilityMeasure σ] (t : ℕ)
variable (policy : Machine.Policy Seed S
  (Model.Point (PhysicalDimension.count Cp s.D s.M (t+1)))
  (Model.OrdinaryReply (PhysicalDimension.count Cp s.D s.M (t+1)))
  (Model.RichReply (PhysicalDimension.count Cp s.D s.M (t+1))))

theorem normalized_success_probability {ell : ℕ} {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*(s.M:ℝ)≤s.r) (N G Hcap : ℕ) (hell : 0<ell) (hellM : ell≤s.M)
    (hcaps : ∀ᵐ x ∂law Cp s t,policy.HasCaps (Model.ordinaryOracle (normalizedObjective Cp K s t x))
      (Model.richOracle (normalizedObjective Cp K s t x)) G Hcap)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(s.M:ℝ)*ell/4)
    (hearly : (∫ w,(earlyCount (ell := ell) Cp s t
      (NormalizationPolicy.transport policy (normalizationScale K) (sourceCoordinates Cp s t)) K N w:ℝ)
      ∂(law Cp s t).prod σ)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256) :
    ((law Cp s t).prod σ).real {w | policy.output
      (policy.run (Model.ordinaryOracle (normalizedObjective Cp K s t w.1))
        (Model.richOracle (normalizedObjective Cp K s t w.1)) N w.2)
      ∈Model.stationary (normalizedObjective Cp K s t w.1)}≤1/32 := by
  let Q := NormalizationPolicy.transport policy (normalizationScale K) (sourceCoordinates Cp s t)
  have hf (w : Sample Cp s t) : ContDiff ℝ 2 (objective Cp K s t w) :=
    (objective_contDiff (by linarith : 0<K) Cp s t w).of_le (by decide : (2 : WithTop ℕ∞)≤3)
  have hc : ∀ᵐ x ∂law Cp s t,Q.HasCaps (ordinaryJet (objective Cp K s t x))
      (richJet (objective Cp K s t x)) G Hcap := by
    filter_upwards [hcaps] with x hx
    exact (NormalizationPolicy.hasCaps policy (normalizationScale K) (sourceCoordinates Cp s t) (hf x) G Hcap).mpr hx
  have hp := source_success_probability Cp s σ t Q hK hCp hr N G Hcap hell hellM hc hrich hordinary hearly
  convert hp using 2
  ext w
  simp only [Set.mem_setOf_eq]
  dsimp only [Q]
  rw [NormalizationPolicy.output policy (normalizationScale K) (sourceCoordinates Cp s t) (hf w.1)]
  exact normalizedEuclideanScalar_stationary (by linarith : 16≤K) t (coefficients Cp s t w.1)
    (sourceCoordinates Cp s t) _

theorem normalized_no_guarantee {ell : ℕ} {K T : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*(s.M:ℝ)≤s.r) (G Hcap : ℕ) (hell : 0<ell) (hellM : ell≤s.M)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(s.M:ℝ)*ell/4)
    (hT : normalizedGapConstant K*8^(t+1)*s.M≤T)
    (A : Model.Algorithm (PhysicalDimension.count Cp s.D s.M (t+1))) :
    letI := A.seedSpace
    letI := A.stateSpace
    letI := A.probability
    (∀ N : ℕ,(∫ w,(earlyCount (ell := ell) Cp s t
      (NormalizationPolicy.transport A.policy (normalizationScale K) (sourceCoordinates Cp s t)) K N w:ℝ)
      ∂(law Cp s t).prod A.seedLaw)≤(8:ℝ)^(t+1)*(s.M:ℝ)/256) →
      ¬A.Guarantees T G Hcap := by
  letI := A.seedSpace
  letI := A.stateSpace
  letI := A.probability
  intro hearly
  apply Model.not_guarantees_of_probability_bound (law Cp s t) (normalizedObjective Cp K s t) A
    (normalized_ordinary_measurable Cp s (by linarith) t)
    (normalized_rich_measurable Cp s (by linarith) t)
  · filter_upwards [normalizedObjective_admissible (by linarith : 16≤K) Cp s t] with w hw
    exact hw.mono hT
  · intro hc N
    exact normalized_success_probability Cp s A.seedLaw t A.policy hK hCp hr N G Hcap hell hellM
      hc hrich hordinary (hearly N)

end GradientHessian.PresampledConstruction
