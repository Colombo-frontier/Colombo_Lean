import Bilevel.ConditionalSupport
import Bilevel.HaarFrame
import Bilevel.ProjectionStabilizer

/-! Actual conditional frame laws after projection queries and column revelations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Bilevel.ProjectionPosterior
open EuclideanGaussian OrthogonalAction ProjectionStabilizer
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

abbrev Frame (d T : ℕ) := Fin T → Space d

instance subgroupAmbientMeasurable (d : ℕ) (V : Submodule ℝ (Space d)) :
    MeasurableSMul₂ (subgroup d V) (Space d) := by
  refine ⟨?_⟩
  have hm : Measurable (fun p : subgroup d V × Space d => (p.1.val,p.2)) :=
    (continuous_subtype_val.measurable.comp measurable_fst).prodMk measurable_snd
  have hc := (OrthogonalAction.action_continuous d).measurable.comp hm
  change Measurable (fun p : subgroup d V × Space d => p.1.val • p.2) at hc
  change Measurable (fun p : subgroup d V × Space d => p.1.val • p.2)
  exact hc

instance frameMeasurableAction (d T : ℕ) (V : Submodule ℝ (Space d)) :
    MeasurableSMul₂ (subgroup d V) (Frame d T) := by
  constructor
  apply measurable_pi_lambda
  intro i
  exact measurable_fst.smul ((measurable_pi_apply i).comp measurable_snd)

def Invariant (d T : ℕ) (V : Submodule ℝ (Space d)) (μ : Measure (Frame d T)) : Prop :=
  ∀ A : subgroup d V, MeasurePreserving (fun U : Frame d T => A • U) μ μ

theorem invariant_mono (d T : ℕ) (V W : Submodule ℝ (Space d)) (hVW : V ≤ W)
    (μ : Measure (Frame d T)) (hμ : Invariant d T V μ) : Invariant d T W μ := by
  intro A
  let B : subgroup d V := ⟨A.val, (membership d V A.val).2
    (fun y hy => (membership d W A.val).1 A.property y (hVW hy))⟩
  exact hμ B

theorem frame_law_invariant (d T : ℕ) (hT : T ≤ d) (V : Submodule ℝ (Space d)) :
    Invariant d T V (HaarFrame.frameLaw d T hT) := by
  intro A
  apply ConditionalSymmetry.pushforward_preserving (OrthogonalHaar.law d)
    (HaarFrame.frame d T hT) (HaarFrame.frame_measurable d T hT)
    (fun B => A.val * B) (fun U : Frame d T => A • U)
    (measurePreserving_mul_left (OrthogonalHaar.law d) A.val)
    (measurable_const.smul measurable_id)
  intro B
  funext i
  exact mul_smul A.val B _

def queryObservation (d T : ℕ) (q : Space d) (U : Frame d T) : Fin T → ℝ :=
  fun i => ⟪q,U i⟫

theorem query_measurable (d T : ℕ) (q : Space d) : Measurable (queryObservation d T q) := by
  apply measurable_pi_lambda
  intro i
  exact (continuous_const.inner (continuous_apply i)).measurable

def revealObservation (d T : ℕ) (i : Fin T) (U : Frame d T) : Space d := U i

theorem reveal_measurable (d T : ℕ) (i : Fin T) : Measurable (revealObservation d T i) :=
  measurable_pi_apply i

theorem query_posterior_invariant (d T : ℕ) (V : Submodule ℝ (Space d))
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T V μ)
    (q : Space d) :
    ∀ᵐ y ∂μ.map (queryObservation d T q),
      Invariant d T (V ⊔ Submodule.span ℝ {q}) (condDistrib id (queryObservation d T q) μ y) := by
  let W := V ⊔ Submodule.span ℝ {q}
  have hp := invariant_mono d T V W le_sup_left μ hμ
  have hqW : q ∈ W := (show Submodule.span ℝ {q} ≤ W from le_sup_right)
    (Submodule.mem_span_singleton_self q)
  have he : ∀ (A : subgroup d W) (U : Frame d T),
      queryObservation d T q (A • U) = queryObservation d T q U := by
    intro A U
    funext i
    change ⟪q, A.val • U i⟫ = ⟪q,U i⟫
    calc
      _ = ⟪A.val • U i,q⟫ := real_inner_comm _ _
      _ = ⟪U i,q⟫ := fixed_inner d W A (U i) q hqW
      _ = _ := real_inner_comm _ _
  exact ConditionalSupport.invariant_observation μ (queryObservation d T q)
    (query_measurable d T q) (ProjectionStabilizer.law d W) hp he

theorem reveal_posterior_invariant (d T : ℕ) (V : Submodule ℝ (Space d))
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T V μ)
    (i : Fin T) :
    ∀ᵐ y ∂μ.map (revealObservation d T i),
      Invariant d T (V ⊔ Submodule.span ℝ {y}) (condDistrib id (revealObservation d T i) μ y) := by
  have he : ∀ (A : subgroup d V) (U : Frame d T),
      revealObservation d T i (A • U) = A • revealObservation d T i U := by
    intro A U
    rfl
  have hp := ConditionalSupport.equivariant_observation μ (revealObservation d T i)
    (reveal_measurable d T i) (ProjectionStabilizer.law d V) hμ he
  filter_upwards [hp] with y hy
  intro A
  let B : subgroup d V := ⟨A.val, (membership d V A.val).2 (fun z hz =>
    (membership d (V ⊔ Submodule.span ℝ {y}) A.val).1 A.property z
      ((show V ≤ V ⊔ Submodule.span ℝ {y} from le_sup_left) hz))⟩
  have hfix : B • y = y := (membership d (V ⊔ Submodule.span ℝ {y}) A.val).1 A.property y
    ((show Submodule.span ℝ {y} ≤ V ⊔ Submodule.span ℝ {y} from le_sup_right)
      (Submodule.mem_span_singleton_self y))
  exact hy B hfix

theorem query_fiber (d T : ℕ) (μ : Measure (Frame d T)) [IsProbabilityMeasure μ]
    (q : Space d) : ∀ᵐ y ∂μ.map (queryObservation d T q),
      ∀ᵐ U ∂condDistrib id (queryObservation d T q) μ y, queryObservation d T q U = y := by
  apply ConditionalSupport.fiber μ _ (query_measurable d T q)
  exact measurableSet_eq_fun ((query_measurable d T q).comp measurable_snd) measurable_fst

theorem reveal_fiber (d T : ℕ) (μ : Measure (Frame d T)) [IsProbabilityMeasure μ]
    (i : Fin T) : ∀ᵐ y ∂μ.map (revealObservation d T i),
      ∀ᵐ U ∂condDistrib id (revealObservation d T i) μ y, U i = y := by
  apply ConditionalSupport.fiber μ _ (reveal_measurable d T i)
  exact measurableSet_eq_fun ((reveal_measurable d T i).comp measurable_snd) measurable_fst

end Bilevel.ProjectionPosterior
