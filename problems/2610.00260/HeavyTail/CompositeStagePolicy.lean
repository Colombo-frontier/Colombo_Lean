import HeavyTail.AcceptedOracleModel
import HeavyTail.AdaptiveKernelRejection
import HeavyTail.AdaptiveKernelModel

/-! The concrete composite stage policy from any public measurable learner.
State records the learner, sum of proximal points, and number of accepted
updates. Each raw observation is charged and tested at its frozen query.
The readout uses the actual average when feasible, with a fixed public
proximal fallback on an invalid/empty state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal InnerProductSpace
namespace HeavyTail
universe u
variable {E W : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace W]
  {θ : OracleParameters}

structure StageLearner (W E : Type u) [MeasurableSpace W] [NormedAddCommGroup E]
    [MeasurableSpace E] (c : E) (R : ℝ) where
  initial : W
  point : W → E
  point_measurable : Measurable point
  point_bound : ∀ w, ‖point w - c‖ ≤ R
  update : W × E → W
  update_measurable : Measurable update

abbrev CompositeStageState (W E : Type u) := W × (E × ℕ)

def stageAverage (s : CompositeStageState W E) : E := (s.2.2 : ℝ)⁻¹ • s.2.1

theorem stageAverage_measurable : Measurable (stageAverage : CompositeStageState W E → E) := by
  have hc : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  exact (hc.comp (measurable_snd.comp measurable_snd)).inv.smul (measurable_fst.comp measurable_snd)

namespace PublicProblem

def stageFallback (B : PublicProblem E θ) : E := B.prox.point 1 B.initial

theorem stageFallback_mem (B : PublicProblem E θ) : B.stageFallback ∈ B.S :=
  B.prox.feasible 1 zero_lt_one B.initial

def stageReadoutValue (B : PublicProblem E θ) (n : ℕ) (s : CompositeStageState W E) : E :=
  if n ≤ s.2.2 ∧ stageAverage s ∈ B.S then stageAverage s else B.stageFallback

theorem stageReadoutValue_measurable (B : PublicProblem E θ) (n : ℕ) :
    Measurable (B.stageReadoutValue n : CompositeStageState W E → E) :=
  Measurable.ite ((measurableSet_le measurable_const (measurable_snd.comp measurable_snd)).inter
    (B.domain_measurable.preimage stageAverage_measurable))
    stageAverage_measurable measurable_const

theorem stageReadoutValue_mem (B : PublicProblem E θ) (n : ℕ) (s : CompositeStageState W E) :
    B.stageReadoutValue n s ∈ B.S := by
  unfold stageReadoutValue
  split_ifs with hs
  · exact hs.2
  · exact B.stageFallback_mem

def stageReadout (B : PublicProblem E θ) (n : ℕ) (s : CompositeStageState W E) : B.X :=
  ⟨B.stageReadoutValue n s, B.domain_subset (B.stageReadoutValue_mem n s)⟩

theorem stageReadout_measurable (B : PublicProblem E θ) (n : ℕ) :
    Measurable (B.stageReadout n : CompositeStageState W E → B.X) :=
  (B.stageReadoutValue_measurable n).subtype_mk

def stageRule (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) :
    CappedRaw.Rule (CompositeStageState W E) B.X E B.X where
  query s := B.stageQuery hR hn (L.point s.1)
  query_measurable := (B.stageQuery_measurable hR hn).comp (L.point_measurable.comp measurable_fst)
  acceptance := {h | (L.point h.1.1, h.2) ∈ B.stageAcceptance hR hn τ}
  acceptance_measurable := (B.stageAcceptance_measurable hR hn τ).preimage
    ((L.point_measurable.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  update h := (L.update (h.1.1, B.correctedReply hR hn (L.point h.1.1) h.2),
    (h.1.2.1 + selectedProximalPoint B.prox θ.G_pos hR hn (L.point h.1.1), h.1.2.2 + 1))
  update_measurable := by
    have hw : Measurable (fun h : CompositeStageState W E × E => h.1.1) := measurable_fst.comp measurable_fst
    have hz := L.point_measurable.comp hw
    have hc := (B.correctedReply_measurable hR hn).comp (hz.prodMk measurable_snd)
    exact (L.update_measurable.comp (hw.prodMk hc)).prodMk
      (((measurable_fst.comp measurable_snd).comp measurable_fst).add
        ((selectedProximalPoint_measurable B.prox B.h_convex θ.G_pos hR hn).comp hz) |>.prodMk
        (((measurable_snd.comp measurable_snd).comp measurable_fst).add_const 1))
  readout := B.stageReadout n
  readout_measurable := B.stageReadout_measurable n

def stageInitial {c : E} {R : ℝ} (L : StageLearner W E c R) :
    PUnit → CompositeStageState W E := fun _ => (L.initial, (0, 0))

def cappedStagePolicy (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (T : ℕ) :
    AdaptiveKernel.Policy PUnit B.X E B.X T :=
  (B.stageRule hR hn τ L).policy (stageInitial L) measurable_const n T

theorem stage_readout_domain (B : PublicProblem E θ) {c : E} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (L : StageLearner W E c R) (T : ℕ)
    (history : AdaptiveKernel.History PUnit E T) :
    ((B.cappedStagePolicy hR hn τ L T).output history : E) ∈ B.S :=
  B.stageReadoutValue_mem n _

end PublicProblem

namespace PrivateInstance
variable {B : PublicProblem E θ}

theorem stageLearner_point_distance (I : PrivateInstance B) {c : E} {R : ℝ}
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (w : W) :
    ‖L.point w - I.minimizer‖ ≤ 2 * R := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (L.point w) c I.minimizer
  have hb := L.point_bound w
  linarith only [ht, hb, hc]

theorem cappedStage_rejection_bound (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R)
    (t : ℕ) (history : AdaptiveKernel.History PUnit E t) :
    (I.oracle ((B.stageRule hR hn τ L).query
      ((B.stageRule hR hn τ L).state (PublicProblem.stageInitial L) n t history).2)).real
      {g | (history, g) ∈ (B.stageRule hR hn τ L).rejection (PublicProblem.stageInitial L) n t} ≤ 1 / 16 := by
  let s := ((B.stageRule hR hn τ L).state (PublicProblem.stageInitial L) n t history).2
  have hb := (I.acceptedRawLaw_bounds hR hn hτ (L.point s.1)
    (I.stageLearner_point_distance L hc s.1)).2.1
  apply le_trans (measureReal_mono (s₂ := (Prod.mk (L.point s.1) ⁻¹' B.stageAcceptance hR hn τ)ᶜ) ?_) hb
  intro g hg
  exact hg.2

theorem cappedStage_failure_probability (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (T : ℕ)
    (P : Measure PUnit) [IsProbabilityMeasure P] :
    ((B.cappedStagePolicy hR hn τ L T).historyLaw P I.oracle (4 * n)).real
      {history | ((B.stageRule hR hn τ L).state (PublicProblem.stageInitial L) n (4 * n) history).1 < n} ≤
        ((2 : ℝ) ^ (8 * n))⁻¹ :=
  (B.stageRule hR hn τ L).failure_probability measurable_const n T P I.oracle
    (I.cappedStage_rejection_bound hR hn hτ L hc)

end PrivateInstance
end HeavyTail
