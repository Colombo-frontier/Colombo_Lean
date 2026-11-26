import Bilevel.TransportControllerQuery
import Bilevel.TransportNetworkProtocol

/-! A whole frozen raw-query insertion phase under the actual network
posterior law. All requests are fixed before this phase, as in the source
round protocol. Energy injections concern the same successively enlarged
physical spaces. The augmented-family version is proved separately in
TransportAuxiliaryQueryPhase. -/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators
namespace Bilevel.TransportRoundQuery
open TransportNetwork EuclideanGaussian ProjectionGeometry TransportObserver
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

abbrev Request (n D : ℕ) := Vertex n × Space D

def queryPhaseKnown {n D : ℕ} : List (Request n D) → Known n D → Known n D
  | [],W => W
  | q::qs,W => queryPhaseKnown qs (insert W q.1 q.2)

def queryPhaseBad {n D : ℕ} (T : ℕ) (hT : T≤D) (a : ℝ) :
    List (Request n D) → Known n D → Latent n D → Prop
  | [],_,_ => False
  | q::qs,W,s =>
    a < frameEnergy (W q.1 ⊔ Submodule.span ℝ {q.2}) (frame T hT s q.1) Finset.univ-
      frameEnergy (W q.1) (frame T hT s q.1) Finset.univ ∨
    queryPhaseBad T hT a qs (insert W q.1 q.2) s

theorem queryPhaseKnown_mono {n D : ℕ} (qs : List (Request n D)) (W : Known n D) :
    ∀ v, W v≤queryPhaseKnown qs W v := by
  induction qs generalizing W with
  | nil => exact fun _ => le_rfl
  | cons q qs ih => exact fun v => (le_insert W q.1 q.2 v).trans (ih _ v)

theorem queryPhaseKnown_dimension {n D : ℕ} (qs : List (Request n D)) (W : Known n D)
    (d : ℕ) (hW : DimensionBound W d) : DimensionBound (queryPhaseKnown qs W) (d+qs.length) := by
  induction qs generalizing W d with
  | nil => exact hW
  | cons q qs ih =>
    simpa only [queryPhaseKnown,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (insert W q.1 q.2) (d+1) (dimensionBound_insert hW q.1 q.2)

theorem queryPhaseBad_measurable {n D : ℕ} (T : ℕ) (hT : T≤D)
    (a : ℝ) (qs : List (Request n D)) (W : Known n D) :
    MeasurableSet {s | queryPhaseBad T hT a qs W s} := by
  induction qs generalizing W with
  | nil => exact MeasurableSet.empty
  | cons q qs ih =>
    apply MeasurableSet.union _ (ih (insert W q.1 q.2))
    simp_rw [TransportControllerQuery.raw_energy_increment]
    have hf : Measurable (fun s : Latent n D =>
        ∑ i, ⟪revelationDirection (W q.1) q.2,frame T hT s q.1 i⟫^2) := by
      apply Finset.measurable_sum
      intro i _
      exact ((continuous_const.inner continuous_id).measurable.comp
        ((measurable_pi_apply i).comp (((measurable_pi_apply q.1).comp (frame_measurable n D T hT))))).pow_const 2
    exact measurableSet_lt measurable_const hf

theorem query_phase_failure {n D : ℕ} (T : ℕ) (hT : T≤D)
    (a : ℝ) (ha : 0<a) (r : ℕ) (hr : 0<r)
    (qs : List (Request n D)) : ∀ (W : Known n D) (d : ℕ), DimensionBound W d → d+qs.length+r≤D →
      ∀ (μ : Measure (Latent n D)) [IsProbabilityMeasure μ], Invariant W μ →
        μ {s | queryPhaseBad T hT a qs W s} ≤
          (qs.length:ℝ≥0∞)*ENNReal.ofReal ((T:ℕ)/((r:ℝ)*a)) := by
  induction qs with
  | nil =>
    intro W d hW hD μ _ hμ
    simp [queryPhaseBad]
  | cons q qs ih =>
    intro W d hW hD μ _ hμ
    have hd : d<D := by simp only [List.length_cons] at hD; omega
    have hden : (r:ℝ)≤(D:ℝ)-d := by
      have hh : d+r≤D := by omega
      exact_mod_cast (show (r:ℤ)≤(D:ℤ)-d by omega)
    have hrR : (0:ℝ)<r := by exact_mod_cast hr
    have hh := TransportControllerQuery.raw_query_failure T hT W μ hμ q.1 d (hW q.1) hd q.2 a ha
    have hb : μ.real {s | a < frameEnergy (W q.1 ⊔ Submodule.span ℝ {q.2})
        (frame T hT s q.1) Finset.univ-
        frameEnergy (W q.1) (frame T hT s q.1) Finset.univ} ≤
        (T:ℕ)/((r:ℝ)*a) := hh.trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hrR ha)
        (mul_le_mul_of_nonneg_right hden ha.le))
    have hhead : μ {s | a < frameEnergy (W q.1 ⊔ Submodule.span ℝ {q.2})
        (frame T hT s q.1) Finset.univ-
        frameEnergy (W q.1) (frame T hT s q.1) Finset.univ} ≤
        ENNReal.ofReal ((T:ℕ)/((r:ℝ)*a)) := by
      simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hb
    have ht := ih (insert W q.1 q.2) (d+1) (dimensionBound_insert hW q.1 q.2)
      (by simp only [List.length_cons] at hD; omega) μ (invariant_mono (le_insert W q.1 q.2) μ hμ)
    change μ ({s | a < frameEnergy (W q.1 ⊔ Submodule.span ℝ {q.2})
        (frame T hT s q.1) Finset.univ-
        frameEnergy (W q.1) (frame T hT s q.1) Finset.univ} ∪
        {s | queryPhaseBad T hT a qs (insert W q.1 q.2) s}) ≤ _
    apply (measure_union_le _ _).trans
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using add_le_add hhead ht

end Bilevel.TransportRoundQuery

