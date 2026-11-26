import Bilevel.TransportNetworkProtocol

/-! Query insertion failure for finite adaptive network observation protocols.
The proof disintegrates the actual shared latent network law after every
observation. No fresh edge map is sampled between protocol nodes. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace Bilevel.TransportNetwork
open EuclideanGaussian
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

theorem observation_tail_bound {Y : Type*} [MeasurableSpace Y]
    {n' D' : ℕ} (μ : Measure (Latent n' D')) [IsProbabilityMeasure μ]
    (o : Latent n' D' → Y) (ho : Measurable o) (bad : Y → Latent n' D' → Prop)
    (hbad : MeasurableSet {p : Y × Latent n' D' | bad p.1 p.2}) (c : ℝ≥0∞)
    (hc : ∀ᵐ y ∂μ.map o, condDistrib id o μ y {z | bad y z} ≤ c) :
    μ {z | bad (o z) z} ≤ c := by
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map ho.aemeasurable
  have he := ConditionalSupport.event_disintegration μ o ho _ hbad
  change μ {z | bad (o z) z} = ∫⁻ y, condDistrib id o μ y {z | bad y z} ∂μ.map o at he
  rw [he]
  calc
    _ ≤ ∫⁻ _y, c ∂μ.map o := lintegral_mono_ae hc
    _ = _ := by simp

def queryFailureBudget (T r : ℕ) (a : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a))

theorem query_failure_protocol {n D T m : ℕ} (hT : T ≤ D) (r : ℕ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (P : Protocol n D T m) :
    ∀ d : ℕ, ∀ W : Known n D, DimensionBound W d → d+m+r ≤ D →
      ∀ (μ : Measure (Latent n D)) [IsProbabilityMeasure μ], Invariant W μ →
        Regular hT a P → Valid P W →
        μ {z | queryBad hT a P z} ≤ (m:ℝ≥0∞)*queryFailureBudget T r a := by
  induction P with
  | halt =>
    intro d W hW hdim μ _ hμ hP hV
    simp only [queryBad,Set.setOf_false,measure_empty]
    exact zero_le _
  | @query m v q next ih =>
    intro d W hW hdim μ _ hμ hP hV
    have hd : d < D := by omega
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hden : (r:ℝ) ≤ (D:ℝ)-d := by
      have hh : d+r ≤ D := by omega
      have hh' : (d:ℝ)+r ≤ D := by exact_mod_cast hh
      linarith
    have hheadR : μ.real {z | a < ∑ i, ⟪q,frame T hT z v i⟫^2} ≤ (T:ℝ)/((r:ℝ)*a) :=
      (query_failure_dimension T hT W μ hμ v d (hW v) hd q hV.1 hV.2.1 a ha).trans
        (div_le_div_of_nonneg_left (Nat.cast_nonneg T) (mul_pos hrR ha)
          (mul_le_mul_of_nonneg_right hden ha.le))
    have hhead : μ {z | a < ∑ i, ⟪q,frame T hT z v i⟫^2} ≤ queryFailureBudget T r a := by
      simpa only [queryFailureBudget,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal hheadR
    have htail : μ {z | queryBad hT a (next (queryObservation T hT v q z)) z} ≤
        (m:ℝ≥0∞)*queryFailureBudget T r a := by
      apply observation_tail_bound μ (queryObservation T hT v q) (query_measurable T hT v q)
        (fun y z => queryBad hT a (next y) z) hP.1
      filter_upwards [query_posterior_invariant T hT W μ hμ v q] with y hy
      exact ih y (d+1) (insert W v q) (dimensionBound_insert hW v q) (by omega)
        _ hy (hP.2 y) (hV.2.2 y)
    change μ ({z | a < ∑ i, ⟪q,frame T hT z v i⟫^2} ∪
      {z | queryBad hT a (next (queryObservation T hT v q z)) z}) ≤ _
    apply (measure_union_le _ _).trans
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using add_le_add hhead htail
  | @named m v i next ih =>
    intro d W hW hdim μ _ hμ hP hV
    have htail : μ {z | queryBad hT a (next (namedObservation T hT v i z)) z} ≤
        (m:ℝ≥0∞)*queryFailureBudget T r a := by
      apply observation_tail_bound μ (namedObservation T hT v i) (named_measurable T hT v i)
        (fun y z => queryBad hT a (next y) z) hP.1
      filter_upwards [named_posterior_invariant T hT W μ hμ v i] with y hy
      exact ih y (d+1) (insert W v y) (dimensionBound_insert hW v y) (by omega)
        _ hy (hP.2 y) (hV y)
    exact htail.trans (mul_le_mul_right' (by exact_mod_cast Nat.le_succ m) _)
  | @forward m e q next ih =>
    intro d W hW hdim μ _ hμ hP hV
    have htail : μ {z | queryBad hT a (next (forwardObservation e q z)) z} ≤
        (m:ℝ≥0∞)*queryFailureBudget T r a := by
      apply observation_tail_bound μ (forwardObservation e q) (forward_measurable e q)
        (fun y z => queryBad hT a (next y) z) hP.1
      filter_upwards [forward_posterior_invariant W μ hμ e q hV.1] with y hy
      exact ih y (d+1) (insert W (dst e) y) (dimensionBound_insert hW (dst e) y) (by omega)
        _ hy (hP.2 y) (hV.2 y)
    exact htail.trans (mul_le_mul_right' (by exact_mod_cast Nat.le_succ m) _)
  | @reverse m e q next ih =>
    intro d W hW hdim μ _ hμ hP hV
    have htail : μ {z | queryBad hT a (next (reverseObservation e q z)) z} ≤
        (m:ℝ≥0∞)*queryFailureBudget T r a := by
      apply observation_tail_bound μ (reverseObservation e q) (reverse_measurable e q)
        (fun y z => queryBad hT a (next y) z) hP.1
      filter_upwards [reverse_posterior_invariant W μ hμ e q hV.1] with y hy
      exact ih y (d+1) (insert W (src e) y) (dimensionBound_insert hW (src e) y) (by omega)
        _ hy (hP.2 y) (hV.2 y)
    exact htail.trans (mul_le_mul_right' (by exact_mod_cast Nat.le_succ m) _)

theorem prior_query_failure_protocol {n D T m : ℕ} (hT : T ≤ D)
    (r : ℕ) (hr : 0 < r) (a : ℝ) (ha : 0 < a) (P : Protocol n D T m)
    (hd : m+r ≤ D) (hP : Regular hT a P) (hV : Valid P (fun _ => ⊥)) :
    law n D {z | queryBad hT a P z} ≤ (m:ℝ≥0∞)*queryFailureBudget T r a :=
  query_failure_protocol hT r hr a ha P 0 (fun _ => ⊥) (fun _ => by simp)
    (by simpa only [zero_add] using hd) (law n D) (law_invariant _) hP hV

end Bilevel.TransportNetwork
