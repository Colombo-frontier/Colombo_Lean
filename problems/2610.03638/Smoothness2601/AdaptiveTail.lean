import Smoothness2601.PrefixPosterior
import Smoothness2601.DeferredDimension

/-! Haar failure probability for the actual deferred simulation of an
arbitrary Adaptive.Algorithm, including an unqueried final output. -/
noncomputable section
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry
open DeferredPrefix
open scoped BigOperators RealInnerProductSpace ENNReal

variable {d T : ℕ}
variable (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)
variable (coins : ℕ → Bool)

theorem simulated_query_tail
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R) (hpR : ∀ q, ‖point q‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (initial : A.Memory) (t : ℕ)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T ⊥ μ)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) :
    μ {U | ∃ i : Fin T, prefixCount T coins t ≤ i.val ∧
      δ ≤ |⟪point (A.query t (simulatedState A reply coins initial U t)),U i⟫|} ≤
      failurePerInspection T n δ R := by
  let q := fun U => point (A.query t (simulatedState A reply coins initial U t))
  have hqm : Measurable q := hp.comp ((A.query_measurable t).comp
    ((simulatedState_measurable A reply coins hr t).comp (measurable_const.prodMk measurable_id)))
  have he (U : Frame d T) : q (truncate U (prefixCount T coins t)) = q U := by
    have hs := simulatedState_prefix A reply coins initial t U (truncate U (prefixCount T coins t))
      (truncate_truncate U (le_refl _)).symm
    exact congrArg (fun m => point (A.query t m)) hs.symm
  have ht := Smoothness2601.PrefixPosterior.prefix_query_tail d T (prefixCount T coins t) n hd
    hδ hR hδR μ hμ hU q hqm (fun U => hpR _)
  simpa only [he] using ht

theorem simulated_output_tail
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Space d → Space d) (hp : Measurable point)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R) (hpR : ∀ x, ‖point x‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (initial : A.Memory) (N : ℕ)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T ⊥ μ)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) :
    μ {U | ∃ i : Fin T, prefixCount T coins N ≤ i.val ∧
      δ ≤ |⟪point (A.output (simulatedState A reply coins initial U N)),U i⟫|} ≤
      failurePerInspection T n δ R := by
  let q := fun U => point (A.output (simulatedState A reply coins initial U N))
  have hqm : Measurable q := hp.comp (A.output_measurable.comp
    ((simulatedState_measurable A reply coins hr N).comp (measurable_const.prodMk measurable_id)))
  have he (U : Frame d T) : q (truncate U (prefixCount T coins N)) = q U := by
    have hs := simulatedState_prefix A reply coins initial N U (truncate U (prefixCount T coins N))
      (truncate_truncate U (le_refl _)).symm
    exact congrArg (fun m => point (A.output m)) hs.symm
  have ht := Smoothness2601.PrefixPosterior.prefix_query_tail d T (prefixCount T coins N) n hd
    hδ hR hδR μ hμ hU q hqm (fun U => hpR _)
  simpa only [he] using ht

def queryBad (point : Adaptive.Query (Space d) ℝ → Space d) (δ : ℝ)
    (initial : A.Memory) (N : ℕ) (U : Frame d T) : Prop :=
  ∃ t : Fin N, ∃ i : Fin T, prefixCount T coins t.val ≤ i.val ∧
    δ ≤ |⟪point (A.query t.val (simulatedState A reply coins initial U t.val)),U i⟫|

def outputBad (point : Space d → Space d) (δ : ℝ)
    (initial : A.Memory) (N : ℕ) (U : Frame d T) : Prop :=
  ∃ i : Fin T, prefixCount T coins N ≤ i.val ∧
    δ ≤ |⟪point (A.output (simulatedState A reply coins initial U N)),U i⟫|

theorem simulated_transcript_failure
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hpR : ∀ q, ‖point q‖ ≤ R) (hoR : ∀ x, ‖outPoint x‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (initial : A.Memory) (N : ℕ)
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T ⊥ μ)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) :
    μ {U | queryBad A reply coins point δ initial N U ∨ outputBad A reply coins outPoint δ initial N U} ≤
      ((N+1 : ℕ) : ℝ≥0∞)*failurePerInspection T n δ R := by
  have hq : μ {U | queryBad A reply coins point δ initial N U} ≤
      (N : ℝ≥0∞)*failurePerInspection T n δ R := by
    have he : {U | queryBad A reply coins point δ initial N U} =
        ⋃ t : Fin N, {U | ∃ i : Fin T, prefixCount T coins t.val ≤ i.val ∧
          δ ≤ |⟪point (A.query t.val (simulatedState A reply coins initial U t.val)),U i⟫|} := by
      ext U
      simp only [queryBad,Set.mem_setOf_eq,Set.mem_iUnion]
    rw [he]
    apply (measure_iUnion_fintype_le μ _).trans
    calc
      _ ≤ ∑ _t : Fin N, failurePerInspection T n δ R := Finset.sum_le_sum fun t _ =>
        simulated_query_tail A reply coins hr point hp hδ hR hδR hpR n hd initial t μ hμ hU
      _ = _ := by simp
  have hout := simulated_output_tail A reply coins hr outPoint ho hδ hR hδR hoR n hd initial N μ hμ hU
  change μ ({U | queryBad A reply coins point δ initial N U} ∪
    {U | outputBad A reply coins outPoint δ initial N U}) ≤ _
  apply (measure_union_le _ _).trans
  have hh := add_le_add hq hout
  simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

theorem queryBad_joint_measurable
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point) (δ : ℝ) (N : ℕ) :
    MeasurableSet {p : A.Memory × Frame d T | queryBad A reply coins point δ p.1 N p.2} := by
  simp only [queryBad,Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : prefixCount T coins t.val ≤ i.val
  · simp only [hi,true_and]
    have hq := hp.comp ((A.query_measurable t.val).comp (simulatedState_measurable A reply coins hr t.val))
    have hm : Measurable (fun p : A.Memory × Frame d T =>
        ⟪point (A.query t.val (simulatedState A reply coins p.1 p.2 t.val)),p.2 i⟫) :=
      (continuous_fst.inner continuous_snd).measurable.comp
        (hq.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact measurableSet_le measurable_const hm.abs
  · simp only [hi,false_and,Set.setOf_false]
    exact MeasurableSet.empty

theorem outputBad_joint_measurable
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Space d → Space d) (hp : Measurable point) (δ : ℝ) (N : ℕ) :
    MeasurableSet {p : A.Memory × Frame d T | outputBad A reply coins point δ p.1 N p.2} := by
  simp only [outputBad,Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : prefixCount T coins N ≤ i.val
  · simp only [hi,true_and]
    have hq := hp.comp (A.output_measurable.comp (simulatedState_measurable A reply coins hr N))
    have hm : Measurable (fun p : A.Memory × Frame d T =>
        ⟪point (A.output (simulatedState A reply coins p.1 p.2 N)),p.2 i⟫) :=
      (continuous_fst.inner continuous_snd).measurable.comp
        (hq.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact measurableSet_le measurable_const hm.abs
  · simp only [hi,false_and,Set.setOf_false]
    exact MeasurableSet.empty

/-- Averaging over arbitrary private initial memory preserves the same bound.
No standard-Borel hypothesis on the algorithm's memory is imposed. -/
theorem randomized_simulated_transcript_failure
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hpR : ∀ q, ‖point q‖ ≤ R) (hoR : ∀ x, ‖outPoint x‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (N : ℕ)
    (ν : Measure A.Memory) [IsProbabilityMeasure ν]
    (μ : Measure (Frame d T)) [IsProbabilityMeasure μ] (hμ : Invariant d T ⊥ μ)
    (hU : ∀ᵐ U ∂μ, Orthonormal ℝ U) :
    (ν.prod μ) {p | queryBad A reply coins point δ p.1 N p.2 ∨
      outputBad A reply coins outPoint δ p.1 N p.2} ≤
      ((N+1 : ℕ) : ℝ≥0∞)*failurePerInspection T n δ R := by
  have hs := (queryBad_joint_measurable A reply coins hr point hp δ N).union
    (outputBad_joint_measurable A reply coins hr outPoint ho δ N)
  change MeasurableSet {p : A.Memory × Frame d T |
    queryBad A reply coins point δ p.1 N p.2 ∨ outputBad A reply coins outPoint δ p.1 N p.2} at hs
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _m, ((N+1 : ℕ) : ℝ≥0∞)*failurePerInspection T n δ R ∂ν := by
      apply lintegral_mono
      intro m
      exact simulated_transcript_failure A reply coins hr point hp outPoint ho
        hδ hR hδR hpR hoR n hd m N μ hμ hU
    _ = _ := by simp

theorem haar_randomized_failure_small
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (point : Adaptive.Query (Space d) ℝ → Space d) (hp : Measurable point)
    (outPoint : Space d → Space d) (ho : Measurable outPoint)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hpR : ∀ q, ‖point q‖ ≤ R) (hoR : ∀ x, ‖outPoint x‖ ≤ R)
    (n : ℕ) (hd : T+(n+1) ≤ d) (N : ℕ) (hT : 1 ≤ T)
    (hlog : Real.log (16*((N+1 : ℕ) : ℝ)*T) ≤ (n : ℝ)*δ^2/(8*R^2))
    (ν : Measure A.Memory) [IsProbabilityMeasure ν] :
    (ν.prod (HaarFrame.frameLaw d T (by omega)))
      {p | queryBad A reply coins point δ p.1 N p.2 ∨ outputBad A reply coins outPoint δ p.1 N p.2} ≤
      ENNReal.ofReal (1/8 : ℝ) := by
  apply (randomized_simulated_transcript_failure A reply coins hr point hp outPoint ho hδ hR hδR hpR hoR
    n hd N ν (HaarFrame.frameLaw d T (by omega)) (frame_law_invariant d T (by omega) ⊥)
    (ProjectionConcentration.haar_orthonormal_ae d T (by omega))).trans
  exact failure_small (N+1) T n (by omega) hT hδ hR hlog

end Smoothness2601.PrefixSimulator
