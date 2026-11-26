import Smoothness2601.InnerBatch
import Smoothness2601.InnerGeometry
import Smoothness2601.GeometricBatches

/-! Actual variable-batch SGD kernels, with all original calls counted.
The schedule is fixed from public constants before any samples are drawn. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Smoothness2601.InnerSolve
open Bilevel.Stateful

variable {Query History Obs Param E : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs] [MeasurableSpace Param]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

def batchedStep (q : Param × E → Query) (hq : Measurable q) (n : ℕ) (α : ℝ) :
    Procedure (Param × E) History E :=
  (InnerBatch.affineBatch O n α).reparam (fun z => (q z,z.2)) (hq.prodMk measurable_snd)

def iterate (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) (α : ℝ) (B : ℕ → ℕ) :
    ℕ → Procedure Param History E
  | 0 => Procedure.pure initial hi
  | k+1 => (iterate q hq initial hi α B k).bind (batchedStep O q hq (B k) α)

omit [CompleteSpace E] in
theorem iterate_calls (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) (α : ℝ) (B : ℕ → ℕ) (k : ℕ) :
    (iterate O q hq initial hi α B k).CallsEq (fun _ => ∑ j ∈ Finset.range k, B j) := by
  induction k with
  | zero => exact Procedure.calls_pure _ _
  | succ k ih =>
    have hb : (batchedStep O q hq (B k) α).CallsEq (fun _ => B k) :=
      Procedure.CallsEq.reparam _ _ (InnerBatch.affineBatch_calls O _ _) _ _
    simpa only [Finset.sum_range_succ] using
      Procedure.CallsEq.bind _ _ _ _ ih hb

theorem iterate_integrable (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) {α : ℝ} (hα : α ≠ 0)
    (B : ℕ → ℕ) (hB : ∀ k, 0 < B k) (c : ℝ) (center : Param → E)
    (hcontract : ∀ p y, ‖y-α • O.truth (q (p,y))-center p‖ ^ 2 ≤ c*‖y-center p‖ ^ 2)
    (k : ℕ) (p : Param) (h : History) :
    Integrable (fun z => ‖z.1-center p‖ ^ 2) ((iterate O q hq initial hi α B k).law (p,h)) := by
  induction k with
  | zero =>
    rw [iterate, Procedure.pure_law]
    exact integrable_dirac'
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1-center p‖ ^ 2)).stronglyMeasurable
  | succ k ih =>
    have hs (z : Outcome E History) := InnerBatch.affineBatch_error O (B k) (hB k) hα
      (q (p,z.1)) z.1 (center p) z.2.1
    exact (Procedure.bind_output_bound (iterate O q hq initial hi α B k)
      (batchedStep O q hq (B k) α) p h (fun y => ‖y-center p‖ ^ 2) (by fun_prop)
      (fun _ => sq_nonneg _) (fun y => c*‖y-center p‖ ^ 2 + α ^ 2*σ ^ 2/(B k : ℝ))
      ((ih.const_mul c).add (integrable_const _)) (fun z => (hs z).1)
      (fun z => (hs z).2.trans (add_le_add_right (hcontract p z.1) _))).1

theorem iterate_recurrence (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) {α : ℝ} (hα : α ≠ 0)
    (B : ℕ → ℕ) (hB : ∀ k, 0 < B k) (c : ℝ) (center : Param → E)
    (hcontract : ∀ p y, ‖y-α • O.truth (q (p,y))-center p‖ ^ 2 ≤ c*‖y-center p‖ ^ 2)
    (k : ℕ) (p : Param) (h : History) :
    (∫ z, ‖z.1-center p‖ ^ 2 ∂(iterate O q hq initial hi α B (k+1)).law (p,h)) ≤
      c*(∫ z, ‖z.1-center p‖ ^ 2 ∂(iterate O q hq initial hi α B k).law (p,h)) +
        α ^ 2*σ ^ 2/(B k : ℝ) := by
  have hI := iterate_integrable O q hq initial hi hα B hB c center hcontract k p h
  have hs (z : Outcome E History) := InnerBatch.affineBatch_error O (B k) (hB k) hα
    (q (p,z.1)) z.1 (center p) z.2.1
  have hb := (Procedure.bind_output_bound (iterate O q hq initial hi α B k)
    (batchedStep O q hq (B k) α) p h (fun y => ‖y-center p‖ ^ 2) (by fun_prop)
    (fun _ => sq_nonneg _) (fun y => c*‖y-center p‖ ^ 2 + α ^ 2*σ ^ 2/(B k : ℝ))
    ((hI.const_mul c).add (integrable_const _)) (fun z => (hs z).1)
    (fun z => (hs z).2.trans (add_le_add_right (hcontract p z.1) _))).2
  simpa only [integral_add (hI.const_mul c) (integrable_const (α ^ 2*σ ^ 2/(B k : ℝ))),
    integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul] using hb

def count (c D u : ℝ) : ℕ := GeometricBatches.iterations c D u
def batchCount (α σ c D u : ℝ) (k : ℕ) : ℕ :=
  GeometricBatches.batch c (α ^ 2*σ ^ 2) u (count c D u) k

def scheduled (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) (α c D u : ℝ) : Procedure Param History E :=
  iterate O q hq initial hi α (batchCount α σ c D u) (count c D u)

theorem scheduled_mse (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) {α c D u : ℝ}
    (hα : α ≠ 0) (hc : 0 < c) (hc1 : c < 1) (hD : 0 ≤ D) (hu : 0 < u)
    (center : Param → E)
    (hcontract : ∀ p y, ‖y-α • O.truth (q (p,y))-center p‖ ^ 2 ≤ c*‖y-center p‖ ^ 2)
    (p : Param) (h : History) (hinit : ‖initial p-center p‖ ≤ D) :
    Integrable (fun z => ‖z.1-center p‖ ^ 2) ((scheduled O q hq initial hi α c D u).law (p,h)) ∧
    (∫ z, ‖z.1-center p‖ ^ 2 ∂(scheduled O q hq initial hi α c D u).law (p,h)) ≤ 3*u ^ 2/4 := by
  have hB : ∀ k, 0 < batchCount α σ c D u k := fun k => GeometricBatches.batch_pos _ _ _ _ k
  refine ⟨iterate_integrable O q hq initial hi hα _ hB c center hcontract _ p h, ?_⟩
  apply GeometricBatches.scheduled_error (A := α ^ 2*σ ^ 2) hc hc1 (by positivity) hD hu (by norm_num : (0 : ℝ) ≤ 0)
    (by simp; positivity) (fun k => ∫ z, ‖z.1-center p‖ ^ 2
      ∂(iterate O q hq initial hi α (batchCount α σ c D u) k).law (p,h))
  · rw [iterate, Procedure.pure_law]
    rw [integral_dirac' _ _
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1-center p‖ ^ 2)).stronglyMeasurable]
    exact (sq_le_sq₀ (norm_nonneg _) hD).mpr hinit
  · intro k _
    simpa only [add_zero] using
      iterate_recurrence O q hq initial hi hα _ hB c center hcontract k p h

omit [CompleteSpace E] in
theorem scheduled_calls (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) (α c D u : ℝ) :
    (scheduled O q hq initial hi α c D u).CallsEq
      (fun _ => ∑ k ∈ Finset.range (count c D u), batchCount α σ c D u k) :=
  iterate_calls O q hq initial hi α _ _

theorem sample_count_bound (α σ c D u : ℝ) (hc : c < 1) :
    ((∑ k ∈ Finset.range (count c D u), batchCount α σ c D u k : ℕ) : ℝ) ≤
      count c D u + 4*(α ^ 2*σ ^ 2)/(u ^ 2*(1-Real.sqrt c) ^ 2) := by
  push_cast
  exact GeometricBatches.total_cost hc (by positivity) _

theorem expected_norm_of_mse {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (f : Ω → F) (hf : AEStronglyMeasurable f ν)
    (hsq : Integrable (fun ω => ‖f ω‖ ^ 2) ν) {u : ℝ} (hu : 0 < u)
    (hbound : (∫ ω, ‖f ω‖ ^ 2 ∂ν) ≤ u ^ 2) :
    Integrable (fun ω => ‖f ω‖) ν ∧ (∫ ω, ‖f ω‖ ∂ν) ≤ u := by
  have hlp : MemLp f 2 ν := (memLp_two_iff_integrable_sq_norm hf).mpr hsq
  have hi := (hlp.integrable (by norm_num)).norm
  refine ⟨hi, ?_⟩
  have hp (ω : Ω) : 2*u*‖f ω‖ ≤ ‖f ω‖ ^ 2 + u ^ 2 := by
    nlinarith [sq_nonneg (‖f ω‖-u)]
  have hh := integral_mono (hi.const_mul (2*u)) (hsq.add (integrable_const _)) hp
  change (∫ ω, 2*u*‖f ω‖ ∂ν) ≤ ∫ ω, ‖f ω‖ ^ 2 + u ^ 2 ∂ν at hh
  rw [integral_const_mul, integral_add hsq (integrable_const (u ^ 2))] at hh
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hh
  nlinarith

theorem scheduled_norm (q : Param × E → Query) (hq : Measurable q)
    (initial : Param → E) (hi : Measurable initial) {α c D u : ℝ}
    (hα : α ≠ 0) (hc : 0 < c) (hc1 : c < 1) (hD : 0 ≤ D) (hu : 0 < u)
    (center : Param → E)
    (hcontract : ∀ p y, ‖y-α • O.truth (q (p,y))-center p‖ ^ 2 ≤ c*‖y-center p‖ ^ 2)
    (p : Param) (h : History) (hinit : ‖initial p-center p‖ ≤ D) :
    Integrable (fun z => ‖z.1-center p‖) ((scheduled O q hq initial hi α c D u).law (p,h)) ∧
    (∫ z, ‖z.1-center p‖ ∂(scheduled O q hq initial hi α c D u).law (p,h)) ≤ u := by
  have hm := scheduled_mse O q hq initial hi hα hc hc1 hD hu center hcontract p h hinit
  exact expected_norm_of_mse _ (measurable_fst.sub_const (center p)).aestronglyMeasurable hm.1 hu
    (hm.2.trans (by nlinarith [sq_nonneg u]))

end Smoothness2601.InnerSolve
