import Smoothness2601.InnerSolve

/-! Composition and geometric scheduling for the actual projected kernels.
The concrete source step is verified separately before applying this rule. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Bilevel.Stateful
namespace Smoothness2601.AdjointIteration

variable {Param History E : Type*} [MeasurableSpace Param] [MeasurableSpace History]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def run (step : ℕ → Procedure (Param × E) History E) : ℕ → Procedure Param History E
  | 0 => Procedure.pure (fun _ => 0) measurable_const
  | k+1 => (run step k).bind (step k)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem run_calls (step : ℕ → Procedure (Param × E) History E)
    (N : ℕ → ℕ) (hN : ∀ k, (step k).CallsEq (fun _ => N k)) (k : ℕ) :
    (run step k).CallsEq (fun _ => ∑ j ∈ Finset.range k, N j) := by
  induction k with
  | zero => exact Procedure.calls_pure _ _
  | succ k ih => simpa only [Finset.sum_range_succ] using
      Procedure.CallsEq.bind _ _ _ _ ih (hN k)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
theorem run_integrable (step : ℕ → Procedure (Param × E) History E)
    (target : Param → E) (q d A : ℝ) (B : ℕ → ℕ)
    (hstep : ∀ k p v h,
      Integrable (fun z => ‖z.1-target p‖ ^ 2) ((step k).law ((p,v),h)) ∧
      (∫ z, ‖z.1-target p‖ ^ 2 ∂(step k).law ((p,v),h)) ≤
        q*‖v-target p‖ ^ 2+d+A/(B k:ℝ))
    (k : ℕ) (p : Param) (h : History) :
    Integrable (fun z => ‖z.1-target p‖ ^ 2) ((run step k).law (p,h)) := by
  induction k with
  | zero =>
    rw [run,Procedure.pure_law]
    exact integrable_dirac' (by fun_prop : Measurable
      (fun z : Outcome E History => ‖z.1-target p‖ ^ 2)).stronglyMeasurable
  | succ k ih =>
    exact (Procedure.bind_output_bound (run step k) (step k) p h
      (fun v => ‖v-target p‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
      (fun v => q*‖v-target p‖ ^ 2+d+A/(B k:ℝ))
      (((ih.const_mul q).add (integrable_const d)).add (integrable_const _))
      (fun z => (hstep k p z.1 z.2.1).1) (fun z => (hstep k p z.1 z.2.1).2)).1

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
theorem run_recurrence (step : ℕ → Procedure (Param × E) History E)
    (target : Param → E) (q d A : ℝ) (B : ℕ → ℕ)
    (hstep : ∀ k p v h,
      Integrable (fun z => ‖z.1-target p‖ ^ 2) ((step k).law ((p,v),h)) ∧
      (∫ z, ‖z.1-target p‖ ^ 2 ∂(step k).law ((p,v),h)) ≤
        q*‖v-target p‖ ^ 2+d+A/(B k:ℝ))
    (k : ℕ) (p : Param) (h : History) :
    (∫ z, ‖z.1-target p‖ ^ 2 ∂(run step (k+1)).law (p,h)) ≤
      q*(∫ z, ‖z.1-target p‖ ^ 2 ∂(run step k).law (p,h))+d+A/(B k:ℝ) := by
  have hi := run_integrable step target q d A B hstep k p h
  have hh := (Procedure.bind_output_bound (run step k) (step k) p h
    (fun v => ‖v-target p‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
    (fun v => q*‖v-target p‖ ^ 2+d+A/(B k:ℝ))
    (((hi.const_mul q).add (integrable_const d)).add (integrable_const _))
    (fun z => (hstep k p z.1 z.2.1).1) (fun z => (hstep k p z.1 z.2.1).2)).2
  have he₁ := integral_add (hi.const_mul q) (integrable_const d)
  have he₂ := integral_add ((hi.const_mul q).add (integrable_const d)) (integrable_const (A/(B k:ℝ)))
  simp only [Pi.add_apply] at he₁ he₂
  rw [he₂,he₁,integral_const_mul] at hh
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hh
  exact hh

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem geometric_norm {q d A D u : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hd : 0 ≤ d) (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 < u)
    (hfloor : d/(1-q) ≤ u ^ 2/4)
    (step : ℕ → Procedure (Param × E) History E) (target : Param → E)
    (hstep : ∀ k p v h,
      Integrable (fun z => ‖z.1-target p‖ ^ 2) ((step k).law ((p,v),h)) ∧
      (∫ z, ‖z.1-target p‖ ^ 2 ∂(step k).law ((p,v),h)) ≤
        q*‖v-target p‖ ^ 2+d+
          A/(GeometricBatches.batch q A u (GeometricBatches.iterations q D u) k:ℝ))
    (p : Param) (h : History) (hinit : ‖target p‖ ≤ D) :
    Integrable (fun z => ‖z.1-target p‖) ((run step (GeometricBatches.iterations q D u)).law (p,h)) ∧
    (∫ z, ‖z.1-target p‖ ∂(run step (GeometricBatches.iterations q D u)).law (p,h)) ≤ u := by
  have hI := run_integrable step target q d A _ hstep (GeometricBatches.iterations q D u) p h
  have hM : (∫ z, ‖z.1-target p‖ ^ 2 ∂(run step (GeometricBatches.iterations q D u)).law (p,h)) ≤
      3*u ^ 2/4 := by
    apply GeometricBatches.scheduled_error hq hq1 hA hD hu hd hfloor
      (fun k => ∫ z, ‖z.1-target p‖ ^ 2 ∂(run step k).law (p,h))
    · rw [run,Procedure.pure_law,integral_dirac' _ _
        (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1-target p‖ ^ 2)).stronglyMeasurable]
      simpa only [zero_sub,norm_neg] using (sq_le_sq₀ (norm_nonneg _) hD).mpr hinit
    · intro k _
      exact run_recurrence step target q d A _ hstep k p h
  exact InnerSolve.expected_norm_of_mse _ (measurable_fst.sub_const (target p)).aestronglyMeasurable
    hI hu (hM.trans (by nlinarith [sq_nonneg u]))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
theorem run_bounded (step : ℕ → Procedure (Param × E) History E) {V : ℝ} (hV : 0 ≤ V)
    (hstep : ∀ k p v h, ∀ᵐ z ∂(step k).law ((p,v),h), ‖z.1‖ ≤ V)
    (k : ℕ) (p : Param) (h : History) : ∀ᵐ z ∂(run step k).law (p,h), ‖z.1‖ ≤ V := by
  cases k with
  | zero =>
    rw [run,Procedure.pure_law]
    apply (ae_dirac_iff (measurableSet_le measurable_fst.norm measurable_const)).mpr
    simpa only [norm_zero] using hV
  | succ k =>
    rw [run]
    apply (Procedure.ae_bind_iff _ _ _ _ _
      (measurableSet_le measurable_fst.norm measurable_const)).mpr
    filter_upwards with z
    exact hstep k p z.1 z.2.1

end Smoothness2601.AdjointIteration
