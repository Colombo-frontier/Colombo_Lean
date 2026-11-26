import GradientHessian.MachinePosterior
import GradientHessian.MachineStopping
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Posterior overlap without a uniform internal-time bound

Finite-time compiled policies obey the same query budget for every cutoff.
Their outputs converge to the actual first-halt output. Dominated convergence
removes the cutoff. Nonhalting runs contribute the zero projector, so almost
sure termination is not needed for this stronger stopped-output inequality.
-/

namespace GradientHessian.MachinePosterior

open MeasureTheory Matrix LowRank MachineCompiler Filter
open scoped Topology
noncomputable section

def timeConfig {State Seed : Type*} [MeasurableSpace State] [MeasurableSpace Seed]
    (initial : MeasurableStateMap Seed State) (N : ℕ) :
    MeasurableStateMap Seed (ℕ × State) :=
  ⟨fun seed => (N, initial.1 seed), measurable_const.prodMk initial.2⟩

/-- Actual stopped-output overlap for an arbitrary measurable matrix machine
with a pathwise query cap, no uniform bound on internal computation, and an
arbitrary measurable output projector. -/
theorem unbounded_stopped_overlap (r s q : ℕ) {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (P : Program (r + q) State (Matrix (Fin (r + q)) (Fin (r + q)) ℝ))
    (initial : MeasurableStateMap Seed State)
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0)
    {rank : ℝ} (hrank : 0 ≤ rank)
    (hout : ∀ state, IsOrthogonalProjector (P.output state) ∧ (P.output state).trace ≤ rank)
    (hcap : ∀ seed (X : Matrix (Fin (r + q)) (Fin (s + q)) ℝ) n,
      P.calls (fun u => (X * Xᵀ) *ᵥ u) n (initial.1 seed) ≤ q) :
    (∫ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ,
      (readOrZero (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1)) *
        leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * ((r : ℝ) - s) * ((q : ℝ) + rank) / r := by
  let μ := seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)
  let Q := fun (n : ℕ) (p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ) =>
    readOrZero (P.eval (fun u => (p.2 * p.2ᵀ) *ᵥ u) n (initial.1 p.1))
  let F := fun n p => (Q n p * leftKernelProjector p.2).trace
  let f := fun p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ =>
    (readOrZero (P.stoppedResult (fun u => (p.2 * p.2ᵀ) *ᵥ u) (initial.1 p.1)) *
      leftKernelProjector p.2).trace
  have hQ : ∀ n, Measurable (Q n) := by
    intro n
    have he : Q n = fun p => compiledOutput P q (timeConfig initial n)
        (runAmbientGram r s q
          (padSymmetricPolicy (r + q) q (P.compile q (timeConfig initial n))) p) := by
      funext p
      exact (compiledOutput_eq_eval P q (timeConfig initial n) _ (by simp)
        p.1 (hcap p.1 p.2 n)).symm
    rw [he]
    exact (compiledOutput_measurable P q (timeConfig initial n)).comp
      (measurable_runAmbientGram r s q _)
  have hQprop : ∀ n p, IsOrthogonalProjector (Q n p) ∧ (Q n p).trace ≤ rank := by
    intro n p
    have h := P.eval_output_property
      (fun A => IsOrthogonalProjector A ∧ A.trace ≤ rank) hout
      (fun u => (p.2 * p.2ᵀ) *ᵥ u) n (initial.1 p.1)
    exact ⟨readOrZero_projector _ (fun hh => (h hh).1),
      readOrZero_trace_le _ hrank (fun hh => (h hh).2)⟩
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    have hK : Measurable (fun p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ =>
        leftKernelProjector p.2) := measurable_leftKernelProjector.comp measurable_snd
    have hm : Measurable (F n) := by
      dsimp only [F]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      fun_prop
    exact hm.stronglyMeasurable.aestronglyMeasurable
  have hb : ∀ n, ∀ᵐ p ∂μ, ‖F n p‖ ≤ rank := by
    intro n
    apply Filter.Eventually.of_forall
    intro p
    have hp := (hQprop n p).1
    have hk := leftKernelProjector_isProjector p.2
    rw [Real.norm_eq_abs, abs_of_nonneg (projector_overlap_nonneg hp hk)]
    exact (projector_overlap_le hp hk).trans (hQprop n p).2
  have hlim : ∀ᵐ p ∂μ, Tendsto (fun n => F n p) atTop (𝓝 (f p)) := by
    apply Filter.Eventually.of_forall
    intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [P.eventually_eval_eq_stopped (fun u => (p.2 * p.2ᵀ) *ᵥ u)
      (initial.1 p.1)] with n hn
    simp only [F, Q, f, hn]
  have hi := tendsto_integral_of_dominated_convergence (fun _ => rank)
    hFmeas (integrable_const rank) hb hlim
  apply le_of_tendsto hi
  apply Filter.Eventually.of_forall
  intro n
  exact finite_time_overlap r s q seedLaw P (timeConfig initial n) hs hr hv hrank hout
    (fun seed X => hcap seed X n)

end
end GradientHessian.MachinePosterior
