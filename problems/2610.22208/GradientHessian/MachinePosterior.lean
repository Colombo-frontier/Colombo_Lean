import GradientHessian.MachineCompiler
import GradientHessian.GaussianPosterior

/-!
# Posterior overlap for actual bounded-time machine runs

The machine can perform any number of internal steps before the chosen time
cutoff. Only matrix products consume its query budget. The policy is compiled
and padded before applying the proved Gaussian posterior theorem.
-/

namespace GradientHessian.MachinePosterior

open MeasureTheory Matrix LowRank MachineCompiler GaussianPosterior
noncomputable section

def readOrZero {d : ℕ} (result : Bool × Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := if result.1 then result.2 else 0

theorem readOrZero_measurable (d : ℕ) : Measurable (@readOrZero d) := by
  exact Measurable.ite (measurable_fst (measurableSet_singleton true))
    measurable_snd measurable_const

theorem readOrZero_projector {d : ℕ} (result : Bool × Matrix (Fin d) (Fin d) ℝ)
    (h : result.1 = true → IsOrthogonalProjector result.2) :
    IsOrthogonalProjector (readOrZero result) := by
  unfold readOrZero
  split_ifs with hh
  · exact h hh
  · exact ⟨by simp, by simp⟩

theorem readOrZero_trace_le {d : ℕ} (result : Bool × Matrix (Fin d) (Fin d) ℝ)
    {rank : ℝ} (hr : 0 ≤ rank) (h : result.1 = true → result.2.trace ≤ rank) :
    (readOrZero result).trace ≤ rank := by
  unfold readOrZero
  split_ifs with hh
  · exact h hh
  · simpa using hr

def compiledOutput {d : ℕ} {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (P : Program d State (Matrix (Fin d) (Fin d) ℝ)) (q : ℕ)
    (c : MeasurableStateMap Seed (ℕ × State))
    (h : OracleHistory d q Seed) : Matrix (Fin d) (Fin d) ℝ :=
  readOrZero (readPaddedSymmetricOutput d q (P.compile q c) h)

theorem compiledOutput_measurable {d : ℕ} {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (P : Program d State (Matrix (Fin d) (Fin d) ℝ)) (q : ℕ)
    (c : MeasurableStateMap Seed (ℕ × State)) :
    Measurable (compiledOutput P q c) :=
  (readOrZero_measurable d).comp (measurable_readPaddedSymmetricOutput d q (P.compile q c))

/-- An overlap bound for the actual compiled computation, with no additional
assumption about the posterior distribution or query mass. -/
theorem compiled_overlap (r s q : ℕ) {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (P : Program (r + q) State (Matrix (Fin (r + q)) (Fin (r + q)) ℝ))
    (c : MeasurableStateMap Seed (ℕ × State))
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0)
    {rank : ℝ} (hrank : 0 ≤ rank)
    (hout : ∀ state, IsOrthogonalProjector (P.output state) ∧ (P.output state).trace ≤ rank) :
    (∫ p, (compiledOutput P q c
        (runAmbientGram r s q (padSymmetricPolicy (r + q) q (P.compile q c)) p) *
        leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * ((r : ℝ) - s) * ((q : ℝ) + rank) / r := by
  have hprop := P.compile_outputs
    (fun Q => IsOrthogonalProjector Q ∧ Q.trace ≤ rank) hout q c
  apply arbitrary_rank_posterior_overlap r s q seedLaw
    (padSymmetricPolicy (r + q) q (P.compile q c)) hs hr hv
    (compiledOutput P q c) (compiledOutput_measurable P q c)
  · intro h
    apply readOrZero_projector
    intro hh
    exact (readPaddedSymmetricOutput_property (r + q) q (P.compile q c)
      _ hprop h hh).1
  · intro h
    apply readOrZero_trace_le _ hrank
    intro hh
    exact (readPaddedSymmetricOutput_property (r + q) q (P.compile q c)
      _ hprop h hh).2

theorem compiledOutput_eq_eval {d : ℕ} {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (P : Program d State (Matrix (Fin d) (Fin d) ℝ)) (q : ℕ)
    (c : MeasurableStateMap Seed (ℕ × State))
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W) (seed : Seed)
    (hcap : P.calls (fun v => W *ᵥ v) (c.1 seed).1 (c.1 seed).2 ≤ q) :
    compiledOutput P q c
      (runAmbientOracle d q (padSymmetricPolicy d q (P.compile q c)) W seed) =
      readOrZero (P.eval (fun v => W *ᵥ v) (c.1 seed).1 (c.1 seed).2) := by
  unfold compiledOutput
  rw [P.padded_simulates q c W hW seed hcap]

/-- The same inequality stated directly for the machine's actual finite-time
evaluation on the presampled factor X, under its actual matrix-product cap. -/
theorem finite_time_overlap (r s q : ℕ) {State Seed : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (P : Program (r + q) State (Matrix (Fin (r + q)) (Fin (r + q)) ℝ))
    (c : MeasurableStateMap Seed (ℕ × State))
    (hs : s ≤ r) (hr : 0 < r) {v : NNReal} (hv : v ≠ 0)
    {rank : ℝ} (hrank : 0 ≤ rank)
    (hout : ∀ state, IsOrthogonalProjector (P.output state) ∧ (P.output state).trace ≤ rank)
    (hcap : ∀ seed (X : Matrix (Fin (r + q)) (Fin (s + q)) ℝ),
      P.calls (fun u => (X * Xᵀ) *ᵥ u) (c.1 seed).1 (c.1 seed).2 ≤ q) :
    (∫ p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ,
      (readOrZero (P.eval (fun u => (p.2 * p.2ᵀ) *ᵥ u) (c.1 p.1).1 (c.1 p.1).2) *
        leftKernelProjector p.2).trace
      ∂seedLaw.prod (iidMatrixLaw (r + q) (s + q) v)) ≤
        2 * ((r : ℝ) - s) * ((q : ℝ) + rank) / r := by
  have he : (fun p : Seed × Matrix (Fin (r + q)) (Fin (s + q)) ℝ =>
      compiledOutput P q c
        (runAmbientGram r s q (padSymmetricPolicy (r + q) q (P.compile q c)) p)) =
      (fun p => readOrZero (P.eval (fun u => (p.2 * p.2ᵀ) *ᵥ u)
        (c.1 p.1).1 (c.1 p.1).2)) := by
    funext p
    exact compiledOutput_eq_eval P q c _ (by simp) p.1 (hcap p.1 p.2)
  have h := compiled_overlap r s q seedLaw P c hs hr hv hrank hout
  have he' := fun p => congrFun he p
  simpa only [he'] using h

end
end GradientHessian.MachinePosterior
