import Matvec.SourceIterationPolicy
import Matvec.SourceEstimator
import Matvec.PolicyRepetition
import Matvec.MaximumAmplification

/-!
# Executable measurable source-to-spectral reduction

This policy only contains the given base solver, ordinary source queries,
the explicit Gaussian start map, and measurable finite computations. The
unknown source operator appears only in the theorem evaluating the policy.
-/

namespace Matvec.SourceIterationPolicy
open MeasureTheory MeasurableSimulation
noncomputable section

variable {E Seed : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Seed] {K : ℕ}

def powerPolicy (applyInverse : Policy E E E K (E × Seed)) (q : ℕ) :
    Policy E E ℝ (q * K) (E × SeedBlock Seed q) :=
  (iteratePolicy (0 : E) (fun _ => applyInverse) q).mapOutput
    (fun _ out => powerRoot ‖out‖ q) (by
      exact measurable_snd.norm.pow_const _)

omit [SecondCountableTopology E] in
theorem powerPolicy_run (applyInverse : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (q : ℕ) (g : E) (seeds : SeedBlock Seed q) :
    (powerPolicy applyInverse q).run H (g, seeds) =
      sourcePowerEstimate (fun r seed => applyInverse.run H (r, seed)) q g seeds := by
  simp only [powerPolicy, Policy.mapOutput_run, iteratePolicy_run,
    sourcePowerEstimate, sourcePower]

variable [FiniteDimensional ℝ E]

def estimatorPolicy (base : Policy E E E K (E × Seed)) (R : ℕ) :
    let d := Module.finrank ℝ E
    let q := inversePowerLengthFor sourceStartComponent d
    let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
    Policy E E ℝ (q * (J * ((R + 1) * (K + 1) + 1)))
      ((Fin d → ℝ) × SeedBlock (SeedBlock (Fin (R + 1) → Seed) J) q) :=
  let d := Module.finrank ℝ E
  let q := inversePowerLengthFor sourceStartComponent d
  let J := refinementLength (inversePowerAccuracyFor sourceStartComponent d)
  (powerPolicy (refinedPolicy (verifiedPolicy base R) J) q).seedMap
    (fun p => (gaussianUnitStart E p.1, p.2))
    ((measurable_gaussianUnitStart.comp measurable_fst).prodMk measurable_snd)

theorem estimatorPolicy_run (base : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (R : ℕ) (seed) :
    (estimatorPolicy base R).run H seed =
      sourceEstimator H (fun r s => base.run H (r, s)) R seed := by
  let J := refinementLength (inversePowerAccuracyFor sourceStartComponent (Module.finrank ℝ E))
  have hverified : (fun r s => (verifiedPolicy base R).run H (r, s)) =
      verifiedSource H (fun r s => base.run H (r, s)) R := by
    funext r s
    exact verifiedPolicy_run base H R r s
  have hrefined : (fun r s => (refinedPolicy (verifiedPolicy base R) J).run H (r, s)) =
      refinedVerifiedSource H (fun r s => base.run H (r, s)) R J := by
    funext r s
    rw [refinedPolicy_run, hverified]
    rfl
  simp only [estimatorPolicy, Policy.seedMap_run, powerPolicy_run, sourceEstimator]
  rw [hrefined]

def maximumPolicy (estimate : Policy E E ℝ K Seed) (S : ℕ) :
    Policy E E ℝ ((S + 1) * K) (Fin (S + 1) → Seed) :=
  (Policy.collect (0 : E) estimate (S + 1)).mapOutput
    (fun _ out => bestCandidate (fun x : ℝ => -x) S out)
    ((measurable_bestCandidate (fun x : ℝ => -x) measurable_neg S).comp measurable_snd)

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
theorem maximumPolicy_run (estimate : Policy E E ℝ K Seed)
    (oracle : E → E) (S : ℕ) (seeds : Fin (S + 1) → Seed) :
    (maximumPolicy estimate S).run oracle seeds = repeatedMaximum (estimate.run oracle) S seeds := by
  rw [maximumPolicy, Policy.mapOutput_run, Policy.collect_run]
  rfl

end
end Matvec.SourceIterationPolicy
