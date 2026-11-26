import Matvec.PolicyComposition
import Matvec.SourceIteration

/-!
# Actual source-query policies for verification and adaptive refinement

Every use of the unknown operator occurs through a source oracle query.
Verification costs one extra query per candidate; updating a refinement
residual costs one extra query per correction. The budgets hold on all
transcripts, and the output functions equal the probabilistic constructions
in `SourceIteration` for each seed, not merely almost everywhere.
-/

namespace Matvec.SourceIterationPolicy
open MeasureTheory MeasurableSimulation

noncomputable section

section Iteration
variable {Q R State Seed : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace State] [MeasurableSpace Seed] {K : ℕ}

def iteratePolicy (q₀ : Q) (step : ℕ → Policy Q R State K (State × Seed)) :
    (n : ℕ) → Policy Q R State (n * K) (State × SeedBlock Seed n)
  | 0 => (Policy.pure q₀ Prod.fst measurable_fst).castHorizon (by omega)
  | n + 1 =>
      (((iteratePolicy q₀ step n).seedMap
        (fun p : State × SeedBlock Seed (n + 1) => (p.1, p.2.1)) (by fun_prop)).bind
          ((step n).seedMap
            (fun p : (State × SeedBlock Seed (n + 1)) × State => (p.2, p.1.2.2))
            (by fun_prop))).castHorizon (by rw [Nat.add_mul, Nat.one_mul])

theorem iteratePolicy_run (q₀ : Q) (step : ℕ → Policy Q R State K (State × Seed))
    (oracle : Q → R) (n : ℕ) (initial : State) (seeds : SeedBlock Seed n) :
    (iteratePolicy q₀ step n).run oracle (initial, seeds) =
      adaptiveRun (fun n state seed => (step n).run oracle (state, seed)) initial n seeds := by
  induction n with
  | zero => simp only [iteratePolicy, Policy.castHorizon_run, Policy.pure_run, adaptiveRun]
  | succ n ih =>
    simp only [iteratePolicy, Policy.castHorizon_run, Policy.bind_run, Policy.seedMap_run,
      ih, adaptiveRun]

end Iteration

section Source
variable {E Seed : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Seed] {K : ℕ}

/-- The returned score is evaluated by one actual source call. -/
def scoreCandidate (base : Policy E E E K (E × Seed)) :
    Policy E E (E × ℝ) (K + 1) (E × Seed) :=
  base.bind (Policy.ask
    (fun p : (E × Seed) × E => p.2) (by fun_prop)
    (fun p reply => (p.2, ‖reply - p.1.1‖)) (by fun_prop))

theorem scoreCandidate_run (base : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (r : E) (seed : Seed) :
    (scoreCandidate base).run H (r, seed) =
      (base.run H (r, seed), ‖H (base.run H (r, seed)) - r‖) := by
  simp only [scoreCandidate, Policy.bind_run, Policy.ask_run]

def chooseScored (a b : E × ℝ) : E × ℝ := if a.2 ≤ b.2 then a else b

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem measurable_chooseScored : Measurable (fun p : (E × ℝ) × (E × ℝ) =>
    chooseScored p.1 p.2) := by
  exact measurable_fst.piecewise
    (measurableSet_le (measurable_snd.comp measurable_fst)
      (measurable_snd.comp measurable_snd)) measurable_snd

def verifiedWithScore (base : Policy E E E K (E × Seed)) :
    (R : ℕ) → Policy E E (E × ℝ) ((R + 1) * (K + 1)) (E × (Fin (R + 1) → Seed))
  | 0 => ((scoreCandidate base).seedMap
      (fun p : E × (Fin 1 → Seed) => (p.1, p.2 0)) (by fun_prop)).castHorizon (by omega)
  | R + 1 =>
      (((scoreCandidate base).seedMap
        (fun p : E × (Fin (R + 2) → Seed) => (p.1, p.2 0)) (by fun_prop)).bind
          (((verifiedWithScore base R).seedMap
            (fun p : (E × (Fin (R + 2) → Seed)) × (E × ℝ) =>
              (p.1.1, fun i => p.1.2 i.succ)) (by fun_prop)).mapOutput
                (fun p out => chooseScored p.2 out)
                (measurable_chooseScored.comp
                  ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))).castHorizon
        (by ring)

theorem verifiedWithScore_run (base : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (R : ℕ) (r : E) (seeds : Fin (R + 1) → Seed) :
    (verifiedWithScore base R).run H (r, seeds) =
      (verifiedSource H (fun r seed => base.run H (r, seed)) R r seeds,
        ‖H (verifiedSource H (fun r seed => base.run H (r, seed)) R r seeds) - r‖) := by
  induction R with
  | zero =>
    simp only [verifiedWithScore, Policy.castHorizon_run, Policy.seedMap_run,
      scoreCandidate_run, verifiedSource, verifiedRepeat, bestCandidate]
  | succ R ih =>
    simp only [verifiedWithScore, Policy.castHorizon_run, Policy.bind_run,
      Policy.seedMap_run, Policy.mapOutput_run, scoreCandidate_run, ih]
    unfold chooseScored verifiedSource verifiedRepeat
    simp only [bestCandidate]
    split <;> rfl

def verifiedPolicy (base : Policy E E E K (E × Seed)) (R : ℕ) :
    Policy E E E ((R + 1) * (K + 1)) (E × (Fin (R + 1) → Seed)) :=
  (verifiedWithScore base R).mapOutput (fun _ out => out.1) (by fun_prop)

theorem verifiedPolicy_run (base : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (R : ℕ) (r : E) (seeds : Fin (R + 1) → Seed) :
    (verifiedPolicy base R).run H (r, seeds) =
      verifiedSource H (fun r seed => base.run H (r, seed)) R r seeds := by
  rw [verifiedPolicy, Policy.mapOutput_run, verifiedWithScore_run]

/-- A correction and its residual update, using `K + 1` actual calls. -/
def correctionPolicy (solve : Policy E E E K (E × Seed)) :
    Policy E E (E × E) (K + 1) ((E × E) × Seed) :=
  (solve.seedMap (fun p : (E × E) × Seed => (p.1.2, p.2)) (by fun_prop)).bind
    (Policy.ask (fun p : ((E × E) × Seed) × E => p.2) (by fun_prop)
      (fun p reply => (p.1.1.1 + p.2, p.1.1.2 - reply)) (by fun_prop))

theorem correctionPolicy_run (solve : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (state : E × E) (seed : Seed) (n : ℕ) :
    (correctionPolicy solve).run H (state, seed) =
      refinementStep H (fun r seed => solve.run H (r, seed)) n state seed := by
  simp only [correctionPolicy, Policy.bind_run, Policy.seedMap_run, Policy.ask_run,
    refinementStep]

def refinedPolicy (solve : Policy E E E K (E × Seed)) (J : ℕ) :
    Policy E E E (J * (K + 1)) (E × SeedBlock Seed J) :=
  ((iteratePolicy (0 : E) (fun _ => correctionPolicy solve) J).seedMap
    (fun p : E × SeedBlock Seed J => ((0, p.1), p.2)) (by fun_prop)).mapOutput
      (fun _ out => out.1) (by fun_prop)

theorem refinedPolicy_run (solve : Policy E E E K (E × Seed))
    (H : E →L[ℝ] E) (J : ℕ) (b : E) (seeds : SeedBlock Seed J) :
    (refinedPolicy solve J).run H (b, seeds) =
      refinedSource H (fun r seed => solve.run H (r, seed)) J b seeds := by
  simp only [refinedPolicy, Policy.mapOutput_run, Policy.seedMap_run, iteratePolicy_run]
  have hstep : (fun n state seed => (correctionPolicy solve).run H (state, seed)) =
      refinementStep H (fun r seed => solve.run H (r, seed)) := by
    funext n state seed
    exact correctionPolicy_run solve H state seed n
  rw [hstep]
  rfl

theorem verified_refinement_budget (K R J : ℕ) :
    J * ((R + 1) * (K + 1) + 1) ≤ J * ((R + 2) * (K + 1)) := by
  apply Nat.mul_le_mul_left
  nlinarith

end Source
end
end Matvec.SourceIterationPolicy
