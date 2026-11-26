import LowRank.RectangularPolicySimulation
import LowRank.PolicyOutputMap
import LowRank.CompletedSchattenTruncation

/-! A rectangular algorithm returning k columns yields a measurable square
algorithm returning a rank-k projector. The reduction preserves every
oracle call and takes successful relative approximation to successful
relative approximation on the unpadded input. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

def reduceRectangularColumnPolicy {a b d k : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S) :
    BoundedTwoSidedPolicy d (Matrix (Fin d) (Fin d) ℝ) n S :=
  (compileRectangularPolicy L R n policy ⟨id, measurable_id⟩).mapOutput d
    ⟨completedTruncatedProjector R, measurable_completedTruncatedProjector R⟩ n

theorem reduceRectangularColumnPolicy_run {a b d k : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (seed : S) :
    runBoundedTwoSided d n (reduceRectangularColumnPolicy L R n policy) A seed =
      completedTruncatedProjector R (runBoundedRectangular a b n policy (L * A * Rᵀ) seed) := by
  rw [reduceRectangularColumnPolicy, runBoundedTwoSided_mapOutput, compileRectangularPolicy_simulates]
  rfl

theorem reduceRectangularColumnPolicy_outputs {a b d k : ℕ} (hk : k ≤ d)
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S) :
    (reduceRectangularColumnPolicy L R n policy).Outputs d
      (fun P => IsOrthogonalProjector P ∧ P.rank = k) n := by
  apply BoundedTwoSidedPolicy.mapOutput_outputs
  intro Z
  obtain ⟨hP, hrank, _⟩ := completedTruncatedProjector_spec hk R Z
  exact ⟨hP, hrank⟩

theorem reduceRectangularColumnPolicy_calls {a b d k : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) (n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (seed : S) :
    ((reduceRectangularColumnPolicy L R n policy).toProgram d n seed).calls (twoSidedOracle A) =
      (policy.toProgram a b n seed).calls (rectangularOracle (L * A * Rᵀ)) := by
  rw [reduceRectangularColumnPolicy, BoundedTwoSidedPolicy.calls_mapOutput,
    compileRectangularPolicy_calls]
  rfl

theorem reduceRectangularColumnPolicy_success {a b d k : ℕ}
    (hk : k ≤ d) {p ε : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin d) ℝ) (hR : Rᵀ * R = 1) (n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S)
    (A : Matrix (Fin d) (Fin d) ℝ) (seed : S)
    (hsuccess : let Z := runBoundedRectangular a b n policy (L * A * Rᵀ) seed
      schattenNorm p (L * A * Rᵀ * (1 - Z * Zᵀ)) ≤
        (1 + ε) * optimalSchattenNorm p (L * A * Rᵀ) k) :
    schattenNorm p (A * (1 - runBoundedTwoSided d n
      (reduceRectangularColumnPolicy L R n policy) A seed)) ≤
      (1 + ε) * optimalSchattenNorm p A k := by
  rw [reduceRectangularColumnPolicy_run]
  exact (completed_relative_schatten_truncation hk hp L hL R hR A _ hsuccess).2.2

theorem reduceRectangularColumnPolicy_probability {a b d k : ℕ}
    (hk : k ≤ d) {p ε : ℝ} (hp : 0 < p)
    (L : Matrix (Fin a) (Fin d) ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix (Fin b) (Fin d) ℝ) (hR : Rᵀ * R = 1) (n : ℕ)
    {S : Type u} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    ν.real {seed | let Z := runBoundedRectangular a b n policy (L * A * Rᵀ) seed
      schattenNorm p (L * A * Rᵀ * (1 - Z * Zᵀ)) ≤
        (1 + ε) * optimalSchattenNorm p (L * A * Rᵀ) k} ≤
    ν.real {seed | schattenNorm p (A * (1 - runBoundedTwoSided d n
      (reduceRectangularColumnPolicy L R n policy) A seed)) ≤
        (1 + ε) * optimalSchattenNorm p A k} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro seed hseed
  exact reduceRectangularColumnPolicy_success hk hp L hL R hR n policy A seed hseed

end
end LowRank
