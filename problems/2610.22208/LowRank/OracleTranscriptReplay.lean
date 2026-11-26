import LowRank.VisibleOraclePolicy

/-! The visible factors can be replayed measurably from just the seed and
stored oracle replies. The replay map does not receive the input matrix. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

def replayVisibleFactors (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    VisibleOraclePolicy d r n q S → (S → VisibleFactorData d q (r + n)) →
    OracleHistory d n S → VisibleFactorData d (factorCount n q) r
  | 0, _, _, _, _, vis => vis
  | n + 1, q, _, _, policy, vis => replayVisibleFactors d r n (q + 1) policy.2
      (fun p => recoverVisibleFactorData (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)
        (policy.1.1 (p.1, vis p.1)) (vis p.1) p.2)

theorem measurable_replayVisibleFactors (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (vis : S → VisibleFactorData d q (r + n))
    (hvis : Measurable vis) : Measurable (replayVisibleFactors d r n q policy vis) := by
  induction n generalizing q S with
  | zero => exact hvis
  | succ n ih =>
    apply ih (q + 1) policy.2
    apply measurable_recoverVisibleFactorData
    · exact policy.1.2.comp (measurable_fst.prodMk (hvis.comp measurable_fst))
    · exact hvis.comp measurable_fst
    · exact measurable_snd

theorem runVisibleOracle_replay (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (vis : S → VisibleFactorData d q (r + n))
    (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    (runVisibleOracle d r n q policy W (x, vis x)).2 =
      replayVisibleFactors d r n q policy vis (runVisibleOracle d r n q policy W (x, vis x)).1 := by
  induction n generalizing q S with
  | zero => rfl
  | succ n ih =>
    let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
    let vis' := fun p : S × (Fin d → ℝ) =>
      recoverVisibleFactorData b (policy.1.1 (p.1, vis p.1)) (vis p.1) p.2
    exact ih (q + 1) policy.2 vis' (x, W *ᵥ ambientQuery (vis x) (policy.1.1 (x, vis x)))

end
end LowRank
