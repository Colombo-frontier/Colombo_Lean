import LowRank.OracleGaussianCompile

/-! Fixed-horizon measurable policies with arbitrary ambient query vectors.
The history contains only the seed and actual oracle replies. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def AmbientOraclePolicy (d : ℕ) : ℕ → (S : Type u) → [MeasurableSpace S] → Type u
  | 0, _, _ => PUnit
  | n + 1, S, _ => MeasurableStateMap S (Fin d → ℝ) ×
      AmbientOraclePolicy d n (S × (Fin d → ℝ))

def runAmbientOracle (d : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    AmbientOraclePolicy d n S → Matrix (Fin d) (Fin d) ℝ → S → OracleHistory d n S
  | 0, _, _, _, _, x => x
  | n + 1, _, _, policy, W, x => runAmbientOracle d n policy.2 W (x, W *ᵥ policy.1.1 x)

theorem measurable_runAmbientOracle (d n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy d n S) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × S => runAmbientOracle d n policy p.1 p.2) := by
  induction n generalizing S with
  | zero => exact measurable_snd
  | succ n ih =>
    have hq : Measurable policy.1.1 := policy.1.2
    have hr : Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × S => p.1 *ᵥ policy.1.1 p.2) := by
      apply measurable_pi_lambda
      intro i
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    exact (ih policy.2).comp (measurable_fst.prodMk (measurable_snd.prodMk hr))

end
end LowRank
