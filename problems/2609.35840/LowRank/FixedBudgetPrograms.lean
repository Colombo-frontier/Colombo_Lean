import LowRank.GaussianAmbientTranscript
import LowRank.OracleProgram

/-! Both fixed-horizon policy models execute exactly n genuine oracle calls.
The normalized simulation spends the same budget even on redundant queries. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section
universe u

def AmbientOraclePolicy.toProgram (d : ℕ) : (n : ℕ) → {S : Type u} → [MeasurableSpace S] →
    AmbientOraclePolicy d n S → S →
    OracleProgram (Fin d → ℝ) (Fin d → ℝ) (OracleHistory d n S)
  | 0, _, _, _, x => .done x
  | n + 1, _, _, policy, x => .ask (policy.1.1 x)
      (fun reply => AmbientOraclePolicy.toProgram d n policy.2 (x, reply))

theorem AmbientOraclePolicy.eval_toProgram (d n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy d n S) (W : Matrix (Fin d) (Fin d) ℝ) (x : S) :
    (policy.toProgram d n x).eval (fun v => W *ᵥ v) = runAmbientOracle d n policy W x := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => exact ih policy.2 (x, W *ᵥ policy.1.1 x)

theorem AmbientOraclePolicy.calls_toProgram (d n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy d n S) (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (x : S) :
    (policy.toProgram d n x).calls oracle = n := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) (ih policy.2 (x, oracle (policy.1.1 x)))

theorem AmbientOraclePolicy.budget_toProgram (d n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy d n S) (x : S) : (policy.toProgram d n x).HasBudget n := by
  induction n generalizing S with
  | zero => trivial
  | succ n ih => exact fun reply => ih policy.2 (x, reply)

def VisibleOraclePolicy.toProgram (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    VisibleOraclePolicy d r n q S → S × VisibleFactorData d q (r + n) →
    OracleProgram (Fin d → ℝ) (Fin d → ℝ)
      (OracleHistory d n S × VisibleFactorData d (factorCount n q) r)
  | 0, _, _, _, _, p => .done p
  | n + 1, q, _, _, policy, p =>
      let b := EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ
      .ask (ambientQuery p.2 (policy.1.1 p)) (fun reply =>
        VisibleOraclePolicy.toProgram d r n (q + 1) policy.2
          ((p.1, reply), recoverVisibleFactorData b (policy.1.1 p) p.2 reply))

theorem VisibleOraclePolicy.eval_toProgram (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (W : Matrix (Fin d) (Fin d) ℝ)
    (p : S × VisibleFactorData d q (r + n)) :
    (policy.toProgram d r n q p).eval (fun v => W *ᵥ v) = runVisibleOracle d r n q policy W p := by
  induction n generalizing q S with
  | zero => rfl
  | succ n ih => exact ih (q + 1) policy.2 _

theorem VisibleOraclePolicy.calls_toProgram (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (p : S × VisibleFactorData d q (r + n)) :
    (policy.toProgram d r n q p).calls oracle = n := by
  induction n generalizing q S with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) (ih (q + 1) policy.2 _)

theorem VisibleOraclePolicy.budget_toProgram (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) (p : S × VisibleFactorData d q (r + n)) :
    (policy.toProgram d r n q p).HasBudget n := by
  induction n generalizing q S with
  | zero => trivial
  | succ n ih => exact fun _ => ih (q + 1) policy.2 _

theorem ambientOracle_program_budget (r s n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : AmbientOraclePolicy (r + n) n S) (oracle : (Fin (r + n) → ℝ) → (Fin (r + n) → ℝ))
    (x : S) :
    let vp := normalizedAmbientPolicy r s n policy
    let init := (x, visibleFactorData (initialFactorData (r + n) (s + n)))
    (vp.toProgram (r + n) r n 0 init).calls oracle = (policy.toProgram (r + n) n x).calls oracle ∧
      (vp.toProgram (r + n) r n 0 init).HasBudget n := by
  dsimp only
  rw [VisibleOraclePolicy.calls_toProgram, AmbientOraclePolicy.calls_toProgram]
  exact ⟨rfl, VisibleOraclePolicy.budget_toProgram _ _ _ _ _ _⟩

end
end LowRank
