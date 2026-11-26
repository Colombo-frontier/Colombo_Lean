import FullJet.RandomizedChain

open scoped ContDiff

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def rescaleJetPacket {p : ℕ} (α β : ℝ) (J : JetPacket p E) : JetPacket p E :=
  fun r => α • (J r).compContinuousLinearMap (fun _ => β • ContinuousLinearMap.id ℝ E)

/-- Exact value-inclusive scaling of the whole finite derivative packet. -/
theorem fullJet_rescale {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (α β : ℝ) (p : ℕ) (x : E) :
    fullJet p (fun y => α * f (β • y)) x = rescaleJetPacket α β (fullJet p f (β • x)) := by
  funext r
  let L : E →L[ℝ] E := β • ContinuousLinearMap.id ℝ E
  have horder : (r.val : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (r.val : ℕ∞) ≤ ⊤ from le_top)
  have hc := (hf.comp L.contDiff).of_le horder
  change iteratedFDeriv ℝ r.val (fun y => α • (f ∘ L) y) x =
    α • (iteratedFDeriv ℝ r.val f (L x)).compContinuousLinearMap (fun _ => L)
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, L.iteratedFDeriv_comp_right hf x horder]

noncomputable def componentJetOracle {n : ℕ} (p : ℕ) (f : Fin n → E → ℝ)
    (z : Fin n × E) : JetPacket p E := fullJet p (f z.1) z.2

noncomputable def componentJetOutput {State : Type*} {n p : ℕ}
    (query : State → Fin n × E) (update : State → JetPacket p E → State)
    (output : State → E) (initial : State) (N : ℕ) (f : Fin n → E → ℝ) : E :=
  output (oracleRun query update (componentJetOracle p f) initial N)

def rescaleQuery {State : Type*} {n : ℕ} (β : ℝ) (query : State → Fin n × E) : State → Fin n × E :=
  fun s => ((query s).1, β • (query s).2)

noncomputable def rescaleUpdate {State : Type*} {p : ℕ}
    (α β : ℝ) (update : State → JetPacket p E → State) : State → JetPacket p E → State :=
  fun s J => update s (rescaleJetPacket α β J)

/-- An algorithm on the scaled objective is simulated exactly on the
original objective, with the same state and the same number of calls. -/
theorem oracleRun_rescale {State : Type*} {n p : ℕ}
    (query : State → Fin n × E) (update : State → JetPacket p E → State)
    (initial : State) (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (α β : ℝ) (N : ℕ) :
    oracleRun query update (componentJetOracle p (fun i y => α * f i (β • y))) initial N =
      oracleRun (rescaleQuery β query) (rescaleUpdate α β update) (componentJetOracle p f) initial N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [oracleRun, componentJetOracle, fullJet_rescale (hf _), ih]
    rfl

theorem componentJetOutput_rescale {State : Type*} {n p : ℕ}
    (query : State → Fin n × E) (update : State → JetPacket p E → State)
    (output : State → E) (initial : State) (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (α β : ℝ) (N : ℕ) :
    β • componentJetOutput query update output initial N (fun i y => α * f i (β • y)) =
      componentJetOutput (rescaleQuery β query) (rescaleUpdate α β update)
        (fun s => β • output s) initial N f := by
  unfold componentJetOutput
  rw [oracleRun_rescale query update initial f hf α β N]

end FullJet
