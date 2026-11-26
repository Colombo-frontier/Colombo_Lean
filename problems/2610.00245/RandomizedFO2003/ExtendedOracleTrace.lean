import RandomizedFO2003.TerminalPrefix
import RandomizedFO2003.ModelOracleTrace

namespace RandomizedFO2003.Model

open MeasureTheory Rotations

variable {d : ℕ} {Seed : Type} [MeasurableSpace Seed]

/-- All submitted queries followed by the unrestricted terminal output. -/
noncomputable def Algorithm.evaluationPoint (A : Algorithm d Seed) (f : Space d → ℝ)
    (seed : Seed) (T : ℕ) : Fin (T + 1) → Space d :=
  Fin.lastCases (A.output T seed (transcript A f seed T))
    (fun j : Fin T => A.query j.val seed (transcript A f seed j.val))

@[simp] theorem Algorithm.evaluationPoint_last (A : Algorithm d Seed) (f : Space d → ℝ)
    (seed : Seed) (T : ℕ) : A.evaluationPoint f seed T (Fin.last T) = A.output T seed (transcript A f seed T) := by
  simp [evaluationPoint]

@[simp] theorem Algorithm.evaluationPoint_castSucc (A : Algorithm d Seed) (f : Space d → ℝ)
    (seed : Seed) (T : ℕ) (i : Fin T) :
    A.evaluationPoint f seed T i.castSucc = A.query i.val seed (transcript A f seed i.val) := by
  simp [evaluationPoint]

theorem Algorithm.evaluationPoint_eq_of_transcript (A : Algorithm d Seed) (f g : Space d → ℝ)
    (seed : Seed) (T : ℕ) (i : Fin (T + 1))
    (hh : transcript A f seed i.val = transcript A g seed i.val) :
    A.evaluationPoint f seed T i = A.evaluationPoint g seed T i := by
  revert hh
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hh
    change transcript A f seed T = transcript A g seed T at hh
    simp only [evaluationPoint_last]
    rw [hh]
  · intro hh
    change transcript A f seed j.val = transcript A g seed j.val at hh
    simp only [evaluationPoint_castSucc]
    rw [hh]

variable {E P : Type} [MeasurableSpace E] [MeasurableSpace P]

noncomputable def Algorithm.extendedAuthorization (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (p : P) (f : Space d → ℝ) (seed : Seed) (T : ℕ) (i : Fin (T + 1)) : Bool :=
  if i.val < T then codec.authorized (p, A.evaluationPoint f seed T i) else false

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

/-- Both traces include the last output round. All previous authorization
decisions are preserved and the output round authorizes no new mark. -/
theorem Algorithm.markedOracle_extended_traces (A : Algorithm d Seed) (codec : OracleCodec d E P)
    (coordinate : Space d → E) (hc : Measurable coordinate) (T : ℕ)
    (M U : E →L[ℝ] E) (u : E) (p : P) (seed : Seed) (f : Space d → ℝ)
    (hcodec : ∀ x, codec.response ((p, x),
      (if codec.authorized (p, x) = true then U u else 0, U (M (U.adjoint (coordinate x))))) = oracle f x)
    (i : Fin (T + 1)) :
    let plan := A.markedOracleProgram codec coordinate hc T
    let full := plan.withTerminal T (coordinate ∘ A.markedOracleOutput codec T)
      (hc.comp (A.measurable_markedOracleOutput codec T))
    let q := (full.compile M (T + 1) Prod.fst measurable_fst).run (markedActionCount (T + 1)) U (u, p, seed)
    markedQueryTrace E (T + 1) q i = U.adjoint (coordinate (A.evaluationPoint f seed T i)) ∧
      full.authorizationTrace (T + 1) q i = A.extendedAuthorization codec p f seed T i := by
  dsimp only
  refine Fin.lastCases ?_ (fun j => ?_) i
  · constructor
    · rw [A.markedOracle_terminal_query codec coordinate hc T M U u p seed f hcodec, evaluationPoint_last]
    · rw [MarkedProgram.withTerminal_last_unauthorized]
      simp [extendedAuthorization]
  · have hpref := (A.markedOracleProgram codec coordinate hc T).withTerminal_prefix_traces T M
      Prod.fst measurable_fst (coordinate ∘ A.markedOracleOutput codec T)
      (hc.comp (A.measurable_markedOracleOutput codec T)) U (u, p, seed) j
    have ht := A.markedOracle_traces codec coordinate hc T M U u p seed f hcodec j
    constructor
    · simpa only [evaluationPoint_castSucc] using hpref.1.trans ht.1
    · simpa only [extendedAuthorization, Fin.coe_castSucc, j.isLt, if_true, evaluationPoint_castSucc]
        using hpref.2.trans ht.2

end RandomizedFO2003.Model
