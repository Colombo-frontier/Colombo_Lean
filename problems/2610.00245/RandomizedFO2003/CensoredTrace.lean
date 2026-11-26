import RandomizedFO2003.CensoredOracleProgram
import RandomizedFO2003.ExtendedOracleTrace

namespace RandomizedFO2003.Cascade

open MeasureTheory Rotations Primitives

variable {N n : ℕ} {E Seed : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Seed]

def Data.readoutFlat (d : Data N E) (i : Fin (N + 1)) (z : BlockProduct (N + 1) E) : Prop :=
  |radialReadout (d.a i) d.B d.α (z i)| ≤ 1 / 4

noncomputable def Data.trueRunPoint (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (A : Model.Algorithm n Seed)
    (seed : Seed) (T : ℕ) (j : Fin (T + 1)) : BlockProduct (N + 1) E :=
  V.symm (A.evaluationPoint (d.coordinateFunction V) seed T j)

noncomputable def Data.censoredRunPoint (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ) : Fin (T + 1) → BlockProduct (N + 1) E :=
  (d.censorGate i).trueRunPoint V A seed T

noncomputable def Data.censoredAuthorization (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ) (j : Fin (T + 1)) : Bool :=
  if j.val < T then d.oracleAuthorized i (d.censoredRunPoint V i A seed T j) else false

/-- A pathwise barrier for every short prefix of one fixed censored run,
including its unrestricted output as the final, unauthorized query. -/
def Data.censoredPrefixBarrier (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T m : ℕ) : Prop :=
  ∀ j : Fin (T + 1), markedQueryDepth (T + 1) (d.censoredAuthorization V i A seed T) 0 j ≤ m →
    d.readoutFlat i (d.censoredRunPoint V i A seed T j)

/-- Earlier flat true queries suffice to identify the current censored
point. The current point may itself be the first exit or the output. -/
theorem Data.censoredRunPoint_eq_true (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ) (j : Fin (T + 1))
    (hflat : ∀ k : Fin (T + 1), k.val < j.val → d.readoutFlat i (d.trueRunPoint V A seed T k)) :
    d.censoredRunPoint V i A seed T j = d.trueRunPoint V A seed T j := by
  have hlocal : ∀ s < j.val, |radialReadout (d.a i) d.B d.α
      (V.symm (A.query s seed (Model.transcript A (d.coordinateFunction V) seed s)) i)| ≤ 1 / 4 := by
    intro s hs
    have hT := j.isLt
    let k : Fin T := ⟨s, by omega⟩
    have hk := hflat k.castSucc hs
    simpa only [readoutFlat, trueRunPoint, Model.Algorithm.evaluationPoint_castSucc] using hk
  have hh := d.transcript_eq_before_true_exit V i A seed j.val hlocal j.val le_rfl
  exact congrArg V.symm
    (A.evaluationPoint_eq_of_transcript (d.coordinateFunction V) ((d.censorGate i).coordinateFunction V) seed T j hh).symm

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The concrete compiled traces match the censored model's block queries
and its preceding-gate authorization rule at every round, including output. -/
theorem Data.censoredProgram_traces (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (h : ℝ) (M U : E →L[ℝ] E) (u : E) (hA : IsSelfAdjoint (d.A i))
    (hforce : h • U u = d.b i) (hmatrix : ∀ y, U (M (U.adjoint y)) = d.A i y)
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ) (j : Fin (T + 1)) :
    let codec := cascadeCodec V i h d.B d.α d.D d.C₀ d.K
    let coordinate := oracleCoordinate V i
    let plan := A.markedOracleProgram codec coordinate coordinate.continuous.measurable T
    let full := plan.withTerminal T (coordinate ∘ A.markedOracleOutput codec T)
      (coordinate.continuous.measurable.comp (A.measurable_markedOracleOutput codec T))
    let q := (full.compile M (T + 1) Prod.fst measurable_fst).run (markedActionCount (T + 1)) U
      (u, (d.publicData i).coefficients, seed)
    markedQueryTrace E (T + 1) q j = U.adjoint (d.censoredRunPoint V i A seed T j i) ∧
      full.authorizationTrace (T + 1) q j = d.censoredAuthorization V i A seed T j := by
  dsimp only
  have ht := A.markedOracle_extended_traces
    (cascadeCodec V i h d.B d.α d.D d.C₀ d.K) (oracleCoordinate V i) (oracleCoordinate V i).continuous.measurable T
    M U u (d.publicData i).coefficients seed ((d.censorGate i).coordinateFunction V)
    (fun x => d.cascadeCodec_correct V i h M U u hA hforce hmatrix x) j
  refine ⟨ht.1, ht.2.trans ?_⟩
  unfold Model.Algorithm.extendedAuthorization censoredAuthorization
  split_ifs
  · exact d.oracleAuthorized_publicData i _
  · rfl

end RandomizedFO2003.Cascade
