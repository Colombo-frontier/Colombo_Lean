import RandomizedFO2003.CascadeModelCodec
import RandomizedFO2003.ModelOracleProgram

namespace RandomizedFO2003.Cascade

open MeasureTheory Rotations

variable {N n : ℕ} {E Seed : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Seed]

noncomputable def oracleCoordinate (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n)
    (i : Fin (N + 1)) : Model.Space n →L[ℝ] E :=
  (blockProjection (E := E) (N + 1) i).comp V.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Instantiate the general compiler with the proved public cascade
decoder. The initial state contains none of the chosen block's three
coefficients; it contains its latent mark and the original private seed. -/
theorem Data.censoredProgram_output (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (h : ℝ) (M U : E →L[ℝ] E) (u : E) (hA : IsSelfAdjoint (d.A i))
    (hforce : h • U u = d.b i) (hmatrix : ∀ y, U (M (U.adjoint y)) = d.A i y)
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ) :
    let codec := cascadeCodec V i h d.B d.α d.D d.C₀ d.K
    let coordinate := oracleCoordinate V i
    A.markedOracleOutput codec T
      (((A.markedOracleProgram codec coordinate coordinate.continuous.measurable T).compile M T Prod.fst
        measurable_fst).run (markedActionCount T) U (u, (d.publicData i).coefficients, seed)) =
      A.output T seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed T) := by
  dsimp only
  exact A.markedOracleOutput_run _ _ _ T M U u (d.publicData i).coefficients seed _
    (fun x => d.cascadeCodec_correct V i h M U u hA hforce hmatrix x)

/-- The concrete censored program has the actual function's output whenever
all preceding censored queries stay in the current gate's flat region. -/
theorem Data.censoredProgram_true_output (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (h : ℝ) (M U : E →L[ℝ] E) (u : E) (hA : IsSelfAdjoint (d.A i))
    (hforce : h • U u = d.b i) (hmatrix : ∀ y, U (M (U.adjoint y)) = d.A i y)
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ)
    (hflat : ∀ t < T, |Primitives.radialReadout (d.a i) d.B d.α
      (V.symm (A.query t seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed t)) i)| ≤ 1 / 4) :
    let codec := cascadeCodec V i h d.B d.α d.D d.C₀ d.K
    let coordinate := oracleCoordinate V i
    A.markedOracleOutput codec T
      (((A.markedOracleProgram codec coordinate coordinate.continuous.measurable T).compile M T Prod.fst
        measurable_fst).run (markedActionCount T) U (u, (d.publicData i).coefficients, seed)) =
      A.output T seed (Model.transcript A (d.coordinateFunction V) seed T) :=
  (d.censoredProgram_output V i h M U u hA hforce hmatrix A seed T).trans
    (d.output_eq_before_censored_exit V i A seed T hflat).symm

/-- The extra terminal round measures exactly the selected block of the
original model's censored-run output, with no norm or query restriction. -/
theorem Data.censoredProgram_terminal_query (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (h : ℝ) (M U : E →L[ℝ] E) (u : E) (hA : IsSelfAdjoint (d.A i))
    (hforce : h • U u = d.b i) (hmatrix : ∀ y, U (M (U.adjoint y)) = d.A i y)
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ) :
    let codec := cascadeCodec V i h d.B d.α d.D d.C₀ d.K
    let coordinate := oracleCoordinate V i
    let plan := A.markedOracleProgram codec coordinate coordinate.continuous.measurable T
    let output := coordinate ∘ A.markedOracleOutput codec T
    let ho := coordinate.continuous.measurable.comp (A.measurable_markedOracleOutput codec T)
    markedQueryTrace E (T + 1)
      (((plan.withTerminal T output ho).compile M (T + 1) Prod.fst measurable_fst).run
        (markedActionCount (T + 1)) U (u, (d.publicData i).coefficients, seed)) (Fin.last T) =
      U.adjoint (V.symm (A.output T seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed T)) i) := by
  dsimp only
  exact A.markedOracle_terminal_query _ _ _ T M U u (d.publicData i).coefficients seed _
    (fun x => d.cascadeCodec_correct V i h M U u hA hforce hmatrix x)

end RandomizedFO2003.Cascade
