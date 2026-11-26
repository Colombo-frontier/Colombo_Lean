import RandomizedFO2003.CensoredTrace
import RandomizedFO2003.RadialEquivariance
import RandomizedFO2003.SampledCascade

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Primitives
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))
  {Seed : Type} [MeasurableSpace Seed]

/-- This whole program is fixed before any sphere direction or rotation is
drawn. Its public-parameter input has the current block removed. -/
noncomputable def censoredGenieProgram (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    MarkedProgram (BlockSpace K) (T + 1) (BlockSpace K × (Coefficients N (BlockSpace K) × Seed)) :=
  let V := cascadeCoordinates K N
  let codec := cascadeCodec V i h (radiusCoefficient * h / γ) (h / (64 * γ))
    (h ^ 2 / γ) forcingOffset saturationThreshold
  let coordinate := oracleCoordinate V i
  let plan := A.markedOracleProgram codec coordinate coordinate.continuous.measurable T
  plan.withTerminal T (coordinate ∘ A.markedOracleOutput codec T)
    (coordinate.continuous.measurable.comp (A.measurable_markedOracleOutput codec T))

noncomputable def censoredGenieHistory (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    (u : Fin (N + 1) → BlockSpace K) (U : Fin (N + 1) → Rotation (BlockSpace K)) (seed : Seed) :
    ActionHistory (BlockSpace K) (markedActionCount (T + 1)) (BlockSpace K × (Coefficients N (BlockSpace K) × Seed)) :=
  let d := S.cascade K N (fun j => isometry _ (U j)) u h
  ((S.censoredGenieProgram K N h A T i).compile (continuousDiagonal K S.node) (T + 1) Prod.fst measurable_fst).run
    (markedActionCount (T + 1)) (U i : BlockSpace K →L[ℝ] BlockSpace K) (u i, (d.publicData i).coefficients, seed)

/-- Self-adjointness and the marked/matrix answer identities are fully
discharged for the actual rotated spectral construction. -/
theorem censoredGenie_traces (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    (u : Fin (N + 1) → BlockSpace K) (U : Fin (N + 1) → Rotation (BlockSpace K)) (seed : Seed)
    (j : Fin (T + 1)) :
    let d := S.cascade K N (fun k => isometry _ (U k)) u h
    let p := S.censoredGenieHistory K N h A T i u U seed
    markedQueryTrace (BlockSpace K) (T + 1) p j =
      (U i : BlockSpace K →L[ℝ] BlockSpace K).adjoint (d.censoredRunPoint (cascadeCoordinates K N) i A seed T j i) ∧
      (S.censoredGenieProgram K N h A T i).authorizationTrace (T + 1) p j =
        d.censoredAuthorization (cascadeCoordinates K N) i A seed T j := by
  dsimp only
  apply (S.cascade K N (fun k => isometry _ (U k)) u h).censoredProgram_traces
    (cascadeCoordinates K N) i h (continuousDiagonal K S.node) (U i : BlockSpace K →L[ℝ] BlockSpace K) (u i)
    (S.cascade_operator_selfAdjoint K N _ u h i) _ _ A seed T j
  · exact ((U i : BlockSpace K →L[ℝ] BlockSpace K).map_smul h (u i)).symm
  · intro y
    rfl

/-- The previously proved Haar-history event supplies the concrete
censored barrier used by the actual multi-block delay induction. -/
theorem censoredPrefixBarrier_of_genie (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    (u : Fin (N + 1) → BlockSpace K) (U : Fin (N + 1) → Rotation (BlockSpace K)) (seed : Seed)
    (hp : S.censoredGenieHistory K N h A T i u U seed ∈
      (S.censoredGenieProgram K N h A T i).prefixFlatEvent K S.residual m (T + 1) Prod.fst
        (radiusCoefficient * h / γ) (h / (64 * γ))) :
    (S.cascade K N (fun k => isometry _ (U k)) u h).censoredPrefixBarrier (cascadeCoordinates K N) i A seed T m := by
  let d := S.cascade K N (fun k => isometry _ (U k)) u h
  let p := S.censoredGenieHistory K N h A T i u U seed
  have ht := S.censoredGenie_traces K N h A T i u U seed
  have ha : (S.censoredGenieProgram K N h A T i).authorizationTrace (T + 1) p =
      d.censoredAuthorization (cascadeCoordinates K N) i A seed T := funext (fun j => (ht j).2)
  have hs : ActionHistory.seed (BlockSpace K) (markedActionCount (T + 1)) p =
      (u i, (d.publicData i).coefficients, seed) := ActionProgram.run_seed _ _ _ _
  intro j hj
  have hr := hp j (by rw [ha]; exact hj)
  rw [hs, (ht j).1] at hr
  change |radialReadout (isometry _ (U i) (direction K (u i) S.residual))
      (radiusCoefficient * h / γ) (h / (64 * γ)) (d.censoredRunPoint (cascadeCoordinates K N) i A seed T j i)| ≤ 1 / 4
  rw [radialReadout_rotation]
  exact hr

end RandomizedFO2003.FiniteSpectralDesign
