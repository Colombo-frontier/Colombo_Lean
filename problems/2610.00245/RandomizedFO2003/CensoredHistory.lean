import RandomizedFO2003.CascadeCensoring
import RandomizedFO2003.Model

namespace RandomizedFO2003.Model

variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

/-- Exact full-history coupling only assumes agreement at the comparison
run's queries before the stopping index. -/
theorem transcript_eq_of_local_oracle (A : Algorithm n Seed) (f g : Space n → ℝ)
    (seed : Seed) (T : ℕ)
    (hlocal : ∀ t < T, oracle f (A.query t seed (transcript A g seed t)) =
      oracle g (A.query t seed (transcript A g seed t))) :
    ∀ t ≤ T, transcript A f seed t = transcript A g seed t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [transcript]
    rw [ih (by omega), hlocal t (by omega)]

end RandomizedFO2003.Model

namespace RandomizedFO2003.Cascade

open Primitives
open scoped Topology

variable {N n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Coordinates are fixed before the random instance is drawn. -/
noncomputable def Data.coordinateFunction (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) : Model.Space n → ℝ :=
  d.energy ∘ V.symm

theorem Data.coordinateOracle_censor_eq (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    {x : Model.Space n} (hx : |radialReadout (d.a i) d.B d.α (V.symm x i)| ≤ 1 / 4) :
    Model.oracle ((d.censorGate i).coordinateFunction V) x =
      Model.oracle (d.coordinateFunction V) x := by
  have he : (d.censorGate i).coordinateFunction V =ᶠ[𝓝 x] d.coordinateFunction V :=
    (d.censorGate_energy_eventuallyEq i hx).comp_tendsto V.symm.continuous.continuousAt
  exact Prod.ext he.self_of_nhds he.gradient_eq

variable {Seed : Type} [MeasurableSpace Seed]

/-- The comparison is with the actual model's complete first-order
transcript, through arbitrary measurable adaptive queries. -/
theorem Data.transcript_eq_before_censored_exit (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ)
    (hflat : ∀ t < T, |radialReadout (d.a i) d.B d.α
      (V.symm (A.query t seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed t)) i)| ≤ 1 / 4) :
    ∀ t ≤ T, Model.transcript A (d.coordinateFunction V) seed t =
      Model.transcript A ((d.censorGate i).coordinateFunction V) seed t := by
  apply Model.transcript_eq_of_local_oracle
  intro t ht
  exact (d.coordinateOracle_censor_eq V i (hflat t ht)).symm

theorem Data.transcript_eq_before_true_exit (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ)
    (hflat : ∀ t < T, |radialReadout (d.a i) d.B d.α
      (V.symm (A.query t seed (Model.transcript A (d.coordinateFunction V) seed t)) i)| ≤ 1 / 4) :
    ∀ t ≤ T, Model.transcript A (d.coordinateFunction V) seed t =
      Model.transcript A ((d.censorGate i).coordinateFunction V) seed t := by
  have he := Model.transcript_eq_of_local_oracle A ((d.censorGate i).coordinateFunction V)
    (d.coordinateFunction V) seed T (fun t ht => d.coordinateOracle_censor_eq V i (hflat t ht))
  exact fun t ht => (he t ht).symm

/-- At the stopping query itself the two points are identical, even though
their oracle responses at that point may no longer agree. -/
theorem Data.query_eq_at_censored_exit (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ)
    (hflat : ∀ t < T, |radialReadout (d.a i) d.B d.α
      (V.symm (A.query t seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed t)) i)| ≤ 1 / 4) :
    A.query T seed (Model.transcript A (d.coordinateFunction V) seed T) =
      A.query T seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed T) := by
  rw [d.transcript_eq_before_censored_exit V i A seed T hflat T le_rfl]

/-- The unrestricted terminal output also couples whenever every submitted
query remains before exit. No assumption is imposed on the output itself. -/
theorem Data.output_eq_before_censored_exit (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T : ℕ)
    (hflat : ∀ t < T, |radialReadout (d.a i) d.B d.α
      (V.symm (A.query t seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed t)) i)| ≤ 1 / 4) :
    A.output T seed (Model.transcript A (d.coordinateFunction V) seed T) =
      A.output T seed (Model.transcript A ((d.censorGate i).coordinateFunction V) seed T) := by
  rw [d.transcript_eq_before_censored_exit V i A seed T hflat T le_rfl]

end RandomizedFO2003.Cascade
