import RandomizedFO2003.CensoredTrace
import RandomizedFO2003.AuthorizationBudget

namespace RandomizedFO2003.Cascade

open Rotations

variable {N n : ℕ} {E Seed : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Seed]

/-- A censored prefix barrier and absence of early true authorization force
all true query/output points before the delayed budget to remain flat.
The proof couples at each prefix, without conditioning on an exit time. -/
theorem Data.flat_before_authorization_budget (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n) (i : Fin (N + 1))
    (A : Model.Algorithm n Seed) (seed : Seed) (T m τ : ℕ)
    (hbarrier : d.censoredPrefixBarrier V i A seed T m)
    (hinactive : ∀ k : Fin (T + 1), k.val < τ → d.oracleAuthorized i (d.trueRunPoint V A seed T k) = false) :
    ∀ j : Fin (T + 1), j.val < τ + m → d.readoutFlat i (d.trueRunPoint V A seed T j) := by
  suffices hall : ∀ s : ℕ, ∀ j : Fin (T + 1), j.val = s → j.val < τ + m →
      d.readoutFlat i (d.trueRunPoint V A seed T j) by
    exact fun j hj => hall j.val j rfl hj
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro j hjs hj
    have hc (k : Fin (T + 1)) (hk : k.val ≤ j.val) :
        d.censoredRunPoint V i A seed T k = d.trueRunPoint V A seed T k := by
      apply d.censoredRunPoint_eq_true V i A seed T k
      intro r hr
      exact ih r.val (by omega) r rfl (by omega)
    have ha : ∀ k : Fin (T + 1), k.val < min τ (j.val + 1) →
        d.censoredAuthorization V i A seed T k = false := by
      intro k hk
      have hkτ := lt_of_lt_of_le hk (min_le_left τ (j.val + 1))
      have hkj := lt_of_lt_of_le hk (min_le_right τ (j.val + 1))
      unfold censoredAuthorization
      split_ifs
      · rw [hc k (by omega)]
        exact hinactive k hkτ
      · rfl
    have hd := markedQueryDepth_le_of_unauthorized_before (T + 1)
      (d.censoredAuthorization V i A seed T) (min τ (j.val + 1)) ha j
    have hb := hbarrier j (show markedQueryDepth (T + 1) (d.censoredAuthorization V i A seed T) 0 j ≤ m by omega)
    rwa [hc j le_rfl] at hb

/-- Every block adds a full m-query delay. This is a statement about the
actual model's queries and arbitrary output, on the intersection of the
separate fixed censored-run barriers. -/
theorem Data.flat_before_stage_budget (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n)
    (A : Model.Algorithm n Seed) (seed : Seed) (T m : ℕ)
    (hbarrier : ∀ i : Fin (N + 1), d.censoredPrefixBarrier V i A seed T m)
    (i : Fin (N + 1)) :
    ∀ j : Fin (T + 1), j.val < (i.val + 1) * m → d.readoutFlat i (d.trueRunPoint V A seed T j) := by
  induction i using Fin.induction with
  | zero =>
    have hh := d.flat_before_authorization_budget V 0 A seed T m 0 (hbarrier 0) (fun k hk => by omega)
    simpa using hh
  | succ i ih =>
    have hi : ∀ k : Fin (T + 1), k.val < i.succ.val * m →
        d.oracleAuthorized i.succ (d.trueRunPoint V A seed T k) = false := by
      intro k hk
      apply Bool.eq_false_iff.mpr
      intro ha
      have he := (d.oracleAuthorized_succ i (d.trueRunPoint V A seed T k)).mp ha
      have hp := ih k (by simpa only [Fin.coe_castSucc, Fin.val_succ] using hk)
      exact (not_lt_of_ge hp) he
    have hh := d.flat_before_authorization_budget V i.succ A seed T m (i.succ.val * m) (hbarrier i.succ) hi
    intro j hj
    apply hh j
    simpa only [Nat.add_mul, Nat.one_mul] using hj

/-- The final block remains flat at the unrestricted output if the full
query budget is below the number of blocks times the per-block delay. -/
theorem Data.terminal_flat_of_censored_barriers (d : Data N E)
    (V : BlockProduct (N + 1) E ≃ₗᵢ[ℝ] Model.Space n)
    (A : Model.Algorithm n Seed) (seed : Seed) (T m : ℕ)
    (hbarrier : ∀ i : Fin (N + 1), d.censoredPrefixBarrier V i A seed T m)
    (hT : T < (N + 1) * m) :
    d.readoutFlat (Fin.last N)
      (V.symm (A.output T seed (Model.transcript A (d.coordinateFunction V) seed T))) := by
  have hh := d.flat_before_stage_budget V A seed T m hbarrier (Fin.last N) (Fin.last T)
    (by simpa using hT)
  simpa only [trueRunPoint, Model.Algorithm.evaluationPoint_last] using hh

end RandomizedFO2003.Cascade
