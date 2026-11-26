import RandomizedFO2003.ResponseEpoch
import RandomizedFO2003.FiniteEpochSelection

namespace RandomizedFO2003.Accelerated

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def replyExitIndex (η θ B : ℝ) (start : E) (g : ℕ → E) (N : ℕ) : ℕ :=
  firstExit (fun n => (n : ℝ) * replyEnergy η θ start g n) (B ^ 2) N

def replyRestartPoint (η θ B : ℝ) (N : ℕ) (start : E) (g : ℕ → E) : E :=
  if B ^ 2 < (N : ℝ) * replyEnergy η θ start g N then
    replyPoint η θ start g (replyExitIndex η θ B start g N)
  else start

def replyOutput (η θ : ℝ) (N : ℕ) (start : E) (g : ℕ → E) : E :=
  prefixAverage (replyQuery η θ start g)
    (halfMinIndex (fun n => ‖replyIncrement η θ start g n‖) N)

section Actual

variable [CompleteSpace E]

def epochOutput (f : E → ℝ) (η θ : ℝ) (N : ℕ) (start : E) : E :=
  prefixAverage (epochQuery f η θ start)
    (halfMinIndex (fun n => ‖epochIncrement f η θ start n‖) N)

theorem replyRestartPoint_eq (f : E → ℝ) (η θ B : ℝ) (N : ℕ) (start : E) (g : ℕ → E)
    (hg : ∀ k < N, g k = gradient f (epochQuery f η θ start k)) :
    replyRestartPoint η θ B N start g = restartPoint f η θ B N start := by
  have he (k : ℕ) (hk : k ≤ N) : replyEnergy η θ start g k = epochEnergy f η θ start k :=
    replyEnergy_eq_epochEnergy f η θ start g k (fun i hi => hg i (by omega))
  have hi : replyExitIndex η θ B start g N = epochExitIndex f η θ B start N := by
    apply firstExit_congr
    intro k hk
    rw [he k hk.le]
  unfold replyRestartPoint restartPoint
  rw [he N le_rfl, hi]
  split_ifs
  · apply replyPoint_eq_epochPoint
    intro k hk
    have hb := firstExit_le (fun n => (n : ℝ) * epochEnergy f η θ start n) (B ^ 2) N
    exact hg k (by change epochExitIndex f η θ B start N ≤ N at hb; omega)
  · rfl

theorem replyOutput_eq (f : E → ℝ) (η θ : ℝ) {N : ℕ} (hN : 0 < N) (start : E) (g : ℕ → E)
    (hg : ∀ k < N, g k = gradient f (epochQuery f η θ start k)) :
    replyOutput η θ N start g = epochOutput f η θ N start := by
  have hi : halfMinIndex (fun n => ‖replyIncrement η θ start g n‖) N =
      halfMinIndex (fun n => ‖epochIncrement f η θ start n‖) N := by
    apply halfMinIndex_congr _ _ hN
    intro k hk
    rw [replyIncrement_eq_epochIncrement f η θ start g k (fun i hi => hg i (by omega))]
  unfold replyOutput epochOutput
  rw [hi]
  unfold prefixAverage
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hq := (halfMinIndex_spec (fun n => ‖epochIncrement f η θ start n‖) hN).2.1
  apply replyQuery_eq_epochQuery
  intro i hi
  have hk' := Finset.mem_range.mp hk
  exact hg i (by omega)

end Actual

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_replyExitIndex (η θ B : ℝ) (N : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyExitIndex η θ B z.1 z.2 N) :=
  measurable_firstExit (fun n => measurable_const.mul (measurable_replyEnergy η θ n)) _ _

theorem measurable_replyRestartPoint (η θ B : ℝ) (N : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyRestartPoint η θ B N z.1 z.2) :=
  Measurable.ite
    (measurableSet_lt measurable_const (measurable_const.mul (measurable_replyEnergy η θ N)))
    (measurable_nat_select (measurable_replyExitIndex η θ B N) (measurable_replyPoint η θ)) measurable_fst

theorem measurable_replyPrefixAverage (η θ : ℝ) (n : ℕ) :
    Measurable (fun z : E × (ℕ → E) => prefixAverage (replyQuery η θ z.1 z.2) n) :=
  measurable_const.smul (Finset.measurable_sum _ (fun k _ => measurable_replyQuery η θ k))

theorem measurable_replyOutput (η θ : ℝ) (N : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyOutput η θ N z.1 z.2) :=
  measurable_nat_select
    (measurable_halfMinIndex (fun n => (measurable_replyIncrement η θ n).norm) N)
    (measurable_replyPrefixAverage η θ)

end

end RandomizedFO2003.Accelerated
