import RandomizedFO2003.EpochTerminal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace RandomizedFO2003.Accelerated

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An epoch reconstructed solely from the gradient components of responses. -/
def replyEpochState (η θ : ℝ) (start : E) (g : ℕ → E) : ℕ → E × E
  | 0 => (start, start)
  | n + 1 => let s := replyEpochState η θ start g n
             (s.2, extrapolate θ s.1 s.2 - η • g n)

def replyPoint (η θ : ℝ) (start : E) (g : ℕ → E) (n : ℕ) : E :=
  (replyEpochState η θ start g n).2

def replyQuery (η θ : ℝ) (start : E) (g : ℕ → E) (n : ℕ) : E :=
  let s := replyEpochState η θ start g n
  extrapolate θ s.1 s.2

def replyIncrement (η θ : ℝ) (start : E) (g : ℕ → E) (n : ℕ) : E :=
  replyPoint η θ start g (n + 1) - replyPoint η θ start g n

def replyEnergy (η θ : ℝ) (start : E) (g : ℕ → E) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ‖replyIncrement η θ start g k‖ ^ 2

theorem replyEpochState_congr (η θ : ℝ) (start : E) (g g' : ℕ → E) (n : ℕ)
    (hg : ∀ k < n, g k = g' k) :
    replyEpochState η θ start g n = replyEpochState η θ start g' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replyEpochState, ih (fun k hk => hg k (by omega)), hg n (by omega)]

theorem replyQuery_congr (η θ : ℝ) (start : E) (g g' : ℕ → E) (n : ℕ)
    (hg : ∀ k < n, g k = g' k) : replyQuery η θ start g n = replyQuery η θ start g' n := by
  unfold replyQuery
  rw [replyEpochState_congr η θ start g g' n hg]

section Actual

variable [CompleteSpace E]

/-- Agreement requires only the replies already read, not an infinite
oracle stream or any regularity assumption on the objective. -/
theorem replyEpochState_eq_epochState (f : E → ℝ) (η θ : ℝ) (start : E) (g : ℕ → E)
    (n : ℕ) (hg : ∀ k < n, g k = gradient f (epochQuery f η θ start k)) :
    replyEpochState η θ start g n = epochState f η θ start n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replyEpochState, ih (fun k hk => hg k (by omega)), hg n (by omega)]
    rfl

theorem replyPoint_eq_epochPoint (f : E → ℝ) (η θ : ℝ) (start : E) (g : ℕ → E)
    (n : ℕ) (hg : ∀ k < n, g k = gradient f (epochQuery f η θ start k)) :
    replyPoint η θ start g n = epochPoint f η θ start n :=
  congrArg Prod.snd (replyEpochState_eq_epochState f η θ start g n hg)

theorem replyQuery_eq_epochQuery (f : E → ℝ) (η θ : ℝ) (start : E) (g : ℕ → E)
    (n : ℕ) (hg : ∀ k < n, g k = gradient f (epochQuery f η θ start k)) :
    replyQuery η θ start g n = epochQuery f η θ start n := by
  unfold replyQuery epochQuery
  rw [replyEpochState_eq_epochState f η θ start g n hg]

theorem replyIncrement_eq_epochIncrement (f : E → ℝ) (η θ : ℝ) (start : E) (g : ℕ → E)
    (n : ℕ) (hg : ∀ k < n + 1, g k = gradient f (epochQuery f η θ start k)) :
    replyIncrement η θ start g n = epochIncrement f η θ start n := by
  unfold replyIncrement epochIncrement
  rw [replyPoint_eq_epochPoint f η θ start g (n + 1) hg,
    replyPoint_eq_epochPoint f η θ start g n (fun k hk => hg k (by omega))]

theorem replyEnergy_eq_epochEnergy (f : E → ℝ) (η θ : ℝ) (start : E) (g : ℕ → E)
    (n : ℕ) (hg : ∀ k < n, g k = gradient f (epochQuery f η θ start k)) :
    replyEnergy η θ start g n = epochEnergy f η θ start n := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [replyIncrement_eq_epochIncrement f η θ start g k (fun i hi => hg i (by
    have := Finset.mem_range.mp hk
    omega))]

end Actual

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_replyEpochState (η θ : ℝ) (n : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyEpochState η θ z.1 z.2 n) := by
  induction n with
  | zero => exact measurable_fst.prodMk measurable_fst
  | succ n ih =>
    have hg : Measurable (fun z : E × (ℕ → E) => z.2 n) :=
      (measurable_pi_apply n).comp measurable_snd
    exact ih.snd.prodMk ((ih.snd.add (measurable_const.smul (ih.snd.sub ih.fst))).sub
      (measurable_const.smul hg))

theorem measurable_replyPoint (η θ : ℝ) (n : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyPoint η θ z.1 z.2 n) :=
  (measurable_replyEpochState η θ n).snd

theorem measurable_replyQuery (η θ : ℝ) (n : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyQuery η θ z.1 z.2 n) := by
  have hs := measurable_replyEpochState (E := E) η θ n
  exact hs.snd.add (measurable_const.smul (hs.snd.sub hs.fst))

theorem measurable_replyIncrement (η θ : ℝ) (n : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyIncrement η θ z.1 z.2 n) :=
  (measurable_replyPoint η θ (n + 1)).sub (measurable_replyPoint η θ n)

theorem measurable_replyEnergy (η θ : ℝ) (n : ℕ) :
    Measurable (fun z : E × (ℕ → E) => replyEnergy η θ z.1 z.2 n) := by
  exact Finset.measurable_sum _ (fun k _ => (measurable_replyIncrement η θ k).norm.pow_const 2)

end

end RandomizedFO2003.Accelerated
