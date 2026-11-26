import Matvec.Amplification
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Fresh independent seeds in adaptive finite iterations

The seed measure below is an actual recursively constructed product measure.
An input to the next randomized call may depend on every previous reply.
The union bound is obtained by integrating the uniform one-step bound over
the previous seeds; no independence of the resulting adaptive inputs is assumed.
-/

namespace Matvec

open MeasureTheory

noncomputable section

universe u

def SeedBlock (Seed : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => SeedBlock Seed n × Seed

instance seedBlockMeasurableSpace (Seed : Type*) [MeasurableSpace Seed] :
    (n : ℕ) → MeasurableSpace (SeedBlock Seed n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 => @Prod.instMeasurableSpace _ _ (seedBlockMeasurableSpace Seed n) _

def seedBlockLaw {Seed : Type*} [MeasurableSpace Seed] (μ : Measure Seed) :
    (n : ℕ) → Measure (SeedBlock Seed n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (seedBlockLaw μ n).prod μ

instance seedBlockLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] :
    (n : ℕ) → IsProbabilityMeasure (seedBlockLaw μ n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | n + 1 => by
      letI := seedBlockLaw_probability μ n
      exact inferInstanceAs (IsProbabilityMeasure ((seedBlockLaw μ n).prod μ))

variable {Seed State : Type*}

def adaptiveRun (step : ℕ → State → Seed → State) (initial : State) :
    (n : ℕ) → SeedBlock Seed n → State
  | 0, _ => initial
  | n + 1, seeds => step n (adaptiveRun step initial n seeds.1) seeds.2

def adaptiveFailure (step : ℕ → State → Seed → State)
    (good : ℕ → State → Seed → Prop) (initial : State) :
    (n : ℕ) → SeedBlock Seed n → Prop
  | 0, _ => False
  | n + 1, seeds => adaptiveFailure step good initial n seeds.1 ∨
      ¬good n (adaptiveRun step initial n seeds.1) seeds.2

theorem measurable_adaptiveRun [MeasurableSpace Seed] [MeasurableSpace State]
    (step : ℕ → State → Seed → State) (initial : State)
    (hstep : ∀ n, Measurable (fun p : State × Seed => step n p.1 p.2)) (n : ℕ) :
    Measurable (adaptiveRun step initial n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hstep n).comp ((ih.comp measurable_fst).prodMk measurable_snd)

theorem measurableSet_adaptiveFailure [MeasurableSpace Seed] [MeasurableSpace State]
    (step : ℕ → State → Seed → State) (good : ℕ → State → Seed → Prop)
    (initial : State)
    (hstep : ∀ n, Measurable (fun p : State × Seed => step n p.1 p.2))
    (hgood : ∀ n, MeasurableSet {p : State × Seed | good n p.1 p.2}) (n : ℕ) :
    MeasurableSet {seeds | adaptiveFailure step good initial n seeds} := by
  induction n with
  | zero => exact MeasurableSet.empty
  | succ n ih =>
      exact (ih.preimage measurable_fst).union
        (((hgood n).preimage
          (((measurable_adaptiveRun step initial hstep n).comp measurable_fst).prodMk
            measurable_snd)).compl)

theorem measurable_adaptiveRun_initial [MeasurableSpace Seed] [MeasurableSpace State]
    (step : ℕ → State → Seed → State)
    (hstep : ∀ n, Measurable (fun p : State × Seed => step n p.1 p.2)) (n : ℕ) :
    Measurable (fun p : State × SeedBlock Seed n => adaptiveRun step p.1 n p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact (hstep n).comp
        ((ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd))

theorem measurableSet_adaptiveFailure_initial
    [MeasurableSpace Seed] [MeasurableSpace State]
    (step : ℕ → State → Seed → State) (good : ℕ → State → Seed → Prop)
    (hstep : ∀ n, Measurable (fun p : State × Seed => step n p.1 p.2))
    (hgood : ∀ n, MeasurableSet {p : State × Seed | good n p.1 p.2}) (n : ℕ) :
    MeasurableSet {p : State × SeedBlock Seed n | adaptiveFailure step good p.1 n p.2} := by
  induction n with
  | zero => exact MeasurableSet.empty
  | succ n ih =>
      let prevSeeds : State × SeedBlock Seed (n + 1) → State × SeedBlock Seed n :=
        fun p => (p.1, p.2.1)
      have hp : Measurable prevSeeds := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      exact (ih.preimage hp).union
        (((hgood n).preimage
          (((measurable_adaptiveRun_initial step hstep n).comp hp).prodMk
            (measurable_snd.comp measurable_snd))).compl)

/-- The fresh call can depend measurably on the entire previous randomness. -/
theorem fresh_failure_probability [MeasurableSpace Seed] [MeasurableSpace State]
    {Past : Type*} [MeasurableSpace Past]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (ν : Measure Past) [IsProbabilityMeasure ν]
    (state : Past → State) (hstate : Measurable state)
    (good : State → Seed → Prop)
    (hgood : MeasurableSet {p : State × Seed | good p.1 p.2})
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hfailure : ∀ x, μ.real {seed | ¬good x seed} ≤ δ) :
    (ν.prod μ).real {p | ¬good (state p.1) p.2} ≤ δ := by
  have hm : MeasurableSet {p : Past × Seed | ¬good (state p.1) p.2} :=
    (hgood.preimage ((hstate.comp measurable_fst).prodMk measurable_snd)).compl
  have hb : (ν.prod μ) {p | ¬good (state p.1) p.2} ≤ ENNReal.ofReal δ := by
    rw [Measure.prod_apply hm]
    calc
      _ ≤ ∫⁻ _ : Past, ENNReal.ofReal δ ∂ν := by
        apply lintegral_mono
        intro p
        exact (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
          (by simpa only [ENNReal.toReal_ofReal hδ] using hfailure (state p))
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hδ)

/-- Uniform one-step failure δ gives nδ for actual adaptive calls on fresh
independent seeds. This theorem does not assume their inputs are independent. -/
theorem adaptive_failure_probability [MeasurableSpace Seed] [MeasurableSpace State]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (step : ℕ → State → Seed → State) (good : ℕ → State → Seed → Prop)
    (initial : State)
    (hstep : ∀ n, Measurable (fun p : State × Seed => step n p.1 p.2))
    (hgood : ∀ n, MeasurableSet {p : State × Seed | good n p.1 p.2})
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hfailure : ∀ n x, μ.real {seed | ¬good n x seed} ≤ δ) (n : ℕ) :
    (seedBlockLaw μ n).real {seeds | adaptiveFailure step good initial n seeds} ≤
      (n : ℝ) * δ := by
  induction n with
  | zero => simp [adaptiveFailure, seedBlockLaw]
  | succ n ih =>
      have hpast : ((seedBlockLaw μ n).prod μ).real
          {p : SeedBlock Seed n × Seed | adaptiveFailure step good initial n p.1} =
          (seedBlockLaw μ n).real {seeds | adaptiveFailure step good initial n seeds} := by
        have heq : {p : SeedBlock Seed n × Seed | adaptiveFailure step good initial n p.1} =
            {seeds | adaptiveFailure step good initial n seeds} ×ˢ Set.univ := by ext p; simp
        rw [heq, measureReal_prod_prod, measureReal_univ_eq_one, mul_one]
      have hfresh := fresh_failure_probability μ (seedBlockLaw μ n)
        (adaptiveRun step initial n) (measurable_adaptiveRun step initial hstep n)
        (good n) (hgood n) δ hδ (hfailure n)
      change ((seedBlockLaw μ n).prod μ).real
        ({p | adaptiveFailure step good initial n p.1} ∪
         {p | ¬good n (adaptiveRun step initial n p.1) p.2}) ≤ _
      calc
        _ ≤ ((seedBlockLaw μ n).prod μ).real {p | adaptiveFailure step good initial n p.1} +
            ((seedBlockLaw μ n).prod μ).real
              {p | ¬good n (adaptiveRun step initial n p.1) p.2} := measureReal_union_le _ _
        _ ≤ (n : ℝ) * δ + δ := add_le_add (by simpa only [hpast] using ih) hfresh
        _ = _ := by push_cast; ring

/-- Deterministic invariant transfer on the complement of the failure event. -/
theorem adaptiveRun_invariant (step : ℕ → State → Seed → State)
    (good : ℕ → State → Seed → Prop) (initial : State)
    (P : ℕ → State → Prop) (hzero : P 0 initial)
    (hstep : ∀ n x seed, P n x → good n x seed → P (n + 1) (step n x seed)) :
    ∀ n seeds, ¬adaptiveFailure step good initial n seeds →
      P n (adaptiveRun step initial n seeds) := by
  intro n
  induction n with
  | zero => intro seeds _; exact hzero
  | succ n ih =>
      intro seeds h
      have hh : ¬adaptiveFailure step good initial n seeds.1 ∧
          good n (adaptiveRun step initial n seeds.1) seeds.2 := by
        simpa only [adaptiveFailure, not_or, not_not] using h
      exact hstep n _ _ (ih seeds.1 hh.1) hh.2

/-- The actual finite run, recorded as a sequence. Values beyond the executed
horizon are irrelevant to all subsequent guarantees. -/
def adaptiveHistory (step : ℕ → State → Seed → State) (initial : State) :
    (n : ℕ) → SeedBlock Seed n → ℕ → State
  | 0, _, _ => initial
  | n + 1, seeds, j =>
      if j = n + 1 then adaptiveRun step initial (n + 1) seeds
      else adaptiveHistory step initial n seeds.1 j

theorem adaptiveHistory_last (step : ℕ → State → Seed → State) (initial : State)
    (n : ℕ) (seeds : SeedBlock Seed n) :
    adaptiveHistory step initial n seeds n = adaptiveRun step initial n seeds := by
  cases n <;> simp [adaptiveHistory, adaptiveRun]

theorem adaptiveHistory_zero (step : ℕ → State → Seed → State) (initial : State)
    (n : ℕ) (seeds : SeedBlock Seed n) : adaptiveHistory step initial n seeds 0 = initial := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [adaptiveHistory, Nat.succ_ne_zero, eq_comm, if_false] using ih seeds.1

theorem adaptiveHistory_good (step : ℕ → State → Seed → State)
    (good : ℕ → State → Seed → Prop) (initial : State)
    (P : ℕ → State → State → Prop)
    (hstep : ∀ n x seed, good n x seed → P n x (step n x seed)) :
    ∀ n seeds, ¬adaptiveFailure step good initial n seeds →
      ∀ j < n, P j (adaptiveHistory step initial n seeds j)
        (adaptiveHistory step initial n seeds (j + 1)) := by
  intro n
  induction n with
  | zero => intro seeds h j hj; omega
  | succ n ih =>
      intro seeds h j hj
      have hh : ¬adaptiveFailure step good initial n seeds.1 ∧
          good n (adaptiveRun step initial n seeds.1) seeds.2 := by
        simpa only [adaptiveFailure, not_or, not_not] using h
      by_cases hjn : j = n
      · subst j
        rw [adaptiveHistory, if_neg (by omega), adaptiveHistory_last,
          adaptiveHistory, if_pos rfl, adaptiveRun]
        exact hstep n _ _ hh.2
      · rw [adaptiveHistory, if_neg (by omega), adaptiveHistory, if_neg (by omega)]
        exact ih seeds.1 hh.1 j (by omega)

end
end Matvec

