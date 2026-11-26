import GradientHessian.DisclosureCompiler
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Exhaustion of the chronological preprocessing cutoff. A branch is opened
only after preprocessing finishes, and its saved state is then fixed forever. -/

namespace GradientHessian.DisclosureCompiler
open Matrix MeasureTheory LowRank OracleComposition Filter Set
open scoped Topology
noncomputable section

variable {d : ℕ} {State : Type*} [MeasurableSpace State]

def Program.step (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ)
    (readout : (Fin d → ℝ) → Fin d → ℝ) (s : State) : State :=
  if P.mode s = 0 then s
  else if P.mode s = 1 then P.think s
  else if P.mode s = 2 then P.next (s,A*ᵥP.query s)
  else P.disclosed (s,readout (P.mark s))

theorem Program.eval_eq_terminal_iterate (P : Program d State)
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (n : ℕ) (s : State) :
    P.eval A readout n s = P.terminal.1 ((P.step A readout)^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      by_cases h0 : P.mode s = 0
      · have hf : ∀ i, (P.step A readout)^[i] s = s :=
          Function.iterate_fixed (by simp [Program.step,h0])
        simp [Program.eval,h0,hf]
      · rw [Function.iterate_succ_apply]
        by_cases h1 : P.mode s = 1
        · simpa [Program.eval,Program.step,h0,h1] using ih (P.think s)
        · by_cases h2 : P.mode s = 2
          · simpa [Program.eval,Program.step,h0,h1,h2] using ih (P.next (s,A*ᵥP.query s))
          · simpa [Program.eval,Program.step,h0,h1,h2] using ih (P.disclosed (s,readout (P.mark s)))

theorem Program.eval_open_iff (P : Program d State)
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    (P.eval A readout n s).1 = true ↔ P.mode ((P.step A readout)^[n] s) = 0 := by
  rw [P.eval_eq_terminal_iterate]
  simp [Program.terminal,Program.flag]

theorem Program.eval_state (P : Program d State)
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ) (n : ℕ) (s : State) :
    (P.eval A readout n s).2 = (P.step A readout)^[n] s := by
  rw [P.eval_eq_terminal_iterate]
  rfl

theorem Program.eval_stable_of_open (P : Program d State)
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    {n m : ℕ} (hnm : n ≤ m) (s : State) (hopen : (P.eval A readout n s).1 = true) :
    P.eval A readout m s = P.eval A readout n s := by
  have hh := (P.eval_open_iff A readout n s).mp hopen
  have hfixed : ∀ k, (P.step A readout)^[k] ((P.step A readout)^[n] s) =
      (P.step A readout)^[n] s := Function.iterate_fixed (by simp [Program.step,hh])
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [P.eval_eq_terminal_iterate,P.eval_eq_terminal_iterate]
  rw [Nat.add_comm n k,Function.iterate_add_apply,hfixed]

variable {Ω : Type*}

def Program.cutoffHit (P : Program d State)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ) (initial : Ω → State)
    (postHit : ℕ → State → Ω → Prop) (n : ℕ) : Set Ω :=
  {ω | (P.eval (A ω) (readout ω) n (initial ω)).1 = true ∧
    postHit n (P.eval (A ω) (readout ω) n (initial ω)).2 ω}

def Program.eventualHit (P : Program d State)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ) (initial : Ω → State)
    (postHit : ℕ → State → Ω → Prop) : Set Ω :=
  {ω | ∃ n, (P.eval (A ω) (readout ω) n (initial ω)).1 = true ∧
    ∃ m, postHit m (P.eval (A ω) (readout ω) n (initial ω)).2 ω}

theorem Program.cutoffHit_mono (P : Program d State)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ) (initial : Ω → State)
    (postHit : ℕ → State → Ω → Prop)
    (hpost : ∀ s ω, Monotone (fun n => postHit n s ω)) :
    Monotone (P.cutoffHit A readout initial postHit) := by
  intro n m hnm ω hω
  obtain ⟨hopen,hhit⟩ := hω
  have he := P.eval_stable_of_open (A ω) (readout ω) hnm (initial ω) hopen
  change (P.eval (A ω) (readout ω) m (initial ω)).1 = true ∧
    postHit m (P.eval (A ω) (readout ω) m (initial ω)).2 ω
  rw [he]
  exact ⟨hopen,hpost _ ω hnm hhit⟩

theorem Program.eventualHit_eq_iUnion (P : Program d State)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ) (initial : Ω → State)
    (postHit : ℕ → State → Ω → Prop)
    (hpost : ∀ s ω, Monotone (fun n => postHit n s ω)) :
    P.eventualHit A readout initial postHit = ⋃ n, P.cutoffHit A readout initial postHit n := by
  ext ω
  constructor
  · rintro ⟨n,hopen,m,hhit⟩
    apply Set.mem_iUnion.mpr
    refine ⟨max n m,?_⟩
    have he := P.eval_stable_of_open (A ω) (readout ω) (le_max_left n m) (initial ω) hopen
    change (P.eval (A ω) (readout ω) (max n m) (initial ω)).1 = true ∧ _
    rw [he]
    exact ⟨hopen,hpost _ ω (le_max_right n m) hhit⟩
  · intro hω
    obtain ⟨n,hopen,hhit⟩ := Set.mem_iUnion.mp hω
    exact ⟨n,hopen,n,hhit⟩

theorem Program.cutoffHit_tendsto (P : Program d State) [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ) (initial : Ω → State)
    (postHit : ℕ → State → Ω → Prop)
    (hpost : ∀ s ω, Monotone (fun n => postHit n s ω)) (μ : Measure Ω) :
    Tendsto (fun n => μ (P.cutoffHit A readout initial postHit n)) atTop
      (𝓝 (μ (P.eventualHit A readout initial postHit))) := by
  rw [P.eventualHit_eq_iUnion A readout initial postHit hpost]
  exact tendsto_measure_iUnion_atTop (P.cutoffHit_mono A readout initial postHit hpost)

theorem Program.eval_measurable (P : Program d State) [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : Measurable A)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ)
    (hr : Measurable (Function.uncurry readout)) (n : ℕ)
    (initial : Ω → State) (hi : Measurable initial) :
    Measurable (fun ω => P.eval (A ω) (readout ω) n (initial ω)) := by
  induction n generalizing initial with
  | zero => exact P.terminal.2.comp hi
  | succ n ih =>
      apply Measurable.ite ((P.mode_measurable.comp hi) (measurableSet_singleton 0))
        (P.terminal.2.comp hi)
      apply Measurable.ite ((P.mode_measurable.comp hi) (measurableSet_singleton 1))
        (ih _ (P.think_measurable.comp hi))
      apply Measurable.ite ((P.mode_measurable.comp hi) (measurableSet_singleton 2))
      · apply ih
        apply P.next_measurable.comp
        apply hi.prodMk
        have hquery : Measurable (fun ω => P.query (initial ω)) := P.query_measurable.comp hi
        apply measurable_pi_lambda
        intro i
        simp only [Matrix.mulVec,dotProduct]
        fun_prop
      · apply ih
        exact P.disclosed_measurable.comp
          (hi.prodMk (hr.comp (measurable_id.prodMk (P.mark_measurable.comp hi))))

theorem Program.cutoffHit_measurable (P : Program d State) [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : Measurable A)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ)
    (hr : Measurable (Function.uncurry readout))
    (initial : Ω → State) (hi : Measurable initial)
    (postHit : ℕ → State → Ω → Prop)
    (hpost : ∀ n, MeasurableSet {t : State × Ω | postHit n t.1 t.2}) (n : ℕ) :
    MeasurableSet (P.cutoffHit A readout initial postHit n) := by
  have he := P.eval_measurable A hA readout hr n initial hi
  exact (he.fst (measurableSet_singleton true)).inter
    ((he.snd.prodMk measurable_id) (hpost n))

/-- The same uniform probability bound survives unlimited internal
computation, including executions that never open the fresh mark. -/
theorem Program.eventualHit_bound (P : Program d State) [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (readout : Ω → (Fin d → ℝ) → Fin d → ℝ) (initial : Ω → State)
    (postHit : ℕ → State → Ω → Prop)
    (hpost : ∀ s ω, Monotone (fun n => postHit n s ω))
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : ℝ)
    (hbound : ∀ n, μ.real (P.cutoffHit A readout initial postHit n) ≤ C) :
    μ.real (P.eventualHit A readout initial postHit) ≤ C := by
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp
    (P.cutoffHit_tendsto A readout initial postHit hpost μ)
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

end
end GradientHessian.DisclosureCompiler
