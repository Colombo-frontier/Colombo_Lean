import RandomizedFO2003.AcceleratedDescent

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One genuine accelerated epoch. The two stored points agree initially,
so resetting this state cancels momentum. -/
noncomputable def epochState (f : E → ℝ) (η θ : ℝ) (start : E) : ℕ → E × E
  | 0 => (start, start)
  | n + 1 => let s := epochState f η θ start n
             (s.2, gradientStep η f (extrapolate θ s.1 s.2))

noncomputable def epochPoint (f : E → ℝ) (η θ : ℝ) (start : E) (n : ℕ) : E :=
  (epochState f η θ start n).2

noncomputable def epochQuery (f : E → ℝ) (η θ : ℝ) (start : E) (n : ℕ) : E :=
  let s := epochState f η θ start n
  extrapolate θ s.1 s.2

noncomputable def epochMomentum (f : E → ℝ) (η θ : ℝ) (start : E) (n : ℕ) : E :=
  let s := epochState f η θ start n
  s.2 - s.1

noncomputable def epochIncrement (f : E → ℝ) (η θ : ℝ) (start : E) (n : ℕ) : E :=
  epochPoint f η θ start (n + 1) - epochPoint f η θ start n

noncomputable def epochEnergy (f : E → ℝ) (η θ : ℝ) (start : E) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ‖epochIncrement f η θ start k‖ ^ 2

noncomputable def epochGradientEnergy (f : E → ℝ) (η θ : ℝ) (start : E) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ‖gradient f (epochQuery f η θ start k)‖ ^ 2

variable (f : E → ℝ) (η θ : ℝ) (start : E)

@[simp] theorem epochPoint_zero : epochPoint f η θ start 0 = start := rfl
@[simp] theorem epochPoint_succ (n : ℕ) : epochPoint f η θ start (n + 1) =
    gradientStep η f (epochQuery f η θ start n) := rfl
@[simp] theorem epochMomentum_zero : epochMomentum f η θ start 0 = 0 := sub_self _
@[simp] theorem epochMomentum_succ (n : ℕ) :
    epochMomentum f η θ start (n + 1) = epochIncrement f η θ start n := rfl
@[simp] theorem epochEnergy_zero : epochEnergy f η θ start 0 = 0 := rfl
@[simp] theorem epochEnergy_succ (n : ℕ) : epochEnergy f η θ start (n + 1) =
    epochEnergy f η θ start n + ‖epochIncrement f η θ start n‖ ^ 2 := Finset.sum_range_succ _ _
@[simp] theorem epochGradientEnergy_zero : epochGradientEnergy f η θ start 0 = 0 := rfl
@[simp] theorem epochGradientEnergy_succ (n : ℕ) : epochGradientEnergy f η θ start (n + 1) =
    epochGradientEnergy f η θ start n + ‖gradient f (epochQuery f η θ start n)‖ ^ 2 :=
  Finset.sum_range_succ _ _

theorem epochEnergy_nonneg (n : ℕ) : 0 ≤ epochEnergy f η θ start n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
theorem epochGradientEnergy_nonneg (n : ℕ) : 0 ≤ epochGradientEnergy f η θ start n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sum_epochIncrement (n : ℕ) :
    ∑ k ∈ Finset.range n, epochIncrement f η θ start k = epochPoint f η θ start n - start := by
  simpa only [epochIncrement, epochPoint_zero] using Finset.sum_range_sub (epochPoint f η θ start) n

variable {f η θ}

/-- Telescoping the actual accelerated recurrence, including the final
momentum term. This is stronger than the bound needed for a large-gradient restart. -/
theorem epoch_energy_scaled (hf : Differentiable ℝ f)
    {L : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hη : 0 ≤ η) (hstep : L * η ≤ 1 / 4) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    8 * η * (f (epochPoint f η θ start n) - f start) +
      5 * ‖epochMomentum f η θ start n‖ ^ 2 + 3 * η ^ 2 * epochGradientEnergy f η θ start n ≤
        epochEnergy f η θ start n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := accelerated_step_energy_scaled hf hlip hη hstep hθ hθ1
      (epochState f η θ start n).1 (epochState f η θ start n).2
    change 8 * η * (f (epochPoint f η θ start (n + 1)) - f (epochPoint f η θ start n)) ≤
      5 * ‖epochMomentum f η θ start n‖ ^ 2 - 4 * ‖epochIncrement f η θ start n‖ ^ 2 -
        3 * η ^ 2 * ‖gradient f (epochQuery f η θ start n)‖ ^ 2 at hs
    rw [epochMomentum_succ, epochGradientEnergy_succ, epochEnergy_succ]
    nlinarith

theorem epoch_last_gradient_bound (hf : Differentiable ℝ f)
    {L : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hη : 0 ≤ η) (hstep : L * η ≤ 1 / 4) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℕ) :
    8 * η * (f (epochPoint f η θ start (n + 1)) - f start) ≤ epochEnergy f η θ start n -
      3 * η ^ 2 * ‖gradient f (epochQuery f η θ start n)‖ ^ 2 := by
  have hs := epoch_energy_scaled start hf hlip hη hstep hθ hθ1 (n + 1)
  rw [epochMomentum_succ, epochGradientEnergy_succ, epochEnergy_succ] at hs
  have hn := epochGradientEnergy_nonneg f η θ start n
  have hp : 0 ≤ 3 * η ^ 2 * epochGradientEnergy f η θ start n := by positivity
  nlinarith [sq_nonneg ‖epochIncrement f η θ start n‖]

/-- The large-last-gradient alternative for the actual accelerated epoch.
The preterminal restart test suffices; no first-exit or oracle hypothesis is hidden. -/
theorem large_gradient_epoch_decrease (hf : Differentiable ℝ f)
    {L B : ℝ} (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hη : 0 < η) (hstep : L * η ≤ 1 / 4) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hB : 0 ≤ B)
    (n : ℕ) (hbudget : (n : ℝ) * epochEnergy f η θ start n ≤ B ^ 2)
    (hlarge : B ≤ η * ‖gradient f (epochQuery f η θ start n)‖) :
    f (epochPoint f η θ start (n + 1)) - f start ≤ -(B ^ 2 / (4 * η)) := by
  have he : epochEnergy f η θ start n ≤ B ^ 2 := by
    by_cases hn : n = 0
    · simp only [hn, epochEnergy_zero]
      exact sq_nonneg B
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      nlinarith [epochEnergy_nonneg f η θ start n]
  have hg : B ^ 2 ≤ η ^ 2 * ‖gradient f (epochQuery f η θ start n)‖ ^ 2 := by
    have hh := (sq_le_sq₀ hB (by positivity)).mpr hlarge
    nlinarith
  have hs := epoch_last_gradient_bound start hf hlip hη.le hstep hθ hθ1 n
  rw [← neg_div, le_div_iff₀ (by positivity : 0 < 4 * η)]
  nlinarith

end RandomizedFO2003.Accelerated
