import NCConcave16991.AcceleratedSteps
import NCConcave16991.AcceleratedParameters
import NCConcave16991.FiniteFailure

/-!
# Actual adaptive accelerated paths from independent finite solver seeds

The next extrapolation uses only the preceding seeds. A final replay merely
names the same chronological path; its prefix agreement is proved below.
-/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {I : Type*}

def seedAt (fallback : I) : (t : ℕ) → FiniteProcess.History I t → ℕ → I
  | 0, _, _ => fallback
  | t + 1, h, k => if k = t then h.2 else seedAt fallback t h.1 k

def replay (fallback : I) (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y))
    (t : ℕ) (h : FiniteProcess.History I t) : ℕ → Y → ProxResult (X := X) (Y := Y) :=
  fun k v ↦ sample k v (seedAt fallback t h k)

theorem states_congr_prefix (τ : ℝ)
    (solve solve' : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) (t : ℕ)
    (he : ∀ k < t, ∀ v, solve k v = solve' k v) :
    states τ solve y0 t = states τ solve' y0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun k hk ↦ he k (by omega))
    change advance τ solve t (states τ solve y0 t) = advance τ solve' t (states τ solve' y0 t)
    rw [hs]
    simp only [advance, he t (by omega)]

theorem resultAt_congr_prefix (τ : ℝ)
    (solve solve' : ℕ → Y → ProxResult (X := X) (Y := Y)) (y0 : Y) {t k : ℕ}
    (hk : k < t) (he : ∀ j < t, ∀ v, solve j v = solve' j v) :
    resultAt τ solve y0 k = resultAt τ solve' y0 k := by
  have hs := states_congr_prefix τ solve solve' y0 k (fun j hj ↦ he j (by omega))
  simp only [resultAt, hs, he k hk]

theorem replay_extend (fallback : I)
    (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y)) (t : ℕ)
    (h : FiniteProcess.History I t) (i : I) (k : ℕ) (hk : k < t) (v : Y) :
    replay fallback sample (t + 1) (h, i) k v = replay fallback sample t h k v := by
  simp only [replay, seedAt, ne_of_lt hk, ite_false]

def randomState (τ : ℝ) (fallback : I)
    (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y)) (y0 : Y)
    (t : ℕ) (h : FiniteProcess.History I t) : State X Y :=
  states τ (replay fallback sample t h) y0 t

def randomBad (F : CompactSaddle X Y) (τ ζ : ℝ) (fallback : I)
    (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y)) (y0 : Y)
    (t : ℕ) (h : FiniteProcess.History I t) (i : I) : Prop :=
  ¬JointCheck F τ ζ (center τ t (randomState τ fallback sample y0 t h))
    (sample t (center τ t (randomState τ fallback sample y0 t h)) i)

def randomOutput (τ : ℝ) (fallback : I)
    (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y)) (y0 : Y)
    (t : ℕ) (h : FiniteProcess.History I t) : X :=
  primalOutput τ (replay fallback sample t h) y0 t

/-- Absence of chronological failures implies every check on the exact final
replayed trajectory, including checks at adaptively selected extrapolations. -/
theorem replay_checks_of_no_failure (F : CompactSaddle X Y) (τ ζ : ℝ) (fallback : I)
    (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y)) (y0 : Y)
    (T : ℕ) (h : FiniteProcess.History I T)
    (hgood : ¬FiniteProcess.everBad (randomBad F τ ζ fallback sample y0) T h) :
    ∀ k < T, JointCheck F τ ζ
      (center τ k (states τ (replay fallback sample T h) y0 k))
      (resultAt τ (replay fallback sample T h) y0 k) := by
  induction T with
  | zero => intro k hk; omega
  | succ T ih =>
    have hprev : ¬FiniteProcess.everBad (randomBad F τ ζ fallback sample y0) T h.1 :=
      fun hh ↦ hgood (Or.inl hh)
    have hlast : ¬randomBad F τ ζ fallback sample y0 T h.1 h.2 :=
      fun hh ↦ hgood (Or.inr hh)
    intro k hk
    by_cases hkT : k < T
    · have hc := ih h.1 hprev k hkT
      have he := fun j hj v ↦ replay_extend fallback sample T h.1 h.2 j hj v
      have hs := states_congr_prefix τ (replay fallback sample (T + 1) h)
        (replay fallback sample T h.1) y0 k (fun j hj ↦ he j (by omega))
      have hr := resultAt_congr_prefix τ (replay fallback sample (T + 1) h)
        (replay fallback sample T h.1) y0 hkT he
      rw [hs, hr]
      exact hc
    · have hkEq : k = T := by omega
      subst k
      have hs := states_congr_prefix τ (replay fallback sample (T + 1) h)
        (replay fallback sample T h.1) y0 T
        (fun j hj ↦ replay_extend fallback sample T h.1 h.2 j hj)
      have hc : JointCheck F τ ζ
          (center τ T (randomState τ fallback sample y0 T h.1))
          (sample T (center τ T (randomState τ fallback sample y0 T h.1)) h.2) := by
        exact Classical.not_not.mp hlast
      simpa only [resultAt, hs, replay, seedAt, ite_true, randomState] using hc

variable [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Uniform actual solver failure probabilities transfer to the genuinely
adaptive sequence; check events need not be independent. -/
theorem random_checks_failure_probability (F : CompactSaddle X Y) (τ ζ : ℝ)
    (fallback : I) (sample : ℕ → Y → I → ProxResult (X := X) (Y := Y)) (y0 : Y)
    (ν : Measure I) [IsProbabilityMeasure ν] {failure : ℝ} (hf : 0 ≤ failure)
    (hsolver : ∀ k v, ν.real {i | ¬JointCheck F τ ζ v (sample k v i)} ≤ failure)
    (T : ℕ) :
    (FiniteProcess.law ν T).real {h | ¬∀ k < T, JointCheck F τ ζ
      (center τ k (states τ (replay fallback sample T h) y0 k))
      (resultAt τ (replay fallback sample T h) y0 k)} ≤ T * failure := by
  have hh := FiniteProcess.adaptive_failure_probability ν (randomBad F τ ζ fallback sample y0)
    hf (fun k h ↦ hsolver k (center τ k (randomState τ fallback sample y0 k h))) T
  letI : IsProbabilityMeasure (FiniteProcess.law ν T) := FiniteProcess.law_probability ν T
  apply le_trans (measureReal_mono (s₁ := {h | ¬∀ k < T, JointCheck F τ ζ
      (center τ k (states τ (replay fallback sample T h) y0 k))
      (resultAt τ (replay fallback sample T h) y0 k)}) (s₂ := _)
    (fun h hb ↦ Classical.byContradiction (fun hn ↦ hb (replay_checks_of_no_failure F τ ζ fallback sample y0 T h hn)))) hh

end NCConcave16991.Accelerated
