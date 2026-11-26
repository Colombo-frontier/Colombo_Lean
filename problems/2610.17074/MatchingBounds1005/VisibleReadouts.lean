import MatchingBounds1005.TensorAdaptiveRows

/-!
# The actual array of disclosed physical readouts

An array starts at zero. A disclosure replaces exactly one entry by the
physical column returned by the Haar oracle. The deterministic layer
calendar therefore produces precisely the visible signal, with hidden
entries remaining zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MatchingBounds1005.VisibleReadouts
open TensorGeometry

variable {d N : ℕ}

def update (i : Fin N) (p : (Fin N → Vec d) × Vec d) : Fin N → Vec d :=
  Function.update p.1 i p.2

theorem update_measurable (i : Fin N) : Measurable (update (d := d) i) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [update, Function.update_self] using (measurable_snd : Measurable (Prod.snd : (Fin N → Vec d) × Vec d → Vec d))
  · simpa only [update, Function.update_of_ne hj] using (measurable_pi_apply j).comp
      (measurable_fst : Measurable (Prod.fst : (Fin N → Vec d) × Vec d → (Fin N → Vec d)))

def reveal (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d) : List (Fin N) → (Fin N → Vec d) → Fin N → Vec d
  | [], stored => stored
  | i :: xs, stored => reveal b U xs (Function.update stored i (U (b i)))

theorem reveal_apply (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (xs : List (Fin N)) (stored : Fin N → Vec d) (i : Fin N) :
    reveal b U xs stored i = if i ∈ xs then U (b i) else stored i := by
  induction xs generalizing stored with
  | nil => simp [reveal]
  | cons j xs ih =>
      rw [reveal, ih]
      by_cases hix : i ∈ xs
      · simp only [hix, List.mem_cons, or_true, if_true]
      · by_cases hij : i = j
        · subst j
          simp [hix]
        · simp [hix, hij, Function.update_of_ne hij]

def due (τ : Fin N → ℕ) (t : ℕ) : List (Fin N) :=
  (Finset.univ.filter (fun i => τ i = t)).toList

theorem mem_due (τ : Fin N → ℕ) (t : ℕ) (i : Fin N) : i ∈ due τ t ↔ τ i = t := by
  simp [due]

def visibleAt (τ : Fin N → ℕ) (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (t : ℕ) : Fin N → Vec d := fun i => if τ i ≤ t then U (b i) else 0

theorem reveal_due (τ : Fin N → ℕ) (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (t : ℕ) : reveal b U (due τ (t + 1)) (visibleAt τ b U t) = visibleAt τ b U (t + 1) := by
  funext i
  rw [reveal_apply]
  simp only [mem_due, visibleAt]
  by_cases hi : τ i = t + 1
  · simp [hi]
  · by_cases ht : τ i ≤ t
    · simp [hi, ht, Nat.le_succ_of_le ht]
    · have hn : ¬ τ i ≤ t + 1 := by omega
      simp [hi, ht, hn]

theorem visibleAt_zero (τ : Fin N → ℕ) (hτ : ∀ i, 0 < τ i)
    (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d) : visibleAt τ b U 0 = 0 := by
  funext i
  exact if_neg (Nat.not_le.mpr (hτ i))

theorem rankOne_zero {k : ℕ} (hk : 1 ≤ k) : rankOne (d := d) k 0 = 0 := by
  ext idx
  change (∏ i : Fin k, (0 : Vec d) (idx i)) = 0
  have hn : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI := hn
  simp [Nat.ne_of_gt hk]

/-- Summing the stored array yields exactly the disclosed tensor signal. -/
theorem signal_visibleAt {k : ℕ} (hk : 1 ≤ k) (w : ℝ) (τ : Fin N → ℕ)
    (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d) (t : ℕ) :
    signal k w (visibleAt τ b U t) = w • ∑ i, if τ i ≤ t then rankOne k (U (b i)) else 0 := by
  unfold signal
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : τ i ≤ t
  · simp only [visibleAt, if_pos hi]
  · simp only [visibleAt, if_neg hi, rankOne_zero hk]

theorem signal_measurable (k : ℕ) (w : ℝ) : Measurable (signal (ι := Fin N) (d := d) k w) := by
  unfold signal
  apply measurable_const.smul
  apply Finset.measurable_sum
  intro i _
  have hconst : Continuous (fun b : Vec d => (fun _ : Fin k => b)) := continuous_pi (fun _ => continuous_id)
  exact ((productTensor_continuous d k).comp hconst).measurable.comp (measurable_pi_apply i)

end MatchingBounds1005.VisibleReadouts
