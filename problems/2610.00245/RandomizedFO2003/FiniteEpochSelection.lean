import RandomizedFO2003.EpochExit
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace RandomizedFO2003.Accelerated

open MeasureTheory

noncomputable section

/-- A total minimum selector on the inclusive interval `[a,a+n]`, with
deterministic finite tie breaking and no optimization oracle. -/
def minFrom (v : ℕ → ℝ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => let q := minFrom v a n
             if v (a + n + 1) ≤ v q then a + n + 1 else q

theorem minFrom_spec (v : ℕ → ℝ) (a n : ℕ) :
    a ≤ minFrom v a n ∧ minFrom v a n ≤ a + n ∧
      ∀ k, a ≤ k → k ≤ a + n → v (minFrom v a n) ≤ v k := by
  induction n with
  | zero =>
    simp only [minFrom, Nat.add_zero, le_refl, true_and]
    intro k hk hk'
    have : k = a := by omega
    subst k
    exact le_rfl
  | succ n ih =>
    simp only [minFrom]
    split_ifs with hh
    · refine ⟨by omega, by omega, ?_⟩
      intro k hk hk'
      by_cases he : k = a + n + 1
      · subst k; exact le_rfl
      · exact hh.trans (ih.2.2 k hk (by omega))
    · refine ⟨ih.1, by omega, ?_⟩
      intro k hk hk'
      by_cases he : k = a + n + 1
      · subst k; exact (le_of_not_ge hh)
      · exact ih.2.2 k hk (by omega)

theorem minFrom_congr (v w : ℕ → ℝ) (a n : ℕ)
    (h : ∀ k, a ≤ k → k ≤ a + n → v k = w k) : minFrom v a n = minFrom w a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ih (fun k hk hk' => h k hk (by omega))
    have hs := minFrom_spec w a n
    simp only [minFrom, he, h (a + n + 1) (by omega) (by omega),
      h (minFrom w a n) hs.1 (by omega)]

def halfMinIndex (v : ℕ → ℝ) (N : ℕ) : ℕ := minFrom v (N / 2) (N - 1 - N / 2)

theorem firstExit_congr (v w : ℕ → ℝ) (threshold : ℝ) (N : ℕ)
    (h : ∀ k < N, v k = w k) : firstExit v threshold N = firstExit w threshold N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [firstExit, h n (by omega), ih (fun k hk => h k (by omega))]

theorem halfMinIndex_spec (v : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    N / 2 ≤ halfMinIndex v N ∧ halfMinIndex v N < N ∧
      ∀ k, N / 2 ≤ k → k < N → v (halfMinIndex v N) ≤ v k := by
  have hhalf : N / 2 < N := Nat.div_lt_self hN (by norm_num)
  have hs := minFrom_spec v (N / 2) (N - 1 - N / 2)
  exact ⟨hs.1, by dsimp [halfMinIndex]; omega, fun k hk hk' => hs.2.2 k hk (by omega)⟩

theorem halfMinIndex_congr (v w : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    (h : ∀ k < N, v k = w k) : halfMinIndex v N = halfMinIndex w N := by
  apply minFrom_congr
  intro k hk hk'
  have hhalf : N / 2 < N := Nat.div_lt_self hN (by norm_num)
  exact h k (by omega)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_nat_select {i : X → ℕ} (hi : Measurable i)
    {v : ℕ → X → Y} (hv : ∀ n, Measurable (v n)) :
    Measurable (fun x => v (i x) x) := by
  have hm : Measurable (fun p : X × ℕ => v p.2 p.1) := measurable_from_prod_countable hv
  exact hm.comp (measurable_id.prodMk hi)

theorem measurable_minFrom {v : X → ℕ → ℝ} (hv : ∀ n, Measurable (fun x => v x n))
    (a n : ℕ) : Measurable (fun x => minFrom (v x) a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite (measurableSet_le (hv (a + n + 1)) (measurable_nat_select ih hv))
      measurable_const ih

theorem measurable_halfMinIndex {v : X → ℕ → ℝ} (hv : ∀ n, Measurable (fun x => v x n))
    (N : ℕ) : Measurable (fun x => halfMinIndex (v x) N) :=
  measurable_minFrom hv _ _

theorem measurable_firstExit {budget : X → ℕ → ℝ}
    (hb : ∀ n, Measurable (fun x => budget x n)) (threshold : ℝ) (N : ℕ) :
    Measurable (fun x => firstExit (budget x) threshold N) := by
  induction N with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite (measurableSet_le (hb n) measurable_const) measurable_const ih

end

end RandomizedFO2003.Accelerated
