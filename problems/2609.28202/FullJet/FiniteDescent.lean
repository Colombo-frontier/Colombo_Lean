import FullJet.UniformPrefixMean

open scoped BigOperators

namespace FullJet

/-- The telescoping identity for the actual consecutive vertices of a finite path. -/
theorem sum_successive_difference {m : ℕ} (F : Fin (m + 1) → ℝ) :
    (∑ t : Fin m, (F t.castSucc - F t.succ)) = F 0 - F (Fin.last m) := by
  have h₁ := Fin.sum_univ_succ F
  have h₂ := Fin.sum_univ_castSucc F
  rw [Finset.sum_sub_distrib]
  linarith

theorem finite_descent_budget {m : ℕ} (F : Fin (m + 1) → ℝ) (d e : Fin m → ℝ)
    (hstep : ∀ t, F t.succ ≤ F t.castSucc - d t + e t) :
    (∑ t, d t) ≤ F 0 - F (Fin.last m) + ∑ t, e t := by
  calc
    _ ≤ ∑ t, (F t.castSucc - F t.succ + e t) :=
      Finset.sum_le_sum (fun t _ => by linarith [hstep t])
    _ = _ := by rw [Finset.sum_add_distrib, sum_successive_difference]

noncomputable def finiteBoundaryCount {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    (step : Fin m → E) (r : ℝ) : ℝ := by
  classical
  exact ∑ t, if ‖step t‖ = r then 1 else 0

theorem finiteBoundaryCount_nonneg {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    (step : Fin m → E) (r : ℝ) : 0 ≤ finiteBoundaryCount step r := by
  classical
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> norm_num

theorem boundary_power_budget {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    (step : Fin m → E) (r A : ℝ) (hA : 0 ≤ A) (q : ℕ) :
    A * r ^ q * finiteBoundaryCount step r ≤ ∑ t, A * ‖step t‖ ^ q := by
  classical
  rw [finiteBoundaryCount, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : ‖step t‖ = r
  · simp [ht]
  · simp only [if_neg ht, mul_zero]
    positivity

/-- A gap bound and noisy descent control how often a path takes a full-radius step. -/
theorem finite_boundary_descent_budget {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    (F : Fin (m + 1) → ℝ) (step : Fin m → E) (ζ : Fin m → ℝ)
    (r A D : ℝ) (hA : 0 ≤ A) (p : ℕ)
    (hstep : ∀ t, F t.succ ≤ F t.castSucc - A * ‖step t‖ ^ (p + 1) +
      r * ζ t + D * r ^ (p + 1)) :
    A * r ^ (p + 1) * finiteBoundaryCount step r ≤
      F 0 - F (Fin.last m) + r * ∑ t, ζ t + (m : ℝ) * D * r ^ (p + 1) := by
  apply (boundary_power_budget step r A hA (p + 1)).trans
  have hb := finite_descent_budget F (fun t => A * ‖step t‖ ^ (p + 1))
    (fun t => r * ζ t + D * r ^ (p + 1)) (fun t => by dsimp only; linarith [hstep t])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  rw [← Finset.mul_sum]
  convert hb using 1 <;> ring

end FullJet
