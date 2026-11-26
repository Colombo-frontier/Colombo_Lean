import NCConcave16991.FiniteProcess
import NCConcave16991.Minibatch

/-! # Independent uniform selection from an actual finite stochastic history -/

open MeasureTheory
open scoped BigOperators

namespace NCConcave16991.FiniteProcess

noncomputable section

variable {I : Type*} [Finite I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Discard exactly the last `extra` draws of a chronological history. -/
def drop (t : ℕ) : (extra : ℕ) → History I (t + extra) → History I t
  | 0, h => h
  | extra + 1, h => drop t extra h.1

/-- The actual prefix, recursively discarding later draws and using none of them. -/
def historyPrefix (t : ℕ) : (T : ℕ) → t ≤ T → History I T → History I t
  | 0, ht, h => by
      have ht0 : t = 0 := by omega
      subst t
      exact h
  | T + 1, ht, h => if heq : t = T + 1 then
      cast (congrArg (History I) heq.symm) h
    else historyPrefix t T (by omega) h.1
variable (ν : Measure I) [IsProbabilityMeasure ν]

theorem integral_drop (t extra : ℕ) (f : History I t → ℝ) :
    (∫ h, f (drop t extra h) ∂law ν (t + extra)) = ∫ h, f h ∂law ν t := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    change (∫ h : History I ((t + extra) + 1), f (drop t extra h.1)
      ∂law ν ((t + extra) + 1)) = _
    exact (integral_previous ν (t + extra) (fun h ↦ f (drop t extra h))).trans ih

theorem integral_prefix (t T : ℕ) (ht : t ≤ T) (f : History I t → ℝ) :
    (∫ h, f (historyPrefix t T ht h) ∂law ν T) = ∫ h, f h ∂law ν t := by
  induction T generalizing t with
  | zero =>
    have ht0 : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases heq : t = T + 1
    · subst t
      simp [historyPrefix]
    · have ht' : t ≤ T := by omega
      calc
        _ = ∫ h : History I (T + 1), f (historyPrefix t T ht' h.1) ∂law ν (T + 1) := by
          apply integral_congr_ae
          filter_upwards with h
          congr 1
          simp [historyPrefix, heq]
        _ = ∫ h, f (historyPrefix t T ht' h) ∂law ν T := integral_previous ν T (fun h ↦ f (historyPrefix t T ht' h))
        _ = _ := ih t ht' f
/-- A final independent uniform index selects a point computed from its actual
prefix. This is an explicit random variable on one fixed finite seed space. -/
def select {E : Type*} (point : (t : ℕ) → History I t → E) {T : ℕ}
    (ω : History I T × Fin T) : E :=
  point ω.2 (historyPrefix ω.2 T (Nat.le_of_lt ω.2.isLt) ω.1)

theorem uniform_prefix_expectation {T : ℕ} [NeZero T]
    [MeasurableSpace (Fin T)] [MeasurableSingletonClass (Fin T)]
    (observable : (t : ℕ) → History I t → ℝ) :
    (∫ ω : History I T × Fin T, select observable ω
      ∂(law ν T).prod (uniformIndexLaw T)) =
        (∑ t ∈ Finset.range T, ∫ h, observable t h ∂law ν t) / T := by
  rw [integral_prod_symm _ Integrable.of_finite]
  have hprefix (j : Fin T) :
      (∫ h, select observable (h, j) ∂law ν T) = ∫ h, observable j h ∂law ν j :=
    integral_prefix ν j T (Nat.le_of_lt j.isLt) (observable j)
  simp_rw [hprefix]
  rw [uniformIndexLaw, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ ∫ h, observable t h ∂law ν t)]
  ring

end

end NCConcave16991.FiniteProcess


