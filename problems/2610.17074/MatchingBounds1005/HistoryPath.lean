import MatchingBounds1005.SeededKernelKL
import MatchingBounds1005.InnovationEnergy

/-!
# Paths of the actual finite adaptive histories

Every finite history is realized by an initial seed and a sequence of raw
answers. Along this path the exposed row spaces are nested and recursive
cumulative costs are ordinary finite sums.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatchingBounds1005.HistoryPath
open SequentialPosterior GaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ}

def path (seed : Ω) (answers : ℕ → Fin T → ℝ) : (n : ℕ) → History Ω T n
  | 0 => seed
  | n + 1 => (path seed answers n, answers n)

theorem path_congr (seed : Ω) (answers answers' : ℕ → Fin T → ℝ)
    (n : ℕ) (heq : ∀ k < n, answers k = answers' k) :
    path seed answers n = path seed answers' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih (fun k hk => heq k (Nat.lt_succ_of_lt hk))) (heq n (Nat.lt_succ_self n))

theorem exists_path (n : ℕ) (h : History Ω T n) :
    ∃ seed answers, path seed answers n = h := by
  induction n with
  | zero => exact ⟨h, fun _ _ => 0, rfl⟩
  | succ n ih =>
      obtain ⟨seed, answers, ha⟩ := ih h.1
      refine ⟨seed, fun k => if k = n then h.2 else answers k, ?_⟩
      change (path seed (fun k => if k = n then h.2 else answers k) n, _) = h
      have hp : path seed (fun k => if k = n then h.2 else answers k) n = path seed answers n := by
        apply path_congr
        intro k hk
        rw [if_neg (Nat.ne_of_lt hk)]
      simp only [hp, ha, if_pos rfl, ite_true, Prod.eta]

theorem cumulativeCost_path (cost : (n : ℕ) → History Ω T n → ℝ)
    (seed : Ω) (answers : ℕ → Fin T → ℝ) (n : ℕ) :
    SeededKernelKL.cumulativeCost cost n (path seed answers n) =
      ∑ k ∈ Finset.range n, cost k (path seed answers k) := by
  induction n with
  | zero => simp [SeededKernelKL.cumulativeCost]
  | succ n ih =>
      simp only [path, SeededKernelKL.cumulativeCost, ih, Finset.sum_range_succ]

theorem cumulativeCost_le_of_path (cost : (n : ℕ) → History Ω T n → ℝ)
    (n : ℕ) (cap : ℝ)
    (hc : ∀ seed answers, (∑ k ∈ Finset.range n, cost k (path seed answers k)) ≤ cap)
    (h : History Ω T n) : SeededKernelKL.cumulativeCost cost n h ≤ cap := by
  obtain ⟨seed, answers, rfl⟩ := exists_path n h
  rw [cumulativeCost_path]
  exact hc seed answers

def pathExposure (A : RowProtocol Ω d T) (seed : Ω) (answers : ℕ → Fin T → ℝ)
    (n : ℕ) : Submodule ℝ (Vec d) := exposure A.rows n (path seed answers n)

theorem pathExposure_monotone (A : RowProtocol Ω d T) (seed : Ω)
    (answers : ℕ → Fin T → ℝ) : Monotone (pathExposure A seed answers) := by
  apply monotone_nat_of_le_succ
  intro n
  exact A.nested n (path seed answers n)

theorem pathExposure_zero (A : RowProtocol Ω d T) (seed : Ω)
    (answers : ℕ → Fin T → ℝ) : pathExposure A seed answers 0 = ⊥ := rfl

end MatchingBounds1005.HistoryPath

