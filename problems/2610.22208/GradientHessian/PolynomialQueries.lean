import LowRank.BoundedTwoSidedPolicy
import LowRank.PolicyOutputMap
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-! Exact polynomial-vector evaluation with its actual matrix-product budget.
The measurable policy works on every matrix, without testing a spectral event. -/

namespace GradientHessian.PolynomialQueries

open Matrix Polynomial MeasureTheory LowRank
open scoped BigOperators
noncomputable section
universe u

variable {d : ℕ}

def nextState (a : ℕ → ℝ) (i : ℕ) {S : Type u} [MeasurableSpace S]
    (c : MeasurableStateMap S ((Fin d → ℝ) × (Fin d → ℝ))) :
    MeasurableStateMap (S × (Fin d → ℝ)) ((Fin d → ℝ) × (Fin d → ℝ)) :=
  ⟨fun h => (h.2, (c.1 h.1).2 + a (i + 1) • h.2), by
    apply measurable_snd.prodMk
    apply measurable_pi_lambda
    intro j
    have hc : Measurable (fun h : S × (Fin d → ℝ) => (c.1 h.1).2 j) :=
      (measurable_pi_apply j).comp (c.2.comp measurable_fst).snd
    have hr : Measurable (fun h : S × (Fin d → ℝ) => h.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    exact hc.add (measurable_const.mul hr)⟩

def powersPolicy (a : ℕ → ℝ) : (i n : ℕ) →
    {S : Type u} → [MeasurableSpace S] →
      MeasurableStateMap S ((Fin d → ℝ) × (Fin d → ℝ)) →
        BoundedTwoSidedPolicy d (Fin d → ℝ) n S
  | _, 0, _, _, c => ⟨fun s => (c.1 s).2, c.2.snd⟩
  | i, n + 1, _, _, c =>
      ({stop := ⟨fun _ => false, measurable_const⟩
        output := ⟨fun s => (c.1 s).2, c.2.snd⟩
        query := ⟨fun s => (false, (c.1 s).1), measurable_const.prodMk c.2.fst⟩},
       powersPolicy a (i + 1) n (nextState a i c))

theorem powersPolicy_calls (a : ℕ → ℝ) (i n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (c : MeasurableStateMap S ((Fin d → ℝ) × (Fin d → ℝ)))
    (A : Matrix (Fin d) (Fin d) ℝ) (seed : S) :
    ((powersPolicy a i n c).toProgram d n seed).calls (twoSidedOracle A) = n := by
  induction n generalizing S i with
  | zero => rfl
  | succ n ih =>
    change ((powersPolicy a (i + 1) n (nextState a i c)).toProgram d n
      (seed, twoSidedOracle A (false, (c.1 seed).1))).calls (twoSidedOracle A) + 1 = n + 1
    rw [ih]

theorem powersPolicy_eval (a : ℕ → ℝ) (i n : ℕ)
    {S : Type u} [MeasurableSpace S]
    (c : MeasurableStateMap S ((Fin d → ℝ) × (Fin d → ℝ)))
    (A : Matrix (Fin d) (Fin d) ℝ) (seed : S) :
    runBoundedTwoSided d n (powersPolicy a i n c) A seed =
      (c.1 seed).2 + ∑ j ∈ Finset.range n,
        a (i + j + 1) • ((A ^ (j + 1)) *ᵥ (c.1 seed).1) := by
  induction n generalizing S i with
  | zero => simp [runBoundedTwoSided, powersPolicy, BoundedTwoSidedPolicy.toProgram,
      OracleProgram.eval]
  | succ n ih =>
    rw [runBoundedTwoSided_step]
    simp only [powersPolicy, Bool.false_eq_true, if_false, twoSidedOracle]
    rw [ih]
    simp only [nextState]
    rw [Finset.sum_range_succ']
    have hsum : (∑ j ∈ Finset.range n,
        a (i + 1 + j + 1) • ((A ^ (j + 1)) *ᵥ (A *ᵥ (c.1 seed).1))) =
        ∑ j ∈ Finset.range n,
          a (i + (j + 1) + 1) • ((A ^ (j + 1 + 1)) *ᵥ (c.1 seed).1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.mulVec_mulVec, ← pow_succ]
      congr 2
      omega
    rw [hsum]
    simp only [Nat.add_zero, zero_add, pow_one]
    abel

def initial (p : ℝ[X]) : MeasurableStateMap (Fin d → ℝ)
    ((Fin d → ℝ) × (Fin d → ℝ)) :=
  ⟨fun w => (w, p.coeff 0 • w), measurable_id.prodMk (by
    apply measurable_pi_lambda
    intro j
    exact measurable_const.mul (measurable_pi_apply j))⟩

def polynomialPolicy (p : ℝ[X]) (n : ℕ) :
    BoundedTwoSidedPolicy d (Fin d → ℝ) n (Fin d → ℝ) :=
  powersPolicy p.coeff 0 n (initial p)

theorem polynomialPolicy_calls (p : ℝ[X]) (n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    ((polynomialPolicy p n).toProgram d n w).calls (twoSidedOracle A) = n :=
  powersPolicy_calls _ _ _ _ _ _

theorem finset_sum_mulVec {I : Type*} (s : Finset I)
    (F : I → Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    (∑ i ∈ s, F i) *ᵥ w = ∑ i ∈ s, F i *ᵥ w := by
  exact map_sum (Matrix.mulVec.addMonoidHomLeft w) F s

theorem polynomialPolicy_eval (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n)
    (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    runBoundedTwoSided d n (polynomialPolicy p n) A w = (aeval A p) *ᵥ w := by
  rw [polynomialPolicy, powersPolicy_eval, aeval_eq_sum_range' (Nat.lt_succ_of_le hn)]
  rw [finset_sum_mulVec]
  simp only [initial, ← Algebra.smul_def, Matrix.smul_mulVec_assoc,
    Nat.zero_add]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mulVec, Nat.add_comm 1]
  abel

/-- A fixed measurable postprocessing of the polynomial result is exact and
does not increase the query count. This includes projections, normalization,
and a fixed zero-denominator default. -/
theorem polynomialPolicy_postprocess {O : Type*} [MeasurableSpace O]
    (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n)
    (post : MeasurableStateMap (Fin d → ℝ) O)
    (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    runBoundedTwoSided d n ((polynomialPolicy p n).mapOutput d post n) A w =
        post.1 ((aeval A p) *ᵥ w) ∧
      (((polynomialPolicy p n).mapOutput d post n).toProgram d n w).calls
        (twoSidedOracle A) = n := by
  constructor
  · rw [runBoundedTwoSided_mapOutput, polynomialPolicy_eval p n hn]
  · rw [BoundedTwoSidedPolicy.calls_mapOutput, polynomialPolicy_calls]

end
end GradientHessian.PolynomialQueries
