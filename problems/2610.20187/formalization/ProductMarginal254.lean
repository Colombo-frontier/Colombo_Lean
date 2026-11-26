import BernoulliAffinity254
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open scoped BigOperators
namespace Paper254

def finiteExpectation {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (f : ι → ℝ) : ℝ :=
  ∑ i, p.weight i*f i

theorem product_expectation_last {n : ℕ} (p : Fin (n+1) → ProbabilityWeights Bool)
    (F : (Fin (n+1) → Bool) → ℝ) :
    finiteExpectation (productWeights p) F =
      ∑ v : Fin n → Bool, (productWeights (fun i => p i.castSucc)).weight v*
        ∑ y : Bool, (p (Fin.last n)).weight y*F (Fin.snoc v y) := by
  classical
  unfold finiteExpectation
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  change (∏ i : Fin (n+1), (p i).weight ((Fin.snoc v y : Fin (n+1) → Bool) i))*F (Fin.snoc v y) = _
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, productWeights]
  ring

theorem product_marginal_last {n : ℕ} (p : Fin (n+1) → ProbabilityWeights Bool)
    (F : (Fin n → Bool) → ℝ) :
    finiteExpectation (productWeights p) (fun ω => F (fun i => ω i.castSucc)) =
      finiteExpectation (productWeights (fun i => p i.castSucc)) F := by
  rw [product_expectation_last]
  simp only [Fin.snoc_castSucc]
  simp_rw [← Finset.sum_mul, ProbabilityWeights.total, one_mul]
  rfl

def prefixRestriction {n N : ℕ} (h : n ≤ N) (ω : Fin N → Bool) : Fin n → Bool :=
  fun i => ω ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem product_marginal_prefix (N n : ℕ) (h : n ≤ N)
    (p : Fin N → ProbabilityWeights Bool) (F : (Fin n → Bool) → ℝ) :
    finiteExpectation (productWeights p) (fun ω => F (prefixRestriction h ω)) =
      finiteExpectation (productWeights (fun i : Fin n => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩)) F := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases he : n = N+1
    · subst n
      rfl
    · have hn : n ≤ N := by omega
      have hh := product_marginal_last p (fun v => F (prefixRestriction hn v))
      have hi := ih hn (fun i => p i.castSucc)
      exact hh.trans hi

theorem finiteExpectation_const {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι) (c : ℝ) :
    finiteExpectation p (fun _ => c) = c := by
  simp [finiteExpectation, ← Finset.sum_mul, p.total]

end Paper254
#print axioms Paper254.product_marginal_prefix
