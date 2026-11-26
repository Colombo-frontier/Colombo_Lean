import MasterWeights254
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
open scoped BigOperators
namespace Paper254

def finiteAffinity {ι : Type*} [Fintype ι] (p q : ProbabilityWeights ι) : ℝ :=
  ∑ i, Real.sqrt (p.weight i)*Real.sqrt (q.weight i)

/-- A two-point estimation inequality proved directly by finite Cauchy--Schwarz.
It applies to every real-valued estimator, without a boundedness premise. -/
theorem finite_two_point_risk {ι : Type*} [Fintype ι] (p q : ProbabilityWeights ι)
    (θ : ℝ) (x : ι → ℝ) :
    θ^2*(finiteAffinity p q)^2 ≤
      (∑ i, (p.weight i*(x i-θ)^2+q.weight i*(x i+θ)^2))/2 := by
  let a : ι × Bool → ℝ := fun z => if z.2 then Real.sqrt (q.weight z.1) else Real.sqrt (p.weight z.1)
  let b : ι × Bool → ℝ := fun z => if z.2 then Real.sqrt (p.weight z.1)*(θ-x z.1) else Real.sqrt (q.weight z.1)*(θ+x z.1)
  have hab : (∑ z, a z*b z) = 2*θ*finiteAffinity p q := by
    rw [Fintype.sum_prod_type]
    unfold finiteAffinity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [a,b]
    ring
  have ha : (∑ z, (a z)^2) = 2 := by
    rw [Fintype.sum_prod_type]
    simp only [a, Bool.false_eq_true, if_false, if_true, Fintype.sum_bool]
    simp_rw [Real.sq_sqrt (p.nonneg _), Real.sq_sqrt (q.nonneg _)]
    rw [Finset.sum_add_distrib, p.total, q.total]
    norm_num
  have hb : (∑ z, (b z)^2) = ∑ i, (p.weight i*(x i-θ)^2+q.weight i*(x i+θ)^2) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp [b, mul_pow, Real.sq_sqrt (p.nonneg i), Real.sq_sqrt (q.nonneg i)]
    ring
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [hab,ha,hb] at hh
  nlinarith

theorem affinity_risk_half {ι : Type*} [Fintype ι] (p q : ProbabilityWeights ι)
    (θ : ℝ) (x : ι → ℝ) (h : (3/4 : ℝ) ≤ finiteAffinity p q) :
    θ^2/2 ≤ (∑ i, (p.weight i*(x i-θ)^2+q.weight i*(x i+θ)^2))/2 := by
  have hh := finite_two_point_risk p q θ x
  have hs : (1/2 : ℝ) ≤ (finiteAffinity p q)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg θ)
  nlinarith

end Paper254
#print axioms Paper254.finite_two_point_risk
