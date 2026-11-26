import HellingerRisk254
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

noncomputable section
open scoped BigOperators
namespace Paper254

def bernoulliWeights (θ : ℝ) (hθ : |θ| ≤ 1) : ProbabilityWeights Bool where
  weight y := if y then (1+θ)/2 else (1-θ)/2
  nonneg y := by
    have hh := abs_le.mp hθ
    cases y <;> simp only [Bool.false_eq_true, if_false, if_true] <;> linarith
  total := by simp; ring

def productWeights {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : κ → ProbabilityWeights ι) : ProbabilityWeights (κ → ι) where
  weight ω := ∏ k, (p k).weight (ω k)
  nonneg ω := Finset.prod_nonneg (fun k _ => (p k).nonneg (ω k))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [ProbabilityWeights.total, Finset.prod_const_one]

theorem sqrt_finite_product {κ : Type*} (s : Finset κ) (a : κ → ℝ)
    (ha : ∀ k ∈ s, 0 ≤ a k) : Real.sqrt (∏ k ∈ s, a k) = ∏ k ∈ s, Real.sqrt (a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk,
      Real.sqrt_mul (ha k (Finset.mem_insert_self _ _)), ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]

theorem product_affinity {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p q : κ → ProbabilityWeights ι) :
    finiteAffinity (productWeights p) (productWeights q) = ∏ k, finiteAffinity (p k) (q k) := by
  classical
  unfold finiteAffinity
  simp only [productWeights]
  simp_rw [sqrt_finite_product _ _ (fun k _ => (p k).nonneg _),
    sqrt_finite_product _ _ (fun k _ => (q k).nonneg _), ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (k : κ) (i : ι) => Real.sqrt ((p k).weight i)*Real.sqrt ((q k).weight i))).symm

theorem bernoulli_affinity (θ : ℝ) (hθ : |θ| ≤ 1) :
    finiteAffinity (bernoulliWeights θ hθ) (bernoulliWeights (-θ) (by simpa using hθ)) = Real.sqrt (1-θ^2) := by
  have hb := abs_le.mp hθ
  have hp : 0 ≤ (1+θ)/2 := by linarith
  have hn : 0 ≤ (1-θ)/2 := by linarith
  unfold finiteAffinity
  simp only [bernoulliWeights, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  have hneg1 : (1+-θ)/2 = (1-θ)/2 := by ring
  have hneg2 : (1- -θ)/2 = (1+θ)/2 := by ring
  rw [hneg1,hneg2]
  have hs : 0 ≤ 2*(Real.sqrt ((1+θ)/2)*Real.sqrt ((1-θ)/2)) := by positivity
  have he : (2*(Real.sqrt ((1+θ)/2)*Real.sqrt ((1-θ)/2)))^2 = 1-θ^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hn]
    ring
  have hh := Real.sqrt_sq hs
  rw [he] at hh
  nlinarith

theorem bernoulli_affinity_lower (θ : ℝ) (hθ : |θ| ≤ 1) :
    1-θ^2 ≤ Real.sqrt (1-θ^2) := by
  have hb := abs_le.mp hθ
  have hz : 0 ≤ 1-θ^2 := by nlinarith
  have hs := Real.sq_sqrt hz
  have hn := Real.sqrt_nonneg (1-θ^2)
  nlinarith [sq_nonneg θ, mul_nonneg hz (sq_nonneg θ)]

theorem repeated_bernoulli_affinity (n : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    1-(n : ℝ)*θ^2 ≤ finiteAffinity
      (productWeights (fun _ : Fin n => bernoulliWeights θ hθ))
      (productWeights (fun _ : Fin n => bernoulliWeights (-θ) (by simpa using hθ))) := by
  rw [product_affinity]
  simp only [bernoulli_affinity, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs := bernoulli_affinity_lower θ hθ
  have hn := Real.sqrt_nonneg (1-θ^2)
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_right ih hn
    have hc := mul_nonneg (Nat.cast_nonneg n (α := ℝ)) (sq_nonneg θ)
    have hupper : Real.sqrt (1-θ^2) ≤ 1 := by
      have hb := abs_le.mp hθ
      have he := Real.sq_sqrt (show 0 ≤ 1-θ^2 by nlinarith)
      nlinarith [sq_nonneg θ]
    calc
      1-((n : ℝ)+1)*θ^2 ≤ (1-(n : ℝ)*θ^2)*Real.sqrt (1-θ^2) := by
        nlinarith [mul_nonneg hc (show 0 ≤ 1-Real.sqrt (1-θ^2) by linarith)]
      _ ≤ Real.sqrt (1-θ^2)^n*Real.sqrt (1-θ^2) := hh
      _ = Real.sqrt (1-θ^2)^(n+1) := (pow_succ _ _).symm

end Paper254
#print axioms Paper254.repeated_bernoulli_affinity
