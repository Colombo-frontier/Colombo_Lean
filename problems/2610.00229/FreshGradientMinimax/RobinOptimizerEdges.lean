import FreshGradientMinimax.RobinIncrement
import FreshGradientMinimax.RobinEnergyFormula

/-! Every edge at the exact quadratic optimizer is strictly inside the
Huber threshold 1000. Endpoint bounds preserve the original constant 70. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem robinQuadraticOptimizer_apply (n : ℕ) (a b : ℝ) (i : Fin (n + 2)) :
    robinQuadraticOptimizer n a b i = Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) *
      (a * robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1) i -
        b * robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1) i) := by
  simp only [robinQuadraticOptimizer, robinQuadraticSource, robinEndpointSource,
    map_smul, map_sub, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]

theorem robin_optimizer_increment_bound {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) (i : Fin (n + 1)) :
    |robinQuadraticOptimizer n a b i.succ - robinQuadraticOptimizer n a b i.castSucc| ≤
      200 / Real.sqrt (n + 2 : ℕ) := by
  let F := robinInverse (n + 2) (by omega) (EuclideanSpace.single 0 1)
  let L := robinInverse (n + 2) (by omega) (EuclideanSpace.single (Fin.last (n + 1)) 1)
  have hF : |F i.succ - F i.castSucc| ≤ 4 := robinInverse_first_increment hn i
  have hL : |L i.succ - L i.castSucc| ≤ 4 := robinInverse_last_increment hn i
  have h1 := mul_le_mul ha hF (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  have h2 := mul_le_mul hb hL (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have htri := abs_sub (a * (F i.succ - F i.castSucc)) (b * (L i.succ - L i.castSucc))
  rw [abs_mul, abs_mul] at htri
  have hbound : |a * (F i.succ - F i.castSucc) - b * (L i.succ - L i.castSucc)| ≤ 18 := by
    linarith only [h1, h2, htri]
  rw [robinQuadraticOptimizer_apply, robinQuadraticOptimizer_apply]
  change |Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) * (a * F i.succ - b * L i.succ) -
    Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) * (a * F i.castSucc - b * L i.castSucc)| ≤ _
  have he : Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) * (a * F i.succ - b * L i.succ) -
      Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) * (a * F i.castSucc - b * L i.castSucc) =
      Real.sqrt (robinC (n + 2) / (n + 2 : ℕ)) *
        (a * (F i.succ - F i.castSucc) - b * (L i.succ - L i.castSucc)) := by ring
  rw [he, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)).trans
  have hC : 0 ≤ robinC (n + 2) := le_trans (by norm_num) (robin_coefficients_bounds hn).1
  rw [Real.sqrt_div hC, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  nlinarith only [robin_sqrt_C_bound hn]

theorem robin_optimizer_scaled_coordinate {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) (i : Fin (n + 2)) :
    |robinQuadraticOptimizer n a b i / Real.sqrt (n + 2 : ℕ)| ≤ 42 := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr (robin_optimizer_coordinate_bound hn ha hb i)

theorem robin_optimizer_first_edge {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    |(robinIncidence (n + 2) (robinQuadraticOptimizer n a b) + robinEdgeShift n a b) 0| ≤ 70 := by
  rw [robinEdgeVector_first]
  have htri := abs_sub (robinQuadraticOptimizer n a b 0 / Real.sqrt (n + 2 : ℕ))
    (Real.sqrt (robinC (n + 2)) * a)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  have hC := mul_le_mul (robin_sqrt_C_bound hn) ha (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 28 / 3)
  linarith only [htri, hC, robin_optimizer_scaled_coordinate hn ha hb 0]

theorem robin_optimizer_last_edge {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) :
    |(robinIncidence (n + 2) (robinQuadraticOptimizer n a b) + robinEdgeShift n a b)
      (Fin.last (n + 2))| ≤ 70 := by
  rw [robinEdgeVector_last, abs_neg]
  have htri := abs_add (robinQuadraticOptimizer n a b (Fin.last (n + 1)) / Real.sqrt (n + 2 : ℕ))
    (Real.sqrt (robinC (n + 2)) * b)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at htri
  have hC := mul_le_mul (robin_sqrt_C_bound hn) hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 28 / 3)
  linarith only [htri, hC, robin_optimizer_scaled_coordinate hn ha hb (Fin.last (n + 1))]

theorem robin_optimizer_all_edges {n : ℕ} (hn : 10 ≤ n + 2) {a b : ℝ}
    (ha : |a| ≤ 3) (hb : |b| ≤ 3 / 2) (e : Fin (n + 3)) :
    |(robinIncidence (n + 2) (robinQuadraticOptimizer n a b) + robinEdgeShift n a b) e| ≤ 200 := by
  refine Fin.lastCases ?_ (fun j => ?_) e
  · exact (robin_optimizer_last_edge hn ha hb).trans (by norm_num)
  · refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.castSucc_zero]
      exact (robin_optimizer_first_edge hn ha hb).trans (by norm_num)
    · rw [robinEdgeVector_interior]
      apply (robin_optimizer_increment_bound hn ha hb i).trans
      apply div_le_self (by norm_num)
      exact Real.one_le_sqrt.mpr (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) n])

end FreshGradientMinimax
