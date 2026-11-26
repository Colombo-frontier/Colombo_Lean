import NCConcave16991.UpperRecurrence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Optimized public persistent-estimator epoch and integer budgets -/

open scoped BigOperators

namespace NCConcave16991

noncomputable section

def persistentEpochLength (n : ℕ) (κ : ℝ) : ℕ :=
  max 1 (Nat.floor (Real.sqrt ((n : ℝ) / κ)))

theorem persistentEpochLength_pos (n : ℕ) (κ : ℝ) :
    0 < persistentEpochLength n κ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem persistentEpochLength_bounds {n : ℕ} {κ : ℝ} (hn : 0 < n) (hκ : 1 ≤ κ) :
    (n : ℝ) / persistentEpochLength n κ ≤ 2 * Real.sqrt ((n : ℝ) * κ) ∧
      κ * persistentEpochLength n κ ≤ κ ^ 2 + Real.sqrt ((n : ℝ) * κ) := by
  let x := Real.sqrt ((n : ℝ) / κ)
  let q := persistentEpochLength n κ
  have hκp : 0 < κ := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (0 : ℝ) < q := by exact_mod_cast persistentEpochLength_pos n κ
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = (n : ℝ) / κ := Real.sq_sqrt (div_nonneg hnr.le hκp.le)
  have hroot : κ * x = Real.sqrt ((n : ℝ) * κ) := by
    apply (sq_eq_sq₀ (mul_nonneg hκp.le hx) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, hxsq, Real.sq_sqrt (mul_nonneg hnr.le hκp.le)]
    field_simp [hκp.ne']
  have hnid : (n : ℝ) = κ * x ^ 2 := by rw [hxsq]; field_simp [hκp.ne']
  have hfloor := Nat.lt_floor_add_one x
  have hfloorq : (Nat.floor x : ℝ) ≤ q := by
    exact_mod_cast (show Nat.floor x ≤ q from le_max_right _ _)
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (show 1 ≤ q from le_max_left _ _)
  have hxq : x ≤ 2 * q := by linarith
  have hqbound : (q : ℝ) ≤ 1 + x := by
    change ((max 1 (Nat.floor x) : ℕ) : ℝ) ≤ 1 + x
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · exact (Nat.floor_le hx).trans (by linarith)
  constructor
  · apply (div_le_iff₀ hq).2
    rw [← hroot, hnid]
    have hh := mul_le_mul_of_nonneg_left hxq (mul_nonneg hκp.le hx)
    nlinarith only [hh]
  · rw [← hroot]
    have hh := mul_le_mul_of_nonneg_left hqbound hκp.le
    nlinarith only [hh, mul_nonneg hκp.le (sub_nonneg.mpr hκ)]

theorem persistent_integer_cost_bounds {n : ℕ} {κ : ℝ}
    (hn : 0 < n) (hκ : 1 ≤ κ) :
    (persistentBatchSize κ (persistentEpochLength n κ) : ℝ) ≤
      4097 * (Real.sqrt ((n : ℝ) * κ) + κ ^ 2) ∧
    (persistentInnerSteps κ : ℝ) ≤ 4294967297 * κ ^ 2 := by
  have hq := persistentEpochLength_pos n κ
  have he := (persistentEpochLength_bounds hn hκ).2
  have hb := (persistentBatchSize_bounds hκ hq).2.2
  have hi := (persistentInnerSteps_bounds κ).2
  have hk : 1 ≤ κ ^ 2 := by nlinarith
  have hs : 0 ≤ Real.sqrt ((n : ℝ) * κ) := Real.sqrt_nonneg _
  constructor
  · nlinarith only [hb, he, hk, hs]
  · norm_num at hi
    linarith only [hi, hk]

theorem persistentQueryBudget_real_bound (n q b k S : ℕ) (hq : 0 < q) :
    (persistentQueryBudget n q b k S : ℝ) ≤
      2 * n + (S : ℝ) * ((n : ℝ) / q + 2 * b + 2 * k) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : (((S + q - 1) / q : ℕ) : ℝ) ≤ (S : ℝ) / q + 1 := by
    have hnat : ((S + q - 1) / q) * q ≤ S + q :=
      (Nat.div_mul_le_self (S + q - 1) q).trans (Nat.sub_le _ _)
    have hh : (((S + q - 1) / q : ℕ) : ℝ) * (q : ℝ) ≤ (S : ℝ) + q := by
      exact_mod_cast hnat
    have hh' := (le_div_iff₀ hqr).2 hh
    convert hh' using 1 <;> field_simp [hqr.ne'] <;> ring
  have hn := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simp only [persistentQueryBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat]
  have hid : (S : ℝ) * ((n : ℝ) / q) = (n : ℝ) * ((S : ℝ) / q) := by ring
  nlinarith only [hn, hid]

/-- A fully explicit universal constant bounds the actual integer ceilings and
refresh overhead at the optimized public epoch length. -/
theorem persistent_optimized_budget {n : ℕ} {κ A : ℝ}
    (hn : 0 < n) (hκ : 1 ≤ κ) (hA : 0 ≤ A) :
    (persistentQueryBudget n (persistentEpochLength n κ)
      (persistentBatchSize κ (persistentEpochLength n κ))
      (persistentInnerSteps κ) (persistentOuterSteps A) : ℝ) ≤
        (2 : ℝ) ^ 48 * ((n : ℝ) + (1 + A) *
          (Real.sqrt ((n : ℝ) * κ) + κ ^ 2)) := by
  let R := Real.sqrt ((n : ℝ) * κ)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg _
  have hq := persistentEpochLength_pos n κ
  have he := (persistentEpochLength_bounds hn hκ).1
  obtain ⟨hb, hi⟩ := persistent_integer_cost_bounds hn hκ
  have hstep : (n : ℝ) / persistentEpochLength n κ +
      2 * (persistentBatchSize κ (persistentEpochLength n κ) : ℝ) +
      2 * (persistentInnerSteps κ : ℝ) ≤ (2 : ℝ) ^ 34 * (R + κ ^ 2) := by
    norm_num
    nlinarith only [he, hb, hi, hR, hκ2]
  have hS := (persistentOuterSteps_bounds hA).2.2
  have hS' : (persistentOuterSteps A : ℝ) ≤ 4097 * (1 + A) := by linarith
  have hbase := persistentQueryBudget_real_bound n (persistentEpochLength n κ)
    (persistentBatchSize κ (persistentEpochLength n κ)) (persistentInnerSteps κ)
    (persistentOuterSteps A) hq
  have hm := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg (persistentOuterSteps A))
  have hs := mul_le_mul_of_nonneg_right hS'
    (show 0 ≤ (2 : ℝ) ^ 34 * (R + κ ^ 2) by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hw : 0 ≤ (1 + A) * (R + κ ^ 2) := mul_nonneg (by linarith) (add_nonneg hR hκ2)
  change _ ≤ (2 : ℝ) ^ 48 * ((n : ℝ) + (1 + A) * (R + κ ^ 2))
  norm_num at hm hs ⊢
  nlinarith only [hbase, hm, hs, hn0, hw]

end

end NCConcave16991
