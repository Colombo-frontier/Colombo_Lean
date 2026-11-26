import Bilevel.AcceleratedInner

/-! Scalar stage and batch accounting for `acc:lem:inner`. The recurrence is
an explicit input here; its analytic one-step derivation is in AcceleratedInner.
This file alone does not construct a stochastic oracle execution. -/

noncomputable section
open scoped BigOperators

namespace Bilevel.AcceleratedInner

def stageBudget (U₀ : ℝ) (s : ℕ) : ℝ := U₀ / 2 ^ s

def stageBatch (M α σ U : ℝ) : ℕ := max 1 ⌈2 * σ ^ 2 / (M * α * U)⌉₊

def stageLength (α : ℝ) : ℕ := ⌈α⁻¹ * Real.log 4⌉₊

theorem stageLength_contracts {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 - α) ^ stageLength α ≤ 1 / 4 := by
  have he : 1 - α ≤ Real.exp (-α) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-α)
  have hn : α⁻¹ * Real.log 4 ≤ (stageLength α : ℝ) := Nat.le_ceil _
  have hn' : Real.log 4 ≤ α * (stageLength α : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hn hα.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul] using hh
  calc
    _ ≤ (Real.exp (-α)) ^ stageLength α :=
      pow_le_pow_left₀ (sub_nonneg.mpr hα1) he _
    _ = Real.exp (-(α * (stageLength α : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (neg_le_neg hn')
    _ = 1 / 4 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num

theorem stageLength_upper {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (stageLength α : ℝ) ≤ (Real.log 4 + 1) / α := by
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hc := Nat.ceil_lt_add_one (mul_nonneg (inv_nonneg.mpr hα.le) hl)
  have hi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr hα1
  change (⌈α⁻¹ * Real.log 4⌉₊ : ℝ) ≤ _
  calc
    _ ≤ α⁻¹ * Real.log 4 + 1 := hc.le
    _ ≤ α⁻¹ * Real.log 4 + α⁻¹ := add_le_add_left hi _
    _ = _ := by ring

theorem stageBatch_pos (M α σ U : ℝ) : 0 < stageBatch M α σ U :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem stageBatch_upper {M α σ U : ℝ} (hM : 0 < M) (hα : 0 < α) (hU : 0 < U) :
    (stageBatch M α σ U : ℝ) ≤ 2 + 2 * σ ^ 2 / (M * α * U) := by
  have hn : 0 ≤ 2 * σ ^ 2 / (M * α * U) := by positivity
  have hc := Nat.ceil_lt_add_one hn
  unfold stageBatch
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

theorem stageBatch_floor {M α σ U : ℝ} (hM : 0 < M) (hα : 0 < α) (hU : 0 < U) :
    σ ^ 2 / ((stageBatch M α σ U : ℝ) * M * α) ≤ U / 2 := by
  have hB : 0 < (stageBatch M α σ U : ℝ) := by exact_mod_cast stageBatch_pos M α σ U
  have hNat : ⌈2 * σ ^ 2 / (M * α * U)⌉₊ ≤ stageBatch M α σ U := le_max_right _ _
  have hb : 2 * σ ^ 2 / (M * α * U) ≤ (stageBatch M α σ U : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNat)
  have hc := (div_le_iff₀ (by positivity : 0 < M * α * U)).mp hb
  apply (div_le_iff₀ (by positivity : 0 < (stageBatch M α σ U : ℝ) * M * α)).mpr
  nlinarith

/-- One stage halves the certified potential under the actual prescribed
batch size and an accelerated contraction horizon. -/
theorem stage_halving (a : ℕ → ℝ) {M α σ U : ℝ}
    (hM : 0 < M) (hα : 0 < α) (hα1 : α ≤ 1) (hU : 0 < U)
    (hstart : a 0 ≤ 2 * U) (K : ℕ) (hK : (1 - α) ^ K ≤ 1 / 4)
    (hstep : ∀ n, a (n + 1) ≤ (1 - α) * a n +
      σ ^ 2 / ((stageBatch M α σ U : ℝ) * M)) : a K ≤ U := by
  have hB : 0 < (stageBatch M α σ U : ℝ) := by exact_mod_cast stageBatch_pos M α σ U
  have hq : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hf : 0 ≤ σ ^ 2 / ((stageBatch M α σ U : ℝ) * M * α) := by positivity
  have he : σ ^ 2 / ((stageBatch M α σ U : ℝ) * M) =
      (1 - (1 - α)) * (σ ^ 2 / ((stageBatch M α σ U : ℝ) * M * α)) := by
    field_simp
    ring
  have hb := StochasticInner.affine_recurrence_floor a hq hf
    (fun n => by rw [← he]; exact hstep n) K
  have hc := mul_le_mul_of_nonneg_left hstart (pow_nonneg hq K)
  have hd := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 2 * U)
  have hn := stageBatch_floor (σ := σ) hM hα hU
  linarith

theorem stageBudget_pos {U₀ : ℝ} (hU : 0 < U₀) (s : ℕ) : 0 < stageBudget U₀ s := by
  unfold stageBudget
  positivity

theorem stageBudget_half (U₀ : ℝ) (s : ℕ) :
    stageBudget U₀ (s + 1) = stageBudget U₀ s / 2 := by
  simp [stageBudget, pow_succ, div_mul_eq_div_div]

theorem reciprocal_stage_sum (U₀ : ℝ) (S : ℕ) :
    (∑ s ∈ Finset.range S, (stageBudget U₀ (s + 1))⁻¹) =
      (2 ^ (S + 1) - 2) / U₀ := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [Finset.sum_range_succ, ih]
    unfold stageBudget
    rw [inv_div]
    simp only [pow_succ]
    ring

theorem reciprocal_stage_sum_le {U₀ : ℝ} (hU : 0 < U₀) (S : ℕ) :
    (∑ s ∈ Finset.range S, (stageBudget U₀ (s + 1))⁻¹) ≤
      2 / stageBudget U₀ S := by
  rw [reciprocal_stage_sum U₀ S]
  unfold stageBudget
  rw [div_div_eq_mul_div, pow_succ]
  have he : (2 ^ S * 2 - 2 : ℝ) ≤ 2 * 2 ^ S := by linarith
  simpa only [mul_comm] using div_le_div_of_nonneg_right he hU.le

/-- The total batch count has no initialization logarithm multiplying its
noise term. Only the deterministic `2 S` contribution retains the stage count. -/
theorem total_batches_bound {M α σ U₀ : ℝ}
    (hM : 0 < M) (hα : 0 < α) (hU : 0 < U₀) (S : ℕ) :
    (∑ s ∈ Finset.range S, (stageBatch M α σ (stageBudget U₀ (s + 1)) : ℝ)) ≤
      2 * (S : ℝ) + 4 * σ ^ 2 / (M * α * stageBudget U₀ S) := by
  have hcoef : 0 ≤ 2 * σ ^ 2 / (M * α) := by positivity
  calc
    _ ≤ ∑ s ∈ Finset.range S,
        (2 + (2 * σ ^ 2 / (M * α)) * (stageBudget U₀ (s + 1))⁻¹) := by
      apply Finset.sum_le_sum
      intro s _
      convert stageBatch_upper hM hα (stageBudget_pos hU (s + 1)) using 1
      ring
    _ = 2 * (S : ℝ) + (2 * σ ^ 2 / (M * α)) *
        (∑ s ∈ Finset.range S, (stageBudget U₀ (s + 1))⁻¹) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      ring
    _ ≤ 2 * (S : ℝ) + (2 * σ ^ 2 / (M * α)) * (2 / stageBudget U₀ S) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (reciprocal_stage_sum_le hU S) hcoef) _
    _ = _ := by ring

def dyadicStageCount (U T : ℝ) : ℕ := ⌈Real.log (U / T) / Real.log 2⌉₊

theorem dyadicStageCount_bounds {U T : ℝ} (hT : 0 < T) (hTU : T < U) :
    T / 2 < stageBudget U (dyadicStageCount U T) ∧
      stageBudget U (dyadicStageCount U T) ≤ T ∧
      (dyadicStageCount U T : ℝ) ≤ Real.log (U / T) / Real.log 2 + 1 := by
  have hU : 0 < U := hT.trans hTU
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 1 < U / T := (one_lt_div hT).mpr hTU
  have hlog : 0 ≤ Real.log (U / T) := Real.log_nonneg hr.le
  have hn : Real.log (U / T) / Real.log 2 ≤ (dyadicStageCount U T : ℝ) := Nat.le_ceil _
  have hn' : (dyadicStageCount U T : ℝ) < Real.log (U / T) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hlog hlog2.le)
  have hp : 0 < (2 : ℝ) ^ dyadicStageCount U T := by positivity
  have hlo : U / T ≤ (2 : ℝ) ^ dyadicStageCount U T := by
    have hh := (div_le_iff₀ hlog2).mp hn
    have he := Real.exp_le_exp.mpr hh
    simpa only [Real.exp_log (div_pos hU hT), Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hhi : (2 : ℝ) ^ dyadicStageCount U T < 2 * (U / T) := by
    have hh := mul_lt_mul_of_pos_right hn' hlog2
    have he := Real.exp_lt_exp.mpr hh
    have hid : (Real.log (U / T) / Real.log 2 + 1) * Real.log 2 =
        Real.log (U / T) + Real.log 2 := by field_simp
    rw [hid, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (div_pos hU hT)] at he
    simpa only [mul_comm] using he
  refine ⟨?_, ?_, hn'.le⟩
  · unfold stageBudget
    apply (lt_div_iff₀ hp).mpr
    have hh := (lt_div_iff₀ hT).mp (show (2 : ℝ) ^ dyadicStageCount U T < 2 * U / T by
      simpa only [mul_div_assoc] using hhi)
    nlinarith
  · unfold stageBudget
    apply (div_le_iff₀ hp).mpr
    have hh := (div_le_iff₀ hT).mp hlo
    nlinarith

/-- Explicit call accounting for all stages. The noise contribution is
independent of the number of initialization stages. -/
theorem scheduled_calls_bound {M μ α σ U T : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ) (hT : 0 < T) (hTU : T < U) :
    let S := dyadicStageCount U T
    (stageLength α : ℝ) *
      (∑ s ∈ Finset.range S, (stageBatch M α σ (stageBudget U (s + 1)) : ℝ)) ≤
      2 * (Real.log 4 + 1) * (S : ℝ) / α +
        8 * (Real.log 4 + 1) * σ ^ 2 / (μ * T) := by
  dsimp only
  let S := dyadicStageCount U T
  have hU : 0 < U := hT.trans hTU
  have hend := (dyadicStageCount_bounds hT hTU).1
  have hUS : 0 < stageBudget U S := stageBudget_pos hU S
  have hc : 0 < Real.log 4 + 1 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hs := total_batches_bound (σ := σ) hM hα hU S
  have hk := stageLength_upper hα hα1
  have hb := mul_le_mul hk hs
    (Finset.sum_nonneg (fun s _ => Nat.cast_nonneg _)) (by positivity : 0 ≤ (Real.log 4 + 1) / α)
  have hid : (Real.log 4 + 1) / α *
      (2 * (S : ℝ) + 4 * σ ^ 2 / (M * α * stageBudget U S)) =
      2 * (Real.log 4 + 1) * (S : ℝ) / α +
        4 * (Real.log 4 + 1) * σ ^ 2 / (μ * stageBudget U S) := by
    rw [← hrel]
    field_simp
    ring
  rw [hid] at hb
  apply hb.trans
  apply add_le_add_left
  apply (div_le_div_iff₀ (mul_pos hμ hUS) (mul_pos hμ hT)).mpr
  have hh : T ≤ 2 * stageBudget U S := by dsimp [S]; linarith
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ 4 * (Real.log 4 + 1) * σ ^ 2 * μ)
  nlinarith

/-- Carrying both accelerated states across stages, as prescribed in the
manuscript, requires no restart penalty in the potential accounting. -/
theorem staged_potential_bound (A : ℕ → ℕ → ℝ) {M α σ U : ℝ}
    (hM : 0 < M) (hα : 0 < α) (hα1 : α ≤ 1) (hU : 0 < U)
    (hinit : A 0 0 ≤ U)
    (hcarry : ∀ s, A (s + 1) 0 = A s (stageLength α))
    (hstep : ∀ s n, A s (n + 1) ≤ (1 - α) * A s n +
      σ ^ 2 / ((stageBatch M α σ (stageBudget U (s + 1)) : ℝ) * M)) (s : ℕ) :
    A s 0 ≤ stageBudget U s := by
  induction s with
  | zero => simpa [stageBudget] using hinit
  | succ s ih =>
    rw [hcarry s]
    apply stage_halving (A s) hM hα hα1 (stageBudget_pos hU (s + 1))
      _ (stageLength α) (stageLength_contracts hα hα1) (hstep s)
    rw [stageBudget_half]
    linarith

theorem scheduled_potential_target (A : ℕ → ℕ → ℝ) {M α σ U T : ℝ}
    (hM : 0 < M) (hα : 0 < α) (hα1 : α ≤ 1) (hT : 0 < T) (hTU : T < U)
    (hinit : A 0 0 ≤ U)
    (hcarry : ∀ s, A (s + 1) 0 = A s (stageLength α))
    (hstep : ∀ s n, A s (n + 1) ≤ (1 - α) * A s n +
      σ ^ 2 / ((stageBatch M α σ (stageBudget U (s + 1)) : ℝ) * M)) :
    A (dyadicStageCount U T) 0 ≤ T :=
  (staged_potential_bound A hM hα hα1 (hT.trans hTU) hinit hcarry hstep _).trans
    (dyadicStageCount_bounds hT hTU).2.1

end Bilevel.AcceleratedInner
