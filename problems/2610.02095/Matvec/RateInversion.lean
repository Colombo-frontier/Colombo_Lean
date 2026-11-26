import Matvec.RateArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Inverting hard accuracies with an actual integer core size

The core is selected by a natural floor. Bounds hold for every sufficiently
small positive accuracy, rather than only on a subsequence. These scalar
lemmas will be consumed by the actual matrix-game sequence theorem.
-/

namespace Matvec

open Filter
open scoped Topology
noncomputable section

def precisionCoreScale (a r t : ℝ) : ℝ := a * t ^ (2 / 3 : ℝ) / (Real.log t) ^ r
def precisionCore (a r t : ℝ) : ℕ := ⌊precisionCoreScale a r t⌋₊

theorem precisionCoreScale_eventually (a r : ℝ) (ha : 0 < a) (hr : 0 ≤ r) (N₀ : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      0 < t ∧ 2 ≤ Real.log t ∧ Real.exp (Real.exp 1) ≤ t ∧
      0 < precisionCore a r t ∧ N₀ ≤ precisionCore a r t ∧
      precisionCoreScale a r t / 2 ≤ (precisionCore a r t : ℝ) ∧
      (precisionCore a r t : ℝ) ≤ precisionCoreScale a r t ∧
      precisionCoreScale a r t ≤ t := by
  let B : ℝ := N₀ + 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hlittle := (isLittleO_log_rpow_rpow_atTop r (by norm_num : (0 : ℝ) < 2 / 3)).bound
    (div_pos ha hB)
  filter_upwards [hlittle, eventually_ge_atTop (Real.exp (Real.exp 1)),
    Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_gt_atTop 0,
    eventually_ge_atTop (a ^ 3)] with t hl htExp htlog ht hta
  have ht1 : 1 ≤ t := (Real.log_nonneg_iff ht).mp (by linarith)
  have hlog : 0 < Real.log t := by linarith
  have hlpow : 0 < (Real.log t) ^ r := Real.rpow_pos_of_pos hlog _
  have htpow : 0 < t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos ht _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)] at hl
  have hscale : B ≤ precisionCoreScale a r t := by
    apply (le_div_iff₀ hlpow).mpr
    have hh := mul_le_mul_of_nonneg_left hl hB.le
    field_simp at hh ⊢
    nlinarith
  have hscalepos : 0 ≤ precisionCoreScale a r t := hB.le.trans hscale
  have hfloor := Nat.floor_le hscalepos
  have hlt := Nat.lt_floor_add_one (precisionCoreScale a r t)
  have hN₀ : N₀ ≤ precisionCore a r t := Nat.le_floor (by dsimp [B] at hscale; linarith)
  have htwo : 2 ≤ precisionCoreScale a r t := by dsimp [B] at hscale; have := Nat.cast_nonneg (α := ℝ) N₀; linarith
  have hNpos : 0 < precisionCore a r t := by
    apply Nat.floor_pos.mpr
    linarith
  have hhalf : precisionCoreScale a r t / 2 ≤ (precisionCore a r t : ℝ) := by
    change precisionCoreScale a r t < (precisionCore a r t : ℝ) + 1 at hlt
    linarith
  have hat : a ≤ t ^ (1 / 3 : ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg ha.le 3) hta (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have heq : (a ^ 3) ^ (1 / 3 : ℝ) = a := by
      simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast ha.le (by norm_num : (3 : ℕ) ≠ 0)
    rwa [heq] at hh
  have hbase : a * t ^ (2 / 3 : ℝ) ≤ t := by
    calc
      _ ≤ t ^ (1 / 3 : ℝ) * t ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_right hat htpow.le
      _ = t := by rw [← Real.rpow_add ht]; norm_num
  have hlone : 1 ≤ (Real.log t) ^ r := Real.one_le_rpow (by linarith) hr
  have hupper : precisionCoreScale a r t ≤ t := by
    calc
      _ ≤ a * t ^ (2 / 3 : ℝ) := div_le_self (by positivity) hlone
      _ ≤ t := hbase
  exact ⟨ht, htlog, htExp, hNpos, hN₀, hhalf, hfloor, hupper⟩

theorem sourceDenominator_precision_bound (N : ℕ) (t : ℝ)
    (ht : 0 < t) (hlog : 2 ≤ Real.log t) (hbig : Real.exp (Real.exp 1) ≤ t)
    (hN : (N : ℝ) ≤ t) :
    sourceDenominator N ≤ 8 * Real.log t ^ 2 * Real.log (Real.log t) := by
  have ht2 : 2 ≤ t := by
    have hh := Real.log_le_sub_one_of_pos ht
    linarith
  have hlogN : Real.log (N + 2 : ℝ) ≤ 2 * Real.log t := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < N + 2)
      (show (N : ℝ) + 2 ≤ t ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hinner : Real.log (N + Real.exp (Real.exp 1)) ≤ 2 * Real.log t := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < N + Real.exp (Real.exp 1))
      (show (N : ℝ) + Real.exp (Real.exp 1) ≤ t ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hinnerpos : 0 < Real.log (N + Real.exp (Real.exp 1)) := by
    apply Real.log_pos
    have h := Real.one_lt_exp_iff.mpr (Real.exp_pos (1 : ℝ))
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hloglog : Real.log (Real.log (N + Real.exp (Real.exp 1))) ≤
      2 * Real.log (Real.log t) := by
    have hh := Real.log_le_log hinnerpos hinner
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : Real.log t ≠ 0)] at hh
    have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlog
    linarith
  have hlogNpos : 0 ≤ Real.log (N + 2 : ℝ) := Real.log_nonneg (by
    have hn := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hsquare := (sq_le_sq₀ hlogNpos (by linarith : 0 ≤ 2 * Real.log t)).mpr hlogN
  have hproduct := mul_le_mul hsquare hloglog (by linarith [source_loglog_ge_one N])
    (sq_nonneg (2 * Real.log t))
  unfold sourceDenominator
  nlinarith

theorem precisionCore_sourceRate (a r t : ℝ) (ha : 0 < a) (ht : 0 < t)
    (hlog : 2 ≤ Real.log t) (hbig : Real.exp (Real.exp 1) ≤ t)
    (hhalf : precisionCoreScale a r t / 2 ≤ (precisionCore a r t : ℝ))
    (hN : (precisionCore a r t : ℝ) ≤ t) :
    (a / 16) * t ^ (2 / 3 : ℝ) /
      ((Real.log t) ^ (r + 2) * Real.log (Real.log t)) ≤ sourceRate (precisionCore a r t) := by
  let N := precisionCore a r t
  have hL : 0 < Real.log t := by linarith
  have hLL : 0 < Real.log (Real.log t) := Real.log_pos (by linarith)
  have hden := sourceDenominator_precision_bound N t ht hlog hbig hN
  calc
    _ = (precisionCoreScale a r t / 2) / (8 * Real.log t ^ 2 * Real.log (Real.log t)) := by
      rw [Real.rpow_add hL, Real.rpow_two]
      unfold precisionCoreScale
      field_simp
      ring
    _ ≤ (N : ℝ) / (8 * Real.log t ^ 2 * Real.log (Real.log t)) :=
      div_le_div_of_nonneg_right hhalf (by positivity)
    _ ≤ (N : ℝ) / sourceDenominator N :=
      div_le_div_of_nonneg_left (by positivity) (sourceDenominator_pos N) hden
    _ = _ := rfl

theorem eventually_small_reciprocal (P : ℝ → Prop) (h : ∀ᶠ t : ℝ in atTop, P t) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → P ε⁻¹ := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  let B := max T 1
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨B⁻¹, inv_pos.mpr hB, ?_⟩
  intro ε hε hsmall
  have hlarge : B ≤ ε⁻¹ := by
    have hh := one_div_le_one_div_of_le hε hsmall
    simpa only [one_div, inv_inv] using hh
  exact hT _ ((le_max_left _ _).trans hlarge)

theorem ball_precisionCore_accuracy (c t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hN : 0 < precisionCore (c ^ (2 / 3 : ℝ)) 0 t)
    (hfloor : (precisionCore (c ^ (2 / 3 : ℝ)) 0 t : ℝ) ≤
      precisionCoreScale (c ^ (2 / 3 : ℝ)) 0 t) :
    1 / t ≤ c / (precisionCore (c ^ (2 / 3 : ℝ)) 0 t : ℝ) ^ (3 / 2 : ℝ) := by
  let N := precisionCore (c ^ (2 / 3 : ℝ)) 0 t
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := Real.rpow_le_rpow (show (0 : ℝ) ≤ N by positivity) hfloor
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have heq : (precisionCoreScale (c ^ (2 / 3 : ℝ)) 0 t) ^ (3 / 2 : ℝ) = c * t := by
    simp only [precisionCoreScale, Real.rpow_zero, div_one]
    rw [Real.mul_rpow (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg ht.le _),
      ← Real.rpow_mul hc.le, ← Real.rpow_mul ht.le]
    norm_num
  rw [heq] at hp
  exact (div_le_div_iff₀ ht (Real.rpow_pos_of_pos hNpos _)).mpr (by simpa only [one_mul] using hp)

theorem simplex_precisionCore_accuracy (c t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hlog : 2 ≤ Real.log t)
    (hN : 0 < precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t)
    (hfloor : (precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t : ℝ) ≤
      precisionCoreScale ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t)
    (hupper : (precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t : ℝ) ≤ t) :
    1 / t ≤ c /
      ((precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t : ℝ) ^ (3 / 2 : ℝ) *
        Real.sqrt (Real.log (precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t + 2))) := by
  let N := precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < Real.log t := by linarith
  have hspos : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hL
  have hp := Real.rpow_le_rpow (show (0 : ℝ) ≤ N by positivity) hfloor
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have heq : (precisionCoreScale ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t) ^ (3 / 2 : ℝ) =
      c * t / (2 * Real.sqrt (Real.log t)) := by
    unfold precisionCoreScale
    rw [Real.div_rpow (by positivity) (Real.rpow_nonneg hL.le _),
      Real.mul_rpow (by positivity) (Real.rpow_nonneg ht.le _),
      ← Real.rpow_mul (show (0 : ℝ) ≤ c / 2 by positivity), ← Real.rpow_mul ht.le,
      ← Real.rpow_mul hL.le]
    norm_num
    rw [← Real.sqrt_eq_rpow]
    ring
  rw [heq] at hp
  have ht2 : 2 ≤ t := by have hh := Real.log_le_sub_one_of_pos ht; linarith
  have hlogN : Real.log (N + 2 : ℝ) ≤ 2 * Real.log t := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < N + 2)
      (show (N : ℝ) + 2 ≤ t ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogNpos : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by linarith)
  have hsN : Real.sqrt (Real.log (N + 2 : ℝ)) ≤ 2 * Real.sqrt (Real.log t) := by
    have hh := Real.sq_sqrt hlogNpos.le
    have hh' := Real.sq_sqrt hL.le
    nlinarith [Real.sqrt_nonneg (Real.log (N + 2 : ℝ)), Real.sqrt_nonneg (Real.log t)]
  have hprod := mul_le_mul hp hsN (Real.sqrt_nonneg _) (by positivity : 0 ≤ c * t / (2 * Real.sqrt (Real.log t)))
  have hbound : (N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (N + 2 : ℝ)) ≤ c * t := by
    convert hprod using 1
    field_simp
  exact (div_le_div_iff₀ ht (mul_pos (Real.rpow_pos_of_pos hNpos _) (Real.sqrt_pos.mpr hlogNpos))).mpr
    (by simpa only [one_mul] using hbound)

/-- Scalar inversion of the ball accuracy sequence, uniformly at every large
reciprocal accuracy t=1/ε. -/
theorem ball_rate_core_eventually (c : ℝ) (hc : 0 < c) (N₀ : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧
      (c ^ (2 / 3 : ℝ) / 2) * t ^ (2 / 3 : ℝ) ≤ N ∧
      (N : ℝ) ≤ c ^ (2 / 3 : ℝ) * t ^ (2 / 3 : ℝ) ∧
      1 / t ≤ c / (N : ℝ) ^ (3 / 2 : ℝ) ∧
      (c ^ (2 / 3 : ℝ) / 16) * t ^ (2 / 3 : ℝ) /
        (Real.log t ^ 2 * Real.log (Real.log t)) ≤ sourceRate N := by
  filter_upwards [precisionCoreScale_eventually (c ^ (2 / 3 : ℝ)) 0
    (Real.rpow_pos_of_pos hc _) le_rfl N₀] with t ht
  obtain ⟨htpos, htlog, htexp, hNpos, hN₀, hhalf, hfloor, hupper⟩ := ht
  refine ⟨precisionCore (c ^ (2 / 3 : ℝ)) 0 t, hN₀, hNpos, ?_, ?_,
    ball_precisionCore_accuracy c t hc htpos hNpos hfloor, ?_⟩
  · simpa only [precisionCoreScale, Real.rpow_zero, div_one, div_mul_eq_mul_div] using hhalf
  · simpa only [precisionCoreScale, Real.rpow_zero, div_one] using hfloor
  · have hh := precisionCore_sourceRate (c ^ (2 / 3 : ℝ)) 0 t
      (Real.rpow_pos_of_pos hc _) htpos htlog htexp hhalf (hfloor.trans hupper)
    simpa only [zero_add, Real.rpow_two] using hh

/-- The simplex hard core has the extra log^(−1/3) factor, and the query rate
therefore has log^(7/3) in its denominator. -/
theorem simplex_rate_core_eventually (c : ℝ) (hc : 0 < c) (N₀ : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧
      (((c / 2) ^ (2 / 3 : ℝ)) / 2) * t ^ (2 / 3 : ℝ) / (Real.log t) ^ (1 / 3 : ℝ) ≤ N ∧
      (N : ℝ) ≤ (c / 2) ^ (2 / 3 : ℝ) * t ^ (2 / 3 : ℝ) / (Real.log t) ^ (1 / 3 : ℝ) ∧
      1 / t ≤ c / ((N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (N + 2))) ∧
      (((c / 2) ^ (2 / 3 : ℝ)) / 16) * t ^ (2 / 3 : ℝ) /
        ((Real.log t) ^ (7 / 3 : ℝ) * Real.log (Real.log t)) ≤ sourceRate N := by
  have hc' : 0 < (c / 2) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  filter_upwards [precisionCoreScale_eventually ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3)
    hc' (by norm_num) N₀] with t ht
  obtain ⟨htpos, htlog, htexp, hNpos, hN₀, hhalf, hfloor, hupper⟩ := ht
  refine ⟨precisionCore ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t, hN₀, hNpos, ?_, hfloor,
    simplex_precisionCore_accuracy c t hc htpos htlog hNpos hfloor (hfloor.trans hupper), ?_⟩
  · convert hhalf using 1 <;> unfold precisionCoreScale <;> ring
  · have hh := precisionCore_sourceRate ((c / 2) ^ (2 / 3 : ℝ)) (1 / 3) t
      hc' htpos htlog htexp hhalf (hfloor.trans hupper)
    norm_num at hh ⊢
    exact hh

def ballPrecisionRate (ε : ℝ) : ℝ :=
  ε ^ (-(2 / 3 : ℝ)) / (Real.log ε⁻¹ ^ 2 * Real.log (Real.log ε⁻¹))

def simplexPrecisionRate (ε : ℝ) : ℝ :=
  ε ^ (-(2 / 3 : ℝ)) /
    ((Real.log ε⁻¹) ^ (7 / 3 : ℝ) * Real.log (Real.log ε⁻¹))

def simplexCoreRate (ε : ℝ) : ℝ :=
  ε ^ (-(2 / 3 : ℝ)) / (Real.log ε⁻¹) ^ (1 / 3 : ℝ)

theorem ball_rate_core_small (c : ℝ) (hc : 0 < c) (N₀ : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧
        (c ^ (2 / 3 : ℝ) / 2) * ε ^ (-(2 / 3 : ℝ)) ≤ N ∧
        (N : ℝ) ≤ c ^ (2 / 3 : ℝ) * ε ^ (-(2 / 3 : ℝ)) ∧
        ε ≤ c / (N : ℝ) ^ (3 / 2 : ℝ) ∧
        (c ^ (2 / 3 : ℝ) / 16) * ballPrecisionRate ε ≤ sourceRate N := by
  obtain ⟨ε₀, hε₀, hh⟩ := eventually_small_reciprocal _ (ball_rate_core_eventually c hc N₀)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  have heq : (ε⁻¹) ^ (2 / 3 : ℝ) = ε ^ (-(2 / 3 : ℝ)) := by
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le]
  obtain ⟨N, hN₀, hNpos, hlo, hhi, hacc, hrate⟩ := hh ε hε hsmall
  refine ⟨N, hN₀, hNpos, by simpa only [heq] using hlo,
    by simpa only [heq] using hhi, by simpa only [one_div, inv_inv] using hacc, ?_⟩
  simpa only [ballPrecisionRate, heq, mul_div_assoc] using hrate

theorem simplex_rate_core_small (c : ℝ) (hc : 0 < c) (N₀ : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧
        (((c / 2) ^ (2 / 3 : ℝ)) / 2) * simplexCoreRate ε ≤ N ∧
        (N : ℝ) ≤ (c / 2) ^ (2 / 3 : ℝ) * simplexCoreRate ε ∧
        ε ≤ c / ((N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (N + 2))) ∧
        (((c / 2) ^ (2 / 3 : ℝ)) / 16) * simplexPrecisionRate ε ≤ sourceRate N := by
  obtain ⟨ε₀, hε₀, hh⟩ := eventually_small_reciprocal _ (simplex_rate_core_eventually c hc N₀)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  have heq : (ε⁻¹) ^ (2 / 3 : ℝ) = ε ^ (-(2 / 3 : ℝ)) := by
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le]
  obtain ⟨N, hN₀, hNpos, hlo, hhi, hacc, hrate⟩ := hh ε hε hsmall
  refine ⟨N, hN₀, hNpos, ?_, ?_, by simpa only [one_div, inv_inv] using hacc, ?_⟩
  · simpa only [simplexCoreRate, heq, mul_div_assoc] using hlo
  · simpa only [simplexCoreRate, heq, mul_div_assoc] using hhi
  · simpa only [simplexPrecisionRate, heq, mul_div_assoc] using hrate

end
end Matvec
