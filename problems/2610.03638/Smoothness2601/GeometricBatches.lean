import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
Geometric allocation (2601.tex, Lemma `lem:batch`). All batches and iteration
counts below are actual natural numbers. The noise scale, initial radius and
bias are nonnegative, as in the uses of this lemma in the manuscript.
-/
noncomputable section
namespace Smoothness2601.GeometricBatches
open scoped BigOperators

def iterations (q D u : ℝ) : ℕ :=
  max 1 ⌈Real.log (4 * (D + 1) ^ 2 / u ^ 2) / (-Real.log q)⌉₊

def batch (q A u : ℝ) (J k : ℕ) : ℕ :=
  max 1 ⌈(4 * A / (u ^ 2 * (1 - Real.sqrt q))) *
    Real.sqrt q ^ (J - 1 - k)⌉₊

/-- The square-root implementation is exactly the real half-power schedule
printed in the source; the division by two is not natural-number division. -/
theorem sqrt_power_eq {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    Real.sqrt q ^ n = q ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hq]
  congr 1
  ring

theorem batch_zero_noise (q u : ℝ) (J k : ℕ) : batch q 0 u J k = 1 := by
  simp [batch]

theorem iterations_pos (q D u : ℝ) : 0 < iterations q D u :=
  lt_of_lt_of_le (by decide) (le_max_left _ _)

theorem initial_term {q D u : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hD : 0 ≤ D) (hu : 0 < u) :
    q ^ iterations q D u * D ^ 2 ≤ u ^ 2 / 4 := by
  let R := 4 * (D + 1) ^ 2 / u ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hc : Real.log R / (-Real.log q) ≤ (iterations q D u : ℝ) :=
    (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right (1 : ℕ) (⌈Real.log R / (-Real.log q)⌉₊)))
  have hcl : Real.log R ≤ iterations q D u * (-Real.log q) :=
    (div_le_iff₀ hlog).mp hc
  have hp : q ^ iterations q D u ≤ R⁻¹ := by
    calc
      q ^ iterations q D u = Real.exp ((iterations q D u : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log hq]
      _ ≤ Real.exp (-Real.log R) := Real.exp_le_exp.mpr (by linarith)
      _ = R⁻¹ := by rw [Real.exp_neg, Real.exp_log hR]
  have hs : R⁻¹ * D ^ 2 ≤ u ^ 2 / 4 := by
    rw [inv_mul_eq_div, div_le_iff₀ hR]
    dsimp [R]
    have he : u ^ 2 / 4 * (4 * (D + 1) ^ 2 / u ^ 2) = (D + 1) ^ 2 := by
      field_simp
      ring
    rw [he]
    nlinarith
  exact (mul_le_mul_of_nonneg_right hp (sq_nonneg D)).trans hs

theorem geometric_sum_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (J : ℕ) :
    ∑ k ∈ Finset.range J, s ^ k ≤ 1 / (1 - s) := by
  have he := geom_sum_mul s J
  apply (le_div_iff₀ (sub_pos.mpr hs1)).mpr
  have hp : 0 ≤ s ^ J := pow_nonneg hs _
  nlinarith

theorem reversed_geometric_sum_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (J : ℕ) :
    ∑ k ∈ Finset.range J, s ^ (J - 1 - k) ≤ 1 / (1 - s) := by
  rw [Finset.sum_range_reflect]
  exact geometric_sum_le hs hs1 J

theorem batch_pos (q A u : ℝ) (J k : ℕ) : 0 < batch q A u J k :=
  lt_of_lt_of_le (by decide) (le_max_left _ _)

theorem batch_lower (q A u : ℝ) (J k : ℕ) :
    (4 * A / (u ^ 2 * (1 - Real.sqrt q))) * Real.sqrt q ^ (J - 1 - k) ≤
      (batch q A u J k : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast le_max_right (1 : ℕ) _)

theorem batch_upper {q A u : ℝ} (hq1 : q < 1) (hA : 0 ≤ A) (J k : ℕ) :
    (batch q A u J k : ℝ) ≤ 1 +
      (4 * A / (u ^ 2 * (1 - Real.sqrt q))) * Real.sqrt q ^ (J - 1 - k) := by
  have hs : Real.sqrt q < 1 := by
    exact (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hq1)
  have hs0 : 0 ≤ 1 - Real.sqrt q := sub_nonneg.mpr hs.le
  have ht : 0 ≤ (4 * A / (u ^ 2 * (1 - Real.sqrt q))) *
      Real.sqrt q ^ (J - 1 - k) := by positivity
  unfold batch
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith
  · linarith [Nat.ceil_lt_add_one ht]

theorem total_cost {q A u : ℝ} (hq1 : q < 1) (hA : 0 ≤ A) (J : ℕ) :
    (∑ k ∈ Finset.range J, (batch q A u J k : ℝ)) ≤
      J + 4 * A / (u ^ 2 * (1 - Real.sqrt q) ^ 2) := by
  have hs : Real.sqrt q < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hq1)
  have hs0 : 0 ≤ 1 - Real.sqrt q := sub_nonneg.mpr hs.le
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range J) =>
    batch_upper (u := u) hq1 hA J k)
  have hg := reversed_geometric_sum_le (Real.sqrt_nonneg q) hs J
  have hcoef : 0 ≤ 4 * A / (u ^ 2 * (1 - Real.sqrt q)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hg hcoef
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hsum
  have he : 4 * A / (u ^ 2 * (1 - Real.sqrt q)) * (1 / (1 - Real.sqrt q)) =
      4 * A / (u ^ 2 * (1 - Real.sqrt q) ^ 2) := by
    rw [mul_one_div, div_div]
    congr 1
    ring
  rw [he] at hm
  exact hsum.trans (add_le_add_left hm _)

theorem weighted_noise_term {q A u : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (_hA : 0 ≤ A) (hu : 0 < u) (J k : ℕ) :
    A * q ^ (J - 1 - k) / (batch q A u J k : ℝ) ≤
      (u ^ 2 * (1 - Real.sqrt q) / 4) * Real.sqrt q ^ (J - 1 - k) := by
  have hs : Real.sqrt q < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hq1)
  have hs0 : 0 ≤ 1 - Real.sqrt q := sub_nonneg.mpr hs.le
  have hd : 0 < (batch q A u J k : ℝ) := by exact_mod_cast batch_pos q A u J k
  apply (div_le_iff₀ hd).mpr
  have hcoef : 0 ≤ (u ^ 2 * (1 - Real.sqrt q) / 4) *
      Real.sqrt q ^ (J - 1 - k) := by positivity
  have hm := mul_le_mul_of_nonneg_left (batch_lower q A u J k) hcoef
  have he : ((u ^ 2 * (1 - Real.sqrt q) / 4) * Real.sqrt q ^ (J - 1 - k)) *
      ((4 * A / (u ^ 2 * (1 - Real.sqrt q))) * Real.sqrt q ^ (J - 1 - k)) =
      A * q ^ (J - 1 - k) := by
    have hpow : (Real.sqrt q ^ (J - 1 - k)) ^ 2 = q ^ (J - 1 - k) := by
      rw [← pow_mul, mul_comm (J - 1 - k) 2, pow_mul, Real.sq_sqrt hq]
    have hne : 1 - Real.sqrt q ≠ 0 := ne_of_gt (sub_pos.mpr hs)
    calc
      _ = A * (Real.sqrt q ^ (J - 1 - k)) ^ 2 := by
        field_simp [hne, ne_of_gt hu]
        ring
      _ = _ := by rw [hpow]
  rw [he] at hm
  exact hm

theorem total_noise {q A u : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hu : 0 < u) (J : ℕ) :
    (∑ k ∈ Finset.range J, A * q ^ (J - 1 - k) / (batch q A u J k : ℝ)) ≤
      u ^ 2 / 4 := by
  have hs : Real.sqrt q < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hq1)
  have hs0 : 0 ≤ 1 - Real.sqrt q := sub_nonneg.mpr hs.le
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range J) =>
    weighted_noise_term hq hq1 hA hu J k)
  have hg := reversed_geometric_sum_le (Real.sqrt_nonneg q) hs J
  have hc : 0 ≤ u ^ 2 * (1 - Real.sqrt q) / 4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hg hc
  have he : (u ^ 2 * (1 - Real.sqrt q) / 4) * (1 / (1 - Real.sqrt q)) =
      u ^ 2 / 4 := by
    field_simp [ne_of_gt (sub_pos.mpr hs)]
    ring
  rw [he] at hm
  rw [← Finset.mul_sum] at hsum
  exact hsum.trans hm

theorem unroll {q : ℝ} (hq : 0 ≤ q) (E noise : ℕ → ℝ) (J : ℕ)
    (hrec : ∀ k < J, E (k + 1) ≤ q * E k + noise k) :
    E J ≤ q ^ J * E 0 + ∑ k ∈ Finset.range J, q ^ (J - 1 - k) * noise k := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hprev := ih (fun k hk => hrec k (Nat.lt.step hk))
    have hsum : (∑ k ∈ Finset.range (J + 1), q ^ (J + 1 - 1 - k) * noise k) =
        q * (∑ k ∈ Finset.range J, q ^ (J - 1 - k) * noise k) + noise J := by
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < J := Finset.mem_range.mp hk
      have he : J - k = (J - 1 - k) + 1 := by omega
      rw [he, pow_succ]
      ring
    calc
      E (J + 1) ≤ q * E J + noise J := hrec J (Nat.lt_succ_self J)
      _ ≤ q * (q ^ J * E 0 + ∑ k ∈ Finset.range J,
          q ^ (J - 1 - k) * noise k) + noise J :=
        add_le_add_right (mul_le_mul_of_nonneg_left hprev hq) _
      _ = q ^ (J + 1) * E 0 +
          ∑ k ∈ Finset.range (J + 1), q ^ (J + 1 - 1 - k) * noise k := by
        rw [hsum, pow_succ]
        ring

theorem scheduled_error {q A D u d : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 < u) (hd : 0 ≤ d)
    (hbias : d / (1 - q) ≤ u ^ 2 / 4) (E : ℕ → ℝ)
    (hinit : E 0 ≤ D ^ 2)
    (hrec : ∀ k < iterations q D u,
      E (k + 1) ≤ q * E k + d + A / (batch q A u (iterations q D u) k : ℝ)) :
    E (iterations q D u) ≤ 3 * u ^ 2 / 4 := by
  let J := iterations q D u
  have hrec' : ∀ k < J, E (k + 1) ≤ q * E k +
      (d + A / (batch q A u J k : ℝ)) := by
    intro k hk
    simpa [add_assoc] using hrec k hk
  have he := unroll hq.le E (fun k => d + A / (batch q A u J k : ℝ)) J hrec'
  have hsum : (∑ k ∈ Finset.range J, q ^ (J - 1 - k) *
      (d + A / (batch q A u J k : ℝ))) =
      d * (∑ k ∈ Finset.range J, q ^ (J - 1 - k)) +
      ∑ k ∈ Finset.range J, A * q ^ (J - 1 - k) / (batch q A u J k : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum] at he
  have hb : d * (∑ k ∈ Finset.range J, q ^ (J - 1 - k)) ≤ u ^ 2 / 4 := by
    have hg := mul_le_mul_of_nonneg_left (reversed_geometric_sum_le hq.le hq1 J) hd
    have hgd : d * (1 / (1 - q)) = d / (1 - q) := by ring
    rw [hgd] at hg
    exact hg.trans hbias
  have hn := total_noise hq.le hq1 hA hu J
  have hi := initial_term hq hq1 hD hu
  have hinit' := mul_le_mul_of_nonneg_left hinit (pow_nonneg hq.le J)
  change q ^ J * D ^ 2 ≤ u ^ 2 / 4 at hi
  linarith

/-- Complete error and fixed-cost statement of Lemma `lem:batch`, with the
nonnegative parameter domains made explicit. No recurrence or allocation
estimate is postulated beyond the source's input recurrence. -/
theorem geometric_allocation {q A D u d : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 < u) (hd : 0 ≤ d)
    (hbias : d / (1 - q) ≤ u ^ 2 / 4) (E : ℕ → ℝ)
    (hinit : E 0 ≤ D ^ 2)
    (hrec : ∀ k < iterations q D u,
      E (k + 1) ≤ q * E k + d + A / (batch q A u (iterations q D u) k : ℝ)) :
    E (iterations q D u) ≤ 3 * u ^ 2 / 4 ∧
    (∑ k ∈ Finset.range (iterations q D u),
      (batch q A u (iterations q D u) k : ℝ)) ≤
      iterations q D u + 4 * A / (u ^ 2 * (1 - Real.sqrt q) ^ 2) :=
  ⟨scheduled_error hq hq1 hA hD hu hd hbias E hinit hrec,
    total_cost hq1 hA _⟩

end Smoothness2601.GeometricBatches
