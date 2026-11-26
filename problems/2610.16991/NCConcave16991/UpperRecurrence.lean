import NCConcave16991.Smoothness
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section

open scoped BigOperators

namespace NCConcave16991

/-- The actual telescope of any one-step energy descent with inexactness. -/
theorem descent_telescopes (energy distance error : ℕ → ℝ) (L : ℝ)
    (hstep : ∀ k, energy (k + 1) ≤ energy k - L * distance k + L * error k)
    (S : ℕ) :
    energy S + L * ∑ k ∈ Finset.range S, distance k ≤
      energy 0 + L * ∑ k ∈ Finset.range S, error k := by
  induction S with
  | zero => simp
  | succ S ih =>
    simp only [Finset.sum_range_succ]
    nlinarith [hstep S]

/-- The rho=1/2 affine recurrence, proved by induction on the actual sequence. -/
theorem half_contraction (a : ℕ → ℝ) {C : ℝ}
    (hstep : ∀ k, a (k + 1) ≤ a k / 2 + C) (k : ℕ) :
    a k ≤ (1 / 2 : ℝ) ^ k * a 0 + 2 * C * (1 - (1 / 2 : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := hstep k
    rw [pow_succ]
    nlinarith

/-- The nonzero noise floor of a half-contraction is at most 2C. -/
theorem half_contraction_bound (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ k, a (k + 1) ≤ a k / 2 + C) (k : ℕ) :
    a k ≤ (1 / 2 : ℝ) ^ k * a 0 + 2 * C := by
  have h := half_contraction a hstep k
  have hp : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  nlinarith

/-- Appendix B's persistent-error absorption, with its actual constants. -/
theorem persistent_error_absorption {D E θ ν : ℝ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hν : 0 ≤ ν) (hθ : θ ≤ 1 / 4096)
    (herror : E ≤ D / 1024 + 3 * θ * (2 * D + 2 * E) + ν) :
    E ≤ D / 128 + 2 * ν := by
  have hterm := mul_le_mul_of_nonneg_right hθ
    (show 0 ≤ 3 * (2 * D + 2 * E) by linarith)
  nlinarith

/-- The prescribed batch ceiling makes gamma*q/b at most 2^-12. -/
theorem batch_ceiling_ratio {γ : ℝ} (hγ : 0 ≤ γ) (q : ℕ)
    (hq : 0 < q) (b : ℕ) (hb : b = Nat.ceil (4096 * γ * q))
    (hbpos : 0 < b) : γ * q / b ≤ 1 / 4096 := by
  have hceil : 4096 * γ * q ≤ (b : ℝ) := by rw [hb]; exact Nat.le_ceil _
  have hbp : (0 : ℝ) < b := by exact_mod_cast hbpos
  apply (div_le_iff₀ hbp).2
  nlinarith

/-- Every public natural ceiling has an explicit additive-one budget. -/
theorem public_ceiling_budget {x : ℝ} (hx : 0 ≤ x) :
    x ≤ (Nat.ceil x : ℝ) ∧ (Nat.ceil x : ℝ) < x + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hx⟩

/-- The Appendix B query accounting evaluated at actual ceiling loop lengths. -/
def persistentQueryBudget (n q b K S : ℕ) : ℕ :=
  n * (1 + (S + q - 1) / q) + 2 * b * S + 2 * K * S

/-- An epoch budget never needs more than one refresh per outer step. -/
theorem persistentQueryBudget_le {n q b K S : ℕ} (hq : 0 < q) :
    persistentQueryBudget n q b K S ≤ n * (1 + S) + 2 * b * S + 2 * K * S := by
  have hmul : S ≤ S * q := by simpa using Nat.mul_le_mul_left S hq
  have hepoch : (S + q - 1) / q ≤ S := by
    apply (Nat.div_le_iff_le_mul hq).2
    omega
  have hm := Nat.mul_le_mul_left n (Nat.add_le_add_left hepoch 1)
  unfold persistentQueryBudget
  omega
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite sum really is a sum of squared primal proximal displacements. -/
def proximalDisplacementSum (c p : ℕ → E) (S : ℕ) : ℝ :=
  ∑ k ∈ Finset.range S, ‖p k - c k‖ ^ 2

/-- Appendix B outer descent, retaining all assumptions about the actual iterates.
No stochastic algorithm is postulated by this deterministic theorem. -/
theorem persistent_outer_descent (c p : ℕ → E) (energy : ℕ → ℝ)
    {L lower η : ℝ} (hL : 0 < L) {S : ℕ} (hS : 0 < S)
    (hstep : ∀ k, energy (k + 1) ≤ energy k - L * ‖p k - c k‖ ^ 2 +
      L * ‖c (k + 1) - p k‖ ^ 2)
    (hlower : lower ≤ energy S)
    (herror : (∑ k ∈ Finset.range S, ‖c (k + 1) - p k‖ ^ 2) ≤
      proximalDisplacementSum c p S / 128 + S * η) :
    proximalDisplacementSum c p S / S ≤
      (128 / 127 : ℝ) * ((energy 0 - lower) / (L * S) + η) := by
  have hs := descent_telescopes energy (fun k => ‖p k - c k‖ ^ 2)
    (fun k => ‖c (k + 1) - p k‖ ^ 2) L hstep S
  change energy S + L * proximalDisplacementSum c p S ≤ _ at hs
  have hE := mul_le_mul_of_nonneg_left herror hL.le
  have hD : proximalDisplacementSum c p S ≤
      (128 / 127 : ℝ) * (energy 0 - lower + L * S * η) / L := by
    apply (le_div_iff₀ hL).2
    nlinarith
  have hSp : (0 : ℝ) < S := by exact_mod_cast hS
  have hm := div_le_div_of_nonneg_right hD hSp.le
  convert hm using 1 <;> field_simp [hL.ne', hSp.ne'] <;> ring

/-- A squared triangle estimate used in the inexact proximal calculation. -/
theorem norm_sub_sq_le_two (x y p : E) :
    ‖x - p‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖y - p‖ ^ 2 := by
  have ht : ‖x - p‖ ≤ ‖y - x‖ + ‖y - p‖ := by
    calc
      ‖x - p‖ = ‖(x - y) + (y - p)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y - p‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev x y]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖y - x‖ - ‖y - p‖)]

/-- Appendix C's exact outer bound for an actual inexact proximal trajectory. -/
theorem inexact_proximal_outer_descent (F : E → ℝ) (x p : ℕ → E)
    {L δ Δ lower : ℝ} (hL : 0 < L) {S : ℕ} (hS : 0 < S)
    (hclose : ∀ k, ‖x (k + 1) - p k‖ ^ 2 ≤ 2 * δ / L)
    (hstep : ∀ k, L * ‖x (k + 1) - x k‖ ^ 2 ≤ F (x k) - F (x (k + 1)) + δ)
    (hlower : lower ≤ F (x S)) (hgap : F (x 0) - lower ≤ Δ) :
    (∑ k ∈ Finset.range S, ‖(2 * L) • (x k - p k)‖ ^ 2) / S ≤
      8 * L * Δ / S + 24 * L * δ := by
  have htel := descent_telescopes (fun k => F (x k))
    (fun k => ‖x (k + 1) - x k‖ ^ 2) (fun _ => δ / L) L
    (fun k => by have h := hstep k; field_simp [hL.ne']; nlinarith) S
  have hconst : L * ∑ k ∈ Finset.range S, δ / L = S * δ := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hL.ne']
  rw [hconst] at htel
  have hmove : L * ∑ k ∈ Finset.range S, ‖x (k + 1) - x k‖ ^ 2 ≤ Δ + S * δ := by
    linarith
  have hpoint (k : ℕ) : ‖(2 * L) • (x k - p k)‖ ^ 2 ≤
      8 * L ^ 2 * ‖x (k + 1) - x k‖ ^ 2 + 16 * L * δ := by
    have ht := norm_sub_sq_le_two (x k) (x (k + 1)) (p k)
    have hc := (le_div_iff₀ hL).mp (hclose k)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 2 * L), mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg (2 * L))]
  have hsum := Finset.sum_le_sum (s := Finset.range S) (fun k _ => hpoint k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hmult := mul_le_mul_of_nonneg_left hmove (show 0 ≤ 8 * L by linarith)
  have hSp : (0 : ℝ) < S := by exact_mod_cast hS
  apply (div_le_iff₀ hSp).2
  have heq : (8 * L * Δ / (S : ℝ) + 24 * L * δ) * S =
      8 * L * Δ + 24 * L * δ * S := by field_simp [hSp.ne']
  rw [heq]
  nlinarith

/-- The public parameters in Appendix C make the deterministic mean square ≤ eps²/6. -/
theorem accelerated_parameter_stationarity {L Δ ε : ℝ} (hL : 0 < L)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) {S : ℕ}
    (hS : 96 * (L * Δ / ε ^ 2) ≤ (S : ℝ)) (hSp : 0 < S) :
    8 * L * Δ / S + 24 * L * (ε ^ 2 / (288 * L)) ≤ ε ^ 2 / 6 := by
  have hSr : (0 : ℝ) < S := by exact_mod_cast hSp
  have hep : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsize := (div_le_iff₀ hep).mp (show 96 * L * Δ / ε ^ 2 ≤ (S : ℝ) by convert hS using 1 <;> ring)
  have hfirst : 8 * L * Δ / (S : ℝ) ≤ ε ^ 2 / 12 := by
    apply (div_le_iff₀ hSr).2
    nlinarith
  have hsecond : 24 * L * (ε ^ 2 / (288 * L)) = ε ^ 2 / 12 := by
    field_simp [hL.ne']
    <;> ring
  linarith

end NCConcave16991


namespace NCConcave16991

/-- Public persistent-estimator loop lengths in Appendix B. -/
def persistentBatchSize (γ : ℝ) (q : ℕ) : ℕ := Nat.ceil (4096 * γ * q)
def persistentInnerSteps (κ : ℝ) : ℕ := Nat.ceil ((2 : ℝ) ^ 32 * κ ^ 2)
def persistentOuterSteps (A : ℝ) : ℕ := Nat.ceil (4096 * (1 + A))

/-- The prescribed outer horizon is positive and has a fixed explicit ceiling budget. -/
theorem persistentOuterSteps_bounds {A : ℝ} (hA : 0 ≤ A) :
    0 < persistentOuterSteps A ∧
    4096 * (1 + A) ≤ (persistentOuterSteps A : ℝ) ∧
    (persistentOuterSteps A : ℝ) < 4096 * (1 + A) + 1 := by
  have hp : 0 < 4096 * (1 + A) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.one_le_ceil_iff.mpr hp
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one hp.le

/-- The prescribed inner horizon and batch both have explicit additive-one overhead. -/
theorem persistentInnerSteps_bounds (κ : ℝ) :
    (2 : ℝ) ^ 32 * κ ^ 2 ≤ (persistentInnerSteps κ : ℝ) ∧
    (persistentInnerSteps κ : ℝ) < (2 : ℝ) ^ 32 * κ ^ 2 + 1 := by
  exact public_ceiling_budget (mul_nonneg (by norm_num) (sq_nonneg κ))

theorem persistentBatchSize_bounds {γ : ℝ} (hγ : 1 ≤ γ) {q : ℕ} (hq : 0 < q) :
    0 < persistentBatchSize γ q ∧
    4096 * γ * q ≤ (persistentBatchSize γ q : ℝ) ∧
    (persistentBatchSize γ q : ℝ) < 4096 * γ * q + 1 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : 0 < 4096 * γ * q := mul_pos (by linarith) hqr
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.one_le_ceil_iff.mpr hp
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one hp.le

end NCConcave16991

namespace NCConcave16991

/-- Query accounting for actual nonnegative per-epoch and per-step oracle counters. -/
theorem fixed_query_accounting {R S n b K : ℕ}
    (refreshCost : Fin R → ℕ) (batchCost innerCost : Fin S → ℕ)
    (hrefresh : ∀ i, refreshCost i ≤ n)
    (hbatch : ∀ i, batchCost i ≤ 2 * b)
    (hinner : ∀ i, innerCost i ≤ 2 * K) :
    (∑ i, refreshCost i) + (∑ i, batchCost i) + (∑ i, innerCost i) ≤
      n * R + 2 * b * S + 2 * K * S := by
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrefresh i)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbatch i)
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hinner i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr hb hi
  nlinarith

end NCConcave16991


namespace NCConcave16991

/-- Appendix B's public outer horizon turns its deterministic descent mean into
an eps²/512 bound for the squared proximal residual. -/
theorem persistent_parameter_stationarity {L Δ r ε M : ℝ} {S : ℕ}
    (hL : 0 < L) (hε : 0 < ε) (hSp : 0 < S)
    (hr : r ≤ ε ^ 2 / L)
    (hS : 4096 * (1 + L * Δ / ε ^ 2) ≤ (S : ℝ))
    (hmean : M ≤ (128 / 127 : ℝ) *
      ((Δ + r) / (L * S) + ε ^ 2 / ((2 : ℝ) ^ 31 * L ^ 2))) :
    4 * L ^ 2 * M ≤ ε ^ 2 / 512 := by
  have hep : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hSr : (0 : ℝ) < S := by exact_mod_cast hSp
  have hrv : r * L ≤ ε ^ 2 := (le_div_iff₀ hL).mp hr
  have hm := mul_le_mul_of_nonneg_right hS hep.le
  have hsize : 4096 * (ε ^ 2 + L * Δ) ≤ (S : ℝ) * ε ^ 2 := by
    convert hm using 1 <;> field_simp [hep.ne'] <;> ring
  have hratio : (Δ + r) / (L * S) ≤ ε ^ 2 / (4096 * L ^ 2) := by
    apply (div_le_div_iff₀ (mul_pos hL hSr)
      (mul_pos (by norm_num) (sq_pos_of_pos hL))).2
    have ht : 4096 * L * (Δ + r) ≤ ε ^ 2 * (S : ℝ) := by nlinarith
    have ht' := mul_le_mul_of_nonneg_left ht hL.le
    nlinarith
  have hmain : M ≤ (128 / 127 : ℝ) *
      (ε ^ 2 / (4096 * L ^ 2) + ε ^ 2 / ((2 : ℝ) ^ 31 * L ^ 2)) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hmain (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (sq_nonneg L))
  have heq : 4 * L ^ 2 * ((128 / 127 : ℝ) *
      (ε ^ 2 / (4096 * L ^ 2) + ε ^ 2 / ((2 : ℝ) ^ 31 * L ^ 2))) =
      (524289 / 532676608 : ℝ) * ε ^ 2 := by
    field_simp [hL.ne']
    <;> ring
  rw [heq] at hmul
  nlinarith

/-- The final transfer constants in Appendix B satisfy the advertised eps²/200 bound. -/
theorem persistent_transfer_numerics {ε : ℝ} (hε : 0 < ε) :
    2 * (ε ^ 2 / 512) + ε ^ 2 / (2 : ℝ) ^ 18 < ε ^ 2 / 200 := by
  nlinarith [sq_pos_of_pos hε]

end NCConcave16991

