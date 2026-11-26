import Matvec.RandomOrthogonal

/-!
# Probabilistic entry normalization with a Walsh testing basis

This uses a finite uniform sign sampler, not an assumed Haar law. Dimensions
are powers of two; dimension extension handles larger ambient dimensions.
-/

namespace Matvec
namespace SimplexNormalization

open Matrix MeasureTheory ProbabilityTheory RandomOrthogonal
open scoped BigOperators ENNReal Classical Matrix
noncomputable section

section Deterministic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def atomIndex : ι ⊕ ι → ι := Sum.elim id id
def atomSign : ι ⊕ ι → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

omit [Fintype ι] [DecidableEq ι] in
theorem atomSign_abs (s : ι ⊕ ι) : |atomSign s| = 1 := by
  cases s <;> norm_num [atomSign]

theorem dictionary_right {ρ : Type*} (A : Matrix ρ ι ℝ) (a : ℝ) (i : ρ) (s : ι ⊕ ι) :
    (A * (signedDictionary a : Matrix ι (ι ⊕ ι) ℝ)) i s =
      a * atomSign s * A i (atomIndex s) := by
  cases s <;> simp [Matrix.mul_apply, signedDictionary, atomIndex, atomSign] <;> ring

theorem dictionary_left (A : Matrix ι ι ℝ) (a : ℝ) (s : ι ⊕ ι) (j : ι) :
    ((signedDictionary a : Matrix ι (ι ⊕ ι) ℝ).transpose * A) s j =
      a * atomSign s * A (atomIndex s) j := by
  cases s <;> simp [Matrix.mul_apply, Matrix.transpose_apply, signedDictionary,
    atomIndex, atomSign]

theorem dictionary_vector (a : ℝ) (v : ι → ℝ) (s : ι ⊕ ι) :
    ((signedDictionary a).transpose *ᵥ v) s = a * atomSign s * v (atomIndex s) := by
  cases s <;> simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, signedDictionary,
    atomIndex, atomSign]

theorem simplex_entry_formula (H Q : Matrix ι ι ℝ) (b : ι → ℝ)
    (a Λ : ℝ) (r c : ι ⊕ ι) :
    simplexMatrix H b (Q * signedDictionary a) (signedDictionary a) Λ r c =
      Λ⁻¹ * (a ^ 2 * atomSign r * atomSign c *
        (Q.transpose * H) (atomIndex r) (atomIndex c) -
          a * atomSign r * (Q.transpose *ᵥ b) (atomIndex r)) := by
  have hmat : (Q * signedDictionary a).transpose * H * signedDictionary a =
      (signedDictionary a).transpose * (Q.transpose * H) * signedDictionary a := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hv : (Q * signedDictionary a).transpose *ᵥ b =
      (signedDictionary a).transpose *ᵥ (Q.transpose *ᵥ b) := by
    rw [Matrix.transpose_mul, Matrix.mulVec_mulVec]
  simp only [simplexMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.vecMulVec, Matrix.of_apply, mul_one, hmat, hv]
  rw [dictionary_right, dictionary_left, dictionary_vector]
  ring

/-- Actual entrywise normalization from projection bounds. -/
theorem simplex_entries_bounded (H Q : Matrix ι ι ℝ) (b : ι → ℝ)
    {a Λ u v : ℝ} (ha : 0 ≤ a) (hΛ : 0 < Λ)
    (hH : ∀ i j, |(Q.transpose * H) i j| ≤ u)
    (hb : ∀ i, |(Q.transpose *ᵥ b) i| ≤ v)
    (hscale : a ^ 2 * u + a * v ≤ Λ) :
    ∀ r c, |simplexMatrix H b (Q * signedDictionary a) (signedDictionary a) Λ r c| ≤ 1 := by
  intro r c
  rw [simplex_entry_formula, abs_mul, abs_inv, abs_of_pos hΛ]
  have ht1 : |a ^ 2 * atomSign r * atomSign c *
      (Q.transpose * H) (atomIndex r) (atomIndex c)| ≤ a ^ 2 * u := by
    simpa only [abs_mul, abs_pow, sq_abs, atomSign_abs, mul_one] using
      mul_le_mul_of_nonneg_left (hH (atomIndex r) (atomIndex c)) (sq_nonneg a)
  have ht2 : |a * atomSign r * (Q.transpose *ᵥ b) (atomIndex r)| ≤ a * v := by
    simpa only [abs_mul, abs_of_nonneg ha, atomSign_abs, mul_one] using
      mul_le_mul_of_nonneg_left (hb (atomIndex r)) ha
  have hnum := (abs_sub _ _).trans ((add_le_add ht1 ht2).trans hscale)
  have hmul := mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hΛ.le)
  simpa only [inv_mul_cancel₀ hΛ.ne'] using hmul

end Deterministic

def tests (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ) (b : Cube k → ℝ) :
    (Cube k × (Cube k ⊕ Unit)) → Cube k → ℝ :=
  fun t l => walsh k l t.1 * Sum.elim (fun j => H l j) (fun _ => b l) t.2

theorem tests_energy (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ) (b : Cube k → ℝ)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hH : ∀ j, ∑ l, H l j ^ 2 ≤ κ ^ 2) (hb : ∑ l, b l ^ 2 ≤ 1) :
    ∀ t, ∑ l, tests k H b t l ^ 2 ≤ κ ^ 2 := by
  intro ⟨i, j⟩
  cases j with
  | inl j => simpa only [tests, Sum.elim_inl, mul_pow, walsh_sq, one_mul] using hH j
  | inr j =>
    simp only [tests, Sum.elim_inr, mul_pow, walsh_sq, one_mul]
    have hk : (1 : ℝ) ≤ κ ^ 2 := by nlinarith
    exact hb.trans hk

/-- A conservative explicit arithmetic bound, uniform in every `d ≥ 1`. -/
theorem normalization_failure_bound {d κ : ℝ} (hd : 1 ≤ d) (hκ : 0 < κ) :
    2 * (d * (d + 1)) *
      Real.exp (-(4 * κ * Real.sqrt (Real.log (d + 2))) ^ 2 / (2 * κ ^ 2)) ≤
        1 / 100 := by
  have hx : 0 < d + 2 := by linarith
  have hlog : 0 ≤ Real.log (d + 2) := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hlog
  have hexponent : -(4 * κ * Real.sqrt (Real.log (d + 2))) ^ 2 / (2 * κ ^ 2) =
      -(8 * Real.log (d + 2)) := by
    field_simp
    nlinarith
  rw [hexponent, Real.exp_neg]
  have he : Real.exp (8 * Real.log (d + 2)) = (d + 2) ^ 8 := by
    calc
      _ = Real.exp (Real.log ((d + 2) ^ 8)) := by
        congr 1
        simp [Real.log_pow]
      _ = _ := Real.exp_log (pow_pos hx 8)
  rw [he]
  have hnum : 2 * (d * (d + 1)) ≤ 4 * (d + 2) ^ 2 := by nlinarith
  have hpow : (729 : ℝ) ≤ (d + 2) ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by linarith : 3 ≤ d + 2) 6
    norm_num at h ⊢
    exact h
  calc
    2 * (d * (d + 1)) * ((d + 2) ^ 8)⁻¹ = 2 * (d * (d + 1)) / (d + 2) ^ 8 := by ring
    _ ≤ (4 * (d + 2) ^ 2) / (d + 2) ^ 8 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 4 / (d + 2) ^ 6 := by field_simp; ring
    _ ≤ 4 / 729 := (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by linarith)
    _ ≤ 1 / 100 := by norm_num

/-- At least 99% of the actual sign vectors simultaneously control all
source-matrix columns and the right-hand side. -/
theorem tests_good_probability (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ)
    (b : Cube k → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hH : ∀ j, ∑ l, H l j ^ 2 ≤ κ ^ 2) (hb : ∑ l, b l ^ 2 ≤ 1) :
    (99 / 100 : ℝ) ≤ (signLaw (Cube k)).real
      {σ | ∀ t, |signedSum σ (tests k H b t)| <
        4 * κ * Real.sqrt (Real.log ((2 ^ k : ℝ) + 2))} := by
  have hd : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hk : 0 < κ := by linarith
  have hτ : 0 ≤ 4 * κ * Real.sqrt (Real.log ((2 ^ k : ℝ) + 2)) := by positivity
  have hg := simultaneous_signedSum_good (tests k H b) κ (tests_energy k H b hκ hH hb) hτ
  have hcard : (Fintype.card (Cube k × (Cube k ⊕ Unit)) : ℝ) =
      (2 ^ k : ℝ) * (2 ^ k + 1) := by
    simp [Fintype.card_prod, Fintype.card_sum, cube_card]
  rw [hcard] at hg
  have harith := normalization_failure_bound hd hk
  linarith

theorem tests_good_projection_bounds (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ)
    (b : Cube k → ℝ) (σ : Cube k → Bool) (τ : ℝ)
    (hgood : ∀ t, |signedSum σ (tests k H b t)| < τ) :
    (∀ i j, |((testingBasis k σ).transpose * H) i j| ≤ τ / Real.sqrt (2 ^ k : ℝ)) ∧
    (∀ i, |((testingBasis k σ).transpose *ᵥ b) i| ≤ τ / Real.sqrt (2 ^ k : ℝ)) := by
  have hs : 0 < Real.sqrt (2 ^ k : ℝ) := by positivity
  constructor
  · intro i j
    have h := hgood (i, Sum.inl j)
    change |signedSum σ (fun l => walsh k l i * H l j)| < τ at h
    change |((testingBasis k σ).transpose *ᵥ (fun l => H l j)) i| ≤ _
    rw [testingBasis_projection, abs_mul, abs_inv, abs_of_pos hs]
    have hm := mul_le_mul_of_nonneg_left h.le (inv_nonneg.mpr hs.le)
    simpa only [div_eq_mul_inv, mul_comm] using hm
  · intro i
    have h := hgood (i, Sum.inr ())
    change |signedSum σ (fun l => walsh k l i * b l)| < τ at h
    rw [testingBasis_projection, abs_mul, abs_inv, abs_of_pos hs]
    have hm := mul_le_mul_of_nonneg_left h.le (inv_nonneg.mpr hs.le)
    simpa only [div_eq_mul_inv, mul_comm] using hm

theorem embedding_scale_bound {d κ : ℝ} (hd : 1 ≤ d) (hκ : 0 ≤ κ) :
    (Real.sqrt d) ^ 2 * (4 * κ * Real.sqrt (Real.log (d + 2)) / Real.sqrt d) +
      Real.sqrt d * (4 * κ * Real.sqrt (Real.log (d + 2)) / Real.sqrt d) ≤
        8 * κ * Real.sqrt (d * Real.log (d + 2)) := by
  have hdpos : 0 < d := by linarith
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  have hs : 1 ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hd
  have ht : 0 ≤ 4 * κ * Real.sqrt (Real.log (d + 2)) := by positivity
  have heq : (Real.sqrt d) ^ 2 *
      (4 * κ * Real.sqrt (Real.log (d + 2)) / Real.sqrt d) +
        Real.sqrt d * (4 * κ * Real.sqrt (Real.log (d + 2)) / Real.sqrt d) =
      (Real.sqrt d + 1) * (4 * κ * Real.sqrt (Real.log (d + 2))) := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hdpos.le]
    ring
  rw [heq, Real.sqrt_mul hdpos.le]
  have h := mul_le_mul_of_nonneg_right (show Real.sqrt d + 1 ≤ 2 * Real.sqrt d by linarith) ht
  nlinarith

def embeddingScale (k : ℕ) (κ : ℝ) : ℝ :=
  8 * κ * Real.sqrt ((2 ^ k : ℝ) * Real.log ((2 ^ k : ℝ) + 2))

def walshGame (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ) (b : Cube k → ℝ)
    (κ : ℝ) (σ : Cube k → Bool) : Matrix (Cube k ⊕ Cube k) (Cube k ⊕ Cube k) ℝ :=
  simplexMatrix H b (testingBasis k σ * signedDictionary (Real.sqrt (2 ^ k : ℝ)))
    (signedDictionary (Real.sqrt (2 ^ k : ℝ))) (embeddingScale k κ)

theorem embeddingScale_pos (k : ℕ) {κ : ℝ} (hκ : 0 < κ) : 0 < embeddingScale k κ := by
  have hd : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hl : 0 < Real.log ((2 ^ k : ℝ) + 2) := Real.log_pos (by linarith)
  unfold embeddingScale
  positivity

/-- Actual admissibility probability of the randomized simplex embedding.
Every matrix entry is bounded, with probability at least `0.99`, for each fixed
source matrix and right-hand side satisfying their normalization promises. -/
theorem walshGame_bounded_probability (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ)
    (b : Cube k → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hH : ∀ j, ∑ l, H l j ^ 2 ≤ κ ^ 2) (hb : ∑ l, b l ^ 2 ≤ 1) :
    (99 / 100 : ℝ) ≤ (signLaw (Cube k)).real
      {σ | ∀ r c, |walshGame k H b κ σ r c| ≤ 1} := by
  have hd : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hk : 0 < κ := by linarith
  refine (tests_good_probability k H b hκ hH hb).trans (measureReal_mono ?_)
  intro σ hσ
  obtain ⟨hprojH, hprojb⟩ := tests_good_projection_bounds k H b σ
    (4 * κ * Real.sqrt (Real.log ((2 ^ k : ℝ) + 2))) hσ
  exact simplex_entries_bounded H (testingBasis k σ) b (Real.sqrt_nonneg _)
    (embeddingScale_pos k hk) hprojH hprojb (embedding_scale_bound hd hk.le)

/-- The dyadic core needed by the alternative construction is never smaller
than half the requested core size. Thus subsequent padding changes only
universal constants, not the accuracy or logarithmic exponents. -/
theorem exists_dyadic_core (N : ℕ) (hN : 0 < N) :
    ∃ k : ℕ, 0 < 2 ^ k ∧ 2 ^ k ≤ N ∧ N < 2 * 2 ^ k := by
  refine ⟨N.log2, by positivity, Nat.log2_self_le hN.ne', ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using (Nat.lt_log2_self (n := N))

theorem dyadic_game_dimensions (N : ℕ) (hN : 0 < N) :
    ∃ k : ℕ, 2 ^ (k + 1) ≤ 2 * N ∧
      2 * 2 ^ (k + 1) ≤ 4 * N ∧ N < 2 ^ (k + 1) := by
  obtain ⟨k, hk, hle, hlt⟩ := exists_dyadic_core N hN
  refine ⟨k, ?_, ?_, ?_⟩ <;> rw [pow_succ] <;> omega

end
end SimplexNormalization
end Matvec
