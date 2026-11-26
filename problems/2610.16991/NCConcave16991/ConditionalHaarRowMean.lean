import NCConcave16991.ConeValueBall

/-!
# Deterministic known-row and unknown-row decomposition of the cone source mean

The learned part of an orthonormal row mean has norm exactly the square root
of the learned fraction. Bounds on the remaining individual correlations then
control the full mean. Combined with the actual Haar tails this prevents a
reference transcript from activating an unfinished cone block.
-/

open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Haar

noncomputable section

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def partialRowMean (w : Fin n → E) (A : Finset (Fin n)) : E :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ A, w i

def rowMean (w : Fin n → E) : E := partialRowMean w Finset.univ

theorem rowMean_decomposition (w : Fin n → E) (A : Finset (Fin n)) :
    rowMean w = partialRowMean w A + partialRowMean w Aᶜ := by
  rw [rowMean, partialRowMean, partialRowMean, partialRowMean, ← smul_add,
    Finset.sum_add_sum_compl]

theorem partialRowMean_norm_sq (hn : 0 < n) (w : Fin n → E) (hw : Orthonormal ℝ w)
    (A : Finset (Fin n)) : ‖partialRowMean w A‖ ^ 2 = (A.card : ℝ) / (n : ℝ) := by
  have hs : ‖∑ i ∈ A, w i‖ ^ 2 = (A.card : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum, orthonormal_iff_ite.mp hw]
    simp
  rw [partialRowMean, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), hs]
  ring

theorem partialRowMean_norm_le (hn : 0 < n) (w : Fin n → E) (hw : Orthonormal ℝ w)
    (A : Finset (Fin n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcard : (A.card : ℝ) ≤ (n : ℝ) * ρ ^ 2) : ‖partialRowMean w A‖ ≤ ρ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ‖partialRowMean w A‖ ^ 2 ≤ ρ ^ 2 := by
    rw [partialRowMean_norm_sq hn w hw]
    exact (div_le_iff₀ hn0).mpr (by nlinarith)
  nlinarith [norm_nonneg (partialRowMean w A)]

theorem partialRowMean_correlation_le (w : Fin n → E) (A : Finset (Fin n)) (a : E)
    {δ : ℝ} (hδ : ∀ i ∈ A, |⟪a, w i⟫_ℝ| ≤ δ) :
    |⟪a, partialRowMean w A⟫_ℝ| ≤ (Real.sqrt (n : ℝ))⁻¹ * (A.card : ℝ) * δ := by
  rw [partialRowMean, real_inner_smul_right, abs_mul, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), inner_sum]
  have hs : |∑ i ∈ A, ⟪a, w i⟫_ℝ| ≤ (A.card : ℝ) * δ := by
    calc
      _ ≤ ∑ i ∈ A, |⟪a, w i⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ A, δ := Finset.sum_le_sum hδ
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (by ring)

/-- Revealed orthonormal rows and small unrevealed correlations control the
literal full source mean. The unseen directions need not be independent. -/
theorem rowMean_correlation_bound (hn : 0 < n) (w : Fin n → E) (hw : Orthonormal ℝ w)
    (A : Finset (Fin n)) (a : E) {C ρ δ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (ha : ‖a‖ ≤ C) (hcard : (A.card : ℝ) ≤ (n : ℝ) * ρ ^ 2)
    (hunseen : ∀ i ∈ Aᶜ, |⟪a, w i⟫_ℝ| ≤ δ) :
    |⟪a, rowMean w⟫_ℝ| ≤ C * ρ + (Real.sqrt (n : ℝ))⁻¹ * (Aᶜ.card : ℝ) * δ := by
  rw [rowMean_decomposition w A, inner_add_right]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul ha (partialRowMean_norm_le hn w hw A hρ hcard) (norm_nonneg _) hC)
  · exact partialRowMean_correlation_le w Aᶜ a hunseen

/-- A concrete small learned fraction and small unobserved row correlations
keep every norm-three cone probe far from the source direction. -/
theorem rowMean_small_correlation (hn : 0 < n) (w : Fin n → E) (hw : Orthonormal ℝ w)
    (A : Finset (Fin n)) (a : E) (ha : ‖a‖ ≤ 3)
    (hcard : (A.card : ℝ) ≤ (n : ℝ) / 4096)
    (hunseen : ∀ i ∈ Aᶜ, |⟪a, w i⟫_ℝ| ≤ 1 / (64 * Real.sqrt (n : ℝ))) :
    |⟪a, rowMean w⟫_ℝ| ≤ 1 / 16 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hfrac : (Aᶜ.card : ℝ) / (n : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hn0).mpr
    have hc : (Aᶜ.card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show Aᶜ.card ≤ n by simpa using Finset.card_le_univ Aᶜ)
    simpa only [one_mul] using hc
  have hrem : (Real.sqrt (n : ℝ))⁻¹ * (Aᶜ.card : ℝ) * (1 / (64 * Real.sqrt (n : ℝ))) =
      ((Aᶜ.card : ℝ) / (n : ℝ)) / 64 := by
    calc
      _ = (Aᶜ.card : ℝ) / (64 * (Real.sqrt (n : ℝ)) ^ 2) := by field_simp [hroot.ne']
      _ = (Aᶜ.card : ℝ) / (64 * (n : ℝ)) := by rw [Real.sq_sqrt hn0.le]
      _ = _ := by ring
  have hh := rowMean_correlation_bound hn w hw A a (C := 3) (ρ := 1 / 64)
    (by norm_num) (by norm_num) ha (by nlinarith [hcard]) hunseen
  rw [hrem] at hh
  have hlast := div_le_div_of_nonneg_right hfrac (by norm_num : (0 : ℝ) ≤ 64)
  norm_num at hlast
  linarith

end

end NCConcave16991.Haar
