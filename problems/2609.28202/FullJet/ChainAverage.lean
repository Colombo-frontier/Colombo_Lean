import FullJet.ChainSmoothness
import FullJet.Model

open scoped ContDiff BigOperators

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

/-- The deterministic average chain in the manuscript. -/
noncomputable def baseChain (θ : Fin (T + 1) → E) (lam : ℝ) (x : BlockSpace T E) : ℝ :=
  -alignment (θ 0) (x 0) -
    ∑ j : Fin T, gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) *
      (alignment (θ j.succ) (x j.succ) + 1) + lam / 2 * ‖x‖ ^ 2

theorem baseChain_eq_componentChain (θ : Fin (T + 1) → E) (lam : ℝ) :
    baseChain θ lam = componentChain θ θ 1 lam := by
  funext x
  simp [baseChain, componentChain, chainLink, concreteLink, gateAlignment, rowFactor,
    adjacentProjection, blockProjection]

theorem baseChain_zero (θ : Fin (T + 1) → E) (lam : ℝ) : baseChain θ lam 0 = 0 := by
  have hg : gate (5 / 32) (9 / 32) 0 = 0 := gate_zero (by norm_num) (by norm_num)
  simp [baseChain, alignment, radial, hg]

/-- A concrete global gap bound, independent of dimension, table, or bias. -/
theorem baseChain_gap (θ : Fin (T + 1) → E) (hθ : ∀ j, ‖θ j‖ ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (x : BlockSpace T E) :
    baseChain θ lam 0 - baseChain θ lam x ≤ 2 * (T + 1 : ℕ) := by
  have ha (j : Fin (T + 1)) : |alignment (θ j) (x j)| ≤ 1 :=
    (alignment_bound _ _).trans (hθ j)
  have hhead : alignment (θ 0) (x 0) ≤ 1 := (le_abs_self _).trans (ha 0)
  have hlink (j : Fin T) :
      gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) *
        (alignment (θ j.succ) (x j.succ) + 1) ≤ 2 := by
    have hq := abs_le.mp (ha j.succ)
    have hg := gate_range (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc))
    nlinarith [mul_nonneg (sub_nonneg.mpr hg.2) (by linarith :
      0 ≤ alignment (θ j.succ) (x j.succ) + 1)]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin T))) => hlink j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hreg : 0 ≤ lam / 2 * ‖x‖ ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
  rw [baseChain_zero]
  unfold baseChain
  push_cast
  linarith

/-- Averaging an affine chain commutes with the exact row averages. -/
theorem average_affine_chain {n : ℕ} (hn : (n : ℝ) ≠ 0)
    (Q : Fin n → Fin (T + 1) → ℝ) (a : Fin (T + 1) → ℝ)
    (w : Fin T → ℝ) (c : ℝ)
    (hQ : ∀ j, (n : ℝ)⁻¹ * ∑ i, Q i j = a j) :
    (n : ℝ)⁻¹ * ∑ i, (-Q i 0 - ∑ j : Fin T, w j * (Q i j.succ + 1) + c) =
      -a 0 - ∑ j : Fin T, w j * (a j.succ + 1) + c := by
  have havg (j : Fin T) : (n : ℝ)⁻¹ * ∑ i, w j * (Q i j.succ + 1) =
      w j * (a j.succ + 1) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have h := hQ j.succ
    calc
      _ = w j * ((n : ℝ)⁻¹ * ∑ i, Q i j.succ + (n : ℝ)⁻¹ * n) := by ring
      _ = _ := by rw [h, inv_mul_cancel₀ hn]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_comm, mul_add, mul_sub, mul_neg, hQ 0, Finset.mul_sum]
  simp only [havg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The fixed sign-table constraint gives the exact deterministic average. -/
theorem componentChain_average {n : ℕ} (hn : 0 < n)
    (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E) (ρ lam : ℝ)
    (hρ : ρ ≠ 0) (htable : ∀ j, ∑ i, s i j = ((n : ℝ) * ρ) • θ j)
    (x : BlockSpace T E) :
    average (fun i => componentChain θ (s i) ρ lam) x = baseChain θ lam x := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change (n : ℝ)⁻¹ * ∑ i, (-(ρ⁻¹ * alignment (s i 0) (x 0)) -
    ∑ j : Fin T, gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) *
      (ρ⁻¹ * alignment (s i j.succ) (x j.succ) + 1) + lam / 2 * ‖x‖ ^ 2) = _
  exact average_affine_chain hn' (fun i j => ρ⁻¹ * alignment (s i j) (x j))
    (fun j => alignment (θ j) (x j)) _ _
    (fun j => alignment_average (fun i => s i j) (θ j) (x j) ρ hn' hρ (htable j))

end FullJet
