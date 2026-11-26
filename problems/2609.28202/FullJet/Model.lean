import FullJet.RareComponent
import FullJet.Opacity

open scoped BigOperators ContDiff

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite sum with the normalization from the paper. -/
noncomputable def average {n : ℕ} (f : Fin n → E → ℝ) (x : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f i x

/-- Actual value-inclusive derivative packet. -/
noncomputable def fullJet (p : ℕ) (f : E → ℝ) (x : E) :
    (r : Fin (p + 1)) → E [×r.val]→L[ℝ] ℝ :=
  fun r => iteratedFDeriv ℝ r.val f x

/-- The paper's componentwise function class, with the gap expressed without
an infimum: `F 0 - F x ≤ Δ` for every `x`, equivalent to the finite-gap condition. -/
structure Admissible (p n : ℕ) (Δ L : ℝ) (f : Fin n → E → ℝ) : Prop where
  n_pos : 0 < n
  smooth : ∀ i, ContDiff ℝ p (f i)
  derivative_lipschitz : ∀ i x y,
    ‖iteratedFDeriv ℝ p (f i) x - iteratedFDeriv ℝ p (f i) y‖ ≤ L * ‖x - y‖
  gap : ∀ x, average f 0 - average f x ≤ Δ

noncomputable def rareComponent {n : ℕ} (J : Fin n) (μ g σ : ℝ) (i : Fin n) : ℝ → ℝ :=
  quadratic μ (if i = J then (n : ℝ) * σ * g else 0)

theorem rareComponent_eq_common {n : ℕ} (J i : Fin n) (μ g σ : ℝ) (hi : i ≠ J) :
    rareComponent J μ g σ i = quadratic μ 0 := by simp [rareComponent, hi]

theorem rare_fullJet_eq_common {n : ℕ} (J i : Fin n) (μ g σ x : ℝ)
    (p : ℕ) (hi : i ≠ J) :
    fullJet p (rareComponent J μ g σ i) x = fullJet p (quadratic μ 0) x := by
  rw [rareComponent_eq_common J i μ g σ hi]

theorem rare_average {n : ℕ} (hn : 0 < n) (J : Fin n) (μ g σ x : ℝ) :
    average (rareComponent J μ g σ) x = quadratic μ (σ * g) x := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold average rareComponent quadratic
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  <;> ring

theorem quadratic_contDiff (μ c : ℝ) : ContDiff ℝ ∞ (quadratic μ c) :=
  (contDiff_const.mul (contDiff_id.pow 2)).sub (contDiff_const.mul contDiff_id)

theorem quadratic_iteratedFDeriv_constant (μ c : ℝ) (p : ℕ) (hp : 2 ≤ p) (x y : ℝ) :
    iteratedFDeriv ℝ p (quadratic μ c) x = iteratedFDeriv ℝ p (quadratic μ c) y := by
  ext v
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  by_cases hp2 : p = 2
  · subst p
    rw [quadratic_second_deriv]
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 3 := ⟨p - 3, by omega⟩
    rw [quadratic_higher_deriv]
    simp

/-- The rare quadratic belongs to the actual full-jet smoothness class for
every `p ≥ 2` and every positive requested smoothness budget. -/
theorem rareComponent_admissible {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p)
    (J : Fin n) (Δ ε L σ : ℝ) (hΔ : 0 < Δ) (hε : 0 < ε) (hL : 0 ≤ L)
    (hσ : σ ^ 2 = 1) :
    Admissible p n Δ L (rareComponent J ((4 * ε) ^ 2 / (2 * Δ)) (4 * ε) σ) := by
  let μ := (4 * ε) ^ 2 / (2 * Δ)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hgap : (σ * (4 * ε)) ^ 2 / (2 * μ) = Δ := by
    rw [mul_pow, hσ, one_mul]
    exact (rare_gap_parameters Δ ε hΔ hε).2
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro i
    exact (quadratic_contDiff _ _).of_le (by
      exact_mod_cast (show (p : ℕ∞) ≤ ⊤ from le_top))
  · intro i x y
    rw [show rareComponent J μ (4 * ε) σ i = quadratic μ _ from rfl,
      quadratic_iteratedFDeriv_constant μ _ p hp x y, sub_self, norm_zero]
    exact mul_nonneg hL (norm_nonneg _)
  · intro x
    rw [rare_average hn, rare_average hn]
    have hmin := quadratic_global_minimum μ (σ * (4 * ε)) hμ
    have hlow := hmin.1 x
    have hvalue := hmin.2
    rw [hgap] at hvalue
    linarith

end FullJet
