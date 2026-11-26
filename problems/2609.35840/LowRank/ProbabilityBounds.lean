import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Measure-theoretic consequences of explicitly supplied posterior bounds.
The Gaussian posterior bounds themselves are not assumed as global axioms. -/

namespace LowRank
open MeasureTheory
open scoped BigOperators

theorem harmonic_query_bound {d k : ℝ} {q : ℕ}
    (hk : 0 ≤ k) (hq : (q : ℝ) < d) :
    (∑ t ∈ Finset.range q, k / (d - t)) ≤ k * q / (d - q) := by
  calc
    _ ≤ ∑ _t ∈ Finset.range q, k / (d - q) := by
      apply Finset.sum_le_sum
      intro t ht
      have htq : (t : ℝ) ≤ q := by exact_mod_cast (Finset.mem_range.mp ht).le
      exact div_le_div_of_nonneg_left hk (by linarith) (by linarith)
    _ = _ := by simp; ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Summation and the tower property for query increments. A later Gaussian module
must prove `hstep` for actual adaptive queries before this can be applied to them. -/
theorem query_mass_of_conditional_bounds {d k : ℝ} {q : ℕ}
    (hk : 0 ≤ k) (hq : (q : ℝ) < d)
    (f : ℕ → Ω → ℝ) (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ mΩ)
    (hfi : ∀ t ∈ Finset.range q, Integrable (f t) μ)
    (hstep : ∀ t ∈ Finset.range q,
      ∀ᵐ ω ∂μ, μ[f t | F t] ω ≤ k / (d - t)) :
    (∫ ω, ∑ t ∈ Finset.range q, f t ω ∂μ) ≤ k * q / (d - q) := by
  rw [integral_finset_sum _ hfi]
  apply le_trans _ (harmonic_query_bound hk hq)
  apply Finset.sum_le_sum
  intro t ht
  rw [← integral_condExp (hF t)]
  have h := integral_mono_ae (integrable_condExp (f := f t))
    (integrable_const (k / (d - t))) (hstep t ht)
  simpa using h

/-- Expectation step after the deterministic PSD block bound has been proved. -/
theorem overlap_expectation_of_posterior {d k q : ℝ} {z mass : Ω → ℝ}
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ)
    (hmass : Integrable mass μ)
    (hpost : ∀ᵐ ω ∂μ, μ[z | F] ω ≤ 2 * mass ω + 2 * k ^ 2 / (d - q))
    (hbudget : (∫ ω, mass ω ∂μ) ≤ k * q / (d - q)) :
    (∫ ω, z ω ∂μ) ≤ 2 * k * (q + k) / (d - q) := by
  rw [← integral_condExp hF]
  have h := integral_mono_ae (integrable_condExp (f := z))
    ((hmass.const_mul 2).add (integrable_const (2 * k ^ 2 / (d - q)))) hpost
  simp only [Pi.add_apply] at h
  rw [integral_add (hmass.const_mul 2) (integrable_const _), integral_const_mul] at h
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at h
  calc
    _ ≤ 2 * (∫ ω, mass ω ∂μ) + 2 * k ^ 2 / (d - q) := h
    _ ≤ 2 * (k * q / (d - q)) + 2 * k ^ 2 / (d - q) := by linarith
    _ = _ := by ring

theorem overlap_tail_bound {d k q : ℝ} {z : Ω → ℝ}
    (hk : 0 < k) (hzi : Integrable z μ) (hz : 0 ≤ᵐ[μ] z)
    (hmean : (∫ ω, z ω ∂μ) ≤ 2 * k * (q + k) / (d - q)) :
    μ.real {ω | 3 * k / 4 ≤ z ω} ≤ (8 / 3) * (q + k) / (d - q) := by
  have h := (mul_meas_ge_le_integral_of_nonneg hz hzi (3 * k / 4)).trans hmean
  have heq : 2 * k * (q + k) / (d - q) =
      (3 * k / 4) * ((8 / 3) * (q + k) / (d - q)) := by ring
  rw [heq] at h
  exact (mul_le_mul_left (by linarith : 0 < 3 * k / 4)).mp h

theorem overlap_tail_constant {d k q : ℝ}
    (hd : 0 < d) (hq : q ≤ d / 100) (hk : k ≤ d / 100) :
    (8 / 3) * (q + k) / (d - q) ≤ 1 / 10 := by
  apply (div_le_iff₀ (by linarith : 0 < d - q)).mpr
  linarith

theorem success_probability_of_good_event {S E T : Set Ω}
    (hS : S ∩ E ⊆ T) (hbad : μ.real Eᶜ ≤ 1 / 20)
    (hT : μ.real T ≤ 1 / 10) : μ.real S ≤ 3 / 20 := by
  have hsub : S ⊆ Eᶜ ∪ T := by
    intro ω hω
    by_cases he : ω ∈ E
    · exact Or.inr (hS ⟨hω, he⟩)
    · exact Or.inl he
  have h := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  linarith

end LowRank
