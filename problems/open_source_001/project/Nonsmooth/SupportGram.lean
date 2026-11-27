import Nonsmooth.FiniteSupport

open MeasureTheory Function
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def supportRowSynthesis {k : ℕ} (a : Fin k → E) : (Fin k → ℝ) →ₗ[ℝ] E where
  toFun c := ∑ i, c i • a i
  map_add' c v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def supportGramMap {k : ℕ} (a : Fin k → E) : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi (fun i => (innerSL ℝ (a i)).toLinearMap.comp (supportRowSynthesis a))

theorem supportGramMap_apply {k : ℕ} (a : Fin k → E) (c : Fin k → ℝ) (i : Fin k) :
    supportGramMap a c i = ⟪a i, supportRowSynthesis a c⟫_ℝ := rfl

theorem supportGramMap_energy {k : ℕ} (a : Fin k → E) (c : Fin k → ℝ) :
    ‖supportRowSynthesis a c‖ ^ 2 = ∑ i, c i * supportGramMap a c i := by
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => lhs; change ∑ i, c i • a i
  simp only [sum_inner, real_inner_smul_left, supportGramMap_apply]

theorem supportGramMap_injective {k : ℕ} (a : Fin k → E)
    (hGram : ∀ c : Fin k → ℝ, (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤ ‖supportRowSynthesis a c‖ ^ 2) :
    Injective (supportGramMap a) := by
  intro c v hcv
  have hz : supportGramMap a (c - v) = 0 := by rw [map_sub, hcv, sub_self]
  have he : ‖supportRowSynthesis a (c - v)‖ ^ 2 = 0 := by
    rw [supportGramMap_energy, hz]
    simp
  have hc := hGram (c - v)
  rw [he] at hc
  have hs : ∑ i, ((c - v) i) ^ 2 ≤ 0 := by linarith
  funext i
  have hi : ((c - v) i) ^ 2 ≤ ∑ j, ((c - v) j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hi0 : (c - v) i = 0 := sq_eq_zero_iff.mp (le_antisymm (hi.trans hs) (sq_nonneg _))
  exact sub_eq_zero.mp hi0

theorem supportGramMap_solve_ones {k : ℕ} (a : Fin k → E)
    (hGram : ∀ c : Fin k → ℝ, (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤ ‖supportRowSynthesis a c‖ ^ 2) :
    ∃ c : Fin k → ℝ, supportGramMap a c = fun _ => 1 :=
  LinearMap.injective_iff_surjective.mp (supportGramMap_injective a hGram) (fun _ => 1)

theorem supportGramMap_solution_norm {k : ℕ} (a : Fin k → E)
    (hGram : ∀ c : Fin k → ℝ, (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤ ‖supportRowSynthesis a c‖ ^ 2)
    (c : Fin k → ℝ) (hc : supportGramMap a c = fun _ => 1) :
    ‖supportRowSynthesis a c‖ ^ 2 ≤ 4 * (k : ℝ) := by
  have he : ‖supportRowSynthesis a c‖ ^ 2 = ∑ i, c i := by
    rw [supportGramMap_energy, hc]
    simp only [mul_one]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) (fun _ => (1 : ℝ)) c
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have hh := hGram c
  have hh' : (k : ℝ) * ∑ i, (c i) ^ 2 ≤ (k : ℝ) * (4 * ‖supportRowSynthesis a c‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
  rw [← he] at hcs
  have hn := sq_nonneg ‖supportRowSynthesis a c‖
  nlinarith

/-- A deterministic witness for the source's negative optimum event from the Gram
lower bound. The Gaussian probability of that lower bound is not assumed proved here. -/
theorem finiteSupport_negative_witness_of_gram_bound {k : ℕ} (hk : 0 < k) (a : Fin k → E)
    (hGram : ∀ c : Fin k → ℝ, (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤ ‖supportRowSynthesis a c‖ ^ 2) :
    ∃ x : E, ‖x‖ ≤ 1 / 2 ∧ ∀ i, ⟪a i, x⟫_ℝ = -(1 / 4 : ℝ) / Real.sqrt k := by
  obtain ⟨c, hc⟩ := supportGramMap_solve_ones a hGram
  have hn := supportGramMap_solution_norm a hGram c hc
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hroot : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk'
  have hns : ‖supportRowSynthesis a c‖ ≤ 2 * Real.sqrt (k : ℝ) := by
    nlinarith [Real.sq_sqrt hk'.le, norm_nonneg (supportRowSynthesis a c)]
  refine ⟨(-(1 / 4 : ℝ) / Real.sqrt k) • supportRowSynthesis a c, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
      abs_of_pos hroot, div_mul_eq_mul_div]
    apply (div_le_iff₀ hroot).mpr
    linarith
  · intro i
    rw [inner_smul_right, ← supportGramMap_apply, hc, mul_one]

theorem boundedFiniteSupport_negative_of_gram_bound {k : ℕ} (hk : 0 < k)
    (a : BoundedSupportRows E (Fin k))
    (hGram : ∀ c : Fin k → ℝ, (1 / 4 : ℝ) * (∑ i, (c i) ^ 2) ≤
      ‖supportRowSynthesis (fun i => (a i).val) c‖ ^ 2) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨x, hx, ha⟩ := finiteSupport_negative_witness_of_gram_bound hk (fun i => (a i).val) hGram
  have hmin := support_minimum_le (boundedFiniteSupport_model a) (show ‖x‖ ≤ 1 by linarith)
  obtain ⟨i, hi⟩ := finiteSupport_attained (fun i => (a i).val) x
  change boundedFiniteSupport a x = _ at hi
  rw [hi, ha] at hmin
  rw [neg_div] at hmin
  linarith

end
end Nonsmooth
