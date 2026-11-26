import Bilevel.ConditionalConfidenceMeasurable

/-! Finite-run form of the manuscript's conditional confidence lemma.
The padding in this proof is deterministic and contributes zero error.
-/
noncomputable section
open MeasureTheory
namespace Bilevel.ConditionalConfidence

variable {Ω E : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [PseudoMetricSpace E] {q : ℕ} [NeZero q]

/-- Finite `q`-run confidence amplification, from conditional second
moments and past measurability alone. This theorem uses the exact selector,
including least-index tie breaking, with no independence assumption. -/
theorem confidence_finite (Z : Ω → Fin q → E) (target : E)
    (past : Fin q → MeasurableSpace Ω) (hpast : ∀ n, past n ≤ m₀)
    (hmeas : ∀ n, Measurable (fun ω => dist (Z ω n) target))
    (hadapted : ∀ i n, i < n →
      Measurable[past n] (fun ω => dist (Z ω i) target))
    (a : ℝ) (ha : 0 < a)
    (hsquare : ∀ n, Integrable (fun ω => dist (Z ω n) target ^ 2) μ)
    (hmse : ∀ n, ∀ᵐ ω ∂μ,
      (μ[(fun ω => dist (Z ω n) target ^ 2) | past n]) ω ≤ a ^ 2 / 144) :
    μ.real {ω | a < dist (select (Z ω)) target} ≤ Real.exp (-(q : ℝ) / 8) := by
  let Zext : Ω → ℕ → E := fun ω n => if hn : n < q then Z ω ⟨n, hn⟩ else target
  let pastExt : ℕ → MeasurableSpace Ω := fun n => if hn : n < q then past ⟨n, hn⟩ else m₀
  have hpastExt : ∀ n, pastExt n ≤ m₀ := by
    intro n
    dsimp only [pastExt]
    split_ifs with hn
    · exact hpast ⟨n, hn⟩
    · exact le_rfl
  have hmeasExt : ∀ n, Measurable (fun ω => dist (Zext ω n) target) := by
    intro n
    by_cases hn : n < q
    · simpa only [Zext, hn, ↓reduceDIte] using hmeas ⟨n, hn⟩
    · simp only [Zext, hn, ↓reduceDIte, dist_self]
      exact measurable_const
  have hadaptedExt : ∀ i n, i < n →
      Measurable[pastExt n] (fun ω => dist (Zext ω i) target) := by
    intro i n hin
    by_cases hn : n < q
    · have hi := hin.trans hn
      simpa only [Zext, pastExt, hn, hi, ↓reduceDIte] using
        hadapted ⟨i, hi⟩ ⟨n, hn⟩ hin
    · simpa only [pastExt, hn, ↓reduceDIte] using hmeasExt i
  have hsquareExt : ∀ n, Integrable (fun ω => dist (Zext ω n) target ^ 2) μ := by
    intro n
    by_cases hn : n < q
    · simpa only [Zext, hn, ↓reduceDIte] using hsquare ⟨n, hn⟩
    · simp only [Zext, hn, ↓reduceDIte, dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact integrable_zero _ _ _
  have hmseExt : ∀ n, ∀ᵐ ω ∂μ,
      (μ[(fun ω => dist (Zext ω n) target ^ 2) | pastExt n]) ω ≤ a ^ 2 / 144 := by
    intro n
    by_cases hn : n < q
    · simpa only [Zext, pastExt, hn, ↓reduceDIte] using hmse ⟨n, hn⟩
    · simp only [Zext, pastExt, hn, ↓reduceDIte, dist_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, condExp_zero, Pi.zero_apply]
      change ∀ᵐ ω ∂μ, (μ[(0 : Ω → ℝ) | m₀]) ω ≤ a ^ 2 / 144
      rw [condExp_zero]
      exact Filter.Eventually.of_forall fun _ =>
        (show (0 : ℝ) ≤ a ^ 2 / 144 from div_nonneg (sq_nonneg a) (by norm_num))
  have hc := confidence_from_conditional_mse Zext target pastExt hpastExt
    hmeasExt hadaptedExt a ha hsquareExt hmseExt q
  have hext : ∀ ω, (fun i : Fin q => Zext ω i) = Z ω := by
    intro ω
    funext i
    simp only [Zext, i.isLt, ↓reduceDIte]
  simpa only [hext] using hc

end Bilevel.ConditionalConfidence
