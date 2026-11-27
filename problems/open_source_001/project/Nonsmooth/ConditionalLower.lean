import Nonsmooth.FiniteSupport

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The modular support hardness proposition used by the lower-bound assembly.
For each k the same prior precedes the budget and policy. CompleteGaussianHardness
proves this proposition with explicit universal constants. -/
def SupportHardnessInput (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (cdim cprob γ : ℝ) (dext : ℕ) : Prop :=
  ∀ (k : ℕ) (hk : 0 < k),
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    dext ≤ Module.finrank ℝ E → (k : ℝ) ≤ cdim * Module.finrank ℝ E →
    ∃ Q : Measure (BoundedSupportRows E (Fin k)), IsProbabilityMeasure Q ∧
      7 / 8 ≤ Q.real {a | γ / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a)} ∧
      ∀ T : ℕ, (T : ℝ) ≤ cprob * Module.finrank ℝ E * k / Real.log (Real.exp 1 * k) →
      ∀ (S : Type) (mS : MeasurableSpace S),
        letI := mS
        ∀ q : Policy Unit S (Feasible E 1), q.IsMeasurable →
          3 / 4 ≤ Q.real {a | 7 * (γ / Real.sqrt k) / 16 <
            boundedFiniteSupport a (q.result (fun x => boundedFiniteSupport a x.val) () T).val -
              minimumValue 1 (boundedFiniteSupport a)}

end
end Nonsmooth
