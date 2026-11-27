import Nonsmooth.ParametricSelection
import Nonsmooth.ObservedBayes

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {n : ℕ}

/-- Actual conditional independence is preserved when an adaptive maximum/winner response is appended. -/
theorem support_conditional_independence_update
    (Q : Measure (Fin (n + 1) → E)) [IsProbabilityMeasure Q]
    (X : (Fin (n + 1) → E) → α) (hX : Measurable X) (u : α → E) (hu : Measurable u)
    (h : ∀ᵐ x ∂Q.map X, iIndepFun (fun i (a : Fin (n + 1) → E) => a i)
      (condDistrib id X Q x)) :
    ∀ᵐ p ∂Q.map (fun a => (X a, supportSingleObservation (u (X a)) a)),
      iIndepFun (fun i (a : Fin (n + 1) → E) => a i)
        (condDistrib id (fun a => (X a, supportSingleObservation (u (X a)) a)) Q p) := by
  let κ := condDistrib id X Q
  let F : α × (Fin (n + 1) → E) → Fin (n + 1) × ℝ :=
    fun p => supportSingleObservation (u p.1) p.2
  have hF : Measurable F := supportParametricObservation_measurable u hu
  have hκ : (Q.map X) ⊗ₘ κ = Q.map (fun a => (X a, id a)) :=
    compProd_map_condDistrib aemeasurable_id
  have hbase := observedPosterior_update_base Q X hX id measurable_id κ hκ F hF
  have heq := observedPosterior_update_ae_eq Q X hX id measurable_id κ hκ F hF
  have hi := supportPosteriorUpdate_independent (Q.map X) κ u hu h
  rw [← hbase] at hi
  filter_upwards [hi, heq] with p hp he
  dsimp only [F, id_eq] at he
  rw [← he]
  exact hp

end
end Nonsmooth
