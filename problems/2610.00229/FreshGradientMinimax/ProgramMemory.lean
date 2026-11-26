import FreshGradientMinimax.ProgramResult

/-! Retaining and updating a countable record of program outputs costs no
additional oracle calls. Exact marginal identities support later sampling. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X : Type} [MeasurableSpace X]

def traceWrite (j : ℕ) (p : (ℕ → X) × X) : ℕ → X := Function.update p.1 (j + 1) p.2

theorem traceWrite_measurable (j : ℕ) : Measurable (traceWrite (X := X) j) := measurable_update'

namespace OracleProgram
variable {dx dy : ℕ} {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]

theorem update_result (P : OracleProgram dx dy X Y) (f : X × Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    (P.update f hf).resultKernel K = (Kernel.id ×ₖ P.resultKernel K).map f := by
  rw [resultKernel, update_law, costedUpdateKernel_first _ _ hf _ measurable_const]
  rfl

theorem update_result_apply (P : OracleProgram dx dy X Y) (f : X × Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (x : X) :
    (P.update f hf).resultKernel K x = (P.resultKernel K x).map (fun y => f (x, y)) := by
  rw [update_result, Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

theorem update_cost (P : OracleProgram dx dy X Y) (f : X × Y → Z) (hf : Measurable f)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (x : X)
    (hi : Integrable costValue (P.lawKernel K x)) :
    Integrable costValue ((P.update f hf).lawKernel K x) ∧
    (∫ t, costValue t ∂(P.update f hf).lawKernel K x) = ∫ t, costValue t ∂P.lawKernel K x := by
  rw [update_law]
  simpa only [Nat.cast_zero, zero_add] using costedUpdateKernel_cost (P.lawKernel K) f hf
    (fun _ => 0) measurable_const x hi

def recordStep (P : OracleProgram dx dy X X) (j : ℕ) : OracleProgram dx dy (ℕ → X) (ℕ → X) :=
  (P.precompose (fun t => t j) (measurable_pi_apply j)).update (traceWrite j) (traceWrite_measurable j)

theorem recordStep_result_new (P : OracleProgram dx dy X X) (j : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    ((P.recordStep j).resultKernel K).map (fun t => t (j + 1)) =
      (P.resultKernel K).comap (fun t => t j) (measurable_pi_apply j) := by
  apply Kernel.ext
  intro t
  rw [Kernel.map_apply _ (measurable_pi_apply (j + 1)), recordStep, update_result_apply,
    Measure.map_map (f := fun y : X => traceWrite j (t, y))
      (g := fun r : ℕ → X => r (j + 1)) (measurable_pi_apply (j + 1))
      ((traceWrite_measurable j).comp (measurable_prodMk_left (x := t)))]
  simp only [Function.comp_def, traceWrite, Function.update_self]
  rw [Measure.map_id', precompose_result, Kernel.comap_apply]

theorem recordStep_result_old (P : OracleProgram dx dy X X) (j k : ℕ) (hk : k ≠ j + 1)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] :
    ((P.recordStep j).resultKernel K).map (fun t => t k) =
      Kernel.deterministic (fun t => t k) (measurable_pi_apply k) := by
  apply Kernel.ext
  intro t
  rw [Kernel.map_apply _ (measurable_pi_apply k), recordStep, update_result_apply,
    Measure.map_map (f := fun y : X => traceWrite j (t, y))
      (g := fun r : ℕ → X => r k) (measurable_pi_apply k)
      ((traceWrite_measurable j).comp (measurable_prodMk_left (x := t)))]
  simp only [Function.comp_def, traceWrite, Function.update_of_ne hk, Measure.map_const,
    measure_univ, one_smul, Kernel.deterministic_apply]

theorem recordStep_new_law (P : OracleProgram dx dy X X) (j : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (ν : Measure (ℕ → X)) :
    ((P.recordStep j).resultKernel K ∘ₘ ν).map (fun t => t (j + 1)) =
      P.resultKernel K ∘ₘ ν.map (fun t => t j) := by
  rw [Measure.map_comp _ _ (measurable_pi_apply (j + 1)), recordStep_result_new,
    ← Measure.deterministic_comp_eq_map (measurable_pi_apply j),
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]

theorem recordStep_old_law (P : OracleProgram dx dy X X) (j k : ℕ) (hk : k ≠ j + 1)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (ν : Measure (ℕ → X)) :
    ((P.recordStep j).resultKernel K ∘ₘ ν).map (fun t => t k) = ν.map (fun t => t k) := by
  rw [Measure.map_comp _ _ (measurable_pi_apply k), recordStep_result_old P j k hk,
    Measure.deterministic_comp_eq_map (measurable_pi_apply k)]

theorem recordStep_cost (P : OracleProgram dx dy X X) (j : ℕ)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (t : ℕ → X)
    (hi : Integrable costValue (P.lawKernel K (t j))) :
    Integrable costValue ((P.recordStep j).lawKernel K t) ∧
    (∫ z, costValue z ∂(P.recordStep j).lawKernel K t) = ∫ z, costValue z ∂P.lawKernel K (t j) := by
  have hi' : Integrable costValue
      ((P.precompose (fun r : ℕ → X => r j) (measurable_pi_apply j)).lawKernel K t) := by
    rwa [precompose_law, Kernel.comap_apply]
  have h := (P.precompose (fun r : ℕ → X => r j) (measurable_pi_apply j)).update_cost
    (traceWrite j) (traceWrite_measurable j) K t hi'
  change Integrable costValue
      (((P.precompose (fun r : ℕ → X => r j) (measurable_pi_apply j)).update
        (traceWrite j) (traceWrite_measurable j)).lawKernel K t) ∧ _
  rw [precompose_law, Kernel.comap_apply] at h
  exact h

end OracleProgram
end FreshGradientMinimax
