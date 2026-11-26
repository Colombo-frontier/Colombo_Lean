import FreshGradientMinimax.RecursiveAccuracy

/-! The known linear coefficient is retained exactly by an actual value
solve. This gives the adjacent-stage coupling used in the gradient proof. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem quadraticValueProgram_result_fiber (O : FreshOracle S.toNCObjective σ) (a e E : ℝ)
    (b : Euclid dy) :
    ((quadraticValueProgram dx dy ℓ α σ μ a e E).resultKernel O.kernel).comap
      (fun z => (b, z)) measurable_prodMk_left =
    (S.valueSolverKernel O (μ + a) (5 * ℓ + a) e E
      (fun v => dualQuadraticCorrection a (b, v))
      ((dualQuadraticCorrection_continuous a).measurable.comp measurable_prodMk_left)).map (fun z => (b, z)) := by
  have h := costed_transport_first _ _ _ measurable_prodMk_left _ measurable_prodMk_left
    (S.parameterValueSolverProgram_fiber O (μ + a) (5 * ℓ + a) e E
      (dualQuadraticCorrection a) (dualQuadraticCorrection_continuous a).measurable b)
  rw [S.costedValueSolverKernel_first] at h
  exact h

theorem quadraticValueProgram_result_apply (O : FreshOracle S.toNCObjective σ) (a e E : ℝ)
    (z : Euclid dy × Joint dx dy) :
    (quadraticValueProgram dx dy ℓ α σ μ a e E).resultKernel O.kernel z =
    (S.valueSolverKernel O (μ + a) (5 * ℓ + a) e E
      (fun v => dualQuadraticCorrection a (z.1, v))
      ((dualQuadraticCorrection_continuous a).measurable.comp measurable_prodMk_left) z.2).map (fun w => (z.1, w)) := by
  have h := congrArg (fun K : Kernel (Joint dx dy) (Euclid dy × Joint dx dy) => K z.2)
    (S.quadraticValueProgram_result_fiber O a e E z.1)
  dsimp only at h
  rw [Kernel.comap_apply, Kernel.map_apply _ measurable_prodMk_left] at h
  exact h

theorem quadraticValueProgram_coefficient (O : FreshOracle S.toNCObjective σ) (a e E : ℝ)
    (z : Euclid dy × Joint dx dy) :
    ∀ᵐ w ∂(quadraticValueProgram dx dy ℓ α σ μ a e E).resultKernel O.kernel z, w.1 = z.1 := by
  rw [S.quadraticValueProgram_result_apply]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_const)).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem recursiveStageProgram_coefficient (O : FreshOracle S.toNCObjective σ)
    (δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ) (z : Euclid dy × Joint dx dy) :
    ∀ᵐ w ∂(recursiveStageProgram dx dy ℓ α σ μ δ N E j).resultKernel O.kernel z, w.1 = z.1 :=
  S.quadraticValueProgram_coefficient O _ _ _ z

theorem recursive_adjacent_coefficient (O : FreshOracle S.toNCObjective σ)
    (δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ) (ν : Measure (Euclid dy × Joint dx dy)) :
    ∀ᵐ p ∂ν ⊗ₘ (((recursiveStageProgram dx dy ℓ α σ μ δ N E (j + 1)).resultKernel O.kernel).comap
      (quadraticAdvance (recursiveMass μ j)) (quadraticAdvance_continuous _).measurable),
      p.2.1 = p.1.1 + recursiveMass μ j • p.1.2.2 := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun measurable_snd.fst
      (measurable_fst.fst.add (measurable_const.smul measurable_fst.snd.snd)))
  exact Filter.Eventually.of_forall (fun z => S.recursiveStageProgram_coefficient O δ N E (j + 1) _)

end SCObjective
end FreshGradientMinimax
