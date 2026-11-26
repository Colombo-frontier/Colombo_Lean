import SecondOrder.GateRegularization

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def regularizedMixture (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ) (δ : ℝ) : E → ℝ :=
  bernoulliMixture (fun i => regularizedGate δ (p i)) V

@[simp] theorem regularizedMixture_zero (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ) :
    regularizedMixture p V 0 = bernoulliMixture p V := by
  simp only [regularizedMixture, regularizedGate_zero]

theorem regularizedMixture_joint_contDiff (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    {k : WithTop ℕ∞} (hp : ∀ i, ContDiff ℝ k (p i)) (hV : ∀ w, ContDiff ℝ k (V w)) :
    ContDiff ℝ k (Function.uncurry (regularizedMixture p V)) :=
  contDiff_bernoulliMixture (fun i (z : ℝ × E) => regularizedGate z.1 (p i) z.2)
    (fun w z => V w z.2) (fun i => regularizedGate_joint_contDiff (hp i))
    (fun w => (hV w).comp contDiff_snd)

/-- Both actual derivative norms converge continuously when regularization is removed. -/
theorem regularizedMixture_continuous_derivatives (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w)) (x : E) :
    Continuous (fun δ : ℝ => ‖fderiv ℝ (regularizedMixture p V δ) x‖) ∧
      Continuous (fun δ : ℝ => ‖fderiv ℝ (fderiv ℝ (regularizedMixture p V δ)) x‖) :=
  continuous_parametric_derivative_norms (regularizedMixture_joint_contDiff p V hp hV) x

theorem continuous_le_at_zero_of_Ioo {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hbound : ∀ δ, 0 < δ → δ < 1/2 → f δ ≤ C) : f 0 ≤ C := by
  have hsub : closure (Set.Ioo (0:ℝ) (1/2)) ⊆ {δ | f δ ≤ C} :=
    closure_minimal (fun δ hδ => hbound δ hδ.1 hδ.2) (isClosed_le hf continuous_const)
  apply hsub
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1/2)]
  norm_num

end
end SecondOrder
