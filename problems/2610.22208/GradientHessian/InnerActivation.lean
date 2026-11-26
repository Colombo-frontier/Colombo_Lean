import GradientHessian.InnerTransition

/-! Complete inner activation for the literal manuscript objective. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace Y] [CompleteSpace E] in
theorem driven_numerical_slice_completed (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) (hp : ∀ i, ports v Z i = 1) (y : Y) :
    driven A b a v l (replaceNumerical Z y) = InverseGate.quadratic A y + (selfSum v Z - l) := by
  have hports : ports v (replaceNumerical Z y) = ports v Z := by
    funext i
    simp [ports]
  have hF : forcingSum b a v (replaceNumerical Z y) = 0 := by
    unfold forcingSum
    rw [hports]
    exact InnerSelector.select_all_one _ _ _ hp
  have hO : outgoing v (replaceNumerical Z y) = 1 := by
    unfold outgoing
    rw [hports, hp]
  have hS : selfSum v (replaceNumerical Z y) = selfSum v Z := by simp [selfSum]
  simp only [driven, objective, numerical_replaceNumerical, hF, hS, hO]
  ring

/-- Source equation (inner-activate), using the actual physical Euclidean
gradient, unrestricted task count, and inverse certificates constructed from
the lower spectral bound. -/
theorem activation (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ)
    (b a : Fin (m + 1) → Y) (v : Fin (m + 1) → Fin (k + 2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1)
    (hcert : ∀ i, InverseGate.H₀ / 4 ≤ ⟪a i, InverseGate.inverse A hA (b i)⟫_ℝ)
    (hv : ∀ i j, ‖v i j‖ = 1) {l : ℝ} (hl : 0 ≤ l)
    (hR : 144 * payloadBound ≤ lastRadius k) (Z : Space Y E (m + 1) (k + 2))
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) :
    (∀ i, ports v Z i = 1) ∧ ‖A (numerical Y E (m + 1) (k + 2) Z)‖ ≤ 1 := by
  have hall : ∀ i, ports v Z i = 1 := by
    intro i
    induction i using (measure (fun j : Fin (m + 1) => j.val)).wf.induction with
    | h i ih =>
      have hprev : ∀ j, j < i → ports v Z j = 1 := fun j hj => ih j hj
      by_cases hi : ports v Z i = 1
      · exact hi
      · have hbounds := ports_bounds v Z i
        by_cases hz : ports v Z i = 0
        · exact (first_zero_impossible A hA hsym b a v hl Z i (hb i) (ha i)
            (hcert i) (hv i) hprev hz hg).elim
        · exact (first_transition_impossible A b a v hl hR Z i (hv i _) hprev
            (lt_of_le_of_ne hbounds.1 (Ne.symm hz)) (lt_of_le_of_ne hbounds.2 hi) hg).elim
  refine ⟨hall, ?_⟩
  have hs := (numerical_slice_gradient_norm_le Z (driven A b a v l)
    ((driven_contDiff A b a v l).differentiable (by norm_num) Z)).trans hg
  rw [funext (driven_numerical_slice_completed A b a v l Z hall),
    (LatchChain.add_constant_hasGradientAt
      (InverseGate.quadratic_hasGradientAt A hsym (numerical Y E (m + 1) (k + 2) Z))
      (selfSum v Z - l)).gradient] at hs
  exact hs

/-- One concrete absolute choice; it is independent of task count and all
register dimensions. It gives 53 physical registers per task. -/
def absoluteDepth : ℕ := 51

theorem absoluteRadius_sufficient : 144 * payloadBound ≤ lastRadius absoluteDepth := by
  norm_num [absoluteDepth, lastRadius, payloadBound, InverseGate.H₀]

theorem absolute_activation (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ)
    (b a : Fin (m + 1) → Y) (v : Fin (m + 1) → Fin (absoluteDepth + 2) → E)
    (hb : ∀ i, ‖b i‖ = InverseGate.H₀) (ha : ∀ i, ‖a i‖ = 1)
    (hcert : ∀ i, InverseGate.H₀ / 4 ≤ ⟪a i, InverseGate.inverse A hA (b i)⟫_ℝ)
    (hv : ∀ i j, ‖v i j‖ = 1) {l : ℝ} (hl : 0 ≤ l)
    (Z : Space Y E (m + 1) (absoluteDepth + 2))
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) :
    (∀ i, ports v Z i = 1) ∧ ‖A (numerical Y E (m + 1) (absoluteDepth + 2) Z)‖ ≤ 1 :=
  activation A hA hsym b a v hb ha hcert hv hl absoluteRadius_sufficient Z hg

end GradientHessian.Inner
