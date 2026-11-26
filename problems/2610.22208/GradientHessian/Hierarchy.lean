import GradientHessian.Selectors
import GradientHessian.JetLocality

/-!
# The literal hierarchy node and its exact branch restrictions

All component functions are lifted to the same physical coordinate space `Z`.
The combinator imposes no artificial norm on concatenated coordinates. Index
`i = 0` is manuscript child one. Scalar identities here are valid for every
choice of the actual child functions, and local identities give actual jets.
-/

noncomputable section

namespace GradientHessian.Hierarchy

open scoped BigOperators Topology
open Filter

variable {Z : Type*}

def nodeScalar (b : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) : ℝ :=
  baseline z +
    (∑ i ∈ Finset.range b, Selectors.weight (fun j => parentPort j z) i *
      (child i z - baseline z - i * spacing - incoming i z * childPort i z)) -
    b * spacing * Selectors.prefixProduct (fun j => parentPort j z) b +
    ∑ i ∈ Finset.range b, parentSelf i z

theorem node_completed (b : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hp : ∀ i < b, parentPort i z = 1) :
    nodeScalar b baseline spacing child childPort parentSelf incoming parentPort z =
      baseline z - b * spacing + ∑ i ∈ Finset.range b, parentSelf i z := by
  have hsum : (∑ i ∈ Finset.range b, Selectors.weight (fun j => parentPort j z) i *
      (child i z - baseline z - i * spacing - incoming i z * childPort i z)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Selectors.weight, hp i (Finset.mem_range.mp hi)]
  simp [nodeScalar, hsum, Selectors.prefix_eq_one hp]

theorem selected_weight {b k : ℕ} {port : ℕ → ℝ}
    (hk : k < b) (hprev : ∀ i < k, port i = 1) (hcurrent : port k = 0) :
    Selectors.weight port k = 1 ∧ Selectors.prefixProduct port b = 0 ∧
      ∀ i < b, i ≠ k → Selectors.weight port i = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Selectors.weight, hcurrent, Selectors.prefix_eq_one hprev]
  · exact Finset.prod_eq_zero (Finset.mem_range.mpr hk) hcurrent
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with hi | hi
    · simp [Selectors.weight, hprev i hi]
    · exact Selectors.weight_zero_after hcurrent hi

theorem node_first_unfinished (b : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) {k : ℕ}
    (hk : k < b) (hprev : ∀ i < k, parentPort i z = 1) (hcurrent : parentPort k z = 0) :
    nodeScalar b baseline spacing child childPort parentSelf incoming parentPort z =
      child k z - k * spacing - incoming k z * childPort k z +
        ∑ i ∈ Finset.range b, parentSelf i z := by
  obtain ⟨hw, hp, hother⟩ := selected_weight hk hprev hcurrent
  have hsum : (∑ i ∈ Finset.range b, Selectors.weight (fun j => parentPort j z) i *
      (child i z - baseline z - i * spacing - incoming i z * childPort i z)) =
      child k z - baseline z - k * spacing - incoming k z * childPort k z := by
    rw [Finset.sum_eq_single k]
    · rw [hw, one_mul]
    · intro i hi hik
      rw [hother i (Finset.mem_range.mp hi) hik, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr hk))
  simp only [nodeScalar, hsum, hp, mul_zero, sub_zero]
  ring

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The branch restriction holds for the entire second jet, provided its
plateau equalities hold on a neighborhood, including hidden incoming terms. -/
theorem node_first_unfinished_jet (b : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z) {k : ℕ}
    (hk : k < b)
    (hnear : ∀ᶠ x in 𝓝 z, (∀ i < k, parentPort i x = 1) ∧ parentPort k x = 0) :
    JetLocality.richJet
      (nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
      JetLocality.richJet (fun x => child k x - k * spacing - incoming k x * childPort k x +
        ∑ i ∈ Finset.range b, parentSelf i x) z := by
  apply JetLocality.richJet_congr_of_eventuallyEq
  filter_upwards [hnear] with x hx
  exact node_first_unfinished b baseline spacing child childPort parentSelf incoming parentPort
    x hk hx.1 hx.2

theorem node_completed_jet (b : ℕ) (baseline : Z → ℝ) (spacing : ℝ)
    (child childPort parentSelf incoming parentPort : ℕ → Z → ℝ) (z : Z)
    (hnear : ∀ᶠ x in 𝓝 z, ∀ i < b, parentPort i x = 1) :
    JetLocality.richJet
      (nodeScalar b baseline spacing child childPort parentSelf incoming parentPort) z =
      JetLocality.richJet (fun x => baseline x - b * spacing +
        ∑ i ∈ Finset.range b, parentSelf i x) z := by
  apply JetLocality.richJet_congr_of_eventuallyEq
  filter_upwards [hnear] with x hx
  exact node_completed b baseline spacing child childPort parentSelf incoming parentPort x hx

end GradientHessian.Hierarchy
