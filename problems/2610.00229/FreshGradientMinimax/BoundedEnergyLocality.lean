import FreshGradientMinimax.BoundedEnergy

/-! Pointwise first-order locality for nonlinear maps into flat Huber
energies. Unchanged component functions have unchanged derivatives; all
other components must be genuinely flat in both versions. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

def FlatComponentAgreement (A B : E → Euclid m) (δ : ℝ) (x : E) : Prop :=
  ∀ i, (∀ v, A v i = B v i) ∨ (|A x i| ≤ δ ∧ |B x i| ≤ δ)

theorem component_derivative_congr {A B : E → Euclid m} {A' B' : E →L[ℝ] Euclid m} {x : E}
    (hA : HasFDerivAt A A' x) (hB : HasFDerivAt B B' x) (i : Fin m)
    (he : ∀ v, A v i = B v i) (v : E) : A' v i = B' v i := by
  have ha : HasFDerivAt (fun u => A u i) ((EuclideanSpace.proj (𝕜 := ℝ) i).comp A') x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hA
  have hb : HasFDerivAt (fun u => A u i) ((EuclideanSpace.proj (𝕜 := ℝ) i).comp B') x := by
    rw [show (fun u => A u i) = (fun u => B u i) from funext he]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hB
  exact congrArg (fun C : E →L[ℝ] ℝ => C v) (ha.unique hb)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem boundedEnergy_component_agreement {A B : E → Euclid m} {δ b : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) {x : E} (h : FlatComponentAgreement A B δ x) :
    boundedEnergy δ b (A x) = boundedEnergy δ b (B x) := by
  apply Finset.sum_congr rfl
  intro i _
  rcases h i with he | ⟨ha, hc⟩
  · rw [he x]
  · rw [boundedFlatEdge_flat hδ hb ha, boundedFlatEdge_flat hδ hb hc]

theorem boundedEnergy_component_derivative_agreement {A B : E → Euclid m} {A' B' : E →L[ℝ] Euclid m}
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) {x : E}
    (hA : HasFDerivAt A A' x) (hB : HasFDerivAt B B' x) (h : FlatComponentAgreement A B δ x) :
    (innerSL ℝ (boundedSlope δ b (A x))).comp A' = (innerSL ℝ (boundedSlope δ b (B x))).comp B' := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply, PiLp.inner_apply, RCLike.inner_apply',
    conj_trivial, boundedSlope_apply]
  apply Finset.sum_congr rfl
  intro i _
  rcases h i with he | ⟨ha, hc⟩
  · rw [he x, component_derivative_congr hA hB i he v]
  · rw [boundedFlatSlope_flat hδ hb ha, boundedFlatSlope_flat hδ hb hc, zero_mul, zero_mul]

theorem boundedEnergy_first_order_agreement {A B : E → Euclid m} {δ b : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) {x : E} (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (h : FlatComponentAgreement A B δ x) :
    boundedEnergy δ b (A x) = boundedEnergy δ b (B x) ∧
      fderiv ℝ (fun u => boundedEnergy δ b (A u)) x = fderiv ℝ (fun u => boundedEnergy δ b (B u)) x := by
  refine ⟨boundedEnergy_component_agreement hδ hb h, ?_⟩
  have ha := ((boundedEnergy_hasFDerivAt hδ hb (A x)).comp x hA.hasFDerivAt).fderiv
  have hc := ((boundedEnergy_hasFDerivAt hδ hb (B x)).comp x hB.hasFDerivAt).fderiv
  simp only [Function.comp_def] at ha hc
  rw [ha, hc]
  exact boundedEnergy_component_derivative_agreement hδ hb hA.hasFDerivAt hB.hasFDerivAt h

theorem boundedEnergy_gradient_agreement {d : ℕ} {A B : Euclid d → Euclid m} {δ b : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) {x : Euclid d} (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (h : FlatComponentAgreement A B δ x) :
    gradient (fun u => boundedEnergy δ b (A u)) x = gradient (fun u => boundedEnergy δ b (B u)) x := by
  rw [gradient, gradient, (boundedEnergy_first_order_agreement hδ hb hA hB h).2]

end FreshGradientMinimax
