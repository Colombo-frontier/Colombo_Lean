import FreshGradientMinimax.LinearFlatEnergy
import FreshGradientMinimax.RadialCap

/-! Pointwise locality of flat linear energies and their actual gradients.
An unobserved row may be deleted only when both versions are flat; otherwise
the entire row functional must agree. The radial cap retains the ambient norm. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {m : ℕ}

def FlatRowAgreement (A B : E →L[ℝ] Euclid m) (δ : ℝ) (x : E) : Prop :=
  ∀ i, (∀ v, A v i = B v i) ∨ (|A x i| ≤ δ ∧ |B x i| ≤ δ)

omit [CompleteSpace E] in
theorem linearFlatEnergy_row_agreement {A B : E →L[ℝ] Euclid m} {δ : ℝ}
    (hδ : 0 ≤ δ) {x : E} (h : FlatRowAgreement A B δ x) (β : ℝ) :
    linearFlatEnergy A β δ x = linearFlatEnergy B β δ x := by
  unfold linearFlatEnergy flatEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases h i with he | ⟨ha, hb⟩
  · rw [he x]
  · rw [flatEdge_flat hδ ha, flatEdge_flat hδ hb]

theorem linearFlatGradient_row_agreement {A B : E →L[ℝ] Euclid m} {δ : ℝ}
    (hδ : 0 ≤ δ) {x : E} (h : FlatRowAgreement A B δ x) (β : ℝ) :
    linearFlatGradient A β δ x = linearFlatGradient B β δ x := by
  unfold linearFlatGradient
  congr 1
  apply ext_inner_right ℝ
  intro v
  simp only [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply,
    flatSlope_apply, RCLike.inner_apply', conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rcases h i with he | ⟨ha, hb⟩
  · rw [he x, he v]
  · rw [flatEdgeSlope_flat hδ ha, flatEdgeSlope_flat hδ hb, zero_mul, zero_mul]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem radialCap_congr_at {Q P : E → ℝ} {x : E} (h : Q x = P x) (β R : ℝ) :
    radialCap Q β R x = radialCap P β R x := by
  simp only [radialCap, h]

omit [CompleteSpace E] in
theorem radialCapGradient_congr_at {Q P : E → ℝ} {G H : E → E} {x : E}
    (hQ : Q x = P x) (hG : G x = H x) (β R : ℝ) :
    radialCapGradient Q G β R x = radialCapGradient P H β R x := by
  simp only [radialCapGradient, radialCapWeight, hQ, hG]

theorem cappedLinearFlatGradient_row_agreement {A B : E →L[ℝ] Euclid m} {δ : ℝ}
    (hδ : 0 ≤ δ) {x : E} (h : FlatRowAgreement A B δ x) (β R : ℝ) :
    radialCapGradient (linearFlatEnergy A β δ) (linearFlatGradient A β δ) β R x =
      radialCapGradient (linearFlatEnergy B β δ) (linearFlatGradient B β δ) β R x :=
  radialCapGradient_congr_at (linearFlatEnergy_row_agreement hδ h β)
    (linearFlatGradient_row_agreement hδ h β) β R

end FreshGradientMinimax
