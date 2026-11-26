import GradientHessian.FirstHeightLeafActivation
import GradientHessian.FirstHeightLeafDerivatives

/-! The complete source first-height interface, for the literal eight-child
construction on shared physical coordinates and one fixed set of constants. -/

noncomputable section
namespace GradientHessian.FirstHeight
open InnerCoordinates

def firstAmplitudeCoefficient : ℝ := 8 * (leafValueConstant + 952)

theorem firstAmplitudeCoefficient_pos : 0 < firstAmplitudeCoefficient := by
  unfold firstAmplitudeCoefficient
  linarith [leafValueConstant_pos]

theorem firstAmplitude_linear (m : ℕ) : firstAmplitude m ≤ firstAmplitudeCoefficient * (m + 1) := by
  have hm : (1 : ℝ) ≤ m + 1 := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hr := (outerRadius_range (M := m + 1) (by omega)).2
  simp only [Nat.cast_add, Nat.cast_one] at hr
  unfold firstAmplitude amplitude spacing firstAmplitudeCoefficient
  norm_num only [Nat.cast_ofNat]
  nlinarith

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Bounds (d : Data Y E m) : Prop where
  smooth : ContDiff ℝ 3 (sourceNode d)
  residual_smooth : ContDiff ℝ 3 (sourceResidual d)
  decomposition : ∀ Z, sourceNode d Z = sourceBaseline m Z + sourceResidual d Z
  nonpositive : ∀ Z, sourceResidual d Z ≤ 0
  bounded_values : ∀ Z, ‖numerical Y E (m + 1) (Inner.absoluteDepth + 2)
      (numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z)‖ ≤ Leaf.numericalRadius →
    -firstAmplitude m ≤ sourceResidual d Z ∧ sourceResidual d Z ≤ 0
  lower_energy : ∀ Z,
    let z := numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z
    ‖numerical Y E (m + 1) (Inner.absoluteDepth + 2) z‖ ^ 2 / 2 +
      Inner.publicQuadratic (m + 1) Inner.absoluteDepth z + Inner.publicQuadratic 8 (depth (m + 1)) Z -
        firstAmplitude m - Inner.innerConstant * (m + 1) ≤ sourceNode d Z
  activation : ∀ l, 0 ≤ l → ∀ Z, ‖gradient (sourceDriven d l) Z‖ ≤ 1 →
    ∀ i, Inner.ports d.outerDirections Z i = 1
  derivatives : ∀ n, 1 ≤ n → n ≤ 3 → ∀ Z,
    ‖iteratedFDeriv ℝ n (sourceResidual d) Z‖ ≤ firstDerivativeConstant * (m + 1 : ℝ) ^ (3 - n)

/-- All three assertions of manuscript `lem:first-height`. `Valid` contains
only source matrix/mark/unit-direction assumptions; every analytic field is
proved from the literal leaf, latch, selector and Euclidean coordinate maps. -/
theorem first_height_lemma (d : Data Y E m) (hd : Valid d) : Bounds d := by
  refine {
    smooth := sourceNode_contDiff d
    residual_smooth := sourceResidual_contDiff d
    decomposition := ?_
    nonpositive := sourceResidual_nonpos d hd.opNorm
    bounded_values := sourceResidual_bounded d hd.opNorm
    lower_energy := sourceNode_energy d hd.lower
    activation := fun l hl Z hg => source_activation d hd hl Z hg
    derivatives := fun n hn0 hn Z => sourceResidual_derivative_bound d hd Z hn0 hn }
  intro Z
  change node _ _ _ _ _ Z = baseline _ _ _ Z + (node _ _ _ _ _ Z - baseline _ _ _ Z)
  ring

theorem source_outgoing_one (d : Data Y E m) (hd : Valid d) {l : ℝ} (hl : 0 ≤ l)
    (Z : SourceSpace Y E m) (hg : ‖gradient (sourceDriven d l) Z‖ ≤ 1) : sourceOutgoing d Z = 1 :=
  source_activation d hd hl Z hg (Fin.last 7)

end GradientHessian.FirstHeight
