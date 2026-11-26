import GradientHessian.NumericalGateJets
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The literal unit-ball test used by the numerical fork experiment. Its
closed miss threshold implies a zero full second jet, including the seam. -/

noncomputable section
namespace GradientHessian.BoundedNumericalTest
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def testScale : ℝ := 3*InverseGate.B₀/2
def test (y : E) : E := testScale⁻¹ • RadialSquash.squash InverseGate.B₀ y

theorem testScale_pos : 0<testScale := by
  unfold testScale
  exact div_pos (mul_pos (by norm_num) InverseGate.B₀_pos) (by norm_num)

theorem test_norm (y : E) : ‖test y‖ ≤ 1 := by
  have h := RadialSquash.norm_squash_bound InverseGate.B₀_pos y
  rw [test, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr testScale_pos)]
  have hm := mul_le_mul_of_nonneg_left h (inv_pos.mpr testScale_pos).le
  change testScale⁻¹ * ‖RadialSquash.squash InverseGate.B₀ y‖ ≤ testScale⁻¹ * testScale at hm
  simpa only [inv_mul_cancel₀ testScale_pos.ne'] using hm

theorem test_contDiff : ContDiff ℝ 4 (test : E → E) :=
  contDiff_const.smul (RadialSquash.squash_contDiff InverseGate.B₀_pos)

theorem test_borel : @Measurable E E (borel _) (borel _) test := test_contDiff.continuous.borel_measurable

theorem gateArg_eq (a y : E) : InverseGate.gateArg a y = 768*⟪a,test y⟫_ℝ := by
  simp only [InverseGate.gateArg, test, inner_smul_right]
  norm_num [testScale, InverseGate.B₀, InverseGate.alpha, InverseGate.H₀]
  ring

theorem miss_gateArg (a y : E) (hmiss : |⟪a,test y⟫_ℝ| ≤ 1/3072) :
    InverseGate.gateArg a y ≤ 1/4 := by
  rw [gateArg_eq]
  have h := (le_abs_self ⟪a,test y⟫_ℝ).trans hmiss
  linarith

theorem miss_richJet (a y : E) (hmiss : |⟪a,test y⟫_ℝ| ≤ 1/3072) :
    JetLocality.richJet (InverseGate.gate a) y = 0 :=
  NumericalGateJets.gate_zero_richJet a y (miss_gateArg a y hmiss)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem miss_after_linear_richJet (L : F →L[ℝ] E) (a : E) (x : F)
    (hmiss : |⟪a,test (L x)⟫_ℝ| ≤ 1/3072) :
    JetLocality.richJet (fun z => InverseGate.gate a (L z)) x = 0 :=
  NumericalGateJets.gate_after_linear_zero_richJet L a x (miss_gateArg a (L x) hmiss)

end GradientHessian.BoundedNumericalTest
