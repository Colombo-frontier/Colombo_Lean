import Smoothness2601.SineGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The hard construction admits actual entire complex extensions in the
lower variable. This is stronger than merely having all real derivatives. -/
noncomputable section
namespace Smoothness2601.SineGeometry

def lowerComplex (m a h B : ℝ) (z : ℂ) : ℂ :=
  (m:ℂ)/2*z^2-(m:ℂ)*a*h*B*Complex.sin (z/(h:ℂ))

def upperComplex (A c : ℝ) (z : ℂ) : ℂ := (A:ℂ)+(c:ℂ)*z

theorem lowerComplex_entire (m a h B : ℝ) : Differentiable ℂ (lowerComplex m a h B) := by
  unfold lowerComplex
  fun_prop

theorem upperComplex_entire (A c : ℝ) : Differentiable ℂ (upperComplex A c) := by
  unfold upperComplex
  fun_prop

theorem lowerComplex_real (m a h B y : ℝ) :
    lowerComplex m a h B (y:ℂ) = (SineLift.lowerObjective m a h B y:ℂ) := by
  simp [lowerComplex,SineLift.lowerObjective]

theorem upperComplex_real (A c y : ℝ) :
    upperComplex A c (y:ℂ) = ((A+c*y:ℝ):ℂ) := by
  simp [upperComplex]

end Smoothness2601.SineGeometry
