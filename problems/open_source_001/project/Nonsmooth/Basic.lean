import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Basic scales of source/main.tex. No oracle-complexity assertion is assumed here. -/
set_option autoImplicit false

namespace Nonsmooth
noncomputable section

def gap (L μ R : ℝ) : ℝ := L - μ * R
def radius (g μ R : ℝ) : ℝ := min R (g / μ)
def energy (g μ R : ℝ) : ℝ := g * radius g μ R - μ / 2 * radius g μ R ^ 2
def scaleH (L g μ R : ℝ) : ℝ := min (L * R) (g ^ 2 / μ)
def localModulus (g μ R : ℝ) : ℝ := g + μ * radius g μ R

end
end Nonsmooth
