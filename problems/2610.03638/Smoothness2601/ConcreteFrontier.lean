import Smoothness2601.CutoffBounds
import Smoothness2601.BoundedFrontier

/-! The article's actual bounded frontier, with all scalar cutoff certificates
proved rather than provided as hypotheses. -/
noncomputable section
open scoped ContDiff
namespace Smoothness2601.Cutoffs

def gateData : BoundedFrontier.GateData where
  a := gate
  d := deriv gate
  e := deriv (deriv gate)
  t₁ := 1
  C := Classical.choose actual_gate_bounds
  M := Classical.choose (Classical.choose_spec actual_gate_bounds)
  C_nonneg := (Classical.choose_spec (Classical.choose_spec actual_gate_bounds)).1.le
  M_nonneg := (Classical.choose_spec (Classical.choose_spec actual_gate_bounds)).2.1.le
  interval := fun t => ⟨gate_nonneg t,gate_le_one t⟩
  unit := gate_one (by norm_num)
  slope_bound := (Classical.choose_spec (Classical.choose_spec actual_gate_bounds)).2.2.1
  curvature_bound := (Classical.choose_spec (Classical.choose_spec actual_gate_bounds)).2.2.2
  hasDeriv := fun t => ((gate_contDiff 1).differentiable (by norm_num) t).hasDerivAt
  hasSecond := fun t => (gate_deriv_contDiff.differentiable (by norm_num) t).hasDerivAt

def bumpData : BoundedFrontier.BumpData where
  ell := bump
  d := deriv bump
  e := deriv (deriv bump)
  B := 1/4
  L := Classical.choose bump_derivative_bounds
  K := Classical.choose (Classical.choose_spec bump_derivative_bounds)
  B_nonneg := by norm_num
  L_nonneg := (Classical.choose_spec (Classical.choose_spec bump_derivative_bounds)).1.le
  K_nonneg := (Classical.choose_spec (Classical.choose_spec bump_derivative_bounds)).2.1.le
  value_bound := bump_abs_le
  slope_bound := (Classical.choose_spec (Classical.choose_spec bump_derivative_bounds)).2.2.1
  curvature_bound := (Classical.choose_spec (Classical.choose_spec bump_derivative_bounds)).2.2.2
  hasDeriv := fun t => ((bump_contDiff 1).differentiable (by norm_num) t).hasDerivAt
  hasSecond := fun t => (bump_deriv_contDiff.differentiable (by norm_num) t).hasDerivAt

def frontier {ι : Type*} [Fintype ι] [LinearOrder ι] (z : EuclideanSpace ℝ ι) : ℝ :=
  BoundedFrontier.frontier gate bump z

def frontierGradientBound : ℝ := (1/4)*Real.sqrt gateData.C + bumpData.L
def frontierHessianBound : ℝ :=
  (1/4)*(2*gateData.C+gateData.M)+2*Real.sqrt gateData.C*bumpData.L+bumpData.K

/-- Full dimension-free `lem:B-bounds` for the functions defined in the source. -/
theorem actual_frontier_bounds {ι : Type*} [Fintype ι] [LinearOrder ι]
    (z : EuclideanSpace ℝ ι) :
    |frontier z| ≤ 1/4 ∧
    ‖gradient frontier z‖ ≤ frontierGradientBound ∧
    ‖fderiv ℝ (gradient frontier) z‖ ≤ frontierHessianBound :=
  BoundedFrontier.frontier_verified_bounds gateData bumpData separated_support z

theorem actual_frontier_differentiable {ι : Type*} [Fintype ι] [LinearOrder ι]
    (z : EuclideanSpace ℝ ι) :
    DifferentiableAt ℝ frontier z ∧ DifferentiableAt ℝ (gradient frontier) z :=
  BoundedFrontier.frontier_differentiable gateData bumpData separated_support z

end Smoothness2601.Cutoffs
