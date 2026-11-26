import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Module

/-!
# Differentiating an exact lower response

The response differentiability and the joint derivatives are explicit
hypotheses. The implicit function theorem establishing those hypotheses from
the primitive assumptions is not included in this module.
-/
noncomputable section
namespace Bilevel.Hypergradient
open scoped RealInnerProductSpace
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Differentiate the identity saying that the lower gradient vanishes. -/
theorem differentiated_stationarity (G : X × Y → Y) (r : X → Y)
    (x : X) (A : X →L[ℝ] Y) (H : Y →L[ℝ] Y) (R : X →L[ℝ] Y)
    (hG : HasFDerivAt G (A.comp (ContinuousLinearMap.fst ℝ X Y) +
      H.comp (ContinuousLinearMap.snd ℝ X Y)) (x, r x))
    (hr : HasFDerivAt r R x) (hzero : ∀ z, G (z, r z) = 0) :
    ∀ v, A v + H (R v) = 0 := by
  have hc := hG.comp x ((hasFDerivAt_id x).prodMk hr)
  have hz : (fun z => G (z, r z)) = fun _ => (0 : Y) := funext hzero
  have hc' : HasFDerivAt (fun z => G (z, r z))
      ((A.comp (ContinuousLinearMap.fst ℝ X Y) +
      H.comp (ContinuousLinearMap.snd ℝ X Y)).comp
      ((ContinuousLinearMap.id ℝ X).prod R)) x := hc
  rw [hz] at hc'
  have hd := hc'.unique (hasFDerivAt_const (0 : Y) x)
  intro v
  have he := congrArg (fun K : X →L[ℝ] Y => K v) hd
  simpa using he

omit [CompleteSpace X] [CompleteSpace Y] in
theorem response_derivative_formula (A R : X →L[ℝ] Y) (H J : Y →L[ℝ] Y)
    (hleft : ∀ v, J (H v) = v) (h : ∀ v, A v + H (R v) = 0) :
    ∀ v, R v = -J (A v) := by
  intro v
  have he := congrArg J (h v)
  rw [map_add, hleft, map_zero] at he
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using he)

/-- Chain rule for the bilevel hypergradient, without any oracle assumptions. -/
theorem hasGradient_objective (f : X × Y → ℝ) (r : X → Y) (x : X)
    (fx : X) (fy : Y) (R : X →L[ℝ] Y)
    (hf : HasFDerivAt f
      ((InnerProductSpace.toDual ℝ X fx).comp (ContinuousLinearMap.fst ℝ X Y) +
      (InnerProductSpace.toDual ℝ Y fy).comp (ContinuousLinearMap.snd ℝ X Y)) (x, r x))
    (hr : HasFDerivAt r R x) :
    HasGradientAt (fun z => f (z, r z)) (fx + R.adjoint fy) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hc := hf.comp x ((hasFDerivAt_id x).prodMk hr)
  convert hc using 1
  ext v
  simp [inner_add_left, ContinuousLinearMap.adjoint_inner_left]

/-- The adjoint form is valid without silently assuming inverse symmetry. -/
theorem hypergradient_formula (A R : X →L[ℝ] Y) (J : Y →L[ℝ] Y)
    (fx : X) (fy : Y) (hR : ∀ v, R v = -J (A v)) :
    fx + R.adjoint fy = fx - A.adjoint (J.adjoint fy) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hR, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  exact (sub_eq_add_neg _ _).symm

end Bilevel.Hypergradient
