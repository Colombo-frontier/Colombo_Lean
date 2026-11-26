import GradientHessian.GaussianFiniteMinMax
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual largest and least expansion of a linear map on the unit
sphere. Compactness supplies extremizers, and both expansions are
one-Lipschitz in operator norm. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Set Metric
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def leastExpansion (T : E →L[ℝ] F) : ℝ := sInf ((fun x => ‖T x‖) '' sphere (0 : E) 1)

omit [FiniteDimensional ℝ E] in
theorem unit_sphere_nonempty : (sphere (0 : E) (1 : ℝ)).Nonempty :=
  NormedSpace.sphere_nonempty.mpr (by norm_num)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem leastExpansion_le (T : E →L[ℝ] F) {x : E} (hx : ‖x‖=1) : leastExpansion T ≤ ‖T x‖ := by
  apply csInf_le
  · exact ⟨0, fun y hy => by rcases hy with ⟨z,_,rfl⟩; exact norm_nonneg _⟩
  · exact ⟨x, by simpa only [mem_sphere, dist_zero_right] using hx, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem leastExpansion_nonneg (T : E →L[ℝ] F) : 0 ≤ leastExpansion T := by
  apply le_csInf (unit_sphere_nonempty.image _)
  rintro _ ⟨z,_,rfl⟩
  exact norm_nonneg _

theorem leastExpansion_attained (T : E →L[ℝ] F) : ∃ x : E, ‖x‖=1 ∧ leastExpansion T=‖T x‖ := by
  obtain ⟨x,hx,hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn unit_sphere_nonempty
    T.continuous.norm.continuousOn
  have hn : ‖x‖=1 := by simpa only [mem_sphere, dist_zero_right] using hx
  refine ⟨x,hn,le_antisymm (leastExpansion_le T hn) ?_⟩
  apply le_csInf (unit_sphere_nonempty.image _)
  rintro _ ⟨z,hz,rfl⟩
  exact hmin hz

theorem largestExpansion_attained (T : E →L[ℝ] F) : ∃ x : E, ‖x‖=1 ∧ ‖T‖=‖T x‖ := by
  obtain ⟨x,hx,hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn unit_sphere_nonempty
    T.continuous.norm.continuousOn
  have hn : ‖x‖=1 := by simpa only [mem_sphere, dist_zero_right] using hx
  refine ⟨x,hn,le_antisymm ?_ ?_⟩
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro z hz
    exact hmax (by simpa only [mem_sphere, dist_zero_right] using hz)
  · simpa only [hn,mul_one] using T.le_opNorm x

theorem leastExpansion_lipschitz : LipschitzWith 1 (leastExpansion (E := E) (F := F)) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  have hdir (A B : E →L[ℝ] F) : leastExpansion A - leastExpansion B ≤ ‖A-B‖ := by
    obtain ⟨x,hx,he⟩ := leastExpansion_attained B
    have ha := leastExpansion_le A hx
    have hb := norm_sub_norm_le (A x) (B x)
    have hc := (A-B).le_opNorm x
    rw [hx,mul_one,ContinuousLinearMap.sub_apply] at hc
    rw [he]
    linarith
  apply abs_le.mpr
  constructor
  · have h := hdir S T
    rw [norm_sub_rev] at h
    linarith
  · exact hdir T S

theorem leastExpansion_le_opNorm (T : E →L[ℝ] F) : leastExpansion T ≤ ‖T‖ := by
  obtain ⟨x,hx,_⟩ := leastExpansion_attained T
  exact (leastExpansion_le T hx).trans (by simpa only [hx,mul_one] using T.le_opNorm x)

end GradientHessian.GaussianConcentration
