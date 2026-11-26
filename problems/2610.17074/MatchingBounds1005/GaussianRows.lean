import MatchingBounds1005.InnovationGaussianKL

/-!
# Linear maps represented by finite observation rows

The row span and innovation space are identified for actual finite linear
observations. Zero rows and dependent rows are allowed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.GaussianRows
open GaussianVector GaussianFitter AdaptiveGaussian InnovationGaussianKL

variable {d T : ℕ}

def rowMap (rows : Fin T → Vec d) : Vec d →L[ℝ] (Fin T → ℝ) :=
  ContinuousLinearMap.pi (fun i => innerSL ℝ (rows i))

@[simp] theorem rowMap_apply (rows : Fin T → Vec d) (x : Vec d) :
    rowMap rows x = rowResponse rows x := rfl

theorem ker_rowMap (rows : Fin T → Vec d) :
    LinearMap.ker (rowMap rows) = (Submodule.span ℝ (Set.range rows))ᗮ := by
  ext x
  constructor
  · intro hx
    have hi (i : Fin T) : @inner ℝ (Vec d) _ x (rows i) = 0 := by
      have h := congrFun hx i
      change @inner ℝ (Vec d) _ (rows i) x = 0 at h
      rw [real_inner_comm]
      exact h
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro y hy
    have hspan : Submodule.span ℝ (Set.range rows) ≤ LinearMap.ker (innerSL ℝ x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hi i
    exact hspan hy
  · intro hx
    apply funext
    intro i
    exact Submodule.inner_right_of_mem_orthogonal (show rows i ∈ Submodule.span ℝ (Set.range rows) from Submodule.subset_span ⟨i, rfl⟩) hx

theorem orthogonal_ker_rowMap (rows : Fin T → Vec d) :
    (LinearMap.ker (rowMap rows))ᗮ = Submodule.span ℝ (Set.range rows) := by
  rw [ker_rowMap, Submodule.orthogonal_orthogonal]

theorem innovationSpace_rowMap (rows : Fin T → Vec d) (V : Submodule ℝ (Vec d))
    (hV : V ≤ Submodule.span ℝ (Set.range rows)) :
    innovationSpace (rowMap rows) V = (Submodule.span ℝ (Set.range rows)) ⊓ Vᗮ := by
  rw [innovationSpace, orthogonal_ker_rowMap, sup_eq_right.mpr hV]

end MatchingBounds1005.GaussianRows

