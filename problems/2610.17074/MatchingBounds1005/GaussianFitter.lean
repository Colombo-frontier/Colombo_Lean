import RandomizedFO2003.MeasurableSpanProjection
import Mathlib.Tactic

/-!
# Measurable exact reconstruction from finite linear observations

The triangular Gram-Schmidt response transformation and its inverse retain
all raw response values. On consistent observations the explicit fitter is
the orthogonal projection of the unknown vector onto the row span, hence the
minimum-norm solution. Dependent or zero rows need no separate rank case.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.GaussianFitter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

def rowResponse (rows : Fin T → E) (x : E) : Fin T → ℝ :=
  fun i => ⟪rows i, x⟫_ℝ

def gsResponse (rows : Fin T → E) (y : Fin T → ℝ) (i : Fin T) : ℝ :=
  y i - ∑ j : Finset.Iio i,
    (⟪gramSchmidt ℝ rows j, rows i⟫_ℝ / ‖gramSchmidt ℝ rows j‖ ^ 2) *
      gsResponse rows y j
termination_by i.val
decreasing_by exact Fin.lt_def.mp (Finset.mem_Iio.mp j.property)

theorem gsResponse_def (rows : Fin T → E) (y : Fin T → ℝ) (i : Fin T) :
    gsResponse rows y i = y i - ∑ j ∈ Finset.Iio i,
      (⟪gramSchmidt ℝ rows j, rows i⟫_ℝ / ‖gramSchmidt ℝ rows j‖ ^ 2) *
        gsResponse rows y j := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, gsResponse]

def rawResponseOfGS (rows : Fin T → E) (g : Fin T → ℝ) : Fin T → ℝ :=
  fun i => g i + ∑ j ∈ Finset.Iio i,
    (⟪gramSchmidt ℝ rows j, rows i⟫_ℝ / ‖gramSchmidt ℝ rows j‖ ^ 2) * g j

/-- Exact replay of every raw scalar response from transformed responses. -/
theorem rawResponseOfGS_gsResponse (rows : Fin T → E) (y : Fin T → ℝ) :
    rawResponseOfGS rows (gsResponse rows y) = y := by
  funext i
  rw [rawResponseOfGS, gsResponse_def]
  exact sub_add_cancel _ _

theorem gsResponse_injective (rows : Fin T → E) : Function.Injective (gsResponse rows) :=
  Function.LeftInverse.injective (rawResponseOfGS_gsResponse rows)

theorem gsResponse_rowResponse (rows : Fin T → E) (x : E) (i : Fin T) :
    gsResponse rows (rowResponse rows x) i = ⟪gramSchmidt ℝ rows i, x⟫_ℝ := by
  induction i using (wellFounded_lt (α := Fin T)).induction with
  | h i ih =>
    rw [gsResponse_def, gramSchmidt_def, inner_sub_left, sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_Iio.mp hj), Submodule.orthogonalProjection_singleton]
    simp [real_inner_smul_left]

def fitter (rows : Fin T → E) (y : Fin T → ℝ) : E :=
  ∑ i, (gsResponse rows y i / ‖gramSchmidt ℝ rows i‖ ^ 2) • gramSchmidt ℝ rows i

theorem fitter_rowResponse [FiniteDimensional ℝ E] (rows : Fin T → E) (x : E) :
    fitter rows (rowResponse rows x) =
      ((Submodule.span ℝ (Set.range rows)).orthogonalProjection x : E) := by
  simp only [fitter, gsResponse_rowResponse]
  exact (RandomizedFO2003.span_projection_gramSchmidt rows x).symm

theorem rowResponse_projection [FiniteDimensional ℝ E] (rows : Fin T → E) (x : E) :
    rowResponse rows ((Submodule.span ℝ (Set.range rows)).orthogonalProjection x) =
      rowResponse rows x := by
  funext i
  exact (Submodule.span ℝ (Set.range rows)).inner_orthogonalProjection_eq_of_mem_left
    ⟨rows i, Submodule.subset_span ⟨i, rfl⟩⟩ x

/-- Every actual observation is reproduced exactly by the fitter. -/
theorem fitter_exact [FiniteDimensional ℝ E] (rows : Fin T → E) (x : E) :
    rowResponse rows (fitter rows (rowResponse rows x)) = rowResponse rows x := by
  rw [fitter_rowResponse, rowResponse_projection]

theorem fitter_minimum_norm [FiniteDimensional ℝ E] (rows : Fin T → E)
    (y : Fin T → ℝ) (x : E) (hx : rowResponse rows x = y) :
    ‖fitter rows y‖ ≤ ‖x‖ := by
  rw [← hx, fitter_rowResponse]
  exact le_trans ((Submodule.span ℝ (Set.range rows)).orthogonalProjection.le_opNorm x)
    (by
      simpa using mul_le_mul_of_nonneg_right
        (Submodule.orthogonalProjection_norm_le (Submodule.span ℝ (Set.range rows)))
        (norm_nonneg x))

theorem fitter_unique_in_span [FiniteDimensional ℝ E] (rows : Fin T → E)
    (y : Fin T → ℝ) (x : E) (hx : rowResponse rows x = y)
    (hspan : x ∈ Submodule.span ℝ (Set.range rows)) : fitter rows y = x := by
  rw [← hx, fitter_rowResponse]
  exact (Submodule.orthogonalProjection_eq_self_iff).mpr hspan

section Measurability
variable {Ω : Type*} [MeasurableSpace Ω]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_gsResponse (rows : Ω → Fin T → E) (y : Ω → Fin T → ℝ)
    (hrows : ∀ i, Measurable (fun h => rows h i))
    (hy : ∀ i, Measurable (fun h => y h i)) (i : Fin T) :
    Measurable (fun h => gsResponse (rows h) (y h) i) := by
  induction i using (wellFounded_lt (α := Fin T)).induction with
  | h i ih =>
    have heq : (fun h => gsResponse (rows h) (y h) i) =
        fun h => y h i - ∑ j ∈ Finset.Iio i,
          (⟪gramSchmidt ℝ (rows h) j, rows h i⟫_ℝ / ‖gramSchmidt ℝ (rows h) j‖ ^ 2) *
            gsResponse (rows h) (y h) j := by
      funext h
      exact gsResponse_def (rows h) (y h) i
    rw [heq]
    apply (hy i).sub
    apply Finset.measurable_sum
    intro j hj
    have hgs := RandomizedFO2003.measurable_gramSchmidt rows hrows j
    exact ((hgs.inner (hrows i)).div (hgs.norm.pow_const 2)).mul
      (ih j (Finset.mem_Iio.mp hj))

theorem measurable_fitter (rows : Ω → Fin T → E) (y : Ω → Fin T → ℝ)
    (hrows : ∀ i, Measurable (fun h => rows h i))
    (hy : ∀ i, Measurable (fun h => y h i)) :
    Measurable (fun h => fitter (rows h) (y h)) := by
  apply Finset.measurable_sum
  intro i _
  have hgs := RandomizedFO2003.measurable_gramSchmidt rows hrows i
  exact ((measurable_gsResponse rows y hrows hy i).div (hgs.norm.pow_const 2)).smul hgs

end Measurability
end MatchingBounds1005.GaussianFitter
