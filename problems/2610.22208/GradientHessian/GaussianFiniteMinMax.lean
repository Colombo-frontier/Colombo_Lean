import GradientHessian.GaussianFiniteMaximum
import GradientHessian.GaussianSoftMinMax

/-! Exact finite min-max and the two deterministic errors in its
soft minimum/maximum approximation. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped BigOperators NNReal

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

def finiteMinimum (x : I → ℝ) : ℝ := -finiteMaximum (-x)

theorem finiteMinimum_attained (x : I → ℝ) : ∃ i, finiteMinimum x = x i := by
  obtain ⟨i, hi⟩ := finiteMaximum_attained (-x)
  exact ⟨i, by simp only [finiteMinimum, hi, Pi.neg_apply, neg_neg]⟩

theorem finiteMinimum_le (x : I → ℝ) (i : I) : finiteMinimum x ≤ x i := by
  have h := le_finiteMaximum (-x) i
  change -x i ≤ finiteMaximum (-x) at h
  exact neg_le.mp (by simpa only [finiteMinimum, neg_neg] using h)

theorem le_finiteMinimum {x : I → ℝ} {a : ℝ} (h : ∀ i, a ≤ x i) : a ≤ finiteMinimum x := by
  have hl : finiteMaximum (-x) ≤ -a := finiteMaximum_le (fun i => neg_le_neg (h i))
  exact neg_le_neg_iff.mp (by simpa only [finiteMinimum, neg_neg] using hl)

theorem finiteMinimum_lipschitz : LipschitzWith 1 (finiteMinimum (I := I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [finiteMinimum, dist_neg_neg] using finiteMaximum_lipschitz.dist_le_mul (-x) (-y)

omit [Nonempty I] in
theorem softMaximum_negative_eq (α : ℝ) (x : I → ℝ) :
    softMaximum (-α) x = -softMaximum α (-x) := by
  simp only [softMaximum, softPartition, Pi.neg_apply, neg_mul, mul_neg, div_neg_eq_neg_div]

theorem softMinimum_bounds {α : ℝ} (hα : 0 < α) (x : I → ℝ) :
    finiteMinimum x - Real.log (Fintype.card I) / α ≤ softMaximum (-α) x ∧
      softMaximum (-α) x ≤ finiteMinimum x := by
  have hl := finiteMaximum_le_softMaximum hα (-x)
  have hu := softMaximum_le_finiteMaximum hα (-x)
  rw [softMaximum_negative_eq]
  dsimp [finiteMinimum]
  constructor <;> linarith

def finiteRows (x : I × J → ℝ) : I → ℝ := fun i => finiteMaximum (rowProjection i x)
def finiteMinMax (x : I × J → ℝ) : ℝ := finiteMinimum (finiteRows x)

omit [Nonempty I] in
theorem finiteRows_lipschitz : LipschitzWith 1 (finiteRows (I := I) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).mpr
  intro i
  have h := finiteMaximum_lipschitz.dist_le_mul (rowProjection i x) (rowProjection i y)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h
  exact h.trans (by simpa only [map_sub] using rowProjection_norm i (x-y))

theorem finiteMinMax_lipschitz : LipschitzWith 1 (finiteMinMax (I := I) (J := J)) := by
  simpa only [one_mul] using finiteMinimum_lipschitz.comp finiteRows_lipschitz

theorem finiteMinMax_soft_bounds {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : I × J → ℝ) :
    finiteMinMax x - Real.log (Fintype.card I) / α ≤ softMinMax α β x ∧
      softMinMax α β x ≤ finiteMinMax x + Real.log (Fintype.card J) / β := by
  have hmin : finiteMinMax x ≤ finiteMinimum (softRows β x) := by
    apply le_finiteMinimum
    intro i
    exact (finiteMinimum_le (finiteRows x) i).trans (finiteMaximum_le_softMaximum hβ _)
  have hmax : finiteMinimum (softRows β x) ≤ finiteMinMax x + Real.log (Fintype.card J) / β := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained (finiteRows x)
    have hl := finiteMinimum_le (softRows β x) i
    have hu := softMaximum_le_finiteMaximum hβ (rowProjection i x)
    change finiteMinMax x = finiteMaximum (rowProjection i x) at hi
    change finiteMinimum (softRows β x) ≤ softMaximum β (rowProjection i x) at hl
    rw [hi]
    exact hl.trans hu
  have hs := softMinimum_bounds hα (softRows β x)
  change _ ≤ softMinMax α β x ∧ softMinMax α β x ≤ _ at hs
  constructor <;> linarith [hs.1, hs.2]

end GradientHessian.GaussianConcentration
