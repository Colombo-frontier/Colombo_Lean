import LowRank.MatrixConditionalTrace

/-! Conditional quadratic forms in a random, adapted unit direction.
The rank-one projector supplies the integrability needed for pull-out. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem vecMulVec_isProjector (u : n → ℝ) (hu : u ⬝ᵥ u = 1) :
    IsOrthogonalProjector (vecMulVec u u) := by
  constructor
  · ext i j
    exact mul_comm _ _
  · ext i j
    change (∑ x, (u i * u x) * (u x * u j)) = u i * u j
    calc
      _ = (u i * u j) * (u ⬝ᵥ u) := by
        simp only [dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [hu, mul_one]

theorem trace_vecMulVec_mul (u : n → ℝ) (A : Matrix n n ℝ) :
    (vecMulVec u u * A).trace = u ⬝ᵥ (A *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem loewner_quadratic_le {A B : Matrix n n ℝ} (hAB : LoewnerLE A B) (u : n → ℝ) :
    u ⬝ᵥ (A *ᵥ u) ≤ u ⬝ᵥ (B *ᵥ u) := by
  have h := hAB.2 u
  simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h

theorem quadratic_coordinates {a : Type*} [Fintype a]
    (B : Matrix a n ℝ) (K : Matrix a a ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (K *ᵥ (B *ᵥ x)) = x ⬝ᵥ ((Bᵀ * K * B) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x Bᵀ, Matrix.vecMul_transpose]

theorem bottom_quadratic {a : Type*} [Fintype a]
    (K : Matrix (a ⊕ n) (a ⊕ n) ℝ) (u : n → ℝ) :
    Sum.elim (0 : a → ℝ) u ⬝ᵥ (K *ᵥ Sum.elim 0 u) =
      u ⬝ᵥ ((K.submatrix Sum.inr Sum.inr) *ᵥ u) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.submatrix]

variable {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)

theorem unit_quadratic_integrable (u : Ω → n → ℝ)
    (hu : ∀ i, AEStronglyMeasurable (fun ω => u ω i) μ)
    (hunit : ∀ᵐ ω ∂μ, u ω ⬝ᵥ u ω = 1)
    (A : Ω → Matrix n n ℝ) (hA : EntryIntegrable A μ) :
    Integrable (fun ω => u ω ⬝ᵥ (A ω *ᵥ u ω)) μ := by
  have hP : ∀ᵐ ω ∂μ, IsOrthogonalProjector (vecMulVec (u ω) (u ω)) := by
    filter_upwards [hunit] with ω hω
    exact vecMulVec_isProjector _ hω
  have hp := projector_mul_entryIntegrable μ (fun ω => vecMulVec (u ω) (u ω)) A
    (fun i j => (hu i).mul (hu j)) hP hA
  have hi : Integrable (fun ω => (vecMulVec (u ω) (u ω) * A ω).trace) μ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact integrable_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ => hp i j))
  simpa only [trace_vecMulVec_mul] using hi

theorem condExp_adapted_unit_quadratic (hm : m ≤ mΩ) (u : Ω → n → ℝ)
    (hu : ∀ i, AEStronglyMeasurable[m] (fun ω => u ω i) μ)
    (hunit : ∀ᵐ ω ∂μ, u ω ⬝ᵥ u ω = 1)
    (A : Ω → Matrix n n ℝ) (hA : EntryIntegrable A μ) :
    μ[fun ω => u ω ⬝ᵥ (A ω *ᵥ u ω) | m] =ᵐ[μ]
      (fun ω => u ω ⬝ᵥ (matrixCondMean μ m A ω *ᵥ u ω)) := by
  have hP : ∀ᵐ ω ∂μ, IsOrthogonalProjector (vecMulVec (u ω) (u ω)) := by
    filter_upwards [hunit] with ω hω
    exact vecMulVec_isProjector _ hω
  simpa only [trace_vecMulVec_mul] using condExp_projector_trace_mul m μ hm
    (fun ω => vecMulVec (u ω) (u ω)) A (fun i j => (hu i).mul (hu j)) hP hA

end
end LowRank
