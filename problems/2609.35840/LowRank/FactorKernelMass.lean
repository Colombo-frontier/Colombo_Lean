import LowRank.FactorKernelFullRank
import LowRank.QueryMassIdentity

/-! Kernel mass at an arbitrary complete factor state. The mass is bounded
and measurable, and a genuine revelation adds exactly the new query mass. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def factorKernelMass {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) : ℝ :=
  ((factorKernelProjector st D).submatrix Sum.inl Sum.inl).trace

def factorQueryMass {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (u : Fin r → ℝ) : ℝ :=
  u ⬝ᵥ ((factorKernelProjector st D).submatrix Sum.inr Sum.inr *ᵥ u)

theorem factorQueryMass_ambient {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (u : Fin r → ℝ) :
    ambientQuery (visibleFactorData st) u ⬝ᵥ
        (leftKernelProjector (representedMatrix st D) *ᵥ ambientQuery (visibleFactorData st) u) =
      factorQueryMass st D u := by
  simp only [ambientQuery, visibleFactorData, quadratic_coordinates, bottom_quadratic,
    factorQueryMass, factorKernelProjector]

theorem factorKernelMass_bounds {d t q r s : ℕ} (st : FactorData d t q r s)
    (D : Matrix (Fin r) (Fin s) ℝ) (hst : st.Orthogonal) :
    0 ≤ factorKernelMass st D ∧ factorKernelMass st D ≤ q := by
  have hP := factorKernelProjector_isProjector st D hst
  constructor
  · change 0 ≤ ∑ i : Fin q, factorKernelProjector st D (Sum.inl i) (Sum.inl i)
    exact Finset.sum_nonneg (fun i _ => psd_diagonal_nonneg hP.posSemidef (Sum.inl i))
  · have hdiag : ∀ i : Fin q, factorKernelProjector st D (Sum.inl i) (Sum.inl i) ≤ 1 := by
      intro i
      have h := psd_diagonal_nonneg hP.complement.posSemidef (Sum.inl i)
      simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h
      linarith
    calc
      _ ≤ ∑ _i : Fin q, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hdiag i)
      _ = _ := by simp

theorem measurable_factorKernelMass {Ω : Type*} [MeasurableSpace Ω] {d t q r s : ℕ}
    (st : Ω → FactorData d t q r s) (D : Ω → Matrix (Fin r) (Fin s) ℝ)
    (hst : Measurable st) (hD : Measurable D) :
    Measurable (fun ω => factorKernelMass (st ω) (D ω)) := by
  have hm := measurable_factorKernelProjector st D hst hD
  unfold factorKernelMass Matrix.trace Matrix.diag
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pi_apply (Sum.inl i)).comp ((measurable_pi_apply (Sum.inl i)).comp hm)

theorem factorKernelProjector_entryIntegrable {Ω : Type*} [MeasurableSpace Ω] {d t q r s : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (st : Ω → FactorData d t q r s) (D : Ω → Matrix (Fin r) (Fin s) ℝ)
    (hst : Measurable st) (hD : Measurable D) (horth : ∀ ω, (st ω).Orthogonal) :
    EntryIntegrable (fun ω => factorKernelProjector (st ω) (D ω)) μ := by
  intro i j
  have hm := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_factorKernelProjector st D hst hD))
  exact (integrable_const (1 : ℝ)).mono' hm.stronglyMeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω =>
      (factorKernelProjector_isProjector (st ω) (D ω) (horth ω)).entry_norm_le_one i j))

theorem factorKernelMass_integrable {Ω : Type*} [MeasurableSpace Ω] {d t q r s : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (st : Ω → FactorData d t q r s) (D : Ω → Matrix (Fin r) (Fin s) ℝ)
    (hst : Measurable st) (hD : Measurable D) (horth : ∀ ω, (st ω).Orthogonal) :
    Integrable (fun ω => factorKernelMass (st ω) (D ω)) μ := by
  apply (integrable_const (q : ℝ)).mono'
    (measurable_factorKernelMass st D hst hD).stronglyMeasurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have h := factorKernelMass_bounds (st ω) (D ω) (horth ω)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] {d t q r s : ℕ}

theorem updateFactorData_kernel_mass (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) (st : FactorData d t q (r + 1) (s + 1))
    (e : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) (K : Matrix (Fin d) (Fin d) ℝ) :
    exposedKernelMass (visibleFactorData (updateFactorData b c u st e)) K =
      exposedKernelMass (visibleFactorData st) K +
        ambientQuery (visibleFactorData st) u ⬝ᵥ (K *ᵥ ambientQuery (visibleFactorData st) u) := by
  have hnew : (fun i => (visibleFactorData (updateFactorData b c u st e)).2 i (Sum.inl 0)) =
      ambientQuery (visibleFactorData st) u := changedBasis_query_column b u hu st.2.1
  have hold : ∀ j : Fin q,
      (fun i => (visibleFactorData (updateFactorData b c u st e)).2 i (Sum.inl j.succ)) =
        (fun i => (visibleFactorData st).2 i (Sum.inl j)) :=
    fun j => changedBasis_old_column b u st.2.1 j
  simp only [exposedKernelMass_eq_sum, Fin.sum_univ_succ, hnew, hold]
  exact add_comm _ _

theorem factorKernelMass_step (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (c : OrthonormalBasis (Fin (s + 1)) ℝ F) (u : Fin (r + 1) → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) (st : FactorData d t q (r + 1) (s + 1))
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    let out := revealGaussianBlock c (rotateMatrixColumns b (rowGauge b u) D)
    factorKernelMass (updateFactorData b c u st out.1) out.2 =
      factorKernelMass st D + factorQueryMass st D u := by
  let out := revealGaussianBlock c (rotateMatrixColumns b (rowGauge b u) D)
  have he : representedMatrix (updateFactorData b c u st out.1) out.2 = representedMatrix st D :=
    updateFactorData_preserves_matrix b c u st D
  change exposedKernelMass (visibleFactorData (updateFactorData b c u st out.1))
    (leftKernelProjector (representedMatrix (updateFactorData b c u st out.1) out.2)) = _
  rw [he, updateFactorData_kernel_mass b c u hu,
    factorQueryMass_ambient]
  rfl

end
end LowRank
