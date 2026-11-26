import LeanArticleAudit.Pilot.HaarColumnMGF
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace LeanArticleAudit.Pilot

noncomputable section

variable {d : ℕ}

/-- Normalized Haar measure on the compact real orthogonal group is also
right invariant.  Mathlib supplies left invariance; uniqueness of normalized
Haar probability gives the right-invariant form needed below. -/
theorem orthogonalHaarProbability_map_mul_right_block (A : RealOrthogonalGroup d) :
    Measure.map (fun Q : RealOrthogonalGroup d => Q * A)
      (orthogonalHaarProbability d) = orthogonalHaarProbability d := by
  let mu' := Measure.map (fun Q : RealOrthogonalGroup d => Q * A)
    (orthogonalHaarProbability d)
  letI : IsProbabilityMeasure mu' :=
    Measure.isProbabilityMeasure_map (measurable_mul_const A).aemeasurable
  letI : Measure.IsHaarMeasure mu' := inferInstance
  exact isHaarMeasure_eq_of_isProbabilityMeasure mu' (orthogonalHaarProbability d)

def blockOrthogonalMatrix (t k : ℕ) (A : RealOrthogonalGroup k) :
    Matrix (Fin (t + k)) (Fin (t + k)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℝ) 0 0 (A : Matrix (Fin k) (Fin k) ℝ))

theorem blockOrthogonalMatrix_mem (t k : ℕ) (A : RealOrthogonalGroup k) :
    blockOrthogonalMatrix t k A ∈ Matrix.orthogonalGroup (Fin (t + k)) ℝ := by
  let B : Matrix (Fin t ⊕ Fin k) (Fin t ⊕ Fin k) ℝ :=
    Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℝ) 0 0
      (A : Matrix (Fin k) (Fin k) ℝ)
  have hB : B * Bᵀ = 1 := by
    dsimp [B]
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    have hA : (A : Matrix (Fin k) (Fin k) ℝ) * (A : Matrix (Fin k) (Fin k) ℝ)ᵀ = 1 := by
      simpa [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using A.property.2
    rw [hA]
    simpa using (Matrix.fromBlocks_one :
      Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℝ) 0 0
        (1 : Matrix (Fin k) (Fin k) ℝ) = 1)
  rw [Matrix.mem_orthogonalGroup_iff]
  change Matrix.reindex finSumFinEquiv finSumFinEquiv B *
      (Matrix.reindex finSumFinEquiv finSumFinEquiv B)ᵀ = 1
  rw [Matrix.transpose_reindex]
  calc
    Matrix.reindex finSumFinEquiv finSumFinEquiv B *
        Matrix.reindex finSumFinEquiv finSumFinEquiv Bᵀ =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (B * Bᵀ) := by
          simpa only [Matrix.reindexAlgEquiv_apply] using
            (Matrix.reindexAlgEquiv_mul ℝ ℝ finSumFinEquiv B Bᵀ).symm
    _ = Matrix.reindex finSumFinEquiv finSumFinEquiv 1 := congrArg _ hB
    _ = 1 := Matrix.reindexLinearEquiv_one ℝ ℝ finSumFinEquiv

def blockOrthogonal (t k : ℕ) (A : RealOrthogonalGroup k) :
    RealOrthogonalGroup (t + k) :=
  ⟨blockOrthogonalMatrix t k A, blockOrthogonalMatrix_mem t k A⟩

theorem blockOrthogonal_one (t k : ℕ) :
    blockOrthogonal t k (1 : RealOrthogonalGroup k) = 1 := by
  apply Subtype.ext
  simp [blockOrthogonal, blockOrthogonalMatrix, Matrix.fromBlocks_one]

theorem blockOrthogonal_mul (t k : ℕ) (A B : RealOrthogonalGroup k) :
    blockOrthogonal t k (A * B) = blockOrthogonal t k A * blockOrthogonal t k B := by
  apply Subtype.ext
  dsimp [blockOrthogonal, blockOrthogonalMatrix]
  let MA : Matrix (Fin t ⊕ Fin k) (Fin t ⊕ Fin k) ℝ :=
    Matrix.fromBlocks 1 0 0 (A : Matrix (Fin k) (Fin k) ℝ)
  let MB : Matrix (Fin t ⊕ Fin k) (Fin t ⊕ Fin k) ℝ :=
    Matrix.fromBlocks 1 0 0 (B : Matrix (Fin k) (Fin k) ℝ)
  have hblock :
      Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℝ) 0 0
          ((A * B : RealOrthogonalGroup k) : Matrix (Fin k) (Fin k) ℝ) =
        MA * MB := by
    dsimp [MA, MB]
    simp [Matrix.fromBlocks_multiply]
  calc
    Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks 1 0 0
          ((A * B : RealOrthogonalGroup k) : Matrix (Fin k) (Fin k) ℝ)) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (MA * MB) :=
      congrArg _ hblock
    _ = Matrix.reindex finSumFinEquiv finSumFinEquiv MA *
        Matrix.reindex finSumFinEquiv finSumFinEquiv MB := by
      simpa only [Matrix.reindexAlgEquiv_apply] using
        Matrix.reindexAlgEquiv_mul ℝ ℝ finSumFinEquiv MA MB

def blockOrthogonalHom (t k : ℕ) :
    RealOrthogonalGroup k →* RealOrthogonalGroup (t + k) where
  toFun := blockOrthogonal t k
  map_one' := blockOrthogonal_one t k
  map_mul' := blockOrthogonal_mul t k

theorem continuous_blockOrthogonal (t k : ℕ) :
    Continuous (blockOrthogonal t k) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun A : RealOrthogonalGroup k => blockOrthogonalMatrix t k A)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases hi : finSumFinEquiv.symm i with a | a
  · rcases hj : finSumFinEquiv.symm j with b | b
    · have heq : (fun A : RealOrthogonalGroup k => blockOrthogonalMatrix t k A i j) =
          (fun _A => (1 : Matrix (Fin t) (Fin t) ℝ) a b) := by
        funext A
        simp [blockOrthogonalMatrix, Matrix.reindex_apply, hi, hj]
      rw [heq]
      exact continuous_const
    · have heq : (fun A : RealOrthogonalGroup k => blockOrthogonalMatrix t k A i j) =
          (fun _A => (0 : Matrix (Fin t) (Fin k) ℝ) a b) := by
        funext A
        simp [blockOrthogonalMatrix, Matrix.reindex_apply, hi, hj]
      rw [heq]
      exact continuous_const
  · rcases hj : finSumFinEquiv.symm j with b | b
    · have heq : (fun A : RealOrthogonalGroup k => blockOrthogonalMatrix t k A i j) =
          (fun _A => (0 : Matrix (Fin k) (Fin t) ℝ) a b) := by
        funext A
        simp [blockOrthogonalMatrix, Matrix.reindex_apply, hi, hj]
      rw [heq]
      exact continuous_const
    · have heq : (fun A : RealOrthogonalGroup k => blockOrthogonalMatrix t k A i j) =
          (fun A : RealOrthogonalGroup k =>
            (A : Matrix (Fin k) (Fin k) ℝ) a b) := by
        funext A
        simp [blockOrthogonalMatrix, Matrix.reindex_apply, hi, hj]
      rw [heq]
      have hm : Continuous
          (fun A : Matrix (Fin k) (Fin k) ℝ => A a b) :=
        (continuous_apply b).comp (continuous_apply a)
      exact hm.comp continuous_subtype_val

theorem measurable_blockOrthogonal (t k : ℕ) :
    Measurable (blockOrthogonal t k) :=
  (continuous_blockOrthogonal t k).measurable

theorem blockOrthogonalMatrix_column_prefix (t k : ℕ)
    (A : RealOrthogonalGroup k) (j : Fin (t + k)) (hj : j.1 < t) :
    (fun r => blockOrthogonalMatrix t k A r j) =
      fun r => (1 : Matrix (Fin (t + k)) (Fin (t + k)) ℝ) r j := by
  let j0 : Fin t := ⟨j.1, hj⟩
  have hjcast : Fin.castAdd k j0 = j := by ext; rfl
  funext r
  rw [← hjcast]
  rcases hr : finSumFinEquiv.symm r with a | a
  · have hrcast : Fin.castAdd k a = r := by
      rw [← finSumFinEquiv_apply_left a]
      exact finSumFinEquiv.apply_symm_apply r ▸ congrArg finSumFinEquiv hr.symm
    rw [← hrcast]
    simp [blockOrthogonalMatrix, Matrix.reindex_apply, Matrix.one_apply]
  · have hrnat : Fin.natAdd t a = r := by
      rw [← finSumFinEquiv_apply_right a]
      exact finSumFinEquiv.apply_symm_apply r ▸ congrArg finSumFinEquiv hr.symm
    have hne : Fin.natAdd t a ≠ Fin.castAdd k j0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    rw [← hrnat]
    simp [blockOrthogonalMatrix, Matrix.reindex_apply, Matrix.one_apply, hne]

theorem mul_blockOrthogonal_prefix_column (t k : ℕ)
    (Q : RealOrthogonalGroup (t + k)) (A : RealOrthogonalGroup k)
    (j : Fin (t + k)) (hj : j.1 < t) :
    orthogonalColumn (Q * blockOrthogonal t k A) j = orthogonalColumn Q j := by
  apply WithLp.ofLp_injective 2
  funext r
  change ((Q : Matrix (Fin (t + k)) (Fin (t + k)) ℝ) *
      blockOrthogonalMatrix t k A) r j = Q r j
  have hcol := blockOrthogonalMatrix_column_prefix t k A j hj
  calc
    ((Q : Matrix (Fin (t + k)) (Fin (t + k)) ℝ) *
        blockOrthogonalMatrix t k A) r j =
        ((Q : Matrix (Fin (t + k)) (Fin (t + k)) ℝ) *
          (1 : Matrix (Fin (t + k)) (Fin (t + k)) ℝ)) r j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro s _hs
      rw [congrFun hcol s]
    _ = Q r j := by simp

theorem measurable_orthogonal_mul_block_dimension (t k : ℕ) : Measurable
    (fun z : RealOrthogonalGroup (t + k) × RealOrthogonalGroup (t + k) =>
      z.1 * z.2) := by
  letI : SecondCountableTopology
      (Matrix (Fin (t + k)) (Fin (t + k)) ℝ) :=
    inferInstanceAs (SecondCountableTopology
      (Fin (t + k) → Fin (t + k) → ℝ))
  letI : SecondCountableTopology (RealOrthogonalGroup (t + k)) :=
    TopologicalSpace.secondCountableTopology_induced (RealOrthogonalGroup (t + k))
      (Matrix (Fin (t + k)) (Fin (t + k)) ℝ) (↑)
  exact (continuous_mul : Continuous
    (fun z : RealOrthogonalGroup (t + k) × RealOrthogonalGroup (t + k) =>
      z.1 * z.2)).measurable

/-- Right-Haar averaging with an arbitrary probability sample space of right
multipliers.  This version avoids pushing a subgroup Haar law forward and is
the form used by the concrete block sampler below. -/
theorem rightHaarSampler_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] (eta : Measure Ω) [IsProbabilityMeasure eta]
    (multiplier : Ω → RealOrthogonalGroup d)
    (X : RealOrthogonalGroup d → ℝ) (hX : Measurable X)
    (hjoint : Measurable (fun z : RealOrthogonalGroup d × Ω =>
      X (z.1 * multiplier z.2)))
    {B : ℝ} (hB : ∀ Q, |X Q| ≤ B) (c : ℝ≥0)
    (hsection : ∀ Q, HasSubgaussianMGF (fun A => X (Q * multiplier A)) c eta) :
    HasSubgaussianMGF X c (orthogonalHaarProbability d) := by
  let mu := orthogonalHaarProbability d
  have hInt (s : ℝ) : Integrable (fun Q => Real.exp (s * X Q)) mu := by
    apply Integrable.of_bound
      ((Real.continuous_exp.measurable.comp (measurable_const.mul hX)).aestronglyMeasurable)
      (Real.exp (|s| * B))
    filter_upwards [] with Q
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      s * X Q ≤ |s * X Q| := le_abs_self _
      _ = |s| * |X Q| := abs_mul _ _
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hB Q) (abs_nonneg s)
  refine ⟨hInt, ?_⟩
  intro s
  let F : RealOrthogonalGroup d × Ω → ℝ :=
    fun z => Real.exp (s * X (z.1 * multiplier z.2))
  have hFmeas : Measurable F :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hjoint)
  have hFint : Integrable F (mu.prod eta) := by
    apply Integrable.of_bound hFmeas.aestronglyMeasurable (Real.exp (|s| * B))
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      s * X (z.1 * multiplier z.2) ≤ |s * X (z.1 * multiplier z.2)| := le_abs_self _
      _ = |s| * |X (z.1 * multiplier z.2)| := abs_mul _ _
      _ ≤ |s| * B :=
        mul_le_mul_of_nonneg_left (hB (z.1 * multiplier z.2)) (abs_nonneg s)
  have hright (A : Ω) :
      (∫ Q, F (Q, A) ∂mu) = mgf X mu s := by
    let f : RealOrthogonalGroup d → ℝ := fun Q => Real.exp (s * X Q)
    calc
      (∫ Q, F (Q, A) ∂mu) = ∫ Q, f (Q * multiplier A) ∂mu := by rfl
      _ = ∫ Q, f Q ∂Measure.map (fun Q => Q * multiplier A) mu :=
        ((MeasurableEquiv.mulRight (multiplier A)).measurableEmbedding.integral_map f).symm
      _ = ∫ Q, f Q ∂mu := by
        rw [orthogonalHaarProbability_map_mul_right_block (multiplier A)]
      _ = mgf X mu s := rfl
  have hdouble :
      (∫ Q, ∫ A, F (Q, A) ∂eta ∂mu) = mgf X mu s := by
    rw [integral_integral_swap hFint]
    simp_rw [hright]
    simp
  have hinnerInt : Integrable (fun Q => ∫ A, F (Q, A) ∂eta) mu :=
    hFint.integral_prod_left
  have hinnerLe :
      (∫ Q, ∫ A, F (Q, A) ∂eta ∂mu) ≤
        ∫ _Q : RealOrthogonalGroup d, Real.exp (c * s ^ 2 / 2) ∂mu := by
    apply integral_mono_ae hinnerInt (integrable_const _)
    filter_upwards [] with Q
    simpa [F, mgf] using (hsection Q).mgf_le s
  calc
    mgf X mu s = ∫ Q, ∫ A, F (Q, A) ∂eta ∂mu := hdouble.symm
    _ ≤ ∫ _Q : RealOrthogonalGroup d, Real.exp (c * s ^ 2 / 2) ∂mu := hinnerLe
    _ = Real.exp (c * s ^ 2 / 2) := by simp [mu]

theorem measurable_mul_blockOrthogonal (t k : ℕ) : Measurable
    (fun z : RealOrthogonalGroup (t + k) × RealOrthogonalGroup k =>
      z.1 * blockOrthogonal t k z.2) := by
  letI : SecondCountableTopology
      (Matrix (Fin (t + k)) (Fin (t + k)) ℝ) :=
    inferInstanceAs (SecondCountableTopology
      (Fin (t + k) → Fin (t + k) → ℝ))
  letI : SecondCountableTopology (RealOrthogonalGroup (t + k)) :=
    TopologicalSpace.secondCountableTopology_induced (RealOrthogonalGroup (t + k))
      (Matrix (Fin (t + k)) (Fin (t + k)) ℝ) (↑)
  letI : SecondCountableTopology (Matrix (Fin k) (Fin k) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℝ))
  letI : SecondCountableTopology (RealOrthogonalGroup k) :=
    TopologicalSpace.secondCountableTopology_induced (RealOrthogonalGroup k)
      (Matrix (Fin k) (Fin k) ℝ) (↑)
  exact (continuous_fst.mul ((continuous_blockOrthogonal t k).comp continuous_snd)).measurable

/-- The block sampler removes prefix adaptation.  Its only analytic input is
the ordinary fixed-vector projection MGF of a later block column under Haar
`O(k)`; no conditional Stiefel law is assumed. -/
theorem adaptedProjectionMGF_of_blockRightHaar
    {N t k : ℕ} {R : ℝ} (hmd : hiddenM N ≤ t + k)
    (i : Fin (hiddenM N)) (hti : t ≤ i.1)
    (x : RealOrthogonalGroup (t + k) → EuclideanSpace ℝ (Fin (t + k)))
    (hproj : Measurable
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)))
    (hprefix : DependsOnlyOnFramePrefix (haarStiefelFrame hmd) t x)
    (hx : ∀ Q, ‖x Q‖ ≤ R) (c : ℝ≥0)
    (hfixedSphereSection : ∀ (Q : RealOrthogonalGroup (t + k))
      (y : EuclideanSpace ℝ (Fin (t + k))), ‖y‖ ≤ R →
      HasSubgaussianMGF
        (fun A : RealOrthogonalGroup k =>
          inner ℝ (haarStiefelFrame hmd (Q * blockOrthogonal t k A) i) y)
        c (orthogonalHaarProbability k)) :
    HasSubgaussianMGF
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)) c
      (orthogonalHaarProbability (t + k)) := by
  let X : RealOrthogonalGroup (t + k) → ℝ :=
    fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)
  apply rightHaarSampler_hasSubgaussianMGF
    (orthogonalHaarProbability k) (blockOrthogonal t k) X hproj
    (hjoint := hproj.comp (measurable_mul_blockOrthogonal t k)) (B := R)
  · intro Q
    calc
      |X Q| ≤ ‖haarStiefelFrame hmd Q i‖ * ‖x Q‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖x Q‖ := by
        rw [(orthonormal_haarStiefelFrame hmd Q).norm_eq_one i, one_mul]
      _ ≤ R := hx Q
  · intro Q
    have hfixed := hfixedSphereSection Q (x Q) (hx Q)
    apply hfixed.congr
    filter_upwards [] with A
    dsimp [X]
    rw [hprefix (Q * blockOrthogonal t k A) Q]
    intro j hj
    exact mul_blockOrthogonal_prefix_column t k Q A (Fin.castLE hmd j) (by
      simpa using hj)

/-- Coordinates of `y` along the final `k` columns of `Q`. -/
def tailCoordinates (t k : ℕ) (Q : RealOrthogonalGroup (t + k))
    (y : EuclideanSpace ℝ (Fin (t + k))) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun s => inner ℝ (orthogonalColumn Q (Fin.natAdd t s)) y)

theorem tailCoordinates_norm_le (t k : ℕ) (Q : RealOrthogonalGroup (t + k))
    (y : EuclideanSpace ℝ (Fin (t + k))) : ‖tailCoordinates t k Q y‖ ≤ ‖y‖ := by
  have hinj : Function.Injective (Fin.natAdd t : Fin k → Fin (t + k)) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    simpa using Nat.add_left_cancel hv
  have hon : Orthonormal ℝ
      (fun s : Fin k => orthogonalColumn Q (Fin.natAdd t s)) := by
    simpa [Function.comp_def] using (orthonormal_orthogonalColumn Q).comp
      (Fin.natAdd t) hinj
  have hsquare : ‖tailCoordinates t k Q y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [tailCoordinates] using
      (hon.sum_inner_products_le y (s := Finset.univ))
  nlinarith [norm_nonneg (tailCoordinates t k Q y), norm_nonneg y]

theorem blockOrthogonalMatrix_apply_natAdd (t k : ℕ)
    (A : RealOrthogonalGroup k) (r : Fin (t + k)) (ell : Fin k) :
    blockOrthogonalMatrix t k A r (Fin.natAdd t ell) =
      match finSumFinEquiv.symm r with
      | Sum.inl _ => 0
      | Sum.inr a => A a ell := by
  rcases hr : finSumFinEquiv.symm r with a | a
  · have hrcast : Fin.castAdd k a = r := by
      rw [← finSumFinEquiv_apply_left a]
      exact finSumFinEquiv.apply_symm_apply r ▸ congrArg finSumFinEquiv hr.symm
    rw [← hrcast]
    simp [blockOrthogonalMatrix, Matrix.reindex_apply]
  · have hrnat : Fin.natAdd t a = r := by
      rw [← finSumFinEquiv_apply_right a]
      exact finSumFinEquiv.apply_symm_apply r ▸ congrArg finSumFinEquiv hr.symm
    rw [← hrnat]
    simp [blockOrthogonalMatrix, Matrix.reindex_apply]

theorem blockSection_projection_eq_tailCoordinates
    (t k : ℕ) (Q : RealOrthogonalGroup (t + k)) (A : RealOrthogonalGroup k)
    (ell : Fin k) (y : EuclideanSpace ℝ (Fin (t + k))) :
    inner ℝ (orthogonalColumn (Q * blockOrthogonal t k A) (Fin.natAdd t ell)) y =
      inner ℝ (orthogonalColumn A ell) (tailCoordinates t k Q y) := by
  simp only [orthogonalColumn, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, tailCoordinates]
  change (∑ r : Fin (t + k), y r *
      (∑ s : Fin (t + k), (Q : Matrix (Fin (t + k)) (Fin (t + k)) ℝ) r s *
        blockOrthogonalMatrix t k A s (Fin.natAdd t ell))) =
    ∑ a : Fin k, (∑ r : Fin (t + k), y r * Q r (Fin.natAdd t a)) * A a ell
  calc
    (∑ r : Fin (t + k), y r *
        (∑ s : Fin (t + k), Q r s *
          blockOrthogonalMatrix t k A s (Fin.natAdd t ell))) =
      ∑ r : Fin (t + k), y r *
        (∑ a : Fin k, Q r (Fin.natAdd t a) * A a ell) := by
          apply Finset.sum_congr rfl
          intro r _hr
          congr 1
          rw [Fin.sum_univ_add]
          simp [blockOrthogonalMatrix, Matrix.reindex_apply]
    _ = ∑ a : Fin k, (∑ r : Fin (t + k), y r * Q r (Fin.natAdd t a)) *
        A a ell := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- Final reduction: the adapted Stiefel projection MGF follows from the
ordinary (non-adapted) MGF of a fixed Haar-orthogonal column in `R^k`. -/
theorem adaptedProjectionMGF_of_haarOrthogonalColumnMGF
    {N t k : ℕ} {R : ℝ} (hmd : hiddenM N ≤ t + k)
    (i : Fin (hiddenM N)) (hti : t ≤ i.1)
    (x : RealOrthogonalGroup (t + k) → EuclideanSpace ℝ (Fin (t + k)))
    (hproj : Measurable
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)))
    (hprefix : DependsOnlyOnFramePrefix (haarStiefelFrame hmd) t x)
    (hx : ∀ Q, ‖x Q‖ ≤ R)
    (hcolumn : ∀ (ell : Fin k) (a : EuclideanSpace ℝ (Fin k)), ‖a‖ ≤ R →
      HasSubgaussianMGF
        (fun A : RealOrthogonalGroup k => inner ℝ (orthogonalColumn A ell) a)
        ⟨R ^ 2 / k, div_nonneg (sq_nonneg R) (Nat.cast_nonneg k)⟩
        (orthogonalHaarProbability k)) :
    HasSubgaussianMGF
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q))
      ⟨R ^ 2 / k, div_nonneg (sq_nonneg R) (Nat.cast_nonneg k)⟩
      (orthogonalHaarProbability (t + k)) := by
  apply adaptedProjectionMGF_of_blockRightHaar hmd i hti x hproj hprefix hx
  intro Q y hy
  let idx : Fin (t + k) := Fin.castLE hmd i
  have hidx : t ≤ idx.1 := by simpa [idx] using hti
  have hidxlt : idx.1 - t < k := by
    have hi_lt : idx.1 < t + k := idx.2
    omega
  let ell : Fin k := ⟨idx.1 - t, hidxlt⟩
  have hell : Fin.natAdd t ell = idx := by
    apply Fin.ext
    dsimp [ell, idx]
    omega
  have htail : ‖tailCoordinates t k Q y‖ ≤ R :=
    (tailCoordinates_norm_le t k Q y).trans hy
  have hmgf := hcolumn ell (tailCoordinates t k Q y) htail
  apply hmgf.congr
  filter_upwards [] with A
  rw [← blockSection_projection_eq_tailCoordinates t k Q A ell y]
  simp only [haarStiefelFrame]
  rw [hell]

/-- The sole remaining spherical input after the right-Haar/block reduction:
a fixed column of a Haar `O(k)` matrix has the sharp `R^2/k` projection MGF.
This has no adaptive probe and no conditional distribution. -/
def HaarOrthogonalColumnProjectionMGF : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (ell : Fin k) (R : ℝ)
    (a : EuclideanSpace ℝ (Fin k)), ‖a‖ ≤ R →
    HasSubgaussianMGF
      (fun A : RealOrthogonalGroup k => inner ℝ (orthogonalColumn A ell) a)
      ⟨R ^ 2 / k, div_nonneg (sq_nonneg R) (Nat.cast_nonneg k)⟩
      (orthogonalHaarProbability k)

theorem hasSubgaussianMGF_mono_parameter
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c c' : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hcc' : c ≤ c') :
    HasSubgaussianMGF X c' μ := by
  refine ⟨hX.integrable_exp_mul, fun s => (hX.mgf_le s).trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hc : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hcc'
  gcongr

/-- In the exact decomposition `d=t+k`, the block result weakens from the
sharper variance `R^2/k` to the article's uniform variance
`R^2/(d-hiddenM N)`. -/
theorem adaptedProjectionMGF_target_of_haarOrthogonalColumnMGF
    {N t k : ℕ} {R : ℝ} (ht : t ≤ hiddenM N)
    (hmd : hiddenM N ≤ t + k) (hmdlt : hiddenM N < t + k)
    (i : Fin (hiddenM N)) (hti : t ≤ i.1)
    (x : RealOrthogonalGroup (t + k) → EuclideanSpace ℝ (Fin (t + k)))
    (hproj : Measurable
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)))
    (hprefix : DependsOnlyOnFramePrefix (haarStiefelFrame hmd) t x)
    (hx : ∀ Q, ‖x Q‖ ≤ R)
    (hcolumn : HaarOrthogonalColumnProjectionMGF) :
    HasSubgaussianMGF
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q))
      ⟨R ^ 2 / ((t + k) - hiddenM N : ℕ),
        div_nonneg (sq_nonneg R) (Nat.cast_nonneg _)⟩
      (orthogonalHaarProbability (t + k)) := by
  have hk : 1 ≤ k := by omega
  have hsharp := adaptedProjectionMGF_of_haarOrthogonalColumnMGF hmd i hti x
    hproj hprefix hx (fun ell a ha => hcolumn k hk ell R a ha)
  apply hasSubgaussianMGF_mono_parameter hsharp
  have hdenposNat : 0 < (t + k) - hiddenM N := Nat.sub_pos_of_lt hmdlt
  have hdenleNat : (t + k) - hiddenM N ≤ k := by omega
  have hdenpos : (0 : ℝ) < ((t + k) - hiddenM N : ℕ) := by exact_mod_cast hdenposNat
  have hdenle : (((t + k) - hiddenM N : ℕ) : ℝ) ≤ k := by exact_mod_cast hdenleNat
  have hreal : R ^ 2 / (k : ℝ) ≤ R ^ 2 / ((t + k) - hiddenM N : ℕ) :=
    div_le_div_of_nonneg_left (sq_nonneg R) hdenpos hdenle
  exact_mod_cast hreal

/-- Concrete, universe-stable recurrence for fixed Haar-orthogonal columns. -/
def HaarOrthogonalColumnEvenMomentRecurrence : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (ell : Fin k)
    (a : EuclideanSpace ℝ (Fin k)) (n : ℕ),
    ((k : ℝ) + 2 * (n : ℝ)) *
        (∫ A, (inner ℝ (orthogonalColumn A ell) a) ^ (2 * (n + 1))
          ∂(orthogonalHaarProbability k)) =
      (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
        (∫ A, (inner ℝ (orthogonalColumn A ell) a) ^ (2 * n)
          ∂(orthogonalHaarProbability k))

/-- `SphereMoments` supplies the ordinary Haar-column MGF once the two
non-adaptive sphere facts are available: the fixed column is rotationally
uniform, and its even moments satisfy the sphere recurrence. -/
theorem haarOrthogonalColumnProjectionMGF_of_uniform_and_recurrence
    (huniform : ∀ (k : ℕ), 1 ≤ k → ∀ ell : Fin k,
      IsUniformUnitSphereLaw k
        (fun A : RealOrthogonalGroup k => orthogonalColumn A ell)
        (orthogonalHaarProbability k))
    (hrec : HaarOrthogonalColumnEvenMomentRecurrence) :
    HaarOrthogonalColumnProjectionMGF := by
  intro k hk ell R a ha
  let v : RealOrthogonalGroup k → EuclideanSpace ℝ (Fin k) :=
    fun A => orthogonalColumn A ell
  have hv : IsUniformUnitSphereLaw k v (orthogonalHaarProbability k) :=
    huniform k hk ell
  have hr : ∀ (a : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      ((k : ℝ) + 2 * (n : ℝ)) *
          (∫ A, (inner ℝ (v A) a) ^ (2 * (n + 1))
            ∂(orthogonalHaarProbability k)) =
        (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
          (∫ A, (inner ℝ (v A) a) ^ (2 * n)
            ∂(orthogonalHaarProbability k)) := by
    exact hrec k hk ell
  have hsharp := uniformSphere_hasSubgaussianMGF_of_evenMomentRecurrence hk hv
    hr a
  apply hasSubgaussianMGF_mono_parameter hsharp
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have hsquare : ‖a‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg a]
  have hkreal : (0 : ℝ) ≤ k := by positivity
  have hreal : ‖a‖ ^ 2 / (k : ℝ) ≤ R ^ 2 / (k : ℝ) :=
    div_le_div_of_nonneg_right hsquare hkreal
  exact_mod_cast hreal

/-- The recurrence obligation above is already discharged by
`SphereRecurrence`; rotational uniformity of a fixed Haar column is therefore
the only remaining geometric input. -/
theorem haarOrthogonalColumnEvenMomentRecurrence_of_uniform
    (huniform : ∀ (k : ℕ), 1 ≤ k → ∀ ell : Fin k,
      IsUniformUnitSphereLaw k
        (fun A : RealOrthogonalGroup k => orthogonalColumn A ell)
        (orthogonalHaarProbability k)) :
    HaarOrthogonalColumnEvenMomentRecurrence := by
  intro k hk ell a n
  exact uniformSphere_even_moment_recurrence hk (huniform k hk ell) a n

theorem haarOrthogonalColumnProjectionMGF_of_uniform
    (huniform : ∀ (k : ℕ), 1 ≤ k → ∀ ell : Fin k,
      IsUniformUnitSphereLaw k
        (fun A : RealOrthogonalGroup k => orthogonalColumn A ell)
        (orthogonalHaarProbability k)) :
    HaarOrthogonalColumnProjectionMGF :=
  haarOrthogonalColumnProjectionMGF_of_uniform_and_recurrence huniform
    (haarOrthogonalColumnEvenMomentRecurrence_of_uniform huniform)

/-- The fixed Haar-column MGF is unconditional: left Haar invariance makes a
column rotationally uniform and `SphereRecurrence` supplies the sharp MGF. -/
theorem haarOrthogonalColumnProjectionMGF_proof :
    HaarOrthogonalColumnProjectionMGF := by
  exact haarOrthogonalColumnProjectionMGF_of_uniform
    (fun _k hk ell => orthogonalHaarColumn_isUniform hk ell)

/-- The adapted Stiefel projection MGF, with no conditional-law premise.
Right multiplication by a block Haar matrix fixes the revealed prefix and
uniformizes every later column inside its orthogonal complement. -/
theorem haarStiefelAdaptedProjectionMGF_proof
    {N d : ℕ} {R : ℝ} (hmd : hiddenM N ≤ d) (hR : 0 < R)
    (hmdlt : hiddenM N < d) :
    HaarStiefelAdaptedProjectionMGF (R := R) hmd hR hmdlt := by
  intro t ht i hti x hproj hprefix hx
  have htd : t ≤ d := ht.trans hmd
  obtain ⟨k, hdk⟩ : ∃ k, d = t + k :=
    ⟨d - t, (Nat.add_sub_of_le htd).symm⟩
  subst d
  exact adaptedProjectionMGF_target_of_haarOrthogonalColumnMGF ht hmd hmdlt i hti
    x hproj hprefix hx haarOrthogonalColumnProjectionMGF_proof

/-- The article's exact adapted slab tail for the concrete normalized-Haar
Stiefel generator. -/
theorem haarStiefelAdaptedSlabTail_proof
    {N d : ℕ} {R : ℝ} (hmd : hiddenM N ≤ d) (hR : 0 < R)
    (hmdlt : hiddenM N < d) :
    HaarStiefelAdaptedSlabTail (R := R) hmd :=
  haarStiefelAdaptedSlabTail_of_projectionMGF hmd hR hmdlt
    (haarStiefelAdaptedProjectionMGF_proof hmd hR hmdlt)

/-- A fully concrete sequential-frame prior: the sample is a normalized Haar
orthogonal matrix and the frame consists of its first `hiddenM N` columns. -/
def haarSequentialFramePriorConcrete
    {N d : ℕ} {R : ℝ} (hmd : hiddenM N ≤ d) (hR : 0 < R)
    (hmdlt : hiddenM N < d) :
    SequentialFramePrior (EuclideanSpace ℝ (Fin d)) N d R :=
  haarSequentialFramePrior hmd
    (haarStiefelAdaptedSlabTail_proof hmd hR hmdlt)

end

end LeanArticleAudit.Pilot
