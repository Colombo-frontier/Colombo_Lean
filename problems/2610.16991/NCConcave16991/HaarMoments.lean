import NCConcave16991.HaarProbability
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace NCConcave16991.Haar

/-- The actual normalized Haar measure, convenient for moment calculations. -/
def haarLaw (k : ℕ) : Measure (OrthogonalGroup k) := orthogonalHaarProbability k

instance haarLaw_probability (k : ℕ) : IsProbabilityMeasure (haarLaw k) := by
  unfold haarLaw
  infer_instance

instance haarLaw_leftInvariant (k : ℕ) : Measure.IsMulLeftInvariant (haarLaw k) :=
  orthogonalHaarProbability_isMulLeftInvariant k

/-- Orthogonal group multiplication agrees with composition of its Euclidean action. -/
theorem action_mul {k : ℕ} (Q R : OrthogonalGroup k) (v : EuclideanSpace ℝ (Fin k)) :
    orthogonalLinearIsometryEquiv (Q * R) v =
      orthogonalLinearIsometryEquiv Q (orthogonalLinearIsometryEquiv R v) := by
  simp only [orthogonalLinearIsometryEquiv_apply]
  change (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) (Q.val * R.val)) v = _
  rw [map_mul]
  rfl

/-- Negating an orthogonal matrix negates every action coordinate. -/
theorem action_neg {k : ℕ} (Q : OrthogonalGroup k) (v : EuclideanSpace ℝ (Fin k)) :
    orthogonalLinearIsometryEquiv (-Q) v = -(orthogonalLinearIsometryEquiv Q v) := by
  simp only [orthogonalLinearIsometryEquiv_apply, Unitary.coe_neg, map_neg,
    ContinuousLinearMap.neg_apply]

/-- Permutation matrices are genuine orthogonal matrices. -/
def permutationOrthogonal {k : ℕ} (σ : Equiv.Perm (Fin k)) : OrthogonalGroup k :=
  ⟨σ.permMatrix ℝ, by
    simp only [Matrix.orthogonalGroup, Unitary.mem_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      mul_inv_cancel, Matrix.permMatrix_one, and_self]⟩

/-- The left permutation action permutes the output coordinates. -/
theorem action_permutation {k : ℕ} (σ : Equiv.Perm (Fin k))
    (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    orthogonalLinearIsometryEquiv (permutationOrthogonal σ) v i = v (σ i) := by
  change ((σ.permMatrix ℝ).mulVec (WithLp.ofLp v)) i = v (σ i)
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- Each action coordinate is continuous and bounded by the fixed input norm. -/
theorem action_coordinate_integrable {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    Integrable (fun Q : OrthogonalGroup k => orthogonalLinearIsometryEquiv Q v i) (haarLaw k) := by
  have hc : Continuous (fun Q : OrthogonalGroup k => orthogonalLinearIsometryEquiv Q v i) :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_orthogonalLinearIsometryEquiv_apply v)
  apply (integrable_const ‖v‖).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro Q
  simpa only [(orthogonalLinearIsometryEquiv Q).norm_map] using
    (PiLp.norm_apply_le (orthogonalLinearIsometryEquiv Q v) i)

/-- Squared action coordinates are integrable under the actual compact Haar law. -/
theorem action_coordinate_sq_integrable {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    Integrable (fun Q : OrthogonalGroup k => (orthogonalLinearIsometryEquiv Q v i) ^ 2) (haarLaw k) := by
  have hc : Continuous (fun Q : OrthogonalGroup k => orthogonalLinearIsometryEquiv Q v i) :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_orthogonalLinearIsometryEquiv_apply v)
  apply (integrable_const (‖v‖ ^ 2)).mono' (hc.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro Q
  have hn : ‖orthogonalLinearIsometryEquiv Q v i‖ ≤ ‖v‖ := by
    simpa only [(orthogonalLinearIsometryEquiv Q).norm_map] using
      (PiLp.norm_apply_le (orthogonalLinearIsometryEquiv Q v) i)
  change |(orthogonalLinearIsometryEquiv Q v i) ^ 2| ≤ ‖v‖ ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- Haar coordinate first moment is exactly zero, proved by left translation by -I. -/
theorem action_coordinate_first_moment {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    (∫ Q, orthogonalLinearIsometryEquiv Q v i ∂haarLaw k) = 0 := by
  have hinv := integral_mul_left_eq_self (μ := haarLaw k)
    (fun Q : OrthogonalGroup k => orthogonalLinearIsometryEquiv Q v i) (-1)
  have hflip (Q : OrthogonalGroup k) :
      orthogonalLinearIsometryEquiv ((-1) * Q) v i = -(orthogonalLinearIsometryEquiv Q v i) := by
    rw [neg_mul, one_mul, action_neg]
    rfl
  simp_rw [hflip] at hinv
  rw [integral_neg] at hinv
  linarith

/-- Coordinate second moments agree, by actual Haar left invariance under swaps. -/
theorem action_coordinate_second_moment_eq {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) (i j : Fin k) :
    (∫ Q, (orthogonalLinearIsometryEquiv Q v i) ^ 2 ∂haarLaw k) =
      ∫ Q, (orthogonalLinearIsometryEquiv Q v j) ^ 2 ∂haarLaw k := by
  have hinv := integral_mul_left_eq_self (μ := haarLaw k)
    (fun Q : OrthogonalGroup k => (orthogonalLinearIsometryEquiv Q v i) ^ 2)
    (permutationOrthogonal (Equiv.swap i j))
  have hswap (Q : OrthogonalGroup k) :
      orthogonalLinearIsometryEquiv (permutationOrthogonal (Equiv.swap i j) * Q) v i =
        orthogonalLinearIsometryEquiv Q v j := by
    rw [action_mul, action_permutation, Equiv.swap_apply_left]
  simp_rw [hswap] at hinv
  exact hinv.symm

/-- Norm preservation and coordinate symmetry establish the true 1/k second moment. -/
theorem action_coordinate_second_moment {k : ℕ} (hk : 0 < k)
    (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    (∫ Q, (orthogonalLinearIsometryEquiv Q v i) ^ 2 ∂haarLaw k) = ‖v‖ ^ 2 / k := by
  have hpoint (Q : OrthogonalGroup k) :
      (∑ j : Fin k, (orthogonalLinearIsometryEquiv Q v j) ^ 2) = ‖v‖ ^ 2 := by
    calc
      _ = ‖orthogonalLinearIsometryEquiv Q v‖ ^ 2 :=
        (EuclideanSpace.real_norm_sq_eq _).symm
      _ = _ := by rw [(orthogonalLinearIsometryEquiv Q).norm_map]
  have hsum : (∑ j : Fin k, ∫ Q,
      (orthogonalLinearIsometryEquiv Q v j) ^ 2 ∂haarLaw k) = ‖v‖ ^ 2 := by
    rw [← integral_finsetSum Finset.univ (fun j _ => action_coordinate_sq_integrable v j)]
    simp_rw [hpoint]
    simp
  have heq (j : Fin k) := action_coordinate_second_moment_eq v j i
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  apply (eq_div_iff hkp.ne').2
  nlinarith

/-- A genuine fixed-coordinate Markov tail, with no assumed isotropy or tail lemma. -/
theorem action_coordinate_tail {k : ℕ} (hk : 0 < k)
    (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) {a : ℝ} (ha : 0 < a) :
    (haarLaw k).real {Q | a ≤ |orthogonalLinearIsometryEquiv Q v i|} ≤
      ‖v‖ ^ 2 / ((k : ℝ) * a ^ 2) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun Q : OrthogonalGroup k =>
      sq_nonneg (orthogonalLinearIsometryEquiv Q v i))) (action_coordinate_sq_integrable v i) (a ^ 2)
  have hsets : {Q : OrthogonalGroup k | a ^ 2 ≤ (orthogonalLinearIsometryEquiv Q v i) ^ 2} =
      {Q | a ≤ |orthogonalLinearIsometryEquiv Q v i|} := by
    ext Q
    change (a ^ 2 ≤ (orthogonalLinearIsometryEquiv Q v i) ^ 2) ↔
      a ≤ |orthogonalLinearIsometryEquiv Q v i|
    rw [← sq_abs (orthogonalLinearIsometryEquiv Q v i)]
    exact sq_le_sq₀ ha.le (abs_nonneg _)
  rw [hsets, action_coordinate_second_moment hk v i] at hm
  rw [← div_div]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  nlinarith

/-- A finite deterministic list of probes admits the actual Haar union bound.
No claim about transcript-dependent probes is made by this theorem. -/
theorem finite_probe_union_tail {k N : ℕ} (hk : 0 < k)
    (v : Fin N → EuclideanSpace ℝ (Fin k)) (coordinate : Fin N → Fin k)
    {a : ℝ} (ha : 0 < a) :
    (haarLaw k).real {Q | ∃ j : Fin N,
      a ≤ |orthogonalLinearIsometryEquiv Q (v j) (coordinate j)|} ≤
        (∑ j, ‖v j‖ ^ 2) / ((k : ℝ) * a ^ 2) := by
  have hsets : {Q : OrthogonalGroup k | ∃ j : Fin N,
      a ≤ |orthogonalLinearIsometryEquiv Q (v j) (coordinate j)|} =
      ⋃ j : Fin N, {Q | a ≤ |orthogonalLinearIsometryEquiv Q (v j) (coordinate j)|} := by
    ext Q
    simp
  rw [hsets]
  calc
    _ ≤ ∑ j : Fin N, (haarLaw k).real
      {Q | a ≤ |orthogonalLinearIsometryEquiv Q (v j) (coordinate j)|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin N, ‖v j‖ ^ 2 / ((k : ℝ) * a ^ 2) :=
      Finset.sum_le_sum (fun j _ => action_coordinate_tail hk (v j) (coordinate j) ha)
    _ = _ := by rw [Finset.sum_div]

end NCConcave16991.Haar


namespace NCConcave16991.Haar

/-- A concrete dimension budget for a bounded finite deterministic probe list. -/
theorem finite_probe_union_tail_of_norm_le {k N : ℕ} (hk : 0 < k)
    (v : Fin N → EuclideanSpace ℝ (Fin k)) (coordinate : Fin N → Fin k)
    {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hv : ∀ j, ‖v j‖ ≤ R) :
    (haarLaw k).real {Q | ∃ j : Fin N,
      a ≤ |orthogonalLinearIsometryEquiv Q (v j) (coordinate j)|} ≤
        (N : ℝ) * R ^ 2 / ((k : ℝ) * a ^ 2) := by
  have hsum : (∑ j : Fin N, ‖v j‖ ^ 2) ≤ (N : ℝ) * R ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin N, R ^ 2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2)
      _ = _ := by simp
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  exact (finite_probe_union_tail hk v coordinate ha).trans
    (div_le_div_of_nonneg_right hsum (mul_nonneg hkp.le (sq_nonneg a)))

end NCConcave16991.Haar
