import NCConcave16991.MixedHaarGramSchmidt
import NCConcave16991.ConditionalHaarSymmetry
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # The actual Gaussian nuisance reservoir and its dimension bound -/

noncomputable section

open Set MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev Space (D : ℕ) := EuclideanSpace ℝ (Fin D)
abbrev Reservoir (m D : ℕ) := Fin m → Space D

def gaussianReservoirLaw (m D : ℕ) : Measure (Reservoir m D) :=
  Measure.pi (fun _ : Fin m ↦ stdGaussian (Space D))

instance gaussianReservoirLaw_probability (m D : ℕ) : IsProbabilityMeasure (gaussianReservoirLaw m D) := by
  unfold gaussianReservoirLaw
  infer_instance

def rotationEquiv {m D : ℕ} (U : Space D ≃ₗᵢ[ℝ] Space D) : Reservoir m D ≃ᵐ Reservoir m D where
  toEquiv := Equiv.piCongrRight (fun _ : Fin m ↦ U.toEquiv)
  measurable_toFun := measurable_pi_iff.mpr (fun i ↦ U.continuous.measurable.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.mpr (fun i ↦ U.symm.continuous.measurable.comp (measurable_pi_apply i))

theorem rotationEquiv_preserving {m D : ℕ} (U : Space D ≃ₗᵢ[ℝ] Space D) :
    MeasurePreserving (rotationEquiv (m := m) U) (gaussianReservoirLaw m D) (gaussianReservoirLaw m D) := by
  apply measurePreserving_pi
  intro i
  exact ⟨U.continuous.measurable, stdGaussian_map U⟩

def coordinateScore {m D : ℕ} (f : Reservoir m D) (j : Fin D) : ℝ :=
  ∑ i, (gramSchmidtNormed ℝ f i j) ^ 2

theorem coordinateScore_nonneg {m D : ℕ} (f : Reservoir m D) (j : Fin D) : 0 ≤ coordinateScore f j :=
  Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)

theorem coordinateScore_measurable {m D : ℕ} (j : Fin D) :
    Measurable (fun f : Reservoir m D ↦ coordinateScore f j) := by
  apply Finset.measurable_sum
  intro i _
  exact (((PiLp.continuous_apply 2 (fun _ : Fin D ↦ ℝ) j).measurable).comp
    (gramSchmidtNormed_measurable i)).pow_const 2

theorem coordinateScore_le {m D : ℕ} (f : Reservoir m D) (j : Fin D) : coordinateScore f j ≤ (m : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (PiLp.norm_apply_le (gramSchmidtNormed ℝ f i) j).trans (gramSchmidtNormed_norm_le f i)
      simpa only [Real.norm_eq_abs, sq_abs, one_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = _ := by simp

theorem coordinateScore_trace_le {m D : ℕ} (f : Reservoir m D) :
    (∑ j, coordinateScore f j) ≤ (m : ℝ) := by
  unfold coordinateScore
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← EuclideanSpace.real_norm_sq_eq]
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (gramSchmidtNormed_norm_le f i) 2
    _ = _ := by simp

theorem coordinateScore_integrable {m D : ℕ} (j : Fin D) :
    Integrable (fun f : Reservoir m D ↦ coordinateScore f j) (gaussianReservoirLaw m D) := by
  apply (integrable_const (m : ℝ)).mono' (coordinateScore_measurable j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro f
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateScore_nonneg f j)]
  exact coordinateScore_le f j

theorem coordinateScore_permutation {m D : ℕ} (σ : Equiv.Perm (Fin D)) (f : Reservoir m D) (j : Fin D) :
    coordinateScore (rotationEquiv (Haar.orthogonalLinearIsometryEquiv (Haar.permutationOrthogonal σ)) f) j =
      coordinateScore f (σ j) := by
  unfold coordinateScore
  apply Finset.sum_congr rfl
  intro i _
  change (gramSchmidtNormed ℝ (fun i ↦ Haar.orthogonalLinearIsometryEquiv (Haar.permutationOrthogonal σ) (f i)) i j) ^ 2 = _
  rw [gramSchmidtNormed_isometry, Haar.action_permutation]

theorem coordinateScore_integral_eq {m D : ℕ} (i j : Fin D) :
    (∫ f, coordinateScore f i ∂gaussianReservoirLaw m D) =
      ∫ f, coordinateScore f j ∂gaussianReservoirLaw m D := by
  let U := Haar.orthogonalLinearIsometryEquiv (Haar.permutationOrthogonal (Equiv.swap i j))
  have hh := (rotationEquiv_preserving (m := m) U).integral_comp' (fun f ↦ coordinateScore f i)
  have he (f : Reservoir m D) : coordinateScore (rotationEquiv U f) i = coordinateScore f j := by
    simpa only [Equiv.swap_apply_left] using coordinateScore_permutation (Equiv.swap i j) f i
  simp_rw [he] at hh
  exact hh.symm

/-- The score is the squared projection onto the generated reservoir span.
The estimate needs no full-rank assertion about a Gaussian matrix. -/
theorem coordinateScore_expectation_le {m D : ℕ} (hD : 0 < D) (i : Fin D) :
    (∫ f, coordinateScore f i ∂gaussianReservoirLaw m D) ≤ (m : ℝ) / D := by
  have hs := integral_mono (integrable_finsetSum _ (fun j _ ↦ coordinateScore_integrable j))
    (integrable_const (m : ℝ)) (coordinateScore_trace_le (m := m) (D := D))
  rw [integral_finsetSum _ (fun j _ ↦ coordinateScore_integrable j)] at hs
  have heq (j : Fin D) := coordinateScore_integral_eq (m := m) j i
  simp_rw [heq] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hs
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  exact (le_div_iff₀ hDR).mpr (by nlinarith only [hs])

theorem coordinateScore_tail {m D : ℕ} (hD : 0 < D) (i : Fin D) {a : ℝ} (ha : 0 < a) :
    (gaussianReservoirLaw m D).real {f | a ≤ coordinateScore f i} ≤ (m : ℝ) / ((D : ℝ) * a) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun f : Reservoir m D ↦ coordinateScore_nonneg f i))
    (coordinateScore_integrable i) a
  have hb := hm.trans (coordinateScore_expectation_le hD i)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hh := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hb)
  simpa only [div_div] using hh

end NCConcave16991.MixedHaar
