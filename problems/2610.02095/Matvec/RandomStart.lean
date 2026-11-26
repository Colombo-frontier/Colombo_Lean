import LowRank.GaussianFrobeniusMean
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-!
# A normalized Gaussian start detects every fixed unit direction

We use a union bound rather than independence of the first coordinate and the
remaining norm. The fixed scalar interval probability `p = P(N(0,1) ∈ [1,2])`
is positive. A Gaussian projection lies in that interval with probability p,
whereas Markov bounds the event `‖z‖² > 2d/p` by p/2. Thus normalization gives
universal constants `ν = √(p/2)` and `pν = p/2`.
-/

namespace Matvec
namespace RandomStart

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

def intervalMass : ℝ := (gaussianReal 0 1).real (Set.Icc 1 2)

theorem intervalMass_pos : 0 < intervalMass := by
  have hne : gaussianReal 0 1 (Set.Icc 1 2) ≠ 0 := by
    intro h
    have hv := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0) h
    norm_num at hv
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

theorem gaussian_one_coordinate (S : Set ℝ) :
    LowRank.iidVectorLaw 1 1 {x | x 0 ∈ S} = gaussianReal 0 1 S := by
  have heq : {x : Fin 1 → ℝ | x 0 ∈ S} = Set.univ.pi (fun _ : Fin 1 => S) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      fin_cases i
      exact h
    · intro h
      exact h 0
  rw [heq, LowRank.iidVectorLaw, Measure.pi_pi]
  simp

theorem projection_interval_probability {d : ℕ} (v : Fin d → ℝ)
    (hv : v ⬝ᵥ v = 1) :
    (LowRank.iidVectorLaw d 1).real {z | v ⬝ᵥ z ∈ Set.Icc 1 2} = intervalMass := by
  let B : Matrix (Fin d) (Fin 1) ℝ := fun i _ => v i
  have hB : B.transpose * B = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.one_apply,
      if_true, dotProduct] using hv
  have hmap := LowRank.iidVectorLaw_orthogonal_compression B hB 1
  have hm : Measurable (fun z : Fin d → ℝ => B.transpose *ᵥ z) := by
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hS : MeasurableSet {x : Fin 1 → ℝ | x 0 ∈ Set.Icc 1 2} :=
    measurableSet_Icc.preimage (measurable_pi_apply 0)
  have heq := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ {x | x 0 ∈ Set.Icc 1 2}) hmap
  dsimp only at heq
  rw [Measure.map_apply hm hS, gaussian_one_coordinate] at heq
  have hprob : LowRank.iidVectorLaw d 1 {z | v ⬝ᵥ z ∈ Set.Icc 1 2} =
      gaussianReal 0 1 (Set.Icc 1 2) := by
    simpa only [Set.preimage, Set.mem_setOf_eq, Matrix.mulVec, Matrix.transpose_apply,
      B, dotProduct] using heq
  exact congrArg ENNReal.toReal hprob

theorem squared_norm_mean (d : ℕ) :
    (∫⁻ z, ENNReal.ofReal (z ⬝ᵥ z) ∂LowRank.iidVectorLaw d 1) = ENNReal.ofReal d := by
  simpa only [Matrix.one_mulVec, Matrix.trace_one, Fintype.card_fin] using
    LowRank.iidVectorLaw_quadratic_mean (Matrix.PosSemidef.one (n := Fin d) (R := ℝ))

theorem squared_norm_tail (d : ℕ) {R : ℝ} (hR : 0 < R) :
    (LowRank.iidVectorLaw d 1).real {z | R < z ⬝ᵥ z} ≤ (d : ℝ) / R := by
  have hm : Measurable (fun z : Fin d → ℝ => ENNReal.ofReal (z ⬝ᵥ z)) := by
    simp only [dotProduct]
    fun_prop
  have hmarkov := meas_ge_le_lintegral_div (μ := LowRank.iidVectorLaw d 1)
    hm.aemeasurable (ε := ENNReal.ofReal R) (by positivity) ENNReal.ofReal_ne_top
  rw [squared_norm_mean] at hmarkov
  have hsub : {z : Fin d → ℝ | R < z ⬝ᵥ z} ⊆
      {z | ENNReal.ofReal R ≤ ENNReal.ofReal (z ⬝ᵥ z)} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal hz.le
  have htail := (measure_mono hsub).trans hmarkov
  rw [← ENNReal.ofReal_div_of_pos hR] at htail
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) htail
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ (d : ℝ) / R)]
    using hreal

def normalizedVector {d : ℕ} (z : Fin d → ℝ) : Fin d → ℝ :=
  (Real.sqrt (z ⬝ᵥ z))⁻¹ • z

theorem measurable_normalizedVector (d : ℕ) :
    Measurable (@normalizedVector d) := by
  unfold normalizedVector
  simp only [dotProduct]
  fun_prop

theorem normalized_projection_of_good {d : ℕ} (_hd : 0 < d)
    (v z : Fin d → ℝ) {p : ℝ} (_hp : 0 < p)
    (hproj : 1 ≤ v ⬝ᵥ z) (hsize : z ⬝ᵥ z ≤ 2 * d / p) :
    Real.sqrt (p / 2) / Real.sqrt d ≤ |v ⬝ᵥ normalizedVector z| := by
  have hzn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hzne : z ⬝ᵥ z ≠ 0 := by
    intro h
    have hz : z = 0 := dotProduct_self_eq_zero.mp h
    norm_num [hz] at hproj
  have hzpos : 0 < z ⬝ᵥ z := lt_of_le_of_ne hzn (Ne.symm hzne)
  have hroot : 0 < Real.sqrt (z ⬝ᵥ z) := Real.sqrt_pos.mpr hzpos
  have hscale : (2 * (d : ℝ) / p) = (d : ℝ) / (p / 2) := by ring
  have hconst : Real.sqrt (p / 2) / Real.sqrt d =
      1 / Real.sqrt (2 * d / p) := by
    rw [hscale, Real.sqrt_div (Nat.cast_nonneg d), one_div_div]
  calc
    _ = 1 / Real.sqrt (2 * d / p) := hconst
    _ ≤ 1 / Real.sqrt (z ⬝ᵥ z) :=
      one_div_le_one_div_of_le hroot (Real.sqrt_le_sqrt hsize)
    _ ≤ |v ⬝ᵥ normalizedVector z| := by
      rw [normalizedVector, dotProduct_smul, smul_eq_mul, abs_mul,
        abs_inv, abs_of_pos hroot, abs_of_nonneg (by linarith : 0 ≤ v ⬝ᵥ z)]
      have h := mul_le_mul_of_nonneg_left hproj (inv_nonneg.mpr hroot.le)
      simpa only [one_div, mul_one] using h

/-- An actual probability bound for the normalized iid Gaussian sampler.
The direction is arbitrary and fixed before sampling. -/
theorem random_start_probability {d : ℕ} (hd : 0 < d)
    (v : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) :
    intervalMass / 2 ≤ (LowRank.iidVectorLaw d 1).real
      {z | Real.sqrt (intervalMass / 2) / Real.sqrt d ≤ |v ⬝ᵥ normalizedVector z|} := by
  let A : Set (Fin d → ℝ) := {z | v ⬝ᵥ z ∈ Set.Icc 1 2}
  let B : Set (Fin d → ℝ) := {z | 2 * d / intervalMass < z ⬝ᵥ z}
  have hp := intervalMass_pos
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : (LowRank.iidVectorLaw d 1).real A = intervalMass :=
    projection_interval_probability v hv
  have hB : (LowRank.iidVectorLaw d 1).real B ≤ intervalMass / 2 := by
    have h := squared_norm_tail d (R := 2 * d / intervalMass) (by positivity)
    have heq : (d : ℝ) / (2 * d / intervalMass) = intervalMass / 2 := by
      field_simp
      ring
    rwa [heq] at h
  have hgood : intervalMass / 2 ≤ (LowRank.iidVectorLaw d 1).real (A \ B) := by
    have hdiff := le_measureReal_diff (μ := LowRank.iidVectorLaw d 1) (s₁ := A) (s₂ := B)
    linarith
  refine hgood.trans (measureReal_mono ?_)
  intro z hz
  exact normalized_projection_of_good hd v z hp hz.1.1 (le_of_not_gt hz.2)

/-- The concrete normalized-Gaussian probability law. Its sphere support is
proved below; no abstract Haar-distribution axiom is used. -/
def normalizedGaussianLaw (d : ℕ) : Measure (Fin d → ℝ) :=
  (LowRank.iidVectorLaw d 1).map normalizedVector

instance normalizedGaussianLaw_probability (d : ℕ) :
    IsProbabilityMeasure (normalizedGaussianLaw d) := by
  unfold normalizedGaussianLaw
  exact isProbabilityMeasure_map (measurable_normalizedVector d).aemeasurable

theorem normalizedGaussian_projection_probability {d : ℕ} (hd : 0 < d)
    (v : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) :
    intervalMass / 2 ≤ (normalizedGaussianLaw d).real
      {g | Real.sqrt (intervalMass / 2) / Real.sqrt d ≤ |v ⬝ᵥ g|} := by
  have hm : MeasurableSet {g : Fin d → ℝ |
      Real.sqrt (intervalMass / 2) / Real.sqrt d ≤ |v ⬝ᵥ g|} := by
    apply measurableSet_le measurable_const
    simp only [dotProduct]
    fun_prop
  simpa only [normalizedGaussianLaw, measureReal_def,
    Measure.map_apply (measurable_normalizedVector d) hm, Set.preimage, Set.mem_setOf_eq]
    using random_start_probability hd v hv

theorem uniform_random_start_constants :
    ∃ ν pν : ℝ, 0 < ν ∧ 0 < pν ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ v : Fin d → ℝ, v ⬝ᵥ v = 1 →
        pν ≤ (normalizedGaussianLaw d).real {g | ν / Real.sqrt d ≤ |v ⬝ᵥ g|} := by
  refine ⟨Real.sqrt (intervalMass / 2), intervalMass / 2, ?_, ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (div_pos intervalMass_pos (by norm_num))
  · exact div_pos intervalMass_pos (by norm_num)
  · intro d hd v hv
    exact normalizedGaussian_projection_probability (by omega) v hv

theorem normalizedVector_on_sphere {d : ℕ} (z : Fin d → ℝ) (hz : z ≠ 0) :
    normalizedVector z ⬝ᵥ normalizedVector z = 1 := by
  have hnonneg : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hne : z ⬝ᵥ z ≠ 0 := fun h => hz (dotProduct_self_eq_zero.mp h)
  have hspos : 0 < Real.sqrt (z ⬝ᵥ z) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne hnonneg (Ne.symm hne))
  have hs := Real.sq_sqrt hnonneg
  simp only [normalizedVector, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp

theorem iidVector_ne_zero_ae {d : ℕ} (hd : 0 < d) :
    ∀ᵐ z ∂LowRank.iidVectorLaw d 1, z ≠ 0 := by
  let i : Fin d := ⟨0, hd⟩
  have hcoord : ∀ᵐ z ∂LowRank.iidVectorLaw d 1, z i ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not, LowRank.iidVectorLaw, Set.preimage, Set.mem_singleton_iff,
      Function.eval] using
      Measure.pi_eval_preimage_null (fun _ : Fin d => gaussianReal 0 1) (i := i)
        ((gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0))
          (measure_singleton (0 : ℝ)))
  filter_upwards [hcoord] with z hz
  intro heq
  exact hz (congrFun heq i)

theorem normalizedGaussian_on_sphere {d : ℕ} (hd : 0 < d) :
    ∀ᵐ g ∂normalizedGaussianLaw d, g ⬝ᵥ g = 1 := by
  unfold normalizedGaussianLaw
  apply (ae_map_iff (measurable_normalizedVector d).aemeasurable ?_).mpr
  · filter_upwards [iidVector_ne_zero_ae hd] with z hz
    exact normalizedVector_on_sphere z hz
  · exact (measurableSet_singleton (1 : ℝ)).preimage (show Measurable (fun g : Fin d → ℝ => g ⬝ᵥ g) by
      simp only [dotProduct]
      fun_prop)

/-- Normalization commutes with every orthogonal coordinate transformation. -/
theorem normalizedVector_orthogonal {d : ℕ} (U : Matrix (Fin d) (Fin d) ℝ)
    (hU : U.transpose * U = 1) (z : Fin d → ℝ) :
    U.transpose *ᵥ normalizedVector z = normalizedVector (U.transpose *ᵥ z) := by
  have hright : U * U.transpose = 1 := Matrix.mul_eq_one_comm.mp hU
  have hnorm := LowRank.orthogonal_columns_dot U.transpose
    (by simpa only [Matrix.transpose_transpose] using hright) z
  simp only [normalizedVector, hnorm, Matrix.mulVec_smul]

/-- The concrete sphere-supported law is orthogonally invariant. Together
with sphere support this supplies the usual normalized-Gaussian sphere sampler
used for the manuscript's Haar starts. -/
theorem normalizedGaussian_orthogonal_invariant {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℝ) (hU : U.transpose * U = 1) :
    (normalizedGaussianLaw d).map (fun z => U.transpose *ᵥ z) = normalizedGaussianLaw d := by
  have hm : Measurable (fun z : Fin d → ℝ => U.transpose *ᵥ z) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hcomp : (fun z => U.transpose *ᵥ z) ∘ normalizedVector =
      normalizedVector ∘ (fun z => U.transpose *ᵥ z) := by
    funext z
    exact normalizedVector_orthogonal U hU z
  unfold normalizedGaussianLaw
  rw [Measure.map_map hm (measurable_normalizedVector d), hcomp,
    ← Measure.map_map (measurable_normalizedVector d) hm,
    LowRank.iidVectorLaw_orthogonal_compression U hU]

end
end RandomStart
end Matvec
