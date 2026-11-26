import MatchingBounds1005.GaussianComparison
import MatchingBounds1005.GaussianVector
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact relative entropy of linear Gaussian observations

All laws below are constructed from actual scalar Gaussian measures. The
recursive product calculation in `GaussianComparison` is first transported
to Euclidean coordinates; linear observations are then identified by their
characteristic functions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.LinearGaussianKL
open GaussianComparison GaussianVector

def coordinatesEquiv : (n : ℕ) → GaussianCoordinates n ≃ᵐ (Fin n → ℝ)
  | 0 => (MeasurableEquiv.ofUniqueOfUnique (Fin 0 → ℝ) Unit).symm
  | n + 1 =>
      ((MeasurableEquiv.refl ℝ).prodCongr (coordinatesEquiv n)).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

theorem coordinatesEquiv_measurePreserving (n : ℕ) (m : ℕ → ℝ) (v : ℝ≥0) :
    MeasurePreserving (coordinatesEquiv n) (gaussianCoordinates n m v)
      (Measure.pi (fun i : Fin n => gaussianReal (m i) v)) := by
  induction n generalizing m with
  | zero => exact (measurePreserving_pi_empty
      (fun i : Fin 0 => gaussianReal (m i) v)).symm
  | succ n ih =>
    have hp := (MeasurePreserving.id (gaussianReal (m 0) v)).prod
      (ih (fun i => m (i + 1)))
    have hq := (measurePreserving_piFinSuccAbove
      (fun i : Fin (n + 1) => gaussianReal (m i) v) 0).symm
    exact hq.comp hp

def euclideanGaussian {n : ℕ} (m : Vec n) (v : ℝ≥0) : Measure (Vec n) :=
  (Measure.pi (fun i : Fin n => gaussianReal (m i) v)).map
    (EuclideanSpace.measurableEquiv (Fin n)).symm

instance euclideanGaussian_probability {n : ℕ} (m : Vec n) (v : ℝ≥0) :
    IsProbabilityMeasure (euclideanGaussian m v) :=
  isProbabilityMeasure_map (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable.aemeasurable

def extendMean {n : ℕ} (m : Vec n) (i : ℕ) : ℝ :=
  if hi : i < n then m ⟨i, hi⟩ else 0

@[simp] theorem extendMean_fin {n : ℕ} (m : Vec n) (i : Fin n) :
    extendMean m i = m i := by simp [extendMean, i.isLt]

def euclideanCoordinatesEquiv (n : ℕ) : GaussianCoordinates n ≃ᵐ Vec n :=
  (coordinatesEquiv n).trans (EuclideanSpace.measurableEquiv (Fin n)).symm

theorem euclideanCoordinates_map {n : ℕ} (m : Vec n) (v : ℝ≥0) :
    (gaussianCoordinates n (extendMean m) v).map (euclideanCoordinatesEquiv n) =
      euclideanGaussian m v := by
  rw [euclideanCoordinatesEquiv, MeasurableEquiv.coe_trans,
    ← Measure.map_map (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable
      (coordinatesEquiv n).measurable,
    (coordinatesEquiv_measurePreserving n (extendMean m) v).map_eq]
  simp only [extendMean_fin, euclideanGaussian]

/-- Exact KL of a full-dimensional Gaussian law, after any injective
measurable embedding. The ambient image is allowed to be singular. -/
theorem euclideanGaussian_embedding_klDiv {n : ℕ} {F : Type*} [MeasurableSpace F]
    (f : Vec n → F) (hf : MeasurableEmbedding f) (m m' : Vec n)
    {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv ((euclideanGaussian m v).map f) ((euclideanGaussian m' v).map f) =
      ENNReal.ofReal (‖m - m'‖ ^ 2 / (2 * (v : ℝ))) := by
  rw [← euclideanCoordinates_map m v, ← euclideanCoordinates_map m' v,
    Measure.map_map hf.measurable (euclideanCoordinatesEquiv n).measurable,
    Measure.map_map hf.measurable (euclideanCoordinatesEquiv n).measurable,
    gaussianCoordinates_embedding_klDiv n _
      (hf.comp (euclideanCoordinatesEquiv n).measurableEmbedding) _ _ hv,
    Finset.sum_range]
  simp only [extendMean_fin]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    div_nonneg (sq_nonneg _) (by positivity)), ← Finset.sum_div,
    norm_sq_coordinates]
  rfl

theorem euclideanGaussian_klDiv {n : ℕ} (m m' : Vec n)
    {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (euclideanGaussian m v) (euclideanGaussian m' v) =
      ENNReal.ofReal (‖m - m'‖ ^ 2 / (2 * (v : ℝ))) := by
  simpa using euclideanGaussian_embedding_klDiv id MeasurableEmbedding.id m m' hv

theorem euclideanGaussian_standard (n : ℕ) :
    euclideanGaussian (0 : Vec n) 1 = standardGaussian n := rfl

/-- The concrete Euclidean product law equals an affine image of the
standard Gaussian, including zero noise. -/
theorem standardGaussian_affine_law {n : ℕ} (m : Vec n) (σ : ℝ) :
    (standardGaussian n).map (fun z => m + σ • z) =
      euclideanGaussian m ⟨σ ^ 2, sq_nonneg _⟩ := by
  have hs (i : Fin n) : MeasurePreserving (fun x : ℝ => m i + σ * x)
      (gaussianReal 0 1) (gaussianReal (m i) ⟨σ ^ 2, sq_nonneg _⟩) := by
    refine ⟨by fun_prop, ?_⟩
    rw [show (fun x : ℝ => m i + σ * x) = (fun x => m i + x) ∘ (fun x => σ * x) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    simp
  have hp := (measurePreserving_pi (fun _ : Fin n => gaussianReal 0 1)
    (fun i : Fin n => gaussianReal (m i) ⟨σ ^ 2, sq_nonneg _⟩) hs).map_eq
  rw [standardGaussian, euclideanGaussian,
    Measure.map_map (by fun_prop) (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable,
    ← hp, Measure.map_map (EuclideanSpace.measurableEquiv (Fin n)).symm.measurable
      (by fun_prop)]
  congr 1

/-- Orthogonal projection followed by orthonormal coordinates maps an
ambient standard Gaussian to a standard Gaussian on the subspace. -/
theorem standardGaussian_projection_law {d k : ℕ} (K : Submodule ℝ (Vec d))
    (e : Vec k ≃ₗᵢ[ℝ] K) :
    (standardGaussian d).map (fun z => e.symm (K.orthogonalProjection z)) =
      standardGaussian k := by
  have hm : Measurable (fun z : Vec d => e.symm (K.orthogonalProjection z)) :=
    (e.symm.continuous.comp K.orthogonalProjection.continuous).measurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,
    integral_map hm.aemeasurable
      ((by fun_prop : Continuous (fun x : Vec k =>
        Complex.exp ((⟪x, t⟫_ℝ : ℂ) * Complex.I))).measurable.aestronglyMeasurable)]
  simp_rw [LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm,
    K.inner_orthogonalProjection_eq_of_mem_right]
  rw [← charFun_apply, standardGaussian_charFun, standardGaussian_charFun]
  simp only [Submodule.norm_coe, e.norm_map]

theorem standardGaussian_projected_affine_law {d k : ℕ}
    (K : Submodule ℝ (Vec d)) (e : Vec k ≃ₗᵢ[ℝ] K) (m : Vec d) (σ : ℝ) :
    (standardGaussian d).map (fun z => e.symm (K.orthogonalProjection (m + σ • z))) =
      euclideanGaussian (e.symm (K.orthogonalProjection m)) ⟨σ ^ 2, sq_nonneg _⟩ := by
  have hm : Measurable (fun z : Vec d => e.symm (K.orthogonalProjection z)) :=
    (e.symm.continuous.comp K.orthogonalProjection.continuous).measurable
  rw [← standardGaussian_affine_law,
    ← standardGaussian_projection_law K e,
    Measure.map_map (by fun_prop) hm]
  congr 1
  funext z
  simp only [Function.comp_apply, map_add, map_smul]

/-- A linear observation factors through any subspace on which it is
injective and whose orthogonal projection preserves the observation. These
are purely linear-algebraic hypotheses, not assumptions about Gaussian laws. -/
theorem linearObservation_klDiv_of_complement {d k : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (B : Vec d →L[ℝ] F) (K : Submodule ℝ (Vec d)) (e : Vec k ≃ₗᵢ[ℝ] K)
    (hpres : ∀ x, B (K.orthogonalProjection x) = B x)
    (hinj : Function.Injective (fun x : K => B x))
    (m m' : Vec d) {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv ((standardGaussian d).map (fun z => B (m + σ • z)))
      ((standardGaussian d).map (fun z => B (m' + σ • z))) =
      ENNReal.ofReal (‖K.orthogonalProjection (m - m')‖ ^ 2 / (2 * σ ^ 2)) := by
  let f : Vec k →L[ℝ] F := B.comp (K.subtypeL.comp e.toLinearIsometry.toContinuousLinearMap)
  have hfi : Function.Injective f := hinj.comp e.injective
  have hfe : MeasurableEmbedding f :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hfi)).measurableEmbedding
  have hlaw (a : Vec d) :
      (standardGaussian d).map (fun z => B (a + σ • z)) =
      (euclideanGaussian (e.symm (K.orthogonalProjection a))
        ⟨σ ^ 2, sq_nonneg _⟩).map f := by
    have hm : Measurable
        (fun z : Vec d => e.symm (K.orthogonalProjection (a + σ • z))) :=
      (e.symm.continuous.comp (K.orthogonalProjection.continuous.comp
        (by fun_prop : Continuous (fun z : Vec d => a + σ • z)))).measurable
    rw [← standardGaussian_projected_affine_law K e a σ,
      Measure.map_map f.continuous.measurable hm]
    congr 1
    funext z
    simpa [f] using (hpres (a + σ • z)).symm
  have hv : (⟨σ ^ 2, sq_nonneg _⟩ : ℝ≥0) ≠ 0 := by
    intro hv
    exact pow_ne_zero 2 hσ (congrArg (fun v : ℝ≥0 => (v : ℝ)) hv)
  rw [hlaw m, hlaw m', euclideanGaussian_embedding_klDiv f hfe _ _ hv]
  rw [← map_sub, ← map_sub, e.symm.norm_map]
  rfl

/-- Exact singular Gaussian KL for every continuous linear observation.
Only the orthogonal projection of the mean difference onto `(ker B)ᗮ`
contributes. The theorem includes the zero map and all intermediate ranks;
no covariance inverse or full-rank hypothesis is used. -/
theorem linearObservation_klDiv {d : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (B : Vec d →L[ℝ] F) (m m' : Vec d) {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv ((standardGaussian d).map (fun z => B (m + σ • z)))
      ((standardGaussian d).map (fun z => B (m' + σ • z))) =
      ENNReal.ofReal (‖(LinearMap.ker B)ᗮ.orthogonalProjection (m - m')‖ ^ 2 /
        (2 * σ ^ 2)) := by
  let K : Submodule ℝ (Vec d) := (LinearMap.ker B)ᗮ
  let e := (stdOrthonormalBasis ℝ K).repr.symm
  have hpres : ∀ x : Vec d, B (K.orthogonalProjection x) = B x := by
    intro x
    have hzero : B ((LinearMap.ker B).orthogonalProjection x) = 0 :=
      ((LinearMap.ker B).orthogonalProjection x).property
    change B ((LinearMap.ker B)ᗮ.orthogonalProjection x) = B x
    rw [Submodule.orthogonalProjection_orthogonal_val, map_sub, hzero, sub_zero]
  have hinj : Function.Injective (fun x : K => B x) := by
    intro x y hxy
    change B (x : Vec d) = B (y : Vec d) at hxy
    apply Subtype.ext
    have hker : (x : Vec d) - (y : Vec d) ∈ LinearMap.ker B := by
      change B ((x : Vec d) - (y : Vec d)) = 0
      rw [map_sub, hxy, sub_self]
    have horth : (x : Vec d) - (y : Vec d) ∈ (LinearMap.ker B)ᗮ :=
      K.sub_mem x.property y.property
    have hzero : (x : Vec d) - (y : Vec d) ∈ (⊥ : Submodule ℝ (Vec d)) := by
      rw [← (LinearMap.ker B).inf_orthogonal_eq_bot]
      exact ⟨hker, horth⟩
    apply sub_eq_zero.mp
    simpa using hzero
  exact linearObservation_klDiv_of_complement B K e hpres hinj m m' hσ

end MatchingBounds1005.LinearGaussianKL
