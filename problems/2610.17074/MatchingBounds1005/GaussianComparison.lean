import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Genuine Gaussian relative entropy calculations

The one-dimensional moment, density and measurable-embedding proofs below are
adapted from the local Lean 4.19 project
`Lean1/FreshGradientMinimax0111/FreshGradientMinimax/`:
`GaussianMoments.lean`, `GaussianKL.lean`, and `KLEmbedding.lean`.
Only their mathematical bodies are reused; there is no dependency on that
project's oracle model, and all claims are rechecked in this project.

This file proves actual KL identities for finite products of scalar Gaussian
measures and their measurable embeddings, including singular laws in a larger
ambient space. The conversion of arbitrary linear observations to these
coordinates, and adaptive posterior factorization, remain separate tasks.
-/

set_option autoImplicit false
noncomputable section
namespace MatchingBounds1005.GaussianComparison
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal BigOperators
theorem gaussianReal_mgf (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    mgf id (gaussianReal m v) t = Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) :=
  mgf_gaussianReal (Measure.map_id) t

theorem gaussianReal_exp_integrable (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianReal m v) := by
  by_contra h
  have hz := mgf_undef (X := id) h
  rw [gaussianReal_mgf] at hz
  exact Real.exp_ne_zero _ hz

theorem gaussianReal_exp_interior (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    t ∈ interior (integrableExpSet id (gaussianReal m v)) := by
  have he : integrableExpSet id (gaussianReal m v) = Set.univ := by
    ext u
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact gaussianReal_exp_integrable m v u
  rw [he, interior_univ]
  trivial

theorem gaussianReal_pow_integrable (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) :=
  integrable_pow_of_mem_interior_integrableExpSet (gaussianReal_exp_interior m v 0) n

theorem gaussianReal_id_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable id (gaussianReal m v) := by
  simpa only [pow_one] using gaussianReal_pow_integrable m v 1

theorem gaussian_exp_derivative (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (m * u + (v : ℝ) * u ^ 2 / 2))
      ((m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)) t := by
  apply (((hasDerivAt_id t).const_mul m).add
    ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2)).exp.congr_deriv
  simp only [id_eq, mul_one, pow_one, Nat.cast_ofNat]
  ring

theorem gaussianReal_weighted_mean (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (∫ x : ℝ, x * Real.exp (t * x) ∂gaussianReal m v) =
      (m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
  have h := hasDerivAt_mgf (gaussianReal_exp_interior m v t)
  have he : mgf id (gaussianReal m v) =
      (fun u : ℝ => Real.exp (m * u + (v : ℝ) * u ^ 2 / 2)) := funext (gaussianReal_mgf m v)
  rw [he] at h
  exact h.unique (gaussian_exp_derivative m v t)

theorem gaussianReal_mean (m : ℝ) (v : ℝ≥0) : (∫ x : ℝ, x ∂gaussianReal m v) = m := by
  simpa using gaussianReal_weighted_mean m v 0

theorem gaussianReal_second_moment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal m v) = (v : ℝ) + m ^ 2 := by
  have h := hasDerivAt_integral_pow_mul_exp_real (gaussianReal_exp_interior m v 0) 1
  have he : (fun t : ℝ => ∫ x : ℝ, x ^ 1 * Real.exp (t * x) ∂gaussianReal m v) =
      (fun t : ℝ => (m + (v : ℝ) * t) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)) := by
    funext t
    simpa only [pow_one] using gaussianReal_weighted_mean m v t
  change HasDerivAt (fun t : ℝ => ∫ x : ℝ, x ^ 1 * Real.exp (t * x) ∂gaussianReal m v)
    (∫ x : ℝ, x ^ (1 + 1) * Real.exp (0 * x) ∂gaussianReal m v) 0 at h
  rw [he] at h
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul (v : ℝ)).const_add m).mul
    (gaussian_exp_derivative m v 0)
  have hu := h.unique hd
  simpa [pow_two] using hu

theorem gaussianReal_centered_square_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x - m) ^ 2) (gaussianReal m v) := by
  have h := ((gaussianReal_pow_integrable m v 2).sub
    ((gaussianReal_id_integrable m v).const_mul (2 * m))).add (integrable_const (m ^ 2))
  convert h using 1
  funext x
  dsimp only [id_eq, Pi.add_apply, Pi.sub_apply]
  ring

theorem gaussianReal_variance (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, (x - m) ^ 2 ∂gaussianReal m v) = (v : ℝ) := by
  have he (x : ℝ) : (x - m) ^ 2 = x ^ 2 - 2 * m * x + m ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun x : ℝ => x ^ 2 - 2 * m * x) (g := fun _ : ℝ => m ^ 2)
      ((gaussianReal_pow_integrable m v 2).sub
      ((gaussianReal_id_integrable m v).const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun x : ℝ => x ^ 2) (g := fun x : ℝ => 2 * m * x)
      (gaussianReal_pow_integrable m v 2) ((gaussianReal_id_integrable m v).const_mul (2 * m)),
    integral_const_mul, gaussianReal_second_moment, gaussianReal_mean]
  simp
  ring


theorem gaussianReal_mutual_ac (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v ≪ gaussianReal n v :=
  (gaussianReal_absolutelyContinuous m hv).trans (gaussianReal_absolutelyContinuous' n hv)

theorem gaussianPDFReal_log_difference (m n x : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Real.log (gaussianPDFReal m v x) - Real.log (gaussianPDFReal n v x) =
      ((m - n) / (v : ℝ)) * x + (n ^ 2 - m ^ 2) / (2 * (v : ℝ)) := by
  have hv0 : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by positivity
  simp only [gaussianPDFReal, Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

theorem gaussianReal_llr (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    llr (gaussianReal m v) (gaussianReal n v) =ᵐ[gaussianReal m v]
      (fun x : ℝ => ((m - n) / (v : ℝ)) * x + (n ^ 2 - m ^ 2) / (2 * (v : ℝ))) := by
  have hr := Measure.rnDeriv_withDensity_right (gaussianReal m v) volume
    (measurable_gaussianPDF n v).aemeasurable
    (Filter.Eventually.of_forall (fun x => (gaussianPDF_pos n hv x).ne'))
    (Filter.Eventually.of_forall (fun _ => gaussianPDF_ne_top))
  rw [← gaussianReal_of_var_ne_zero n hv] at hr
  apply (gaussianReal_absolutelyContinuous m hv).ae_eq
  filter_upwards [hr, rnDeriv_gaussianReal m v] with x hx hy
  rw [llr, hx, hy, ENNReal.toReal_mul, ENNReal.toReal_inv,
    toReal_gaussianPDF, toReal_gaussianPDF,
    Real.log_mul (inv_ne_zero (gaussianPDFReal_pos n v x hv).ne') (gaussianPDFReal_pos m v x hv).ne',
    Real.log_inv]
  have h := gaussianPDFReal_log_difference m n x hv
  linarith

theorem gaussianReal_llr_integrable (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m v) (gaussianReal n v)) (gaussianReal m v) := by
  apply (integrable_congr (gaussianReal_llr m n hv)).mpr
  exact ((gaussianReal_id_integrable m v).const_mul _).add (integrable_const _)

theorem gaussianReal_klDiv (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal m v) (gaussianReal n v) =
      ENNReal.ofReal ((m - n) ^ 2 / (2 * (v : ℝ))) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_mutual_ac m n hv) (gaussianReal_llr_integrable m n hv),
    integral_congr_ae (gaussianReal_llr m n hv),
    integral_add (f := fun x : ℝ => ((m - n) / (v : ℝ)) * x)
      (g := fun _ : ℝ => (n ^ 2 - m ^ 2) / (2 * (v : ℝ)))
      ((gaussianReal_id_integrable m v).const_mul _) (integrable_const _),
    integral_const_mul, gaussianReal_mean]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, add_sub_cancel_right]
  congr 1
  ring


theorem llr_map_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : α → β} (hf : MeasurableEmbedding f) (hPQ : P ≪ Q) :
    (fun x => llr (P.map f) (Q.map f) (f x)) =ᵐ[P] llr P Q := by
  filter_upwards [hPQ.ae_eq (hf.rnDeriv_map P Q)] with x hx
  simp only [llr, hx]

theorem klDiv_map_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : α → β} (hf : MeasurableEmbedding f) (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P) :
    klDiv (P.map f) (Q.map f) = klDiv P Q := by
  have hi' : Integrable (llr (P.map f) (Q.map f)) (P.map f) := by
    rw [hf.integrable_map_iff]
    exact hi.congr (llr_map_embedding hf hPQ).symm
  rw [klDiv_of_ac_of_integrable (hf.absolutelyContinuous_map hPQ) hi',
    klDiv_of_ac_of_integrable hPQ hi,
    integral_map hf.measurable.aemeasurable (measurable_llr _ _).aestronglyMeasurable,
    integral_congr_ae (llr_map_embedding hf hPQ)]
  simp [measureReal_def, Measure.map_apply hf.measurable MeasurableSet.univ]


/-- Equal-variance Gaussian KL is unchanged by any measurable embedding.
In particular, embedding a scalar Gaussian into a higher-dimensional space
does not require a nonsingular ambient covariance. -/
theorem gaussianReal_klDiv_embedding {F : Type*} [MeasurableSpace F]
    (f : ℝ → F) (hf : MeasurableEmbedding f)
    (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv ((gaussianReal m v).map f) ((gaussianReal n v).map f) =
      ENNReal.ofReal ((m - n) ^ 2 / (2 * (v : ℝ))) := by
  rw [klDiv_map_embedding hf (gaussianReal_mutual_ac m n hv)
    (gaussianReal_llr_integrable m n hv), gaussianReal_klDiv m n hv]

/-- A Gaussian law on the affine line through `base` in direction `direction`.
Its covariance in the ambient space has rank at most one. -/
def rankOneGaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (base direction : E) (m : ℝ) (v : ℝ≥0) : Measure E :=
  (gaussianReal m v).map (fun t : ℝ => base + t • direction)

/-- Actual KL between affine rank-one Gaussian measures on the same support.
The displayed covariance is singular whenever the ambient dimension exceeds
one; no density with respect to ambient Lebesgue measure is used. -/
theorem rankOneGaussian_klDiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (base direction : E) (hd : direction ≠ 0) (m n : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (rankOneGaussian base direction m v) (rankOneGaussian base direction n v) =
      ENNReal.ofReal ((m - n) ^ 2 / (2 * (v : ℝ))) := by
  apply gaussianReal_klDiv_embedding _ _ m n hv
  exact (Homeomorph.addLeft base).isClosedEmbedding.measurableEmbedding.comp
    (isClosedEmbedding_smul_left hd).measurableEmbedding

/-- A rank-zero observation is identical under both laws and has zero KL. -/
theorem rankZeroGaussian_klDiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (base : E) (m n : ℝ) (v : ℝ≥0) :
    klDiv (rankOneGaussian base 0 m v) (rankOneGaussian base 0 n v) = 0 := by
  simp [rankOneGaussian]

section Products

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P Q : Measure α} {R S : Measure β}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R] [IsProbabilityMeasure S]

/-- The actual likelihood ratio for a binary product of absolutely continuous
probability measures splits into the two coordinate likelihood ratios. -/
theorem prod_llr (hPQ : P ≪ Q) (hRS : R ≪ S) :
    llr (P.prod R) (Q.prod S) =ᵐ[P.prod R]
      (fun z => llr P Q z.1 + llr R S z.2) := by
  have he : P.prod R = (Q.prod S).withDensity
      (fun z => P.rnDeriv Q z.1 * R.rnDeriv S z.2) := by
    calc
      P.prod R = (Q.withDensity (P.rnDeriv Q)).prod
          (S.withDensity (R.rnDeriv S)) := by
        rw [P.withDensity_rnDeriv_eq Q hPQ, R.withDensity_rnDeriv_eq S hRS]
      _ = _ := prod_withDensity (P.measurable_rnDeriv Q) (R.measurable_rnDeriv S)
  have hr : (P.prod R).rnDeriv (Q.prod S) =ᵐ[Q.prod S]
      (fun z => P.rnDeriv Q z.1 * R.rnDeriv S z.2) := by
    conv_lhs => rw [he]
    exact (Q.prod S).rnDeriv_withDensity
      (((P.measurable_rnDeriv Q).comp measurable_fst).mul
        ((R.measurable_rnDeriv S).comp measurable_snd))
  have hp : ∀ᵐ a ∂P, 0 < (P.rnDeriv Q a).toReal := by
    filter_upwards [Measure.rnDeriv_pos hPQ, hPQ.ae_le (P.rnDeriv_ne_top Q)] with a ha ht
    exact ENNReal.toReal_pos ha.ne' ht
  have hs : ∀ᵐ b ∂R, 0 < (R.rnDeriv S b).toReal := by
    filter_upwards [Measure.rnDeriv_pos hRS, hRS.ae_le (R.rnDeriv_ne_top S)] with b hb ht
    exact ENNReal.toReal_pos hb.ne' ht
  filter_upwards [(hPQ.prod hRS).ae_eq hr,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := R)).ae hp,
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := R)).ae hs] with z hz hpz hsz
  simp only [llr, hz, ENNReal.toReal_mul]
  exact Real.log_mul hpz.ne' hsz.ne'

/-- Exact KL additivity for binary products, derived from actual densities and
Bochner integrals. Iteration supplies the finite-coordinate Gaussian step. -/
theorem klDiv_prod (hPQ : P ≪ Q) (hRS : R ≪ S)
    (hiP : Integrable (llr P Q) P) (hiR : Integrable (llr R S) R) :
    klDiv (P.prod R) (Q.prod S) = klDiv P Q + klDiv R S := by
  have hi1 : Integrable (fun z : α × β => llr P Q z.1) (P.prod R) := by
    simpa using hiP.mul_prod (integrable_const (1 : ℝ) (μ := R))
  have hi2 : Integrable (fun z : α × β => llr R S z.2) (P.prod R) := by
    simpa using (integrable_const (1 : ℝ) (μ := P)).mul_prod hiR
  have hi : Integrable (llr (P.prod R) (Q.prod S)) (P.prod R) :=
    (hi1.add hi2).congr (prod_llr hPQ hRS).symm
  have hnP : 0 ≤ ∫ a, llr P Q a ∂P := by
    simpa using integral_llr_add_sub_measure_univ_nonneg hPQ hiP
  have hnR : 0 ≤ ∫ b, llr R S b ∂R := by
    simpa using integral_llr_add_sub_measure_univ_nonneg hRS hiR
  rw [klDiv_of_ac_of_integrable (hPQ.prod hRS) hi,
    klDiv_of_ac_of_integrable hPQ hiP, klDiv_of_ac_of_integrable hRS hiR,
    integral_congr_ae (prod_llr hPQ hRS), integral_add hi1 hi2,
    integral_fun_fst, integral_fun_snd]
  simp only [measureReal_univ_eq_one, one_smul, add_sub_cancel_right]
  exact ENNReal.ofReal_add hnP hnR

end Products

/-- Two independent Gaussian channels add their actual KL contributions. -/
theorem gaussianReal_pair_klDiv (m₁ n₁ m₂ n₂ : ℝ) {v₁ v₂ : ℝ≥0}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    klDiv ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂))
      ((gaussianReal n₁ v₁).prod (gaussianReal n₂ v₂)) =
      ENNReal.ofReal ((m₁ - n₁) ^ 2 / (2 * (v₁ : ℝ))) +
      ENNReal.ofReal ((m₂ - n₂) ^ 2 / (2 * (v₂ : ℝ))) := by
  rw [klDiv_prod (gaussianReal_mutual_ac m₁ n₁ hv₁)
    (gaussianReal_mutual_ac m₂ n₂ hv₂) (gaussianReal_llr_integrable m₁ n₁ hv₁)
    (gaussianReal_llr_integrable m₂ n₂ hv₂), gaussianReal_klDiv m₁ n₁ hv₁,
    gaussianReal_klDiv m₂ n₂ hv₂]

/-- A finite tuple represented recursively, so the Gaussian product and its
likelihood are built from actual binary product measures. -/
def GaussianCoordinates : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × GaussianCoordinates n

instance gaussianCoordinatesMeasurableSpace (n : ℕ) : MeasurableSpace (GaussianCoordinates n) :=
  match n with
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 =>
    letI := gaussianCoordinatesMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ℝ × GaussianCoordinates n))

/-- The first `n` coordinates have independent scalar Gaussian laws. -/
def gaussianCoordinates (n : ℕ) (m : ℕ → ℝ) (v : ℝ≥0) :
    Measure (GaussianCoordinates n) :=
  match n with
  | 0 => Measure.dirac ()
  | n + 1 => (gaussianReal (m 0) v).prod
      (gaussianCoordinates n (fun i => m (i + 1)) v)

instance gaussianCoordinates_probability (n : ℕ) (m : ℕ → ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianCoordinates n m v) := by
  induction n generalizing m with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
    letI := ih (fun i => m (i + 1))
    exact inferInstanceAs (IsProbabilityMeasure
      ((gaussianReal (m 0) v).prod (gaussianCoordinates n (fun i => m (i + 1)) v)))

theorem gaussianCoordinates_ac (n : ℕ) (m m' : ℕ → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianCoordinates n m v ≪ gaussianCoordinates n m' v := by
  induction n generalizing m m' with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ n ih =>
    exact (gaussianReal_mutual_ac (m 0) (m' 0) hv).prod
      (ih (fun i => m (i + 1)) (fun i => m' (i + 1)))

theorem gaussianCoordinates_llr_integrable (n : ℕ) (m m' : ℕ → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr (gaussianCoordinates n m v) (gaussianCoordinates n m' v))
      (gaussianCoordinates n m v) := by
  induction n generalizing m m' with
  | zero =>
    apply (integrable_congr (llr_self (Measure.dirac ()))).mpr
    exact integrable_zero _ _ _
  | succ n ih =>
    have hi1 : Integrable
        (fun z : ℝ × GaussianCoordinates n => llr (gaussianReal (m 0) v)
          (gaussianReal (m' 0) v) z.1)
        ((gaussianReal (m 0) v).prod (gaussianCoordinates n (fun i => m (i + 1)) v)) := by
      simpa using (gaussianReal_llr_integrable (m 0) (m' 0) hv).mul_prod
        (integrable_const (1 : ℝ) (μ := gaussianCoordinates n (fun i => m (i + 1)) v))
    have hi2 : Integrable
        (fun z : ℝ × GaussianCoordinates n =>
          llr (gaussianCoordinates n (fun i => m (i + 1)) v)
            (gaussianCoordinates n (fun i => m' (i + 1)) v) z.2)
        ((gaussianReal (m 0) v).prod (gaussianCoordinates n (fun i => m (i + 1)) v)) := by
      simpa using (integrable_const (1 : ℝ) (μ := gaussianReal (m 0) v)).mul_prod
        (ih (fun i => m (i + 1)) (fun i => m' (i + 1)))
    exact (hi1.add hi2).congr (prod_llr
      (gaussianReal_mutual_ac (m 0) (m' 0) hv)
      (gaussianCoordinates_ac n (fun i => m (i + 1)) (fun i => m' (i + 1)) hv)).symm

/-- Exact relative entropy of independent Gaussian coordinates in every
finite dimension, proved by finite product induction. -/
theorem gaussianCoordinates_klDiv (n : ℕ) (m m' : ℕ → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianCoordinates n m v) (gaussianCoordinates n m' v) =
      ∑ i ∈ Finset.range n, ENNReal.ofReal ((m i - m' i) ^ 2 / (2 * (v : ℝ))) := by
  induction n generalizing m m' with
  | zero => simp [gaussianCoordinates]
  | succ n ih =>
    change klDiv ((gaussianReal (m 0) v).prod _)
      ((gaussianReal (m' 0) v).prod _) = _
    rw [klDiv_prod (gaussianReal_mutual_ac (m 0) (m' 0) hv)
      (gaussianCoordinates_ac n (fun i => m (i + 1)) (fun i => m' (i + 1)) hv)
      (gaussianReal_llr_integrable (m 0) (m' 0) hv)
      (gaussianCoordinates_llr_integrable n
        (fun i => m (i + 1)) (fun i => m' (i + 1)) hv),
      gaussianReal_klDiv (m 0) (m' 0) hv, ih, Finset.sum_range_succ']
    exact add_comm _ _

/-- Every injectively embedded finite-coordinate Gaussian law has the same
KL. For an injective affine embedding, this covers arbitrary finite-rank
Gaussian laws on a common affine support, including singular ambient laws. -/
theorem gaussianCoordinates_embedding_klDiv {F : Type*} [MeasurableSpace F]
    (n : ℕ) (f : GaussianCoordinates n → F) (hf : MeasurableEmbedding f)
    (m m' : ℕ → ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv ((gaussianCoordinates n m v).map f) ((gaussianCoordinates n m' v).map f) =
      ∑ i ∈ Finset.range n, ENNReal.ofReal ((m i - m' i) ^ 2 / (2 * (v : ℝ))) := by
  rw [klDiv_map_embedding hf (gaussianCoordinates_ac n m m' hv)
    (gaussianCoordinates_llr_integrable n m m' hv), gaussianCoordinates_klDiv n m m' hv]

end MatchingBounds1005.GaussianComparison

