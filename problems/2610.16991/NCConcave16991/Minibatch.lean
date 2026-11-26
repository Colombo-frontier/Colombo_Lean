import NCConcave16991.Smoothness
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991

/-- An actual uniform distribution over the persistent component identities. -/
def uniformIndexLaw (n : ℕ) [NeZero n] [MeasurableSpace (Fin n)]
    [MeasurableSingletonClass (Fin n)] : Measure (Fin n) :=
  (PMF.uniformOfFintype (Fin n)).toMeasure

instance uniformIndexLaw_probability (n : ℕ) [NeZero n] [MeasurableSpace (Fin n)]
    [MeasurableSingletonClass (Fin n)] : IsProbabilityMeasure (uniformIndexLaw n) := by
  unfold uniformIndexLaw
  infer_instance

/-- The genuine independent-with-replacement b-sample law, on all Fin b → Fin n arrays. -/
def minibatchLaw (n b : ℕ) [NeZero n] [MeasurableSpace (Fin n)]
    [MeasurableSingletonClass (Fin n)] : Measure (Fin b → Fin n) :=
  Measure.pi (fun _ : Fin b => uniformIndexLaw n)

instance minibatchLaw_probability (n b : ℕ) [NeZero n] [MeasurableSpace (Fin n)]
    [MeasurableSingletonClass (Fin n)] : IsProbabilityMeasure (minibatchLaw n b) := by
  unfold minibatchLaw
  infer_instance

variable {n b : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- Evaluation of the genuine product law recovers the one-sample finite mean. -/
theorem minibatch_coordinate_integral (v : Fin n → H) (j : Fin b) :
    (∫ I, v (I j) ∂minibatchLaw n b) = (n : ℝ)⁻¹ • ∑ i, v i := by
  unfold minibatchLaw
  rw [integral_comp_eval (Integrable.of_finite : Integrable v (uniformIndexLaw n)).aestronglyMeasurable]
  simp [uniformIndexLaw, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ← Finset.smul_sum]

/-- Coordinate independence is proved for the actual product law; it is not an assumption. -/
theorem minibatch_coordinates_independent (v : Fin n → H) :
    iIndepFun (fun j : Fin b => fun I : Fin b → Fin n => v (I j)) (minibatchLaw n b) := by
  unfold minibatchLaw
  exact iIndepFun_pi (fun _ => (measurable_of_countable v).aemeasurable)

/-- The mean of b independent component samples, retaining persistent component identities. -/
def minibatchMean (v : Fin n → H) (I : Fin b → Fin n) : H :=
  (b : ℝ)⁻¹ • ∑ j, v (I j)

/-- The exact algebraic centering of the sampled mean. -/
theorem minibatchMean_centered (hb : 0 < b) (v : Fin n → H) (I : Fin b → Fin n) :
    minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i =
      (b : ℝ)⁻¹ • ∑ j, (v (I j) - (n : ℝ)⁻¹ • ∑ i, v i) := by
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [minibatchMean, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hbp.ne', one_smul]

/-- Exact first moment: the minibatch estimator is centered under its actual product law. -/
theorem minibatch_centered_integral (hb : 0 < b) (v : Fin n → H) :
    (∫ I, minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i ∂minibatchLaw n b) = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp_rw [minibatchMean_centered hb v]
  rw [integral_smul, integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [minibatch_coordinate_integral (fun i => v i - (n : ℝ)⁻¹ • ∑ l, v l)]
  rw [finite_centered_sum_eq_zero hn v]
  simp

/-- Off-diagonal Hilbert cross terms vanish for the actual independent uniform law. -/
theorem minibatch_centered_cross_integral (v : Fin n → H) {j k : Fin b} (hjk : j ≠ k) :
    (∫ I, ⟪v (I j) - (n : ℝ)⁻¹ • ∑ i, v i,
      v (I k) - (n : ℝ)⁻¹ • ∑ i, v i⟫_ℝ ∂minibatchLaw n b) = 0 := by
  let w : Fin n → H := fun i => v i - (n : ℝ)⁻¹ • ∑ l, v l
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm (j : Fin b) : (∫ I, w (I j) ∂minibatchLaw n b) = 0 := by
    rw [minibatch_coordinate_integral]
    dsimp [w]
    rw [finite_centered_sum_eq_zero hn v, smul_zero]
  have hind := (minibatch_coordinates_independent (b := b) w).indepFun hjk
  have hbilin := hind.integral_bilin Integrable.of_finite Integrable.of_finite (innerSL ℝ)
  rw [hm j, hm k] at hbilin
  change (∫ I, ⟪w (I j), w (I k)⟫_ℝ ∂minibatchLaw n b) = ⟪(0 : H), 0⟫_ℝ at hbilin
  simpa only [inner_zero_left] using hbilin

/-- The squared-norm sum expansion and genuine product integration give b times
one centered second moment, with every off-diagonal term proved zero. -/
theorem minibatch_centered_sum_second_moment (v : Fin n → H) :
    (∫ I, ‖∑ j : Fin b, (v (I j) - (n : ℝ)⁻¹ • ∑ i, v i)‖ ^ 2 ∂minibatchLaw n b) =
      (b : ℝ) * ((n : ℝ)⁻¹ * ∑ i, ‖v i - (n : ℝ)⁻¹ • ∑ l, v l‖ ^ 2) := by
  let w : Fin n → H := fun i => v i - (n : ℝ)⁻¹ • ∑ l, v l
  have hexpand (I : Fin b → Fin n) : ‖∑ j, w (I j)‖ ^ 2 =
      ∑ j : Fin b, ∑ k : Fin b, ⟪w (I j), w (I k)⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  change (∫ I, ‖∑ j, w (I j)‖ ^ 2 ∂minibatchLaw n b) =
    (b : ℝ) * ((n : ℝ)⁻¹ * ∑ i, ‖w i‖ ^ 2)
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  have hentry (j k : Fin b) :
      (∫ I, ⟪w (I j), w (I k)⟫_ℝ ∂minibatchLaw n b) =
        if j = k then (n : ℝ)⁻¹ * ∑ i, ‖w i‖ ^ 2 else 0 := by
    by_cases hjk : j = k
    · subst k
      simp only [↓reduceIte, real_inner_self_eq_norm_sq]
      simpa [smul_eq_mul] using
        (minibatch_coordinate_integral (H := ℝ) (fun i => ‖w i‖ ^ 2) j)
    · simp only [hjk, ↓reduceIte]
      exact minibatch_centered_cross_integral v hjk
  simp_rw [hentry]
  simp

/-- Lemma A.1(ii), exact minibatch variance with its actual independent finite product law. -/
theorem minibatch_variance_identity (hb : 0 < b) (v : Fin n → H) :
    (∫ I, ‖minibatchMean v I - (n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 ∂minibatchLaw n b) =
      (b : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 - ‖(n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2) := by
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp_rw [minibatchMean_centered hb v, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hbp.le), mul_pow]
  rw [integral_const_mul, minibatch_centered_sum_second_moment, finite_variance_identity hn v]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow]
  field_simp [hbp.ne']
  <;> ring

end NCConcave16991



namespace NCConcave16991

variable {n b : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lemma A.1(ii)'s actual independent minibatch variance bound follows from AS. -/
theorem AveragedSmooth.minibatch_variance_bound {G : Fin n → E → H}
    {s : Set E} {L : ℝ} (hG : AveragedSmooth G s L) (hb : 0 < b)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (∫ I, ‖minibatchMean (fun i => G i x - G i y) I -
      (averageMap G x - averageMap G y)‖ ^ 2 ∂minibatchLaw n b) ≤
        (L ^ 2 / b) * ‖x - y‖ ^ 2 := by
  have hdiff : averageMap G x - averageMap G y =
      (n : ℝ)⁻¹ • ∑ i, (G i x - G i y) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  rw [hdiff, minibatch_variance_identity hb]
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hbase := hG x hx y hy
  have hcenter : (n : ℝ)⁻¹ * ∑ i, ‖G i x - G i y‖ ^ 2 -
      ‖(n : ℝ)⁻¹ • ∑ i, (G i x - G i y)‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    linarith [sq_nonneg ‖(n : ℝ)⁻¹ • ∑ i, (G i x - G i y)‖]
  have hm := mul_le_mul_of_nonneg_left hcenter (inv_nonneg.mpr hbp.le)
  convert hm using 1 <;> ring

end NCConcave16991

namespace NCConcave16991

variable {n b : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The same actual product-law bound in any dominated quadratic weight. -/
theorem AveragedSmooth.weighted_minibatch_variance_bound {G : Fin n → E → H}
    {s : Set E} {L κ : ℝ} (hG : AveragedSmooth G s L) (hb : 0 < b)
    (hκ : 0 ≤ κ) (U : H →ₗ[ℝ] K) (hU : ∀ v, ‖U v‖ ^ 2 ≤ κ * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (∫ I, ‖U (minibatchMean (fun i => G i x - G i y) I -
      (averageMap G x - averageMap G y))‖ ^ 2 ∂minibatchLaw n b) ≤
        κ * (L ^ 2 / b) * ‖x - y‖ ^ 2 := by
  have hm := integral_mono (μ := minibatchLaw n b) Integrable.of_finite
    Integrable.of_finite (fun I => hU (minibatchMean (fun i => G i x - G i y) I -
      (averageMap G x - averageMap G y)))
  rw [integral_const_mul] at hm
  have hc := mul_le_mul_of_nonneg_left (hG.minibatch_variance_bound hb hx hy) hκ
  nlinarith

end NCConcave16991
