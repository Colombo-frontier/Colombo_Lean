import NCConcave16991.VariationalInequality
import NCConcave16991.PersistentEstimator
import Mathlib.Tactic.Abel

/-!
# Actual projected finite-sum inner steps

The estimator uses an anchor estimate with arbitrary fixed bias and one fresh
uniform component index. All expectations below use the actual uniform law.
The projection comparison uses a VI fixed point, not a vanishing constrained
gradient. Operator smoothness and monotonicity are explicit mathematical
interfaces; the algorithmic recurrence is derived from the sampled step.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.InnerAlgorithm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [NeZero n] [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)]

/-- Exact integration against the persistent identities' genuine uniform law. -/
theorem uniformIndex_integral (f : Fin n → E) :
    (∫ i, f i ∂uniformIndexLaw n) = (n : ℝ)⁻¹ • ∑ i, f i := by
  simp [uniformIndexLaw, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ← Finset.smul_sum]

 theorem uniformIndex_integral_real (f : Fin n → ℝ) :
    (∫ i, f i ∂uniformIndexLaw n) = (n : ℝ)⁻¹ * ∑ i, f i := by
  simpa only [smul_eq_mul] using (uniformIndex_integral (E := ℝ) f)

/-- The actual sampled centered component difference. -/
def sampledError (G : Fin n → E → E) (anchor z : E) (i : Fin n) : E :=
  G i z - G i anchor - (averageMap G z - averageMap G anchor)

 theorem sampledError_mean_zero (G : Fin n → E → E) (anchor z : E) :
    (∫ i, sampledError G anchor z i ∂uniformIndexLaw n) = 0 := by
  rw [uniformIndex_integral]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hdiff : averageMap G z - averageMap G anchor =
      (n : ℝ)⁻¹ • ∑ i, (G i z - G i anchor) := by
    simp [averageMap, Finset.sum_sub_distrib, smul_sub]
  simp only [sampledError, hdiff]
  rw [finite_centered_sum_eq_zero hn]
  simp

 theorem sampledError_variance {G : Fin n → E → E} {S : Set E} {L : ℝ}
    (hAS : AveragedSmooth G S L) {anchor z : E} (ha : anchor ∈ S) (hz : z ∈ S) :
    (∫ i, ‖sampledError G anchor z i‖ ^ 2 ∂uniformIndexLaw n) ≤ L ^ 2 * ‖z - anchor‖ ^ 2 := by
  rw [uniformIndex_integral_real]
  exact hAS.centered_difference_bound (Nat.pos_of_ne_zero (NeZero.ne n)) hz ha

/-- Centering removes the exact Hilbert cross term under the actual uniform law. -/
theorem centered_step_second_moment (a : E) (η : ℝ) (ζ : Fin n → E)
    (hζ : (∫ i, ζ i ∂uniformIndexLaw n) = 0) :
    (∫ i, ‖a - η • ζ i‖ ^ 2 ∂uniformIndexLaw n) =
      ‖a‖ ^ 2 + η ^ 2 * ∫ i, ‖ζ i‖ ^ 2 ∂uniformIndexLaw n := by
  have hcross : (∫ i, ⟪a, ζ i⟫_ℝ ∂uniformIndexLaw n) = 0 := by
    have h := (innerSL ℝ a).integral_comp_comm
      (Integrable.of_finite : Integrable ζ (uniformIndexLaw n))
    simpa only [innerSL_apply_apply, hζ, inner_zero_right] using h
  have hexp (i : Fin n) : ‖a - η • ζ i‖ ^ 2 =
      ‖a‖ ^ 2 - (2 * η) * ⟪a, ζ i⟫_ℝ + η ^ 2 * ‖ζ i‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  simp_rw [hexp]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul, hcross]
  simp

/-- The actual estimator in Appendix B.3, retaining the persistent component identity. -/
def estimator (G : Fin n → E → E) (regularizer : E → E) (anchor bias z : E)
    (i : Fin n) : E :=
  (averageMap G anchor + bias) + (G i z - G i anchor) + regularizer z

/-- The signed averaged regularized operator associated with this estimator. -/
def operator (G : Fin n → E → E) (regularizer : E → E) (z : E) : E :=
  averageMap G z + regularizer z

 theorem estimator_decomposition (G : Fin n → E → E) (regularizer : E → E)
    (anchor bias z : E) (i : Fin n) :
    estimator G regularizer anchor bias z i =
      operator G regularizer z + bias + sampledError G anchor z i := by
  dsimp [estimator, operator, sampledError]
  abel

variable (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- One genuine sampled projected inner iteration. -/
def step (G : Fin n → E → E) (regularizer : E → E) (anchor bias : E) (η : ℝ)
    (z : S) (i : Fin n) : S :=
  VariationalInequality.projection S hne hclosed hconvex
    ((z : E) - η • estimator G regularizer anchor bias z i)

/-- The exact one-step projection/centering estimate before any smoothness bounds. -/
theorem step_second_moment (G : Fin n → E → E) (regularizer : E → E)
    (anchor bias : E) {η : ℝ} (hη : 0 < η) (z star : S)
    (hstar : VariationalInequality.IsSolution S
      (fun w ↦ operator G regularizer w + bias) star) :
    (∫ i, ‖(step S hne hclosed hconvex G regularizer anchor bias η z i : E) - star‖ ^ 2
      ∂uniformIndexLaw n) ≤
      ‖((z : E) - star) - η • (operator G regularizer z - operator G regularizer star)‖ ^ 2 +
        η ^ 2 * ∫ i, ‖sampledError G anchor z i‖ ^ 2 ∂uniformIndexLaw n := by
  have hfix := (VariationalInequality.projectedStep_fixed_iff S hne hclosed hconvex
    (fun w ↦ operator G regularizer w + bias) hη star).mpr hstar
  have hp (i : Fin n) :
      ‖(step S hne hclosed hconvex G regularizer anchor bias η z i : E) - star‖ ^ 2 ≤
      ‖(((z : E) - star) - η • (operator G regularizer z - operator G regularizer star)) -
        η • sampledError G anchor z i‖ ^ 2 := by
    have h := VariationalInequality.projection_nonexpansive S hne hclosed hconvex
      ((z : E) - η • estimator G regularizer anchor bias z i)
      ((star : E) - η • (operator G regularizer star + bias))
    change VariationalInequality.projection S hne hclosed hconvex
      ((star : E) - η • (operator G regularizer star + bias)) = star at hfix
    rw [hfix] at h
    have hid : ((z : E) - η • estimator G regularizer anchor bias z i) -
        ((star : E) - η • (operator G regularizer star + bias)) =
        (((z : E) - star) - η • (operator G regularizer z - operator G regularizer star)) -
          η • sampledError G anchor z i := by
      rw [estimator_decomposition]
      simp only [smul_add, smul_sub]
      abel
    rw [hid] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hi := integral_mono (μ := uniformIndexLaw n) Integrable.of_finite Integrable.of_finite hp
  rw [centered_step_second_moment _ η _ (sampledError_mean_zero G anchor z)] at hi
  exact hi

/-- The elementary squared triangle estimate in the anchor comparison. -/
theorem anchor_distance_sq (z star anchor : E) :
    ‖z - anchor‖ ^ 2 ≤ 2 * ‖z - star‖ ^ 2 + 2 * ‖star - anchor‖ ^ 2 := by
  have h := norm_add_le (z - star) (star - anchor)
  rw [sub_add_sub_cancel] at h
  nlinarith [norm_nonneg (z - anchor), norm_nonneg (z - star), norm_nonneg (star - anchor),
    sq_nonneg (‖z - star‖ - ‖star - anchor‖)]

/-- The source's `11 η² L²` estimate is derived from the actual sampled step. -/
theorem step_raw_descent {G : Fin n → E → E} (regularizer : E → E)
    {L : ℝ} (hL : 0 ≤ L) (hAS : AveragedSmooth G S L)
    (anchor bias : E) (ha : anchor ∈ S) {η : ℝ} (hη : 0 < η) (z star : S)
    (hstar : VariationalInequality.IsSolution S (fun w ↦ operator G regularizer w + bias) star)
    (W Vstar : ℝ)
    (hLip : ‖operator G regularizer z - operator G regularizer star‖ ≤ 3 * L * ‖(z : E) - star‖)
    (hMono : W ≤ ⟪operator G regularizer z - operator G regularizer star, (z : E) - star⟫_ℝ)
    (hanchor : ‖(star : E) - anchor‖ ^ 2 ≤ Vstar) :
    (∫ i, ‖(step S hne hclosed hconvex G regularizer anchor bias η z i : E) - star‖ ^ 2
      ∂uniformIndexLaw n) ≤ ‖(z : E) - star‖ ^ 2 - 2 * η * W +
        11 * η ^ 2 * L ^ 2 * ‖(z : E) - star‖ ^ 2 + 2 * η ^ 2 * L ^ 2 * Vstar := by
  have hs := step_second_moment S hne hclosed hconvex G regularizer anchor bias hη z star hstar
  have hv := sampledError_variance hAS ha z.property
  have ht : ‖operator G regularizer z - operator G regularizer star‖ ^ 2 ≤
      9 * L ^ 2 * ‖(z : E) - star‖ ^ 2 := by
    nlinarith [norm_nonneg (operator G regularizer z - operator G regularizer star),
      norm_nonneg ((z : E) - star)]
  have hdist : ‖(z : E) - anchor‖ ^ 2 ≤ 2 * ‖(z : E) - star‖ ^ 2 + 2 * Vstar := by
    have := anchor_distance_sq (z : E) (star : E) anchor
    linarith
  have hvariance : (∫ i, ‖sampledError G anchor z i‖ ^ 2 ∂uniformIndexLaw n) ≤
      2 * L ^ 2 * ‖(z : E) - star‖ ^ 2 + 2 * L ^ 2 * Vstar := by
    have := mul_le_mul_of_nonneg_left hdist (sq_nonneg L)
    nlinarith
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη] at hs
  have hMono' := hMono
  rw [real_inner_comm] at hMono'
  have hm := mul_le_mul_of_nonneg_left hMono' (by positivity : 0 ≤ 2 * η)
  have hl := mul_le_mul_of_nonneg_left ht (sq_nonneg η)
  have hv' := mul_le_mul_of_nonneg_left hvariance (sq_nonneg η)
  nlinarith

/-- The usable one-step descent, after absorption by the actual coercive energy. -/
theorem step_descent {G : Fin n → E → E} (regularizer : E → E)
    {L μ : ℝ} (hL : 0 ≤ L) (hAS : AveragedSmooth G S L)
    (anchor bias : E) (ha : anchor ∈ S) {η : ℝ} (hη : 0 < η)
    (hsmall : 11 * η * L ^ 2 ≤ μ) (z star : S)
    (hstar : VariationalInequality.IsSolution S (fun w ↦ operator G regularizer w + bias) star)
    (W Vstar : ℝ)
    (hLip : ‖operator G regularizer z - operator G regularizer star‖ ≤ 3 * L * ‖(z : E) - star‖)
    (hMono : W ≤ ⟪operator G regularizer z - operator G regularizer star, (z : E) - star⟫_ℝ)
    (hcoercive : μ * ‖(z : E) - star‖ ^ 2 ≤ W)
    (hanchor : ‖(star : E) - anchor‖ ^ 2 ≤ Vstar) :
    (∫ i, ‖(step S hne hclosed hconvex G regularizer anchor bias η z i : E) - star‖ ^ 2
      ∂uniformIndexLaw n) ≤ ‖(z : E) - star‖ ^ 2 - η * W + 2 * η ^ 2 * L ^ 2 * Vstar := by
  have hs := step_raw_descent S hne hclosed hconvex regularizer hL hAS anchor bias ha hη z star
    hstar W Vstar hLip hMono hanchor
  have hc := mul_le_mul_of_nonneg_left hcoercive hη.le
  have hh := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg hη.le (sq_nonneg ‖(z : E) - star‖))
  nlinarith

end NCConcave16991.InnerAlgorithm



