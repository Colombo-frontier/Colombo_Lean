import HeavyTail.AdaptiveErasure
import HeavyTail.HardFamily

/-!
# Actual confidence hard instances and adaptive objective-error events

A fixed unit direction embeds the binary absolute-value family in every
positive finite dimension. Replies are genuine vector-valued importance-weighted
erasure samples. The policy and its arbitrary seed are independent of the hidden
hypothesis; the objective lower event follows from actual recursive execution.
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace HeavyTail
noncomputable section

def confidenceSign (h : Bool) : ℝ := if h then 1 else -1

lemma confidenceSign_cases (h : Bool) : confidenceSign h = -1 ∨ confidenceSign h = 1 := by
  cases h <;> simp [confidenceSign]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def vectorErasureReply (u : ℝ) (g : E) (b : Bool) : E :=
  if b then 0 else (1 - u)⁻¹ • g

theorem erasure_vector_expectation [CompleteSpace E] {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (f : Bool → E) :
    (∫ b, f b ∂(erasureCoin u hu1).toMeasure) = u • f true + (1 - u) • f false := by
  rw [PMF.integral_eq_sum]
  simp only [erasureCoin, PMF.bernoulli_apply, Fintype.sum_bool, Bool.cond_false,
    Bool.cond_true]
  rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr hu1) (by simp),
    ENNReal.toReal_one, ENNReal.toReal_ofReal hu0]

theorem vectorErasureReply_unbiased [CompleteSpace E] {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (g : E) :
    (∫ b, vectorErasureReply u g b ∂(erasureCoin u hu1.le).toMeasure) = g := by
  rw [erasure_vector_expectation hu0]
  simp [vectorErasureReply, smul_smul, ne_of_gt (sub_pos.mpr hu1)]

theorem vectorErasureReply_centered_norm (u : ℝ) (g : E) (b : Bool) :
    ‖vectorErasureReply u g b - g‖ = |erasureReply u ‖g‖ b - ‖g‖| := by
  cases b
  · simp only [vectorErasureReply, erasureReply, Bool.false_eq_true, if_false]
    have hv : (1 - u)⁻¹ • g - g = ((1 - u)⁻¹ - 1) • g := by
      rw [sub_smul, one_smul]
    rw [hv, norm_smul, Real.norm_eq_abs]
    have hr : ‖g‖ / (1 - u) - ‖g‖ = ((1 - u)⁻¹ - 1) * ‖g‖ := by ring
    rw [hr, abs_mul, abs_of_nonneg (norm_nonneg g)]
  · simp [vectorErasureReply, erasureReply]

theorem vectorErasureReply_centered_moment {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (g : E) (p : ℝ) :
    (∫ b, ‖vectorErasureReply u g b - g‖ ^ p ∂(erasureCoin u hu1.le).toMeasure) =
      ‖g‖ ^ p * (u + u ^ p / (1 - u) ^ (p - 1)) := by
  simp_rw [vectorErasureReply_centered_norm]
  simpa only [abs_of_nonneg (norm_nonneg g)] using
    erasure_centered_moment hu0 hu1 ‖g‖ p

def confidenceLoss (e : E) (a ρ : ℝ) (h : Bool) (x : E) : ℝ :=
  a * |⟪e, x⟫_ℝ - ρ * confidenceSign h|

def confidenceRegularizer (μ : ℝ) (x : E) : ℝ := μ / 2 * ‖x‖ ^ 2

def confidenceObjective (e : E) (a μ ρ : ℝ) (h : Bool) (x : E) : ℝ :=
  confidenceLoss e a ρ h x + confidenceRegularizer μ x

def confidenceCenter (e : E) (ρ : ℝ) (h : Bool) : E := (ρ * confidenceSign h) • e

def confidenceMean (e : E) (a ρ : ℝ) (h : Bool) (x : E) : E :=
  (a * Real.sign (⟪e, x⟫_ℝ - ρ * confidenceSign h)) • e

def confidenceOracle (e : E) (a ρ u : ℝ) (h : Bool) (x : E) (b : Bool) : E :=
  vectorErasureReply u (confidenceMean e a ρ h x) b

/-- Zero is decoded as the negative hidden sign, as in the manuscript. -/
def confidenceDecode (e : E) (x : E) : Bool := if ⟪e, x⟫_ℝ ≤ 0 then false else true

lemma confidence_projection_abs_le (e x : E) (he : ‖e‖ = 1) : |⟪e, x⟫_ℝ| ≤ ‖x‖ := by
  simpa only [he, one_mul] using abs_real_inner_le_norm e x

lemma confidence_projection_sq_le (e x : E) (he : ‖e‖ = 1) : ⟪e, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := confidence_projection_abs_le e x he
  nlinarith [sq_abs ⟪e, x⟫_ℝ, abs_nonneg ⟪e, x⟫_ℝ, norm_nonneg x]

theorem confidenceMean_norm_le (e : E) (he : ‖e‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (h : Bool) (x : E) : ‖confidenceMean e a ρ h x‖ ≤ a := by
  unfold confidenceMean
  rw [norm_smul, he, mul_one, Real.norm_eq_abs]
  rcases Real.sign_apply_eq (⟪e, x⟫_ℝ - ρ * confidenceSign h) with hh | hh | hh
  · rw [hh]; simp [abs_of_nonneg ha]
  · rw [hh]; simpa using ha
  · rw [hh]; simp [abs_of_nonneg ha]

theorem confidenceMean_subgradient (e : E) {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (h : Bool) (x y : E) :
    confidenceLoss e a ρ h x - confidenceLoss e a ρ h y ≤
      ⟪confidenceMean e a ρ h x, x - y⟫_ℝ := by
  have hb := mul_le_mul_of_nonneg_left
    (scalar_abs_subgradient ⟪e, x⟫_ℝ ⟪e, y⟫_ℝ (ρ * confidenceSign h)) ha
  simpa [confidenceLoss, confidenceMean, real_inner_smul_left, inner_sub_right,
    mul_sub, mul_assoc] using hb

theorem confidenceLoss_lipschitz (e : E) (he : ‖e‖ = 1) {a : ℝ} (ha : 0 ≤ a)
    (ρ : ℝ) (h : Bool) : LipschitzWith ⟨a, ha⟩ (confidenceLoss e a ρ h) := by
  have hdiff (x y : E) : confidenceLoss e a ρ h x - confidenceLoss e a ρ h y ≤ a * ‖x - y‖ := by
    calc
      _ ≤ ⟪confidenceMean e a ρ h x, x - y⟫_ℝ := confidenceMean_subgradient e ha ρ h x y
      _ ≤ ‖confidenceMean e a ρ h x‖ * ‖x - y‖ := real_inner_le_norm _ _
      _ ≤ a * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (confidenceMean_norm_le e he ha ρ h x) (norm_nonneg _)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  change |confidenceLoss e a ρ h x - confidenceLoss e a ρ h y| ≤ a * ‖x - y‖
  apply abs_le.mpr
  refine ⟨?_, hdiff x y⟩
  have hrev := hdiff y x
  rw [norm_sub_rev] at hrev
  linarith

theorem confidenceLoss_convex (e : E) {a : ℝ} (ha : 0 ≤ a) (ρ : ℝ) (h : Bool) :
    ConvexOn ℝ Set.univ (confidenceLoss e a ρ h) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy α β hα hβ hsum
  let z := α • x + β • y
  have hvec : α • (z - x) + β • (z - y) = 0 := by
    have hβ' : β = 1 - α := by linarith
    dsimp [z]
    rw [hβ']
    module
  have hi : α * ⟪confidenceMean e a ρ h z, z - x⟫_ℝ +
      β * ⟪confidenceMean e a ρ h z, z - y⟫_ℝ = 0 := by
    calc
      _ = ⟪confidenceMean e a ρ h z, α • (z - x) + β • (z - y)⟫_ℝ := by
        simp [inner_add_right, inner_smul_right]
      _ = 0 := by rw [hvec]; simp
  have hx' := mul_le_mul_of_nonneg_left (confidenceMean_subgradient e ha ρ h z x) hα
  have hy' := mul_le_mul_of_nonneg_left (confidenceMean_subgradient e ha ρ h z y) hβ
  have hzsum : α * confidenceLoss e a ρ h z + β * confidenceLoss e a ρ h z =
      confidenceLoss e a ρ h z := by rw [← add_mul, hsum, one_mul]
  change confidenceLoss e a ρ h z ≤ α * confidenceLoss e a ρ h x + β * confidenceLoss e a ρ h y
  linarith only [hx', hy', hi, hzsum]

theorem confidenceRegularizer_strongConvex (μ : ℝ) :
    StrongConvexOn (Set.univ : Set E) μ (confidenceRegularizer μ) := by
  rw [strongConvexOn_iff_convex]
  simpa only [confidenceRegularizer, sub_self] using
    (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))

lemma confidenceCenter_projection (e : E) (he : ‖e‖ = 1) (ρ : ℝ) (h : Bool) :
    ⟪e, confidenceCenter e ρ h⟫_ℝ = ρ * confidenceSign h := by
  simp [confidenceCenter, inner_smul_right, real_inner_self_eq_norm_sq, he]

lemma confidenceCenter_norm_sq (e : E) (he : ‖e‖ = 1) (ρ : ℝ) (h : Bool) :
    ‖confidenceCenter e ρ h‖ ^ 2 = ρ ^ 2 := by
  cases h <;> simp [confidenceCenter, confidenceSign, norm_smul, he, Real.norm_eq_abs, sq_abs]

theorem confidenceObjective_center (e : E) (he : ‖e‖ = 1)
    (a μ ρ : ℝ) (h : Bool) :
    confidenceObjective e a μ ρ h (confidenceCenter e ρ h) = μ / 2 * ρ ^ 2 := by
  simp [confidenceObjective, confidenceLoss, confidenceRegularizer,
    confidenceCenter_projection e he, confidenceCenter_norm_sq e he]

lemma confidenceObjective_scalar_le (e : E) (he : ‖e‖ = 1)
    (a μ ρ : ℝ) (hμ : 0 ≤ μ) (h : Bool) (x : E) :
    coordinateSignLoss a μ ρ (confidenceSign h) ⟪e, x⟫_ℝ ≤
      confidenceObjective e a μ ρ h x := by
  have hnorm := mul_le_mul_of_nonneg_left (confidence_projection_sq_le e x he)
    (show 0 ≤ μ / 2 by positivity)
  unfold coordinateSignLoss confidenceObjective confidenceLoss confidenceRegularizer
  linarith

theorem confidenceObjective_minimizer (e : E) (he : ‖e‖ = 1)
    {a μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hcurv : μ * ρ ≤ a)
    (h : Bool) (x : E) :
    confidenceObjective e a μ ρ h (confidenceCenter e ρ h) ≤
      confidenceObjective e a μ ρ h x := by
  rw [confidenceObjective_center e he]
  have hs := coordinateSignLoss_minimizer hμ hρ hcurv (confidenceSign_cases h) ⟪e, x⟫_ℝ
  rw [coordinateSignLoss_at_center a μ ρ _ (confidenceSign_cases h)] at hs
  exact hs.trans (confidenceObjective_scalar_le e he a μ ρ hμ h x)

theorem confidenceCenter_initialization (e : E) (he : ‖e‖ = 1)
    {a μ D : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a) (h : Bool) :
    ‖confidenceCenter e (envelopeRadius μ D a) h‖ ≤ D := by
  have hs := confidenceCenter_norm_sq e he (envelopeRadius μ D a) h
  have hr := envelopeRadius_nonneg hμ hD ha
  have hrD := envelopeRadius_le (μ := μ) (D := D) (a := a)
  nlinarith [norm_nonneg (confidenceCenter e (envelopeRadius μ D a) h)]

lemma confidenceDecode_wrong (e x : E) (h : Bool)
    (hwrong : confidenceDecode e x ≠ h) : ⟪e, x⟫_ℝ * confidenceSign h ≤ 0 := by
  cases h <;> unfold confidenceDecode confidenceSign at *
  · split_ifs at hwrong with hx
    · exact (hwrong rfl).elim
    · simp only [Bool.false_eq_true, if_false, mul_neg_one]
      linarith
  · split_ifs at hwrong with hx
    · simpa using hx
    · exact (hwrong rfl).elim

theorem confidence_wrong_objective_gap (e : E) (he : ‖e‖ = 1)
    {a μ D : ℝ} (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (h : Bool) (x : E) (hwrong : confidenceDecode e x ≠ h) :
    envelope μ D a ≤
      confidenceObjective e a μ (envelopeRadius μ D a) h x -
      confidenceObjective e a μ (envelopeRadius μ D a) h
        (confidenceCenter e (envelopeRadius μ D a) h) := by
  have hs := coordinateSignLoss_wrong_halfline ha hμ (envelopeRadius_nonneg hμ hD ha)
    (confidenceSign_cases h) (confidenceDecode_wrong e x h hwrong)
  rw [coordinateSignLoss_at_center a μ _ _ (confidenceSign_cases h)] at hs
  have hobj := confidenceObjective_scalar_le e he a μ (envelopeRadius μ D a) hμ h x
  rw [confidenceObjective_center e he]
  change a * envelopeRadius μ D a - μ / 2 * (envelopeRadius μ D a) ^ 2 ≤ _
  linarith

section Measurable
variable [MeasurableSpace E] [BorelSpace E]

theorem confidenceMean_measurable (e : E) (a ρ : ℝ) (h : Bool) :
    Measurable (confidenceMean e a ρ h) := by
  unfold confidenceMean
  exact ((real_sign_measurable.comp ((continuous_const.inner continuous_id).measurable.sub_const
    (ρ * confidenceSign h))).const_mul a).smul_const e

theorem confidenceOracle_measurable (e : E) (a ρ u : ℝ) (h : Bool) :
    Measurable (fun z : E × Bool ↦ confidenceOracle e a ρ u h z.1 z.2) := by
  unfold confidenceOracle vectorErasureReply
  exact Measurable.ite (measurable_snd (MeasurableSet.singleton true)) measurable_const
    (((confidenceMean_measurable e a ρ h).comp measurable_fst).const_smul _)

theorem confidenceDecode_measurable (e : E) : Measurable (confidenceDecode e) := by
  unfold confidenceDecode
  have hm : Measurable (fun x : E ↦ ⟪e, x⟫_ℝ) :=
    (continuous_const.inner continuous_id).measurable
  exact Measurable.ite (hm measurableSet_Iic)
    measurable_const measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
theorem confidenceObjective_continuous (e : E) (a μ ρ : ℝ) (h : Bool) :
    Continuous (confidenceObjective e a μ ρ h) := by
  unfold confidenceObjective confidenceLoss confidenceRegularizer
  fun_prop

/-- A fixed hard hypothesis defeats every measurable adaptive randomized policy. -/
theorem confidence_objective_probability_lower
    {S : Type*} [MeasurableSpace S] {T : ℕ}
    (A : AdaptivePolicy S E E E T) (P : Measure S) [IsProbabilityMeasure P]
    (e : E) (he : ‖e‖ = 1) {a μ D u : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ h : Bool,
      MeasurableSet {ω | envelope μ D a ≤
        confidenceObjective e a μ (envelopeRadius μ D a) h
          (A.execute (confidenceOracle e a (envelopeRadius μ D a) u) h ω) -
        confidenceObjective e a μ (envelopeRadius μ D a) h
          (confidenceCenter e (envelopeRadius μ D a) h)} ∧
      u ^ T / 2 ≤ (P.prod (erasureSequenceLaw u hu1.le T)).real
        {ω | envelope μ D a ≤
          confidenceObjective e a μ (envelopeRadius μ D a) h
            (A.execute (confidenceOracle e a (envelopeRadius μ D a) u) h ω) -
          confidenceObjective e a μ (envelopeRadius μ D a) h
            (confidenceCenter e (envelopeRadius μ D a) h)} := by
  let O := confidenceOracle e a (envelopeRadius μ D a) u
  have hO0 : ∀ h x, O h x true = 0 := by simp [O, confidenceOracle, vectorErasureReply]
  have hOm : ∀ h, Measurable (fun z : E × Bool ↦ O h z.1 z.2) :=
    confidenceOracle_measurable e a (envelopeRadius μ D a) u
  obtain ⟨h, _, htest⟩ := adaptive_erasure_testing_lower A O hO0 hOm
    P (confidenceDecode e) (confidenceDecode_measurable e) hu0 hu1.le
  refine ⟨h, ?_, htest.trans (measureReal_mono ?_)⟩
  · exact (((confidenceObjective_continuous e a μ (envelopeRadius μ D a) h).measurable.comp
      (A.execute_measurable O hOm h)).sub_const _) measurableSet_Ici
  · intro ω hω
    exact confidence_wrong_objective_gap e he hμ hD ha h (A.execute O h ω) hω

end Measurable

theorem confidenceOracle_unbiased [CompleteSpace E] (e : E) (a ρ : ℝ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (h : Bool) (x : E) :
    (∫ b, confidenceOracle e a ρ u h x b ∂(erasureCoin u hu1.le).toMeasure) =
      confidenceMean e a ρ h x :=
  vectorErasureReply_unbiased hu0 hu1 _

theorem confidenceOracle_centered_moment_bound (e : E) (he : ‖e‖ = 1)
    {a ρ u p s : ℝ} (ha : 0 ≤ a) (hu0 : 0 < u) (hu1 : u < 1) (hp : 0 ≤ p)
    (hbudget : a ^ p * (u + u ^ p / (1 - u) ^ (p - 1)) ≤ s ^ p)
    (h : Bool) (x : E) :
    (∫ b, ‖confidenceOracle e a ρ u h x b - confidenceMean e a ρ h x‖ ^ p
      ∂(erasureCoin u hu1.le).toMeasure) ≤ s ^ p := by
  change (∫ b, ‖vectorErasureReply u (confidenceMean e a ρ h x) b - confidenceMean e a ρ h x‖ ^ p
    ∂(erasureCoin u hu1.le).toMeasure) ≤ s ^ p
  rw [vectorErasureReply_centered_moment hu0 hu1]
  have hpow := Real.rpow_le_rpow (norm_nonneg _) (confidenceMean_norm_le e he ha ρ h x) hp
  have hq : 0 < 1 - u := sub_pos.mpr hu1
  exact (mul_le_mul_of_nonneg_right hpow (by positivity)).trans hbudget

theorem confidenceOracle_two_moment_admissible (e : E) (he : ‖e‖ = 1)
    {a ρ u p s L : ℝ} (ha : 0 ≤ a) (hu0 : 0 < u) (hu1 : u < 1) (hp : 0 ≤ p)
    (hs : 0 ≤ s) (hsL : s ≤ L)
    (hbudget : a ^ p * (u + u ^ p / (1 - u) ^ (p - 1)) ≤ s ^ p)
    (h : Bool) (x : E) :
    (∫ b, ‖confidenceOracle e a ρ u h x b - confidenceMean e a ρ h x‖ ^ p
      ∂(erasureCoin u hu1.le).toMeasure) ≤ L ^ p ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ b, |⟪v, confidenceOracle e a ρ u h x b - confidenceMean e a ρ h x⟫_ℝ| ^ p
        ∂(erasureCoin u hu1.le).toMeasure) ≤ s ^ p := by
  have hm := confidenceOracle_centered_moment_bound (ρ := ρ) e he ha hu0 hu1 hp hbudget h x
  refine ⟨hm.trans (Real.rpow_le_rpow hs hsL hp), ?_⟩
  intro v hv
  apply le_trans _ hm
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  apply Finset.sum_le_sum
  intro b hb
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply Real.rpow_le_rpow (abs_nonneg _) _ hp
  simpa only [hv, one_mul] using abs_real_inner_le_norm v
    (confidenceOracle e a ρ u h x b - confidenceMean e a ρ h x)

/-- Every positive Euclidean dimension admits the direction used above. -/
theorem confidence_unit_direction_exists {d : ℕ} (hd : 0 < d) :
    ∃ e : HardSpace d, ‖e‖ = 1 := by
  refine ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), ?_⟩
  simp

end
end HeavyTail
