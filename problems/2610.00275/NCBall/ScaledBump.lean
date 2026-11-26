import NCBall.RadialBump
import NCBall.LocalityBounds

/-! # Translation and scaling of the actual localized perturbations -/

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology ContDiff InnerProductSpace BigOperators NNReal
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scaledBump (a ρ : ℝ) (c v x : E) : ℝ :=
  a * ρ * radialLinearBump v (ρ⁻¹ • (x - c))

def scaledBumpGradient (a ρ : ℝ) (c v x : E) : E :=
  a • radialBumpGradient v (ρ⁻¹ • (x - c))

omit [CompleteSpace E] in
theorem scaledBump_smooth (a ρ : ℝ) (c v : E) : ContDiff ℝ ∞ (scaledBump a ρ c v) :=
  contDiff_const.mul ((radialLinearBump_smooth v).comp
    (contDiff_const.smul (contDiff_id.sub contDiff_const)))

omit [CompleteSpace E] in
theorem scaledBumpGradient_smooth (a ρ : ℝ) (c v : E) :
    ContDiff ℝ ∞ (scaledBumpGradient a ρ c v) :=
  contDiff_const.smul ((radialBumpGradient_smooth v).comp
    (contDiff_const.smul (contDiff_id.sub contDiff_const)))

theorem scaledBump_hasGradientAt (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c v x : E) :
    HasGradientAt (scaledBump a ρ c v) (scaledBumpGradient a ρ c v x) x := by
  have hs : HasFDerivAt (fun y : E => ρ⁻¹ • (y - c))
      (ρ⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul ρ⁻¹
  have h := ((radialLinearBump_hasGradientAt v (ρ⁻¹ • (x - c))).hasFDerivAt.comp x hs).const_mul (a * ρ)
  change HasFDerivAt (scaledBump a ρ c v) (toDual ℝ E (scaledBumpGradient a ρ c v x)) x
  convert h using 1
  ext y
  simp [scaledBumpGradient, ContinuousLinearMap.comp_apply, inner_smul_left, inner_smul_right]
  field_simp
  ring

theorem scaledBump_gradient (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c v x : E) :
    gradient (scaledBump a ρ c v) x = scaledBumpGradient a ρ c v x :=
  (scaledBump_hasGradientAt a hρ c v x).gradient

omit [CompleteSpace E] in
theorem scaledBumpGradient_bound {a ρ : ℝ} (ha : 0 ≤ a) (c v x : E) :
    ‖scaledBumpGradient a ρ c v x‖ ≤ a * (3 * radialProfileBound * ‖v‖) := by
  rw [scaledBumpGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (radialBumpGradient_bound v _) ha

omit [CompleteSpace E] in
theorem scaledBumpGradient_norm_sub {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (c v x y : E) :
    ‖scaledBumpGradient a ρ c v x - scaledBumpGradient a ρ c v y‖ ≤
      (a / ρ * (10 * radialProfileBound * ‖v‖)) * ‖x - y‖ := by
  have hdiff : ρ⁻¹ • (x - c) - ρ⁻¹ • (y - c) = ρ⁻¹ • (x - y) := by
    rw [← smul_sub]
    congr 1
    abel
  have hb := (radialBumpGradient_lipschitz v).dist_le_mul (ρ⁻¹ • (x - c)) (ρ⁻¹ • (y - c))
  simp only [dist_eq_norm, NNReal.coe_mk, hdiff] at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)] at hb
  simp only [scaledBumpGradient, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have h := mul_le_mul_of_nonneg_left hb ha
  convert h using 1
  ring

omit [CompleteSpace E] in
theorem scaledBumpGradient_lipschitz {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (c v : E) :
    LipschitzWith ⟨a / ρ * (10 * radialProfileBound * ‖v‖), by
      have := radialProfileBound_ge_one
      positivity⟩ (scaledBumpGradient a ρ c v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mk] using scaledBumpGradient_norm_sub ha hρ c v x y

omit [CompleteSpace E] in
theorem scaledBumpGradient_fderiv_bound {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (c v x : E) :
    ‖fderiv ℝ (scaledBumpGradient a ρ c v) x‖ ≤ a / ρ * (10 * radialProfileBound * ‖v‖) :=
  norm_fderiv_le_of_lipschitz ℝ (scaledBumpGradient_lipschitz ha hρ c v)

theorem scaledBump_fderiv_bound {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ) (c v x : E) :
    ‖fderiv ℝ (scaledBump a ρ c v) x‖ ≤ a * (3 * radialProfileBound * ‖v‖) := by
  rw [(scaledBump_hasGradientAt a hρ c v x).hasFDerivAt.fderiv, (toDual ℝ E).norm_map]
  exact scaledBumpGradient_bound ha c v x

omit [CompleteSpace E] in
theorem scaledBumpGradient_zero_off (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c v x : E)
    (hx : x ∉ closedBall c ρ) : scaledBumpGradient a ρ c v x = 0 := by
  have hd : ρ < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
  have hs : 1 < ‖ρ⁻¹ • (x - c)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), ← div_eq_inv_mul]
    exact (one_lt_div hρ).2 hd
  simp [scaledBumpGradient, radialBumpGradient_zero v _ hs]

omit [CompleteSpace E] in
theorem scaledBump_zero_off (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c v x : E)
    (hx : x ∉ closedBall c ρ) : scaledBump a ρ c v x = 0 := by
  have hd : ρ < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
  have hs : 1 ≤ ‖ρ⁻¹ • (x - c)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ), ← div_eq_inv_mul]
    exact ((one_lt_div hρ).2 hd).le
  simp [scaledBump, radialLinearBump, radialCutoff_zero hs]

omit [CompleteSpace E] in
theorem scaledBumpGradient_bound_C {a ρ : ℝ} (ha : 0 ≤ a) (c v x : E) :
    ‖scaledBumpGradient a ρ c v x‖ ≤ a * bumpConstant * ‖v‖ := by
  have h := scaledBumpGradient_bound (ρ := ρ) ha c v x
  have hA := radialProfileBound_ge_one
  have hmul := mul_nonneg ha (norm_nonneg v)
  unfold bumpConstant
  nlinarith [mul_nonneg (by linarith : 0 ≤ radialProfileBound) hmul]

theorem hasGradientAt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (g : ι → E) (x : E) (h : ∀ i ∈ s, HasGradientAt (f i) (g i) x) :
    HasGradientAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, g i) x := by
  change HasFDerivAt _ (toDual ℝ E (∑ i ∈ s, g i)) x
  simpa using HasFDerivAt.sum (fun i hi => (h i hi).hasFDerivAt)

theorem hasGradientAt_add (f g : E → ℝ) (u v x : E)
    (hf : HasGradientAt f u x) (hg : HasGradientAt g v x) :
    HasGradientAt (fun y => f y + g y) (u + v) x := by
  change HasFDerivAt _ (toDual ℝ E (u + v)) x
  simpa using hf.hasFDerivAt.add hg.hasFDerivAt

end NCBall
