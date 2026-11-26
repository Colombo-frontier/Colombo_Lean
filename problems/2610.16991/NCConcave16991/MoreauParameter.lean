import NCConcave16991.MoreauEnvelope
import Mathlib.Tactic.FieldSimp

/-!
# Changing the Moreau parameter (Appendix A.4)

Here the coefficient `a` denotes the quadratic coefficient in
`f x + a * ‖x-c‖²`, so the conventional Moreau parameter is `1/(2*a)`.
Strong convexity and all residual comparisons below are derived from the
definition of weak convexity and actual global proximal minimizers. In
particular, no subdifferential hypomonotonicity hypothesis is postulated.
-/

open Set Filter Asymptotics
open scoped InnerProductSpace Topology

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- General quadratic coefficient: the proximal objective has curvature
`2*a-ρ`, directly from the convexity defining `WeaklyConvex ρ f`. -/
theorem weaklyConvex_prox_strong_general {f : E → ℝ} {a ρ : ℝ}
    (hf : WeaklyConvex ρ f) (c : E) :
    StrongConvexOn univ (2 * a - ρ) (proxObjective f a c) := by
  rw [strongConvexOn_iff_convex]
  have ha : ConvexOn ℝ (univ : Set E)
      (fun x ↦ -2 * a * ⟪x, c⟫_ℝ + a * ‖c‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy u v hu hv huv
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
    apply le_of_eq
    rw [show v = 1 - u by linarith]
    ring
  convert hf.add ha using 1
  ext x
  simp only [Pi.add_apply, proxObjective, norm_sub_sq_real]
  ring

theorem proxPoint_unique_general {f : E → ℝ} {a ρ : ℝ} {c p q : E}
    (hμ : 0 < 2 * a - ρ) (hf : WeaklyConvex ρ f)
    (hp : IsProxPoint f a c p) (hq : IsProxPoint f a c q) : p = q := by
  have hg := strongConvex_min_growth (weaklyConvex_prox_strong_general hf c) hp q
  have hh := hq p
  have hz : ‖p - q‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p - q‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Cancellation of a nonnegative norm factor, including the zero case. -/
theorem norm_factor_cancel {μ T d : ℝ} (hd : 0 ≤ d) (hT : 0 ≤ T)
    (h : μ * d ^ 2 ≤ T * d) : μ * d ≤ T := by
  rcases eq_or_lt_of_le hd with hz | hpos
  · rw [← hz]
    simpa using hT
  · apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith

/-- Global minimizer growth yields proximal Lipschitzness for arbitrary
curvature and quadratic coefficient. -/
theorem proxPoint_center_bound_general {f : E → ℝ} {a ρ : ℝ}
    (ha : 0 ≤ a) (hf : WeaklyConvex ρ f) {c d p q : E}
    (hp : IsProxPoint f a c p) (hq : IsProxPoint f a d q) :
    (2 * a - ρ) * ‖p - q‖ ≤ 2 * a * ‖c - d‖ := by
  have h1 := strongConvex_min_growth (weaklyConvex_prox_strong_general hf c) hp q
  have h2 := strongConvex_min_growth (weaklyConvex_prox_strong_general hf d) hq p
  rw [norm_sub_rev q p] at h2
  have hid : ‖q - c‖ ^ 2 + ‖p - d‖ ^ 2 - ‖p - c‖ ^ 2 - ‖q - d‖ ^ 2 =
      2 * ⟪p - q, c - d⟫_ℝ := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    ring
  have hsq : (2 * a - ρ) * ‖p - q‖ ^ 2 ≤
      a * (2 * ⟪p - q, c - d⟫_ℝ) := by
    rw [← hid]
    dsimp [proxObjective] at h1 h2
    linarith
  have hip := mul_le_mul_of_nonneg_left (real_inner_le_norm (p - q) (c - d))
    (show 0 ≤ 2 * a by positivity)
  apply norm_factor_cancel (norm_nonneg _) (show 0 ≤ 2 * a * ‖c - d‖ by positivity)
  nlinarith

theorem proxPoint_lipschitz_general {f : E → ℝ} {a ρ : ℝ}
    (ha : 0 ≤ a) (hμ : 0 < 2 * a - ρ) (hf : WeaklyConvex ρ f) {c d p q : E}
    (hp : IsProxPoint f a c p) (hq : IsProxPoint f a d q) :
    ‖p - q‖ ≤ (2 * a / (2 * a - ρ)) * ‖c - d‖ := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  simpa only [mul_comm] using
    (proxPoint_center_bound_general ha hf hp hq)

/-- Comparing minimizers at the same center but different quadratic
coefficients. This is proved by adding the two strong-growth inequalities. -/
theorem proxPoint_parameter_distance {f : E → ℝ} {a b ρ : ℝ}
    (hba : b ≤ a) (hf : WeaklyConvex ρ f) {c p q : E}
    (hp : IsProxPoint f a c p) (hq : IsProxPoint f b c q) :
    (2 * b - ρ) * ‖p - q‖ ≤ 2 * (a - b) * ‖c - p‖ := by
  have h1 := strongConvex_min_growth (weaklyConvex_prox_strong_general hf c) hp q
  have h2 := strongConvex_min_growth (weaklyConvex_prox_strong_general hf c) hq p
  rw [norm_sub_rev q p] at h2
  have hid : ‖q - c‖ ^ 2 - ‖p - c‖ ^ 2 =
      ‖p - q‖ ^ 2 + 2 * ⟪p - q, c - p⟫_ℝ := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm q p]
    ring
  have hsq : (2 * b - ρ) * ‖p - q‖ ^ 2 ≤
      2 * (a - b) * ⟪p - q, c - p⟫_ℝ := by
    have hid' := congrArg (fun v : ℝ ↦ (a - b) * v) hid
    dsimp [proxObjective] at h1 h2
    nlinarith
  have hip := mul_le_mul_of_nonneg_left (real_inner_le_norm (p - q) (c - p))
    (show 0 ≤ 2 * (a - b) by linarith)
  apply norm_factor_cancel (norm_nonneg _)
    (show 0 ≤ 2 * (a - b) * ‖c - p‖ by positivity)
  nlinarith

/-- General Appendix A.4 residual comparison, with the conventional-parameter
factor written in quadratic coefficients. -/
theorem proxResidual_parameter_comparison {f : E → ℝ} {a b ρ : ℝ}
    (hρ : 0 ≤ ρ) (hba : b ≤ a) (hμ : ρ < 2 * b)
    (hf : WeaklyConvex ρ f) {c p q : E}
    (hp : IsProxPoint f a c p) (hq : IsProxPoint f b c q) :
    ‖proxResidual b c q‖ ≤
      (b * (2 * a - ρ) / (a * (2 * b - ρ))) * ‖proxResidual a c p‖ := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := hb.trans_le hba
  have hκ : 0 < 2 * b - ρ := by linarith
  have hdist := proxPoint_parameter_distance hba hf hp hq
  have htri : ‖c - q‖ ≤ ‖c - p‖ + ‖p - q‖ := by
    have he : (c - p) + (p - q) = c - q := by module
    simpa only [he] using norm_add_le (c - p) (p - q)
  have hscaled : (2 * b - ρ) * ‖c - q‖ ≤ (2 * a - ρ) * ‖c - p‖ := by
    have hmul := mul_le_mul_of_nonneg_left htri hκ.le
    nlinarith
  have hnorm : ‖c - q‖ ≤ ((2 * a - ρ) / (2 * b - ρ)) * ‖c - p‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).mpr
    nlinarith
  have hna : ‖proxResidual a c p‖ = 2 * a * ‖c - p‖ := by
    simp only [proxResidual, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * a by positivity)]
  have hnb : ‖proxResidual b c q‖ = 2 * b * ‖c - q‖ := by
    simp only [proxResidual, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * b by positivity)]
  rw [hnb, hna]
  calc
    2 * b * ‖c - q‖ ≤
        2 * b * (((2 * a - ρ) / (2 * b - ρ)) * ‖c - p‖) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (b * (2 * a - ρ) / (a * (2 * b - ρ))) * (2 * a * ‖c - p‖) := by
      field_simp [ne_of_gt ha, ne_of_gt hκ]

/-- Exact `3/2` transfer required by balanced replication in F.2. -/
theorem proxResidual_parameter_three_halves {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : WeaklyConvex (L / 2) f) {c p q : E}
    (hp : IsProxPoint f L c p) (hq : IsProxPoint f (L / 2) c q) :
    ‖proxResidual (L / 2) c q‖ ≤ (3 / 2 : ℝ) * ‖proxResidual L c p‖ := by
  have hh := proxResidual_parameter_comparison
    (show 0 ≤ L / 2 by positivity) (show L / 2 ≤ L by linarith)
    (show L / 2 < 2 * (L / 2) by linarith) hf hp hq
  have hfactor : (L / 2) * (2 * L - L / 2) / (L * (2 * (L / 2) - L / 2)) =
      (3 / 2 : ℝ) := by
    field_simp [ne_of_gt hL]
    ring
  simpa only [hfactor] using hh

/-- The full quadratic error estimate for the minimized value with arbitrary
weak-convexity modulus below `2*a`. -/
theorem minimizedValue_error_general {f : E → ℝ} {a ρ : ℝ} {P : E → E}
    (ha : 0 < a) (hμ : 0 < 2 * a - ρ) (hf : WeaklyConvex ρ f)
    (hP : ∀ c, IsProxPoint f a c (P c)) (c d : E) :
    |minimizedValue f a P d - minimizedValue f a P c -
      ⟪proxResidual a c (P c), d - c⟫_ℝ| ≤
      (a + 2 * a * (2 * a / (2 * a - ρ))) * ‖d - c‖ ^ 2 := by
  have hu := hP d (P c)
  have hl := hP c (P d)
  have hprox := proxPoint_lipschitz_general ha.le hμ hf (hP d) (hP c)
  have he1 : ‖P c - d‖ ^ 2 - ‖P c - c‖ ^ 2 =
      2 * ⟪c - P c, d - c⟫_ℝ + ‖d - c‖ ^ 2 := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm c d]
    ring
  have he2 : ‖P d - d‖ ^ 2 - ‖P d - c‖ ^ 2 =
      2 * ⟪c - P c, d - c⟫_ℝ + ‖d - c‖ ^ 2 -
        2 * ⟪P d - P c, d - c⟫_ℝ := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm c d]
    ring
  have hip := real_inner_le_norm (P d - P c) (d - c)
  have hip' : ⟪P d - P c, d - c⟫_ℝ ≤
      (2 * a / (2 * a - ρ)) * ‖d - c‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hprox (norm_nonneg (d - c))]
  have hi : ⟪proxResidual a c (P c), d - c⟫_ℝ =
      2 * a * ⟪c - P c, d - c⟫_ℝ := by
    simp [proxResidual, real_inner_smul_left]
  have hK : 0 ≤ 2 * a * (2 * a / (2 * a - ρ)) := by positivity
  apply abs_le.mpr
  dsimp [minimizedValue, proxObjective] at *
  rw [hi]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hip' (show 0 ≤ 2 * a by positivity)
    have he2a := congrArg (fun v : ℝ ↦ a * v) he2
    nlinarith [mul_nonneg ha.le (sq_nonneg ‖d - c‖)]
  · have he1a := congrArg (fun v : ℝ ↦ a * v) he1
    nlinarith [mul_nonneg hK (sq_nonneg ‖d - c‖)]

/-- The residual is the actual gradient of the minimized value, now for every
valid coefficient `a > ρ/2`. -/
theorem minimizedValue_hasGradientAt_general [CompleteSpace E]
    {f : E → ℝ} {a ρ : ℝ} {P : E → E}
    (ha : 0 < a) (hμ : 0 < 2 * a - ρ) (hf : WeaklyConvex ρ f)
    (hP : ∀ c, IsProxPoint f a c (P c)) (c : E) :
    HasGradientAt (minimizedValue f a P) (proxResidual a c (P c)) c := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have ho : (fun h : E ↦ minimizedValue f a P (c + h) - minimizedValue f a P c -
      ⟪proxResidual a c (P c), h⟫_ℝ) =O[𝓝 0] (fun h : E ↦ ‖h‖ ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨a + 2 * a * (2 * a / (2 * a - ρ)), Filter.Eventually.of_forall fun h ↦ ?_⟩
    have hh := minimizedValue_error_general ha hμ hf hP c (c + h)
    simpa only [add_sub_cancel_left, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖h‖)] using hh
  exact ho.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < 2))

/-- This identifies the gradient of the actual infimum-defined envelope. -/
theorem moreauEnvelope_hasGradientAt_general [CompleteSpace E]
    {f : E → ℝ} {a ρ : ℝ} {P : E → E}
    (ha : 0 < a) (hμ : 0 < 2 * a - ρ) (hf : WeaklyConvex ρ f)
    (hP : ∀ c, IsProxPoint f a c (P c)) (c : E) :
    HasGradientAt (moreauEnvelope f a) (proxResidual a c (P c)) c := by
  have he : moreauEnvelope f a = minimizedValue f a P :=
    funext (moreauEnvelope_eq_minimizedValue hP)
  rw [he]
  exact minimizedValue_hasGradientAt_general ha hμ hf hP c

/-- The complete Appendix A.4 comparison for actual envelope gradients, with
proximal minimizers supplied by the proved existence theorem. -/
theorem moreauEnvelope_parameter_gradient_comparison [ProperSpace E] [CompleteSpace E]
    {f : E → ℝ} {a b ρ : ℝ}
    (hρ : 0 ≤ ρ) (hba : b ≤ a) (hμ : ρ < 2 * b)
    (hf : Continuous f) (hbdd : BddBelow (range f)) (hw : WeaklyConvex ρ f) (c : E) :
    ‖gradient (moreauEnvelope f b) c‖ ≤
      (b * (2 * a - ρ) / (a * (2 * b - ρ))) * ‖gradient (moreauEnvelope f a) c‖ := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := hb.trans_le hba
  have hμa : 0 < 2 * a - ρ := by linarith
  have hμb : 0 < 2 * b - ρ := by linarith
  have hPa := proximalMap_spec ha hf hbdd
  have hPb := proximalMap_spec hb hf hbdd
  have hga := moreauEnvelope_hasGradientAt_general ha hμa hw hPa c
  have hgb := moreauEnvelope_hasGradientAt_general hb hμb hw hPb c
  rw [hga.gradient, hgb.gradient]
  exact proxResidual_parameter_comparison hρ hba hμ hw (hPa c) (hPb c)

/-- The exact `3/2` envelope-gradient transfer used in balanced replication. -/
theorem moreauEnvelope_parameter_gradient_three_halves [ProperSpace E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : Continuous f) (hbdd : BddBelow (range f)) (hw : WeaklyConvex (L / 2) f)
    (c : E) :
    ‖gradient (moreauEnvelope f (L / 2)) c‖ ≤
      (3 / 2 : ℝ) * ‖gradient (moreauEnvelope f L) c‖ := by
  have hPa := proximalMap_spec hL hf hbdd
  have hb : 0 < L / 2 := by positivity
  have hPb := proximalMap_spec hb hf hbdd
  have hga := moreauEnvelope_hasGradientAt_general hL
    (show 0 < 2 * L - L / 2 by linarith) hw hPa c
  have hgb := moreauEnvelope_hasGradientAt_general hb
    (show 0 < 2 * (L / 2) - L / 2 by linarith) hw hPb c
  rw [hga.gradient, hgb.gradient]
  exact proxResidual_parameter_three_halves hL hw (hPa c) (hPb c)

end NCConcave16991
