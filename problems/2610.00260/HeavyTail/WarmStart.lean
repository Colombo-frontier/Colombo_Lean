import HeavyTail.ZeroQuery

/-! A public finite proximal warm start gives the exact radius in eq:warm. -/
noncomputable section
open Set
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def warmStartPoint {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    (μ D G : ℝ) (x₁ : E) : E :=
  if μ * D ≤ G then x₁ else P.point (zeroQueryStep μ D G) x₁

def warmStartRadius (μ D G : ℝ) : ℝ :=
  if μ * D ≤ G then D else Real.sqrt 2 * G / μ

theorem finite_proximal_warm_start {S : Set E} {f h : E → ℝ} {μ D G : ℝ}
    (P : ProximalOracle S h) (hf : ConvexOn ℝ S f) (hh : StrongConvexOn S μ h)
    (hμ : 0 < μ) (hD : 0 < D) (hG : 0 < G)
    (x₁ xstar : E) (hx₁ : x₁ ∈ S) (hx : xstar ∈ S) (hinit : ‖x₁ - xstar‖ ≤ D)
    (hmin : ∀ u ∈ S, f xstar + h xstar ≤ f u + h u)
    (hlip : ∀ u ∈ S, f u - f xstar ≤ G * ‖u - xstar‖) :
    warmStartPoint P μ D G x₁ ∈ S ∧
    ‖warmStartPoint P μ D G x₁ - xstar‖ ≤ warmStartRadius μ D G ∧
    warmStartRadius μ D G ≤ Real.sqrt 2 * G / μ := by
  by_cases hcase : μ * D ≤ G
  · simp only [warmStartPoint, warmStartRadius, if_pos hcase]
    refine ⟨hx₁, hinit, ?_⟩
    have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hmul := mul_le_mul_of_nonneg_right hroot hG.le
    apply (le_div_iff₀ hμ).mpr
    nlinarith only [hcase, hmul]
  · simp only [warmStartPoint, warmStartRadius, if_neg hcase]
    have hη := zeroQueryStep_pos hμ.le hD hG
    have hy := P.feasible (zeroQueryStep μ D G) hη x₁
    refine ⟨hy, ?_, le_rfl⟩
    have he := (zero_query_envelope_cap P hh hμ.le hD hG x₁ xstar hx hinit hlip).2
    rw [envelope_quadratic hμ (le_of_not_ge hcase)] at he
    have hrid : μ / 2 * (Real.sqrt 2 * G / μ) ^ 2 = 2 * (G ^ 2 / (2 * μ)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      ring
    apply radius_of_objective_error hμ (by positivity) (composite_strongConvexOn hf hh) hx hy hmin
    rw [hrid]
    exact he

/-- The radius certificate does not require the supplied initial point to lie
in the effective domain of the regularizer. -/
theorem finite_proximal_warm_start_radius {S : Set E} {f h : E → ℝ} {μ D G : ℝ}
    (P : ProximalOracle S h) (hf : ConvexOn ℝ S f) (hh : StrongConvexOn S μ h)
    (hμ : 0 < μ) (hD : 0 < D) (hG : 0 < G)
    (x₁ xstar : E) (hx : xstar ∈ S) (hinit : ‖x₁ - xstar‖ ≤ D)
    (hmin : ∀ u ∈ S, f xstar + h xstar ≤ f u + h u)
    (hlip : ∀ u ∈ S, f u - f xstar ≤ G * ‖u - xstar‖) :
    ‖warmStartPoint P μ D G x₁ - xstar‖ ≤ warmStartRadius μ D G ∧
    warmStartRadius μ D G ≤ Real.sqrt 2 * G / μ := by
  by_cases hcase : μ * D ≤ G
  · simp only [warmStartPoint, warmStartRadius, if_pos hcase]
    refine ⟨hinit, ?_⟩
    have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hmul := mul_le_mul_of_nonneg_right hroot hG.le
    apply (le_div_iff₀ hμ).mpr
    nlinarith only [hcase, hmul]
  · simp only [warmStartPoint, warmStartRadius, if_neg hcase]
    refine ⟨?_, le_rfl⟩
    have hy := P.feasible (zeroQueryStep μ D G) (zeroQueryStep_pos hμ.le hD hG) x₁
    have he := (zero_query_envelope_cap P hh hμ.le hD hG x₁ xstar hx hinit hlip).2
    rw [envelope_quadratic hμ (le_of_not_ge hcase)] at he
    have hrid : μ / 2 * (Real.sqrt 2 * G / μ) ^ 2 = 2 * (G ^ 2 / (2 * μ)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      ring
    apply radius_of_objective_error hμ (by positivity) (composite_strongConvexOn hf hh) hx hy hmin
    rw [hrid]
    exact he

theorem warmStartPoint_feasible {S X : Set E} {h : E → ℝ} {μ D G : ℝ}
    (P : ProximalOracle S h) (hSX : S ⊆ X) (hμ : 0 ≤ μ) (hD : 0 < D) (hG : 0 < G)
    (x₁ : E) (hx₁ : x₁ ∈ X) : warmStartPoint P μ D G x₁ ∈ X := by
  unfold warmStartPoint
  split_ifs
  · exact hx₁
  · exact hSX (P.feasible _ (zeroQueryStep_pos hμ hD hG) x₁)

end HeavyTail
