import HeavyTail.ProximalOracle

/-! Actual finite proximal evaluations realize the zero-query envelope cap.
The proximal inequalities are derived from the public minimization contract. -/
noncomputable section
open Set
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def zeroQueryStep (μ D G : ℝ) : ℝ :=
  if μ * D ≤ G then D / G else μ * D ^ 2 / G ^ 2

theorem zeroQueryStep_pos {μ D G : ℝ} (hμ : 0 ≤ μ) (hD : 0 < D) (hG : 0 < G) :
    0 < zeroQueryStep μ D G := by
  unfold zeroQueryStep
  split_ifs with hcase
  · positivity
  · have hμpos : 0 < μ := by
      by_contra hn
      have : μ = 0 := le_antisymm (le_of_not_gt hn) hμ
      simp [this, hG.le] at hcase
    positivity

theorem proximal_zero_query_realized {S : Set E} {f h : E → ℝ} {μ D G η : ℝ}
    (P : ProximalOracle S h) (hh : StrongConvexOn S μ h)
    (hμ : 0 ≤ μ) (hη : 0 < η) (x₁ xstar : E) (hx : xstar ∈ S)
    (hinit : ‖x₁ - xstar‖ ≤ D)
    (hlip : ∀ u ∈ S, f u - f xstar ≤ G * ‖u - xstar‖) :
    (f (P.point η x₁) + h (P.point η x₁)) - (f xstar + h xstar) ≤
      D ^ 2 / (2 * η) + G ^ 2 / (2 * (μ + η⁻¹)) := by
  apply proximal_zero_query_bound hη hμ hinit (hlip _ (P.feasible η hη x₁))
  simpa only [norm_sub_rev xstar (P.point η x₁), norm_sub_rev xstar x₁] using
    proximalOracle_growth P hh hμ hη x₁ xstar hx

theorem zeroQuery_arithmetic_cap {μ D G : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 < D) (hG : 0 < G) :
    D ^ 2 / (2 * zeroQueryStep μ D G) +
      G ^ 2 / (2 * (μ + (zeroQueryStep μ D G)⁻¹)) ≤ 2 * envelope μ D G := by
  by_cases hcase : μ * D ≤ G
  · rw [zeroQueryStep, if_pos hcase]
    have hbase : G ^ 2 / (2 * (μ + (D / G)⁻¹)) ≤ G ^ 2 / (2 * (D / G)⁻¹) := by
      apply div_le_div_of_nonneg_left (sq_nonneg G) (by positivity)
      linarith
    have he : D ^ 2 / (2 * (D / G)) + G ^ 2 / (2 * (D / G)⁻¹) = D * G := by
      field_simp
      ring
    have hDG : D * G ≤ 2 * envelope μ D G := by
      by_cases hμ0 : μ = 0
      · rw [hμ0, envelope_zero_curvature]
        nlinarith only [mul_pos hD hG]
      · rw [envelope_linear (lt_of_le_of_ne hμ (Ne.symm hμ0)) hcase]
        have hmul := mul_le_mul_of_nonneg_right hcase hD.le
        nlinarith only [hmul]
    calc
      _ ≤ D ^ 2 / (2 * (D / G)) + G ^ 2 / (2 * (D / G)⁻¹) := add_le_add_left hbase _
      _ = D * G := he
      _ ≤ _ := hDG
  · have hμpos : 0 < μ := by
      by_contra hn
      have : μ = 0 := le_antisymm (le_of_not_gt hn) hμ
      simp [this, hG.le] at hcase
    rw [zeroQueryStep, if_neg hcase]
    have hbase : G ^ 2 / (2 * (μ + (μ * D ^ 2 / G ^ 2)⁻¹)) ≤ G ^ 2 / (2 * μ) := by
      apply div_le_div_of_nonneg_left (sq_nonneg G) (by positivity)
      have hη : 0 < μ * D ^ 2 / G ^ 2 := by positivity
      have hi := (inv_pos.mpr hη).le
      linarith
    have he : D ^ 2 / (2 * (μ * D ^ 2 / G ^ 2)) + G ^ 2 / (2 * μ) =
        2 * (G ^ 2 / (2 * μ)) := by field_simp; ring
    rw [envelope_quadratic hμpos (le_of_not_ge hcase)]
    exact (add_le_add_left hbase _).trans_eq he

theorem zero_query_envelope_cap {S : Set E} {f h : E → ℝ} {μ D G : ℝ}
    (P : ProximalOracle S h) (hh : StrongConvexOn S μ h)
    (hμ : 0 ≤ μ) (hD : 0 < D) (hG : 0 < G)
    (x₁ xstar : E) (hx : xstar ∈ S) (hinit : ‖x₁ - xstar‖ ≤ D)
    (hlip : ∀ u ∈ S, f u - f xstar ≤ G * ‖u - xstar‖) :
    let y := P.point (zeroQueryStep μ D G) x₁
    y ∈ S ∧ (f y + h y) - (f xstar + h xstar) ≤ 2 * envelope μ D G := by
  have hη := zeroQueryStep_pos hμ hD hG
  exact ⟨P.feasible _ hη x₁,
    (proximal_zero_query_realized P hh hμ hη x₁ xstar hx hinit hlip).trans
      (zeroQuery_arithmetic_cap hμ hD hG)⟩

end HeavyTail
