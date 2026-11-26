import HeavyTail.StageBudgets
import HeavyTail.WarmStart

/-! The rounded phase sum with the warm-start assumption discharged by the
actual finite proximal preprocessing theorem. All raw-call factors are retained. -/
noncomputable section
open Set
open scoped BigOperators
namespace HeavyTail

theorem physical_raw_stage_budget_of_radius {C A G s μ R rp ell : ℝ}
    (hC : 1 ≤ C) (hA : G ^ 2 ≤ A) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hμ : 0 < μ) (hR : 0 < R) (hrp : 0 < rp) (hell : 1 ≤ ell) (N : ℕ)
    (hstart : (2 : ℝ) ^ N * R ≤ Real.sqrt 2 * G / μ) :
    4 * (∑ m ∈ Finset.range N, (⌈C * physicalStageWeight A G s μ R rp ell m⌉₊ : ℝ)) ≤
      12 * C * stageSumConstant rp *
        (A / (μ ^ 2 * R ^ 2) + (G / (μ * R)) * ell +
          ((s / (μ * R)) ^ rp) * ell) := by
  apply physical_raw_stage_budget_bound hC ((sq_nonneg G).trans hA) hG hs hμ hR hrp hell N
  intro m hm
  have hmN : m + 1 ≤ N := Finset.mem_range.mp hm
  have hpow : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hmN
  have hrad : (2 : ℝ) ^ (m + 1) * R ≤ Real.sqrt 2 * G / μ :=
    (mul_le_mul_of_nonneg_right hpow hR.le).trans hstart
  have hprod : μ * ((2 : ℝ) ^ (m + 1) * R) ≤ Real.sqrt 2 * G := by
    have h := (le_div_iff₀ hμ).mp hrad
    nlinarith only [h]
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ μ * ((2 : ℝ) ^ (m + 1) * R)) hprod 2
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsquare
  apply (le_div_iff₀ (by positivity : 0 < μ ^ 2 * ((2 : ℝ) ^ (m + 1) * R) ^ 2)).mpr
  nlinarith only [hsquare, hA]

def finalLocalizationRadius (R₀ : ℝ) (N : ℕ) : ℝ := R₀ / (2 : ℝ) ^ N

theorem warmStartRadius_pos {μ D G : ℝ} (hμ : 0 < μ) (hD : 0 < D) (hG : 0 < G) :
    0 < warmStartRadius μ D G := by
  unfold warmStartRadius
  split_ifs <;> positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact prescribed ceiling budgets after a certified proximal warm start.
The right-hand constant is independent of the number of stages. -/
theorem phase_sum_after_proximal_warm_start
    {S : Set E} {f h : E → ℝ} {μ D G A C s rp ell : ℝ}
    (P : ProximalOracle S h) (hf : ConvexOn ℝ S f) (hh : StrongConvexOn S μ h)
    (hμ : 0 < μ) (hD : 0 < D) (hG : 0 < G) (hC : 1 ≤ C)
    (hA : G ^ 2 ≤ A) (hs : 0 ≤ s) (hrp : 0 < rp) (hell : 1 ≤ ell)
    (x₁ xstar : E) (hx : xstar ∈ S) (hinit : ‖x₁ - xstar‖ ≤ D)
    (hmin : ∀ u ∈ S, f xstar + h xstar ≤ f u + h u)
    (hlip : ∀ u ∈ S, f u - f xstar ≤ G * ‖u - xstar‖) (N : ℕ) :
    let R := finalLocalizationRadius (warmStartRadius μ D G) N
    4 * (∑ m ∈ Finset.range N, (⌈C * physicalStageWeight A G s μ R rp ell m⌉₊ : ℝ)) ≤
      12 * C * stageSumConstant rp *
        (A / (μ ^ 2 * R ^ 2) + (G / (μ * R)) * ell +
          ((s / (μ * R)) ^ rp) * ell) := by
  have hR₀ := warmStartRadius_pos hμ hD hG
  have hwarm := (finite_proximal_warm_start_radius P hf hh hμ hD hG x₁ xstar hx hinit hmin hlip).2
  apply physical_raw_stage_budget_of_radius hC hA hG.le hs hμ (by unfold finalLocalizationRadius; positivity)
    hrp hell N
  have heq : (2 : ℝ) ^ N * finalLocalizationRadius (warmStartRadius μ D G) N =
      warmStartRadius μ D G := by
    unfold finalLocalizationRadius
    field_simp
  rw [heq]
  exact hwarm

end HeavyTail
