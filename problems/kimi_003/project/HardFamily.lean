import OracleSemantics
import LowerAudit

open MeasureTheory ProbabilityTheory

namespace Task006.Full
namespace HardFamily

noncomputable section

def law (L A : ℝ) (hA : 16 ≤ A) : Measure ℝ :=
  bernoulliMeasure (L * A ^ 2 / 256) 0 (Task006LowerAudit.rareParameter A hA)

instance (L A : ℝ) (hA : 16 ≤ A) : IsProbabilityMeasure (law L A hA) := by
  unfold law
  infer_instance

lemma slope_nonneg {L A : ℝ} (hL : 0 ≤ L) : 0 ≤ L * A ^ 2 / 256 := by positivity

lemma integral_abs_moment (L A : ℝ) (hL : 0 ≤ L) (hA : 16 ≤ A) :
    (∫ g, |g| ^ (3 / 2 : ℝ) ∂law L A hA) = L ^ (3 / 2 : ℝ) := by
  rw [law, integral_bernoulliMeasure]
  simpa only [Task006LowerAudit.rareParameter,smul_eq_mul,
    abs_of_nonneg (slope_nonneg hL),abs_zero,
    Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0),mul_zero,add_zero] using
    Task006LowerAudit.rare_moment_calibration L A hL hA

/-- The actual two-atom hard instance, admissible under exactly the original
sample contract. No information or risk assertion is part of this structure. -/
def instanceOfDirection {d : ℕ} (L R A : ℝ) (hL : 0 ≤ L) (hA : 16 ≤ A)
    (θ : Space d) (hθ : ‖θ‖ = 1) : SampleInstance d L R ℝ (law L A hA) where
  sample x g := g * inner ℝ θ x
  modulus g := |g|
  measurable_sample x hx := measurable_id.mul_const _
  measurable_modulus := measurable_id.abs
  nonneg_modulus := Filter.Eventually.of_forall abs_nonneg
  convex_sample := by
    apply Filter.Eventually.of_forall
    intro g
    refine ⟨convex_closedBall _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (Task006LowerAudit.hard_linear_convex g θ).2 (Set.mem_univ x)
      (Set.mem_univ y) ha hb hab
  lipschitz_sample := by
    apply Filter.Eventually.of_forall
    intro g x hx y hy
    rw [← mul_sub, abs_mul, ← inner_sub_right]
    have h := norm_inner_le_norm (𝕜 := ℝ) θ (x-y)
    have hi : |inner ℝ θ (x-y)| ≤ ‖x-y‖ := by
      simpa only [Real.norm_eq_abs,hθ,one_mul] using h
    exact mul_le_mul_of_nonneg_left hi (abs_nonneg g)
  integrable_origin := by simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => 0) (law L A hA))
  integrable_moment := integrable_bernoulliMeasure _ _ _ _
  moment_bound := (integral_abs_moment L A hL hA).le

theorem objective_formula {d : ℕ} (L R A : ℝ) (hL : 0 ≤ L) (hA : 16 ≤ A)
    (θ : Space d) (hθ : ‖θ‖ = 1) (x : Space d) :
    (instanceOfDirection L R A hL hA θ hθ).objective x =
      (16 * L / A) * inner ℝ θ x := by
  change (∫ g, g * inner ℝ θ x ∂law L A hA) = _
  rw [integral_mul_const]
  congr 1
  exact Task006LowerAudit.bernoulli_slope_mean L A hA

theorem optimalValue_formula {d : ℕ} (L R A : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hA : 16 ≤ A) (θ : Space d) (hθ : ‖θ‖ = 1) :
    optimalValue (instanceOfDirection L R A hL hA θ hθ) = -(16 * L / A) * R := by
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨(-R) • θ, ?_, ?_⟩
    · change ‖(-R) • θ - 0‖ ≤ R
      simpa only [sub_zero] using
        (Task006LowerAudit.hard_linear_minimizer R (16*L/A) hR θ hθ).1
    · rw [objective_formula]
      exact (Task006LowerAudit.hard_linear_minimizer R (16*L/A) hR θ hθ).2
  · rintro z ⟨x,hx,rfl⟩
    rw [objective_formula]
    have hm : 0 ≤ 16*L/A := by positivity
    have hy : ‖x‖ ≤ R := by simpa [outputDomain,Metric.mem_closedBall,dist_eq_norm] using hx
    have hg := (Task006LowerAudit.hard_linear_gap R (16*L/A) hR hm θ x hθ hy).1
    linarith

end
end HardFamily
end Task006.Full
