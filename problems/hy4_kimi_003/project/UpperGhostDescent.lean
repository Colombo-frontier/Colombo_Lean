import UpperGhostShadowLaw
import UpperOptimizationRecurrence

/-! Actual projected descent under a state-dependent accepted-block kernel. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set
namespace Task006.Full

theorem goodStateLaw_succ_eq_compProd {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (hpos : ∀ x, ν (G x) ≠ 0)
    (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    goodStateLaw ν G hG step x0 (n + 1) =
      ((goodStateLaw ν G hG step x0 n) ⊗ₘ goodProposalKernel ν G hG).map step := by
  letI := goodProposalKernel_markov ν G hG hpos
  letI := goodStateLaw_probability ν G hG hpos step hstep x0 n
  rw [goodStateLaw, goodStepKernel, ← Measure.map_comp _ _ hstep, ← Measure.compProd_eq_comp_prod]

theorem goodStateLaw_succ_integral {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1}) (hpos : ∀ x, ν (G x) ≠ 0)
    (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ)
    (H : E → ℝ) (hH : Measurable H) (hHi : Integrable H (goodStateLaw ν G hG step x0 (n + 1))) :
    Integrable (fun x => ∫ b, H (step (x, b)) ∂goodRestrictedLaw ν (G x))
        (goodStateLaw ν G hG step x0 n) ∧
      (∫ x, H x ∂goodStateLaw ν G hG step x0 (n + 1)) =
        ∫ x, (∫ b, H (step (x, b)) ∂goodRestrictedLaw ν (G x))
          ∂goodStateLaw ν G hG step x0 n := by
  letI := goodProposalKernel_markov ν G hG hpos
  letI := goodStateLaw_probability ν G hG hpos step hstep x0 n
  rw [goodStateLaw_succ_eq_compProd ν G hG hpos step hstep x0 n] at hHi ⊢
  have hj : Integrable (fun p : E × B => H (step p))
      ((goodStateLaw ν G hG step x0 n) ⊗ₘ goodProposalKernel ν G hG) :=
    (integrable_map_measure hH.aestronglyMeasurable hstep.aemeasurable).mp hHi
  refine ⟨hj.integral_compProd, ?_⟩
  rw [integral_map hstep.aemeasurable hH.aestronglyMeasurable, Measure.integral_compProd hj]
  rfl

theorem upperGhost_conditional_step {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (ν : Measure (UpperSampleBlock d Ω)) [IsProbabilityMeasure ν]
    (f : Space d → ℝ) (v x z : Space d) {β W : ℝ}
    (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ)) (hz : ‖z‖ ≤ P.R - (P.ρ + P.δ))
    (hsub : f x - f z ≤ inner ℝ (x - z) v)
    (hbias : ‖(∫ b, upperBlockDirection P F x b ∂ν) - v‖ ≤ β)
    (hmoment : (∫ b, ‖upperBlockDirection P F x b‖ ^ 2 ∂ν) ≤ W) :
    f x - f z ≤
      (‖x - z‖ ^ 2 - (∫ b, ‖ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg
        (x - P.η • upperBlockDirection P F x b) - z‖ ^ 2 ∂ν)) / (2 * P.η) +
          2 * P.R * β + P.η * W / 2 := by
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  have hrR : P.R - (P.ρ + P.δ) ≤ P.R := by linarith [P.rho_nonneg, P.delta_pos]
  have hdist : ‖x - z‖ ≤ 2 * P.R := by linarith [norm_sub_le x z]
  let g := upperBlockDirection (d := d) (Ω := Ω) P F x
  have hgm : Measurable g := by
    change Measurable (upperBlockDirection (d := d) (Ω := Ω) P F x)
    exact (upperBlockDirection_measurable (d := d) (Ω := Ω) (F := F) P hF).of_uncurry_left
  have hgi : Integrable g ν := Integrable.of_bound hgm.aestronglyMeasurable _
    (ae_of_all _ (upperBlockDirection_norm_le P F x))
  have hinner : Integrable (fun b => inner ℝ (x - z) (g b)) ν := hgi.const_inner _
  have hg2 : Integrable (fun b => ‖g b‖ ^ 2) ν := by
    apply Integrable.of_bound (hgm.norm.pow_const 2).aestronglyMeasurable ((Real.sqrt d * P.b) ^ 2)
    filter_upwards [] with b
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (upperBlockDirection_norm_le P F x b) 2
  let xn := fun b => ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg (x - P.η • g b)
  have hxnM : Measurable xn := (ballProj_lipschitz (E := Space d) P.inner_nonneg).continuous.measurable.comp
    (measurable_const.sub (hgm.const_smul P.η))
  have hxnI : Integrable (fun b => ‖xn b - z‖ ^ 2) ν := by
    apply Integrable.of_bound ((hxnM.sub measurable_const).norm.pow_const 2).aestronglyMeasurable ((2 * P.R) ^ 2)
    filter_upwards [] with b
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp : ‖xn b‖ ≤ P.R - (P.ρ + P.δ) := by simpa only [mem_closedBall, dist_zero_right] using ballProj_mem _ P.inner_nonneg (x - P.η • g b)
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_sub_le (xn b) z] : ‖xn b - z‖ ≤ 2 * P.R) 2
  have hmean : f x - f z ≤ (∫ b, inner ℝ (x - z) (g b) ∂ν) + 2 * P.R * β := by
    rw [integral_inner hgi]
    have hb : ‖v - ∫ b, g b ∂ν‖ ≤ β := by rw [norm_sub_rev]; exact hbias
    have he := (real_inner_le_norm (x - z) (v - ∫ b, g b ∂ν)).trans
      (mul_le_mul hdist hb (norm_nonneg _) (by positivity))
    rw [inner_sub_right] at he
    linarith
  have he := projected_step_expected_of_inner (μ := ν) P.inner_nonneg P.eta_pos (by positivity : 0 ≤ 2 * P.R)
    (fun _ => x) xn g (fun _ => v) (fun _ => f x - f z) z hz
    (ae_of_all _ (fun _ => rfl)) hinner (integrable_const _) hxnI hg2 (integrable_const _)
    (by simpa only [integral_const, probReal_univ, one_smul] using hmean) hmoment
  simpa only [integral_const, probReal_univ, one_smul] using he

#print axioms upperGhost_conditional_step
end Task006.Full
