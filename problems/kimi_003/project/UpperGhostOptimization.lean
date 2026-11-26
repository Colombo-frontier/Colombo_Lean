import UpperGhostDescent
import UpperGhostJensen

/-! Full finite-time regret of the genuine adaptive accepted-block Markov
process. Kernel mean/moment assumptions are local estimator facts, discharged
for the sample model by UpperGhostMoments. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set
open scoped NNReal BigOperators
namespace Task006.Full

set_option maxHeartbeats 3000000 in
theorem goodStateLaw_upper_regret {d T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) (hT : 0 < T)
    (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (ν : Measure (UpperSampleBlock d Ω)) [IsProbabilityMeasure ν]
    (G : UpperGhostState d → Set (UpperSampleBlock d Ω))
    (hG : MeasurableSet {p : UpperGhostState d × UpperSampleBlock d Ω | p.2 ∈ G p.1})
    (hpos : ∀ x, ν (G x) ≠ 0)
    (f : Space d → ℝ) (C : ℝ≥0) (hfLip : LipschitzWith C f)
    (hfConvex : ConvexOn ℝ (closedBall (0 : Space d) (P.R - (P.ρ + P.δ))) f)
    (v : Space d → Space d) {β W : ℝ}
    (hbias : ∀ x : UpperGhostState d, ‖x.1‖ ≤ P.R - (P.ρ + P.δ) →
      ‖(∫ b, upperBlockDirection P F x.1 b ∂goodRestrictedLaw ν (G x)) - v x.1‖ ≤ β)
    (hmoment : ∀ x : UpperGhostState d, ‖x.1‖ ≤ P.R - (P.ρ + P.δ) →
      (∫ b, ‖upperBlockDirection P F x.1 b‖ ^ 2 ∂goodRestrictedLaw ν (G x)) ≤ W)
    (z : Space d) (hz : ‖z‖ ≤ P.R - (P.ρ + P.δ))
    (hsub : ∀ x, ‖x‖ ≤ P.R - (P.ρ + P.δ) → f x - f z ≤ inner ℝ (x - z) (v x)) :
    (∫ state, f ((T : ℝ)⁻¹ • state.2) - f z
      ∂goodStateLaw ν G hG (upperGhostStep P F) (0, 0) T) ≤
        P.R ^ 2 / (2 * P.η * T) + 2 * P.R * β + P.η * W / 2 := by
  let step := upperGhostStep (d := d) (Ω := Ω) P F
  have hstep : Measurable step := upperGhostStep_measurable P hF
  let σ := goodStateLaw ν G hG step (0, 0)
  let a : ℕ → ℝ := fun n => ∫ x : UpperGhostState d, ‖x.1 - z‖ ^ 2 ∂σ n
  let Δ : ℕ → ℝ := fun n => ∫ x : UpperGhostState d, f x.1 - f z ∂σ n
  let avg : ℕ → ℝ := fun n => ∫ x : UpperGhostState d, f ((n : ℝ)⁻¹ • x.2) - f z ∂σ n
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  have hrR : P.R - (P.ρ + P.δ) ≤ P.R := by linarith [P.rho_nonneg, P.delta_pos]
  have hσ (n : ℕ) : IsProbabilityMeasure (σ n) := goodStateLaw_probability ν G hG hpos step hstep (0, 0) n
  have hfeas (n : ℕ) : ∀ᵐ x ∂σ n, ‖x.1‖ ≤ P.R - (P.ρ + P.δ) ∧
      ‖x.2‖ ≤ n * (P.R - (P.ρ + P.δ)) := goodStateLaw_upperStep_feasible P F hF ν G hG hpos n
  have hdist {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ)) : ‖x - z‖ ≤ 2 * P.R := by
    linarith [norm_sub_le x z]
  have havgNorm (n : ℕ) {x : UpperGhostState d}
      (hx : ‖x.2‖ ≤ n * (P.R - (P.ρ + P.δ))) : ‖(n : ℝ)⁻¹ • x.2‖ ≤ P.R - (P.ρ + P.δ) := by
    by_cases hn : n = 0
    · simpa only [hn, Nat.cast_zero, inv_zero, zero_smul, norm_zero] using P.inner_nonneg
    · exact upperGhost_average_norm_le P (Nat.pos_of_ne_zero hn) hx
  have hgapI (n : ℕ) : Integrable (fun x : UpperGhostState d => f x.1 - f z) (σ n) := by
    letI := hσ n
    apply Integrable.of_bound ((hfLip.continuous.measurable.comp measurable_fst).sub measurable_const).aestronglyMeasurable
      ((C : ℝ) * (2 * P.R))
    filter_upwards [hfeas n] with x hx
    exact (hfLip.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left (hdist hx.1) C.coe_nonneg)
  have henergyM : Measurable (fun x : UpperGhostState d => ‖x.1 - z‖ ^ 2) :=
    (measurable_fst.sub measurable_const).norm.pow_const 2
  have henergyI (n : ℕ) : Integrable (fun x : UpperGhostState d => ‖x.1 - z‖ ^ 2) (σ n) := by
    letI := hσ n
    apply Integrable.of_bound henergyM.aestronglyMeasurable ((2 * P.R) ^ 2)
    filter_upwards [hfeas n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdist hx.1) 2
  have havgM (n : ℕ) : Measurable (fun x : UpperGhostState d => f ((n : ℝ)⁻¹ • x.2) - f z) :=
    (hfLip.continuous.measurable.comp (measurable_snd.const_smul ((n : ℝ)⁻¹))).sub measurable_const
  have havgI (n : ℕ) : Integrable (fun x : UpperGhostState d => f ((n : ℝ)⁻¹ • x.2) - f z) (σ n) := by
    letI := hσ n
    apply Integrable.of_bound (havgM n).aestronglyMeasurable ((C : ℝ) * (2 * P.R))
    filter_upwards [hfeas n] with x hx
    exact (hfLip.norm_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (hdist (havgNorm n hx.2)) C.coe_nonneg)
  have hrec (n : ℕ) (_hn : n < T) :
      Δ n ≤ (a n - a (n + 1)) / (2 * P.η) + (2 * P.R * β + P.η * W / 2) := by
    letI := hσ n
    have hi := goodStateLaw_succ_integral ν G hG hpos step hstep (0, 0) n _ henergyM (henergyI (n + 1))
    have hpoint : ∀ᵐ x ∂σ n, f x.1 - f z ≤
        (‖x.1 - z‖ ^ 2 - (∫ b, ‖(step (x, b)).1 - z‖ ^ 2 ∂goodRestrictedLaw ν (G x))) /
          (2 * P.η) + (2 * P.R * β + P.η * W / 2) := by
      filter_upwards [hfeas n] with x hx
      letI := goodRestrictedLaw_probability ν (G x) (hpos x)
      have he := upperGhost_conditional_step P F hF (goodRestrictedLaw ν (G x)) f (v x.1) x.1 z
        hx.1 hz (hsub x.1 hx.1) (hbias x hx.1) (hmoment x hx.1)
      dsimp only [step, upperGhostStep]
      linarith [he]
    have hRHS := (((henergyI n).sub hi.1).div_const (2 * P.η)).add
      (integrable_const (2 * P.R * β + P.η * W / 2))
    have hm := integral_mono_ae (hgapI n) hRHS hpoint
    have hadd := integral_add (((henergyI n).sub hi.1).div_const (2 * P.η))
      (integrable_const (2 * P.R * β + P.η * W / 2))
    have hsubI := integral_sub (henergyI n) hi.1
    simp only [Pi.add_apply, Pi.sub_apply] at hm hadd hsubI
    rw [hadd, integral_div, hsubI, ← hi.2] at hm
    simpa only [integral_const, probReal_univ, one_smul, a, Δ] using hm
  have hinit : a 0 ≤ P.R ^ 2 := by
    have hn : ‖z‖ ≤ P.R := hz.trans hrR
    have hp := pow_le_pow_left₀ (norm_nonneg z) hn 2
    simpa only [a, σ, goodStateLaw, integral_dirac, Prod.fst, zero_sub, norm_neg] using hp
  have hregret := finite_descent_regret hT P.eta_pos a Δ hinit
    (integral_nonneg (fun _ => sq_nonneg _)) hrec
  have havgRec (n : ℕ) (_hn : n < T) :
      ((n + 1 : ℕ) : ℝ) * avg (n + 1) ≤ (n : ℝ) * avg n + Δ n := by
    letI := hσ n
    have hi := goodStateLaw_succ_integral ν G hG hpos step hstep (0, 0) n _ (havgM (n + 1)) (havgI (n + 1))
    have heq (x : UpperGhostState d) :
        (∫ b, (f (((n + 1 : ℕ) : ℝ)⁻¹ • (step (x, b)).2) - f z) ∂goodRestrictedLaw ν (G x)) =
          f (((n + 1 : ℕ) : ℝ)⁻¹ • (x.2 + x.1)) - f z := by
      letI := goodRestrictedLaw_probability ν (G x) (hpos x)
      change (∫ _b : UpperSampleBlock d Ω, f (((n + 1 : ℕ) : ℝ)⁻¹ • (x.2 + x.1)) - f z
        ∂goodRestrictedLaw ν (G x)) = _
      simp
    have hnewI : Integrable (fun x : UpperGhostState d =>
        f (((n + 1 : ℕ) : ℝ)⁻¹ • (x.2 + x.1)) - f z) (σ n) :=
      hi.1.congr (ae_of_all _ heq)
    have havgEq : avg (n + 1) = ∫ x : UpperGhostState d,
        f (((n + 1 : ℕ) : ℝ)⁻¹ • (x.2 + x.1)) - f z ∂σ n :=
      hi.2.trans (integral_congr_ae (ae_of_all _ heq))
    have hp : ∀ᵐ x ∂σ n,
        ((n + 1 : ℕ) : ℝ) * (f (((n + 1 : ℕ) : ℝ)⁻¹ • (x.2 + x.1)) - f z) ≤
          (n : ℝ) * (f ((n : ℝ)⁻¹ • x.2) - f z) + (f x.1 - f z) :=
      (hfeas n).mono (fun x hx => Task006.UpperGhostJensen.running_average_step P.inner_nonneg hfConvex
        x.1 x.2 z n hx.1 hx.2)
    have hm := integral_mono_ae (hnewI.const_mul ((n + 1 : ℕ) : ℝ))
      (((havgI n).const_mul (n : ℝ)).add (hgapI n)) hp
    have hadd := integral_add ((havgI n).const_mul (n : ℝ)) (hgapI n)
    simp only [Pi.add_apply] at hm hadd
    rw [hadd, integral_const_mul, integral_const_mul, ← havgEq] at hm
    exact hm
  have hj := Task006.UpperGhostJensen.average_sequence_telescope avg Δ T havgRec
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have havgBound : avg T ≤ (∑ n ∈ Finset.range T, Δ n) / T := by
    apply (le_div_iff₀ hTr).mpr
    nlinarith [hj]
  exact havgBound.trans (by linarith [hregret])

#print axioms goodStateLaw_upper_regret
end Task006.Full
