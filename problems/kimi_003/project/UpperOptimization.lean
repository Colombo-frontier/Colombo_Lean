import Mathlib

/-!
Projected stochastic descent on the actual closed Euclidean ball.
The projection is constructed as a nearest point, rather than postulated to
decrease distances. Its one-step energy inequality is proved below.
-/

open MeasureTheory Metric
open scoped BigOperators

namespace Task006.Full

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem ball_nearest_exists (r : ℝ) (hr : 0 ≤ r) (u : E) :
    ∃ v ∈ closedBall (0 : E) r, ‖u - v‖ = ⨅ w : closedBall (0 : E) r, ‖u - w‖ := by
  apply exists_norm_eq_iInf_of_complete_convex
  · exact ⟨0, by simpa using hr⟩
  · exact isClosed_closedBall.isComplete
  · exact convex_closedBall _ _

/-- The actual metric projection onto the closed ball of radius `r`. -/
noncomputable def ballProj (r : ℝ) (hr : 0 ≤ r) (u : E) : E :=
  Classical.choose (ball_nearest_exists r hr u)

theorem ballProj_mem (r : ℝ) (hr : 0 ≤ r) (u : E) :
    ballProj r hr u ∈ closedBall (0 : E) r :=
  (Classical.choose_spec (ball_nearest_exists r hr u)).1

theorem ballProj_minimizes (r : ℝ) (hr : 0 ≤ r) (u : E) :
    ‖u - ballProj r hr u‖ = ⨅ w : closedBall (0 : E) r, ‖u - w‖ :=
  (Classical.choose_spec (ball_nearest_exists r hr u)).2

theorem ballProj_inner_le_zero {r : ℝ} (hr : 0 ≤ r) (u z : E)
    (hz : ‖z‖ ≤ r) :
    inner ℝ (u - ballProj r hr u) (z - ballProj r hr u) ≤ 0 := by
  apply (norm_eq_iInf_iff_real_inner_le_zero
    (convex_closedBall (0 : E) r) (ballProj_mem r hr u)).mp
    (ballProj_minimizes r hr u) z
  simpa using hz

theorem ballProj_nonexpansive {r : ℝ} (hr : 0 ≤ r) (u v : E) :
    ‖ballProj r hr u - ballProj r hr v‖ ≤ ‖u - v‖ := by
  let p := ballProj r hr u
  let q := ballProj r hr v
  have hp : ‖p‖ ≤ r := by simpa [p] using ballProj_mem r hr u
  have hq : ‖q‖ ≤ r := by simpa [q] using ballProj_mem r hr v
  have h₁ := ballProj_inner_le_zero hr u q hq
  have h₂ := ballProj_inner_le_zero hr v p hp
  change inner ℝ (u - p) (q - p) ≤ 0 at h₁
  change inner ℝ (v - q) (p - q) ≤ 0 at h₂
  have hneg : q - p = -(p - q) := by abel
  rw [hneg, inner_neg_right] at h₁
  have henergy : ‖p - q‖ ^ 2 ≤ inner ℝ (p - q) (u - v) := by
    rw [← real_inner_self_eq_norm_sq]
    have hid : u - v = (u - p) + (p - q) - (v - q) := by abel
    conv_rhs => rw [hid, inner_sub_right, inner_add_right]
    rw [← real_inner_comm (p - q) (u - p), ← real_inner_comm (p - q) (v - q)]
    linarith
  have hcauchy := real_inner_le_norm (p - q) (u - v)
  by_cases hpq : ‖p - q‖ = 0
  · simpa [p, q, hpq] using norm_nonneg (u - v)
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpq)
    have : ‖p - q‖ ≤ ‖u - v‖ := by nlinarith
    exact this

theorem ballProj_lipschitz {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith 1 (ballProj (E := E) r hr) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using ballProj_nonexpansive hr u v

theorem ballProj_distance_sq_le {r : ℝ} (hr : 0 ≤ r) (u z : E)
    (hz : ‖z‖ ≤ r) : ‖ballProj r hr u - z‖ ^ 2 ≤ ‖u - z‖ ^ 2 := by
  have hmem : z ∈ closedBall (0 : E) r := by simpa using hz
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero
    (convex_closedBall (0 : E) r) (ballProj_mem r hr u)).mp
    (ballProj_minimizes r hr u) z hmem
  have hid : u - z = (u - ballProj r hr u) - (z - ballProj r hr u) := by abel
  rw [hid, norm_sub_sq_real (u - ballProj r hr u) (z - ballProj r hr u)]
  have hsym : ‖ballProj r hr u - z‖ = ‖z - ballProj r hr u‖ := norm_sub_rev _ _
  rw [hsym]
  nlinarith [sq_nonneg ‖u - ballProj r hr u‖]

/-- Source Section 4.4's actual projected-step energy inequality. -/
theorem projected_step_sq {r η : ℝ} (hr : 0 ≤ r) (hη : 0 ≤ η)
    (x g z : E) (hz : ‖z‖ ≤ r) :
    ‖ballProj r hr (x - η • g) - z‖ ^ 2 ≤
      ‖x - z‖ ^ 2 - 2 * η * inner ℝ (x - z) g + η ^ 2 * ‖g‖ ^ 2 := by
  have hp := ballProj_distance_sq_le hr (x - η • g) z hz
  have hid : x - η • g - z = (x - z) - η • g := by abel
  rw [hid, norm_sub_sq_real (x - z) (η • g), inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hη] at hp
  convert hp using 1 <;> ring

end Projection

section ConditionalRecurrence

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The past-measurable displacement can be pulled through the actual Bochner
conditional expectation of the stochastic gradient. -/
theorem predictable_inner_integral {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {a g : Ω → E} (ha : StronglyMeasurable[m] a)
    (hag : Integrable (fun ω => inner ℝ (a ω) (g ω)) μ) (hg : Integrable g μ) :
    (∫ ω, inner ℝ (a ω) (g ω) ∂μ) =
      ∫ ω, inner ℝ (a ω) ((μ[g | m]) ω) ∂μ := by
  calc
    (∫ ω, inner ℝ (a ω) (g ω) ∂μ) =
        ∫ ω, (μ[fun ω => inner ℝ (a ω) (g ω) | m]) ω ∂μ :=
      (integral_condExp hm).symm
    _ = _ := integral_congr_ae
      (condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) ha hag hg)

/-- The bias term in stochastic descent is obtained from the actual conditional
mean bound, rather than assumed as an expected regret inequality. -/
theorem expected_subgradient_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {a g v : Ω → E} {Δ : Ω → ℝ} {C B : ℝ}
    (hC : 0 ≤ C) (ha : StronglyMeasurable[m] a)
    (hag : Integrable (fun ω => inner ℝ (a ω) (g ω)) μ)
    (hg : Integrable g μ) (hΔ : Integrable Δ μ)
    (hsub : ∀ᵐ ω ∂μ, Δ ω ≤ inner ℝ (a ω) (v ω))
    (had : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ C)
    (hbias : ∀ᵐ ω ∂μ, ‖(μ[g | m]) ω - v ω‖ ≤ B) :
    (∫ ω, Δ ω ∂μ) ≤ (∫ ω, inner ℝ (a ω) (g ω) ∂μ) + C * B := by
  have hpull := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) ha hag hg
  have himean : Integrable (fun ω => inner ℝ (a ω) ((μ[g | m]) ω)) μ :=
    (integrable_congr hpull).mp integrable_condExp
  have hpoint : ∀ᵐ ω ∂μ,
      Δ ω ≤ inner ℝ (a ω) ((μ[g | m]) ω) + C * B := by
    filter_upwards [hsub, had, hbias] with ω hs hd hb
    have hbn : ‖v ω - (μ[g | m]) ω‖ ≤ B := by rwa [norm_sub_rev]
    have he : inner ℝ (a ω) (v ω - (μ[g | m]) ω) ≤ C * B :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul hd hbn (norm_nonneg _) hC)
    rw [inner_sub_right] at he
    linarith
  calc
    (∫ ω, Δ ω ∂μ) ≤ ∫ ω, inner ℝ (a ω) ((μ[g | m]) ω) + C * B ∂μ :=
      integral_mono_ae hΔ (himean.add (integrable_const _)) hpoint
    _ = (∫ ω, inner ℝ (a ω) ((μ[g | m]) ω) ∂μ) + C * B := by
      rw [integral_add himean (integrable_const _)]
      simp
    _ = _ := by rw [← predictable_inner_integral (mΩ := mΩ) (μ := μ) hm ha hag hg]

/-- Source U8's one-step stochastic recurrence, obtained from the actual
projected update, first-order convexity, conditional clipping bias, and second
moment. The expected recurrence is the conclusion, not a premise. -/
theorem projected_step_expected {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {r η C B W : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hC : 0 ≤ C)
    (x xn g v : Ω → E) (Δ : Ω → ℝ) (z : E) (hz : ‖z‖ ≤ r)
    (hstep : ∀ᵐ ω ∂μ, xn ω = ballProj r hr (x ω - η • g ω))
    (ha : StronglyMeasurable[m] (fun ω => x ω - z))
    (hg : Integrable g μ)
    (hinner : Integrable (fun ω => inner ℝ (x ω - z) (g ω)) μ)
    (hsq : Integrable (fun ω => ‖x ω - z‖ ^ 2) μ)
    (hnsq : Integrable (fun ω => ‖xn ω - z‖ ^ 2) μ)
    (hgsq : Integrable (fun ω => ‖g ω‖ ^ 2) μ)
    (hΔ : Integrable Δ μ)
    (hsub : ∀ᵐ ω ∂μ, Δ ω ≤ inner ℝ (x ω - z) (v ω))
    (had : ∀ᵐ ω ∂μ, ‖x ω - z‖ ≤ C)
    (hbias : ∀ᵐ ω ∂μ, ‖(μ[g | m]) ω - v ω‖ ≤ B)
    (hmoment : (∫ ω, ‖g ω‖ ^ 2 ∂μ) ≤ W) :
    (∫ ω, Δ ω ∂μ) ≤
      ((∫ ω, ‖x ω - z‖ ^ 2 ∂μ) - (∫ ω, ‖xn ω - z‖ ^ 2 ∂μ)) / (2 * η)
        + C * B + η * W / 2 := by
  have henergy : ∀ᵐ ω ∂μ,
      ‖xn ω - z‖ ^ 2 ≤ ‖x ω - z‖ ^ 2 -
        2 * η * inner ℝ (x ω - z) (g ω) + η ^ 2 * ‖g ω‖ ^ 2 := by
    filter_upwards [hstep] with ω hw
    rw [hw]
    exact projected_step_sq hr (le_of_lt hη) _ _ _ hz
  have henergyInt := integral_mono_ae hnsq
    ((hsq.sub (hinner.const_mul (2 * η))).add (hgsq.const_mul (η ^ 2))) henergy
  simp only [Pi.add_apply, Pi.sub_apply] at henergyInt
  have heqAdd := integral_add (hsq.sub (hinner.const_mul (2 * η)))
    (hgsq.const_mul (η ^ 2))
  have heqSub := integral_sub hsq (hinner.const_mul (2 * η))
  simp only [Pi.add_apply, Pi.sub_apply] at heqAdd heqSub
  rw [heqAdd, heqSub, integral_const_mul, integral_const_mul] at henergyInt
  have hgradient := expected_subgradient_le (mΩ := mΩ) (μ := μ) hm hC ha hinner hg hΔ hsub had hbias
  have hmoment' := mul_le_mul_of_nonneg_left hmoment (sq_nonneg η)
  have hnum : ((∫ ω, Δ ω ∂μ) - C * B - η * W / 2) * (2 * η) ≤
      (∫ ω, ‖x ω - z‖ ^ 2 ∂μ) - (∫ ω, ‖xn ω - z‖ ^ 2 ∂μ) := by
    nlinarith
  have hdiv := (le_div_iff₀ (by positivity : 0 < 2 * η)).mpr hnum
  linarith

end ConditionalRecurrence

section FiniteRegret

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact time average of the implemented iterates (zero-based indices). -/
noncomputable def iterateAverage (x : ℕ → E) (T : ℕ) : E :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t

theorem convex_time_average_gap {K : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ K f) {x : ℕ → E} {T : ℕ} (hT : 0 < T)
    (hx : ∀ t < T, x t ∈ K) (z : E) :
    f (iterateAverage x T) - f z ≤
      (∑ t ∈ Finset.range T, (f (x t) - f z)) / T := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hw : ∑ _t ∈ Finset.range T, (T : ℝ)⁻¹ = 1 := by simp [hT0]
  have hj := hf.map_sum_le (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
    (p := x) (fun _ _ => by positivity) hw (fun t ht => hx t (Finset.mem_range.mp ht))
  rw [← Finset.smul_sum] at hj
  simp only [smul_eq_mul] at hj
  have hsum : (∑ t ∈ Finset.range T, (f (x t) - f z)) / T =
      (∑ t ∈ Finset.range T, (T : ℝ)⁻¹ * f (x t)) - f z := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hT0]
    <;> ring
  rw [hsum]
  exact sub_le_sub_right hj _

/-- Telescoping all the one-step energy inequalities without discarding the
terminal energy before it has been proved nonnegative. -/
theorem finite_descent_regret {T : ℕ} (hT : 0 < T) {η R K : ℝ} (hη : 0 < η)
    (a Δ : ℕ → ℝ) (ha0 : a 0 ≤ R ^ 2) (haT : 0 ≤ a T)
    (hstep : ∀ t < T, Δ t ≤ (a t - a (t + 1)) / (2 * η) + K) :
    (∑ t ∈ Finset.range T, Δ t) / T ≤ R ^ 2 / (2 * η * T) + K := by
  have htel : ∑ t ∈ Finset.range T, (a t - a (t + 1)) / (2 * η) =
      (a 0 - a T) / (2 * η) := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_range_sub']
  have hs : (∑ t ∈ Finset.range T, Δ t) ≤ (a 0 - a T) / (2 * η) + T * K := by
    calc
      (∑ t ∈ Finset.range T, Δ t) ≤
          ∑ t ∈ Finset.range T, ((a t - a (t + 1)) / (2 * η) + K) :=
        Finset.sum_le_sum (fun t ht => hstep t (Finset.mem_range.mp ht))
      _ = _ := by rw [Finset.sum_add_distrib, htel]; simp
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  apply (div_le_iff₀ hTreal).mpr
  calc
    (∑ t ∈ Finset.range T, Δ t) ≤ R ^ 2 / (2 * η) + T * K := by
      have hquot := div_le_div_of_nonneg_right
        (show a 0 - a T ≤ R ^ 2 by linarith) (show 0 ≤ 2 * η by positivity)
      linarith
    _ = (R ^ 2 / (2 * η * T) + K) * T := by
      field_simp [ne_of_gt hη, ne_of_gt hTreal]
      <;> ring

end FiniteRegret

section StochasticRegret

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A complete finite-time stochastic projected-descent bound from the actual
updates and conditional estimator laws. No one-step or terminal regret estimate
is assumed. In the paper `C=2R` and `B` includes the finite-difference bias. -/
theorem projected_stochastic_regret {T : ℕ} (hT : 0 < T)
    {r η C B W R : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hC : 0 ≤ C)
    (f : E → ℝ) (hf : ConvexOn ℝ (closedBall (0 : E) r) f)
    (x g v : ℕ → Ω → E) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ t < T, m t ≤ mΩ) (z : E) (hz : ‖z‖ ≤ r)
    (hstep : ∀ t < T, ∀ᵐ ω ∂μ,
      x (t + 1) ω = ballProj r hr (x t ω - η • g t ω))
    (ha : ∀ t < T, StronglyMeasurable[m t] (fun ω => x t ω - z))
    (hg : ∀ t < T, Integrable (g t) μ)
    (hinner : ∀ t < T, Integrable (fun ω => inner ℝ (x t ω - z) (g t ω)) μ)
    (hsq : ∀ t ≤ T, Integrable (fun ω => ‖x t ω - z‖ ^ 2) μ)
    (hgsq : ∀ t < T, Integrable (fun ω => ‖g t ω‖ ^ 2) μ)
    (hgap : ∀ t < T, Integrable (fun ω => f (x t ω) - f z) μ)
    (havg : Integrable (fun ω => f (iterateAverage (fun t => x t ω) T) - f z) μ)
    (hsub : ∀ t < T, ∀ᵐ ω ∂μ,
      f (x t ω) - f z ≤ inner ℝ (x t ω - z) (v t ω))
    (had : ∀ t < T, ∀ᵐ ω ∂μ, ‖x t ω - z‖ ≤ C)
    (hbias : ∀ t < T, ∀ᵐ ω ∂μ, ‖(μ[g t | m t]) ω - v t ω‖ ≤ B)
    (hmoment : ∀ t < T, (∫ ω, ‖g t ω‖ ^ 2 ∂μ) ≤ W)
    (hfeas : ∀ᵐ ω ∂μ, ∀ t < T, ‖x t ω‖ ≤ r)
    (hinit : (∫ ω, ‖x 0 ω - z‖ ^ 2 ∂μ) ≤ R ^ 2) :
    (∫ ω, f (iterateAverage (fun t => x t ω) T) - f z ∂μ) ≤
      R ^ 2 / (2 * η * T) + C * B + η * W / 2 := by
  have hrec : ∀ t < T,
      (∫ ω, f (x t ω) - f z ∂μ) ≤
        ((∫ ω, ‖x t ω - z‖ ^ 2 ∂μ) - (∫ ω, ‖x (t + 1) ω - z‖ ^ 2 ∂μ)) /
          (2 * η) + (C * B + η * W / 2) := by
    intro t ht
    have hs := projected_step_expected (mΩ := mΩ) (μ := μ) (hm t ht) hr hη hC
      (x t) (x (t + 1)) (g t) (v t) (fun ω => f (x t ω) - f z) z hz
      (hstep t ht) (ha t ht) (hg t ht) (hinner t ht) (hsq t (by omega))
      (hsq (t + 1) (by omega)) (hgsq t ht) (hgap t ht) (hsub t ht)
      (had t ht) (hbias t ht) (hmoment t ht)
    linarith
  have hterminal := finite_descent_regret hT hη
    (fun t => ∫ ω, ‖x t ω - z‖ ^ 2 ∂μ)
    (fun t => ∫ ω, f (x t ω) - f z ∂μ)
    hinit (integral_nonneg (fun _ => sq_nonneg _)) hrec
  have hjensen : ∀ᵐ ω ∂μ,
      f (iterateAverage (fun t => x t ω) T) - f z ≤
        (∑ t ∈ Finset.range T, (f (x t ω) - f z)) / T := by
    filter_upwards [hfeas] with ω hω
    exact convex_time_average_gap hf hT (fun t ht => by simpa using hω t ht) z
  have hsumInt := integrable_finsetSum (Finset.range T)
    (fun t ht => hgap t (Finset.mem_range.mp ht))
  have hmean := integral_mono_ae havg (hsumInt.div_const (T : ℝ)) hjensen
  simp only [integral_div] at hmean
  rw [integral_finsetSum (Finset.range T) (fun t ht => hgap t (Finset.mem_range.mp ht))] at hmean
  exact hmean.trans (by linarith [hterminal])

end StochasticRegret

#print axioms ballProj_nonexpansive
#print axioms projected_step_expected
#print axioms convex_time_average_gap
#print axioms finite_descent_regret
#print axioms projected_stochastic_regret

end Task006.Full
