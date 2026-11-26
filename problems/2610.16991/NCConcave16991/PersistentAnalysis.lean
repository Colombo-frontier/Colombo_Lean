import NCConcave16991.PersistentProcess
import NCConcave16991.MoreauDescent

/-! # Expected descent of the constructed persistent process -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.PersistentProcess

noncomputable section

variable {n b dx dy : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
  {J : Type*} [Finite J] [MeasurableSpace J] [MeasurableSingletonClass J]
  (G : Fin n → JointSpace dx dy → JointSpace dx dy) (y0 : DualSpace dy)
  (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
  (σ : Measure J) [IsProbabilityMeasure σ] (c : PrimalSpace dx)

def meanAt (f : State dx dy → ℝ) (t : ℕ) : ℝ :=
  ∫ h, f (process G y0 q solve c t h)
    ∂FiniteProcess.law (σ.prod (minibatchLaw n b)) t

def meanStep (f : State dx dy → State dx dy → ℝ) (t : ℕ) : ℝ :=
  ∫ h, f (process G y0 q solve c t h.1) (process G y0 q solve c (t + 1) h)
    ∂FiniteProcess.law (σ.prod (minibatchLaw n b)) (t + 1)

theorem meanStep_previous (f : State dx dy → ℝ) (t : ℕ) :
    meanStep (b := b) G y0 q solve σ c (fun z _ ↦ f z) t = meanAt (b := b) G y0 q solve σ c f t := by
  exact FiniteProcess.integral_previous (σ.prod (minibatchLaw n b)) t
    (fun h ↦ f (process G y0 q solve c t h))

theorem meanStep_current (f : State dx dy → ℝ) (t : ℕ) :
    meanStep (b := b) G y0 q solve σ c (fun _ z ↦ f z) t = meanAt (b := b) G y0 q solve σ c f (t + 1) := rfl

theorem meanStep_bound (f : State dx dy → State dx dy → ℝ)
    (bound : State dx dy → ℝ) (t : ℕ)
    (hlocal : ∀ z, (∫ ω, f z (advance G y0 q solve t z ω)
      ∂σ.prod (minibatchLaw n b)) ≤ bound z) :
    meanStep (b := b) G y0 q solve σ c f t ≤ meanAt (b := b) G y0 q solve σ c bound t := by
  exact FiniteProcess.integral_step_le _ t _ _
    (fun h ↦ hlocal (process G y0 q solve c t h))

/-- Independent inner sampling gives an unconditional error bound for the
actual process. The persistent bias may depend on all previous samples. -/
theorem mean_inner_error_bound (prox : PrimalSpace dx → PrimalSpace dx)
    (κ L a noise : ℝ)
    (hsolve : ∀ z, (∫ j, ‖solve z j - prox z.center‖ ^ 2 ∂σ) ≤
      a * ‖prox z.center - z.center‖ ^ 2 +
        3 * weightedErrorSq κ (error G y0 z) / L ^ 2 + noise)
    (t : ℕ) :
    meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2) t ≤
      a * meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t +
      3 * meanAt (b := b) G y0 q solve σ c (fun z ↦ weightedErrorSq κ (error G y0 z)) t / L ^ 2 + noise := by
  have hlocal (z : State dx dy) :
      (∫ ω, ‖(advance G y0 q solve t z ω).center - prox z.center‖ ^ 2
        ∂σ.prod (minibatchLaw n b)) ≤
      a * ‖prox z.center - z.center‖ ^ 2 +
        3 * weightedErrorSq κ (error G y0 z) / L ^ 2 + noise := by
    rw [integral_prod _ Integrable.of_finite]
    simpa only [advance_center, integral_const, probReal_univ, one_smul] using hsolve z
  have hh := meanStep_bound (b := b) G y0 q solve σ c
    (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2)
    (fun z ↦ a * ‖prox z.center - z.center‖ ^ 2 +
      3 * weightedErrorSq κ (error G y0 z) / L ^ 2 + noise) t hlocal
  simpa only [meanAt, integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_div, integral_const, probReal_univ, one_smul] using hh

theorem mean_movement_bound (prox : PrimalSpace dx → PrimalSpace dx) (t : ℕ) :
    meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - z.center‖ ^ 2) t ≤
      2 * meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t +
      2 * meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2) t := by
  letI : IsProbabilityMeasure (FiniteProcess.law (σ.prod (minibatchLaw n b)) (t + 1)) :=
    FiniteProcess.law_probability _ _
  have hp (h : FiniteProcess.History (J × (Fin b → Fin n)) (t + 1)) :
      ‖(process G y0 q solve c (t + 1) h).center - (process G y0 q solve c t h.1).center‖ ^ 2 ≤
      2 * ‖prox (process G y0 q solve c t h.1).center - (process G y0 q solve c t h.1).center‖ ^ 2 +
      2 * ‖(process G y0 q solve c (t + 1) h).center - prox (process G y0 q solve c t h.1).center‖ ^ 2 := by
    have hh := norm_sub_sq_le_two (process G y0 q solve c (t + 1) h).center
      (prox (process G y0 q solve c t h.1).center) (process G y0 q solve c t h.1).center
    rw [norm_sub_rev (prox _) (process G y0 q solve c (t + 1) h).center] at hh
    linarith only [hh]
  have hh := integral_mono
    (μ := FiniteProcess.law (σ.prod (minibatchLaw n b)) (t + 1))
    Integrable.of_finite Integrable.of_finite hp
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul] at hh
  have hprev := meanStep_previous (b := b) G y0 q solve σ c
    (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t
  dsimp [meanStep] at hprev
  rw [hprev] at hh
  exact hh

/-- The expected envelope descent is derived from the true proximal
optimality inequality and the actual history marginals. -/
theorem mean_envelope_descent {f : PrimalSpace dx → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hb : BddBelow (range f))
    (prox : PrimalSpace dx → PrimalSpace dx) (hp : ∀ x, IsProxPoint f L x (prox x))
    (t : ℕ) :
    meanAt (b := b) G y0 q solve σ c (fun z ↦ moreauEnvelope f L z.center) (t + 1) ≤
      meanAt (b := b) G y0 q solve σ c (fun z ↦ moreauEnvelope f L z.center) t -
        L * meanAt (b := b) G y0 q solve σ c (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t +
        L * meanStep (b := b) G y0 q solve σ c (fun z z' ↦ ‖z'.center - prox z.center‖ ^ 2) t := by
  letI : IsProbabilityMeasure (FiniteProcess.law (σ.prod (minibatchLaw n b)) (t + 1)) :=
    FiniteProcess.law_probability _ _
  have hpoint (h : FiniteProcess.History (J × (Fin b → Fin n)) (t + 1)) :=
    moreauEnvelope_proximal_descent hL hb
      (hp (process G y0 q solve c t h.1).center) (process G y0 q solve c (t + 1) h).center
  have hh := integral_mono
    (μ := FiniteProcess.law (σ.prod (minibatchLaw n b)) (t + 1))
    Integrable.of_finite Integrable.of_finite hpoint
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul] at hh
  have he := meanStep_previous (b := b) G y0 q solve σ c
    (fun z ↦ moreauEnvelope f L z.center) t
  have hd := meanStep_previous (b := b) G y0 q solve σ c
    (fun z ↦ ‖prox z.center - z.center‖ ^ 2) t
  dsimp [meanStep] at he hd
  rw [he, hd] at hh
  exact hh

end

end NCConcave16991.PersistentProcess

