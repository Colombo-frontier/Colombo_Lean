import SecondOrder.Model

/-! The manuscript model, with actual derivatives of a common scalar loss.
The sample-wise conditions hold on a single probability-one set for all points.
No algorithmic success or complexity bound is included in the assumptions. -/

open MeasureTheory
open scoped InnerProductSpace

namespace SampleReuse
noncomputable section

abbrev Point := SecondOrder.Point
abbrev hessian := @SecondOrder.hessian
abbrev IsSOSP := @SecondOrder.IsSOSP

structure Parameters where
  gap : ℝ
  gradientLip : ℝ
  hessianLip : ℝ
  gradientNoise : ℝ
  hessianNoise : ℝ
  gradientBound : ℝ
  gap_pos : 0 < gap
  gradientLip_pos : 0 < gradientLip
  hessianLip_pos : 0 < hessianLip
  gradientNoise_pos : 0 < gradientNoise
  hessianNoise_pos : 0 < hessianNoise
  gradientBound_pos : 0 < gradientBound

/-- Assumptions 1--5, plus the measurability and integrability needed to give
the random oracle its mathematical meaning. The initial point is explicit. -/
structure Admissible {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d) : Prop where
  population_smooth : ContDiff ℝ 2 f
  gap_bound : ∀ x, f x₀ - f x ≤ P.gap
  value_measurable : Measurable (fun zx : Ω × Point d => F zx.1 zx.2)
  gradient_measurable : Measurable (fun zx : Ω × Point d => gradient (F zx.1) zx.2)
  hessian_measurable : Measurable (fun zx : Ω × Point d => hessian (F zx.1) zx.2)
  sample_regularity : ∀ᵐ z ∂μ, ContDiff ℝ 2 (F z) ∧
    (∀ x y, ‖gradient (F z) x - gradient (F z) y‖ ≤ P.gradientLip * ‖x-y‖) ∧
    (∀ x y, ‖hessian (F z) x - hessian (F z) y‖ ≤ P.hessianLip * ‖x-y‖)
  value_integrable : ∀ x, Integrable (fun z => F z x) μ
  gradient_integrable : ∀ x, Integrable (fun z => gradient (F z) x) μ
  hessian_integrable : ∀ x, Integrable (fun z => hessian (F z) x) μ
  value_unbiased : ∀ x, (∫ z, F z x ∂μ) = f x
  gradient_unbiased : ∀ x, (∫ z, gradient (F z) x ∂μ) = gradient f x
  hessian_unbiased : ∀ x, (∫ z, hessian (F z) x ∂μ) = hessian f x
  noise_bound : ∀ᵐ z ∂μ, ∀ x,
    ‖gradient (F z) x - gradient f x‖ ≤ P.gradientNoise ∧
    ‖hessian (F z) x - hessian f x‖ ≤ P.hessianNoise
  population_gradient_bound : ∀ x, ‖gradient f x‖ ≤ P.gradientBound

theorem Admissible.bounded_below {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) : BddBelow (Set.range f) := by
  refine ⟨f x₀ - P.gap, ?_⟩
  rintro _ ⟨x, rfl⟩
  linarith [h.gap_bound x]

/-- Jensen's step deriving population Lipschitzness from uniform sample
Lipschitzness. The conclusion is not an additional model assumption. -/
theorem mean_lipschitz {Ω E X : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Ω → X → E) (a : X → E) (L : ℝ)
    (hi : ∀ x, Integrable (fun z => A z x) μ)
    (ha : ∀ x, (∫ z, A z x ∂μ) = a x)
    (hL : ∀ᵐ z ∂μ, ∀ x y, ‖A z x-A z y‖ ≤ L*‖x-y‖) :
    ∀ x y, ‖a x-a y‖ ≤ L*‖x-y‖ := by
  intro x y
  rw [← ha x, ← ha y, ← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ z, ‖A z x-A z y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Ω, L*‖x-y‖ ∂μ := integral_mono_ae
      ((hi x).sub (hi y)).norm (integrable_const _) (hL.mono fun _ hz => hz x y)
    _ = L*‖x-y‖ := by simp

theorem Admissible.population_gradient_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) :
    ∀ x y, ‖gradient f x-gradient f y‖ ≤ P.gradientLip*‖x-y‖ :=
  mean_lipschitz (fun z => gradient (F z)) (gradient f) P.gradientLip
    h.gradient_integrable h.gradient_unbiased (h.sample_regularity.mono fun _ hz => hz.2.1)

theorem Admissible.population_hessian_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (h : Admissible μ P f F x₀) :
    ∀ x y, ‖hessian f x-hessian f y‖ ≤ P.hessianLip*‖x-y‖ :=
  mean_lipschitz (fun z => hessian (F z)) (hessian f) P.hessianLip
    h.hessian_integrable h.hessian_unbiased (h.sample_regularity.mono fun _ hz => hz.2.2)

/-- The actual stopping certificate with the manuscript's 3/4 and 1/4
thresholds. The Hessian test is expressed by its Rayleigh quotients. -/
theorem stopping_certificate {d : ℕ} {f : Point d → ℝ} {x g : Point d}
    {H : Point d →L[ℝ] Point d} {ε γ : ℝ}
    (hg : ‖g‖ ≤ 3*ε/4) (hge : ‖g-gradient f x‖ ≤ ε/4)
    (hH : ∀ v : Point d, -(3*γ/4)*‖v‖^2 ≤ ⟪H v,v⟫_ℝ)
    (hHe : ‖H-hessian f x‖ ≤ γ/4) : IsSOSP f ε γ x := by
  refine ⟨?_, ?_⟩
  · have ht := norm_add_le (gradient f x-g) g
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith
  · intro v
    have hnorm := (H-hessian f x).le_opNorm v
    have hip := abs_real_inner_le_norm ((H-hessian f x) v) v
    have he : |⟪(H-hessian f x) v,v⟫_ℝ| ≤ (γ/4)*‖v‖^2 := by
      calc
        _ ≤ ‖(H-hessian f x) v‖*‖v‖ := hip
        _ ≤ (‖H-hessian f x‖*‖v‖)*‖v‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ ≤ ((γ/4)*‖v‖)*‖v‖ := by
          gcongr
        _ = (γ/4)*‖v‖^2 := by ring
    have hdiff : ⟪(H-hessian f x) v,v⟫_ℝ =
        ⟪H v,v⟫_ℝ - ⟪hessian f x v,v⟫_ℝ := by
      simp only [ContinuousLinearMap.sub_apply, inner_sub_left]
    rw [hdiff] at he
    have hu := (abs_le.mp he).2
    linarith [hH v]

end
end SampleReuse
