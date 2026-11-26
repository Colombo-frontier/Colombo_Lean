import SampleReuse.Model

/-! Centered same-sample derivative differences. The deterministic bounds are
connected to the actual common-loss gradient and Hessian in `Admissible`.
The expectation identities use Bochner integration under the probability law.
These results concern one fixed pair of endpoints, not a concentration bound
for an adaptive trajectory. -/

open MeasureTheory

namespace SampleReuse
noncomputable section

def centeredChord {Ω X E : Type*} [AddCommGroup E]
    (A : Ω → X → E) (a : X → E) (x y : X) (z : Ω) : E :=
  (A z x - A z y) - (a x - a y)

@[simp] theorem centeredChord_self {Ω X E : Type*} [AddCommGroup E]
    (A : Ω → X → E) (a : X → E) (x : X) (z : Ω) :
    centeredChord A a x x z = 0 := by
  simp [centeredChord]

theorem centeredChord_norm_le {Ω X E : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup X]
    (A : Ω → X → E) (a : X → E) (x y : X) (z : Ω) (σ L : ℝ)
    (hx : ‖A z x - a x‖ ≤ σ) (hy : ‖A z y - a y‖ ≤ σ)
    (hs : ‖A z x - A z y‖ ≤ L * ‖x-y‖)
    (hp : ‖a x - a y‖ ≤ L * ‖x-y‖) :
    ‖centeredChord A a x y z‖ ≤ 2 * min σ (L * ‖x-y‖) := by
  have hn : ‖centeredChord A a x y z‖ ≤ 2 * σ := by
    have heq : centeredChord A a x y z =
        (A z x - a x) - (A z y - a y) := by
      unfold centeredChord
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith)
  have hl : ‖centeredChord A a x y z‖ ≤ 2 * (L * ‖x-y‖) :=
    (norm_sub_le _ _).trans (by linarith)
  rcases le_total σ (L * ‖x-y‖) with h | h
  · simpa [min_eq_left h] using hn
  · simpa [min_eq_right h] using hl

theorem centeredChord_integrable {Ω X E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Ω → X → E) (a : X → E) (x y : X)
    (hx : Integrable (fun z => A z x) μ)
    (hy : Integrable (fun z => A z y) μ) :
    Integrable (centeredChord A a x y) μ :=
  (hx.sub hy).sub (integrable_const _)

theorem centeredChord_integral_eq_zero {Ω X E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Ω → X → E) (a : X → E) (x y : X)
    (hx : Integrable (fun z => A z x) μ)
    (hy : Integrable (fun z => A z y) μ)
    (hux : (∫ z, A z x ∂μ) = a x)
    (huy : (∫ z, A z y ∂μ) = a y) :
    (∫ z, centeredChord A a x y z ∂μ) = 0 := by
  simp only [centeredChord]
  have hi : Integrable (fun z => A z x - A z y) μ := hx.sub hy
  rw [integral_sub hi (integrable_const (a x - a y)), integral_sub hx hy,
    hux, huy]
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.gradient_chord_bound (h : Admissible μ P f F x₀) :
    ∀ᵐ z ∂μ, ∀ x y,
      ‖centeredChord (fun z => gradient (F z)) (gradient f) x y z‖ ≤
        2 * min P.gradientNoise (P.gradientLip * ‖x-y‖) := by
  filter_upwards [h.noise_bound, h.sample_regularity] with z hz hr
  intro x y
  exact centeredChord_norm_le _ _ _ _ _ _ _ (hz x).1 (hz y).1
    (hr.2.1 x y) (h.population_gradient_lipschitz x y)

theorem Admissible.hessian_chord_bound (h : Admissible μ P f F x₀) :
    ∀ᵐ z ∂μ, ∀ x y,
      ‖centeredChord (fun z => hessian (F z)) (hessian f) x y z‖ ≤
        2 * min P.hessianNoise (P.hessianLip * ‖x-y‖) := by
  filter_upwards [h.noise_bound, h.sample_regularity] with z hz hr
  intro x y
  exact centeredChord_norm_le _ _ _ _ _ _ _ (hz x).2 (hz y).2
    (hr.2.2 x y) (h.population_hessian_lipschitz x y)

theorem Admissible.gradient_chord_unbiased (h : Admissible μ P f F x₀)
    (x y : Point d) :
    (∫ z, centeredChord (fun z => gradient (F z)) (gradient f) x y z ∂μ) = 0 :=
  centeredChord_integral_eq_zero _ _ x y (h.gradient_integrable x)
    (h.gradient_integrable y) (h.gradient_unbiased x) (h.gradient_unbiased y)

theorem Admissible.hessian_chord_unbiased (h : Admissible μ P f F x₀)
    (x y : Point d) :
    (∫ z, centeredChord (fun z => hessian (F z)) (hessian f) x y z ∂μ) = 0 :=
  centeredChord_integral_eq_zero _ _ x y (h.hessian_integrable x)
    (h.hessian_integrable y) (h.hessian_unbiased x) (h.hessian_unbiased y)

end
end SampleReuse
