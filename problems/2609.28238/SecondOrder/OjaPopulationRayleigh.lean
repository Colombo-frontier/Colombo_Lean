import SecondOrder.OjaRandomNoise

open MeasureTheory Filter
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

theorem probability_lower_outside_bad_event {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {E G B : Set Ω} {a b : ℝ}
    (hE : a ≤ μ.real E) (hB : μ.real B ≤ b)
    (himp : ∀ w ∈ E, w ∉ B → w ∈ G) : a-b ≤ μ.real G := by
  have hs : E ⊆ G ∪ B := by
    intro w hw
    by_cases hb : w ∈ B
    · exact Or.inr hb
    · exact Or.inl (himp w hw hb)
  have hm := (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans (measureReal_union_le G B)
  linarith

theorem log_one_add_lower_quadratic {t : ℝ} (ht : 0 ≤ t) :
    t-t^2 ≤ Real.log (1+t) := by
  have hpos : 0 < 1+t := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have he : 1-(1+t)⁻¹ = t/(1+t) := by field_simp
  rw [he] at hl
  refine le_trans ?_ hl
  apply (le_div_iff₀ hpos).mpr
  nlinarith [mul_nonneg ht (sq_nonneg t)]

/-- Conversion of the exact logarithmic growth bound to a simple regret
bound. The leading loss is quadratic in the learning rate. -/
theorem oja_population_regret_algebra {η ℓ n L r S : ℝ}
    (hη : 0 ≤ η) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hn : 0 ≤ n)
    (hS : S ≤ ℓ*n)
    (hlower : 2*n*Real.log (1+η*ℓ)-L-(2*η+η^2)*r ≤ (2*η+η^2)*S) :
    2*η*(ℓ*n-S) ≤ 3*η^2*n + L + (2*η+η^2)*r := by
  have hlog := log_one_add_lower_quadratic (mul_nonneg hη hℓ0)
  have hl := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*n by positivity)
  have hℓsq : ℓ^2 ≤ 1 := by nlinarith
  have hquad := mul_le_mul_of_nonneg_left hℓsq (show 0 ≤ 2*η^2*n by positivity)
  have hcap : S ≤ n := hS.trans (by nlinarith)
  have hSη := mul_le_mul_of_nonneg_left hcap (sq_nonneg η)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The cumulative population Rayleigh values obey the growth lower bound
after paying a directly proved martingale-tail probability. -/
theorem CommonLoss.ojaRandomMeanRayleighSum_log_lower (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η p r : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 < r) (x : Point d) (N : ℕ)
    (hscale : η^2 * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) *
      (N : ℝ) ≤ p / 100) :
    (1-p)/12 - (N:ℝ)/r^2 ≤ (ojaRandomLaw μ d N).real {w |
      2*(N:ℝ)*Real.log (1+η*topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))) -
        Real.log (4*(d:ℝ)) - (2*η+η^2)*r ≤
          (2*η+η^2)*ojaRandomMeanRayleighSum P F f η x N w} := by
  apply probability_lower_outside_bad_event
    (h.ojaRandomRayleighSum_lower hd hη hη1 hp hp1 x N hscale)
    (h.ojaRandomNoise_tail_real hd hη x N hr)
  intro w he hn
  have hn' : ojaRandomNoise P F f η x N w ≤ r :=
    (le_abs_self _).trans (le_of_lt (lt_of_not_ge hn))
  have hc : 0 ≤ 2*η+η^2 := by positivity
  change _ ≤ (2*η+η^2)*ojaRandomRayleighSum P f η x N w at he
  rw [ojaRandomRayleigh_decomposition] at he
  change _ ≤ (2*η+η^2)*ojaRandomMeanRayleighSum P F f η x N w
  nlinarith [mul_le_mul_of_nonneg_left hn' hc]

theorem CommonLoss.ojaMeanRayleighSum_top_bound (h : CommonLoss μ P ν F f)
    (hd : 0 < d) {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ∀ v : Point d, ‖v‖ = 1 →
      ojaMeanRayleighSum P F f η x v N w ≤
        topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) * (N:ℝ) := by
  have htop := (h.mean_shifted_top_eigenpair hd x).2.2.1
  induction N with
  | zero => filter_upwards with w v hv; simp [ojaMeanRayleighSum]
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hu := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae
      (h.ojaHvpRun_ae_norm hη N)
    filter_upwards [hp,hu] with w hw hu
    intro v hv
    have hr := htop (ojaHvpRun P f η x v N w.1)
    rw [hu x v hv, one_pow, mul_one] at hr
    change ojaMeanRayleighSum P F f η x v N w.1 + _ ≤ _
    have hi := hw v hv
    push_cast
    nlinarith

theorem CommonLoss.ojaRandomMeanRayleighSum_top_bound (h : CommonLoss μ P ν F f)
    (hd : 0 < d) {η : ℝ} (hη : 0 ≤ η) (x : Point d) (N : ℕ) :
    ∀ᵐ w ∂ojaRandomLaw μ d N, ojaRandomMeanRayleighSum P F f η x N w ≤
      topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) * (N:ℝ) := by
  have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := signLaw d)).ae
    (h.ojaMeanRayleighSum_top_bound hd hη x N)
  filter_upwards [hp] with w hw
  exact hw (rademacherInit w.2) (rademacherInit_norm hd w.2)

theorem CommonLoss.ojaRandomMeanRayleighSum_regret (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η p r : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 < r) (x : Point d) (N : ℕ)
    (hscale : η^2 * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) *
      (N : ℝ) ≤ p / 100) :
    (1-p)/12 - (N:ℝ)/r^2 ≤ (ojaRandomLaw μ d N).real {w |
      2*η*(topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))*(N:ℝ) -
        ojaRandomMeanRayleighSum P F f η x N w) ≤
          3*η^2*(N:ℝ) + Real.log (4*(d:ℝ)) + (2*η+η^2)*r} := by
  have hl := h.ojaRandomMeanRayleighSum_log_lower hd hη hη1 hp hp1 hr x N hscale
  obtain ⟨hℓ0,hℓ1,_⟩ := h.mean_shifted_top_eigenpair hd x
  have hm : ojaRandomLaw μ d N {w |
      2*(N:ℝ)*Real.log (1+η*topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))) -
        Real.log (4*(d:ℝ)) - (2*η+η^2)*r ≤
          (2*η+η^2)*ojaRandomMeanRayleighSum P F f η x N w} ≤
      ojaRandomLaw μ d N {w |
        2*η*(topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x))*(N:ℝ) -
          ojaRandomMeanRayleighSum P F f η x N w) ≤
            3*η^2*(N:ℝ) + Real.log (4*(d:ℝ)) + (2*η+η^2)*r} := by
    apply measure_mono_ae
    filter_upwards [h.ojaRandomMeanRayleighSum_top_bound hd hη x N] with w hw
    intro he
    exact oja_population_regret_algebra hη hℓ0 hℓ1 (Nat.cast_nonneg N) hw he
  exact hl.trans (ENNReal.toReal_mono (measure_ne_top _ _) hm)

end
end SecondOrder
