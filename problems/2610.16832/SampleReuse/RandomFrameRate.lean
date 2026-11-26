import SampleReuse.RandomFrameCalibrated
import SampleReuse.CurvatureChainLength

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory

theorem calibrated_dimension_formula (P : Parameters) (γ : ℝ) (m N : ℕ) :
    calibratedFrameDimension P γ m N = m+N+
      ⌈(32*(curvatureRadiusScale P/curvatureScaleK P)^2/γ^4)*
        Real.log (24*(m:ℝ)*(N+1))⌉₊ := by
  have he : 32*(curvatureRadius P γ/(curvatureScaleK P*γ))^2 =
      32*(curvatureRadiusScale P/curvatureScaleK P)^2/γ^4 := by
    unfold curvatureRadius
    simp only [div_eq_mul_inv, mul_inv_rev, mul_pow, inv_pow]
    ring
  simp only [calibratedFrameDimension, hardFrameDimension, he]

theorem calibrated_dimension_upper (P : Parameters) (γ : ℝ) {m : ℕ}
    (hm : 0 < m) (N : ℕ) :
    (calibratedFrameDimension P γ m N : ℝ) < (m:ℝ)+N+
      (32*(curvatureRadiusScale P/curvatureScaleK P)^2/γ^4)*
        Real.log (24*(m:ℝ)*(N+1)) + 1 := by
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (24*(m:ℝ)*(N+1)) := Real.log_nonneg (by nlinarith)
  have hcoef : 0 ≤ 32*(curvatureRadiusScale P/curvatureScaleK P)^2/γ^4 := by positivity
  have hc := Nat.ceil_lt_add_one (mul_nonneg hcoef hlog)
  rw [calibrated_dimension_formula]
  simp only [Nat.cast_add]
  linarith

/-- Actual deterministic full-jet hardness at the manuscript's `γ⁻³` scale.
The constants and tolerance threshold depend only on the fixed model bounds,
and every chosen hard loss satisfies all model fields. -/
theorem deterministic_curvature_rate (P : Parameters) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      c/γ^3 ≤ (curvatureChainLength P γ : ℝ) ∧
      (curvatureChainLength P γ : ℝ) ≤ 2*c/γ^3 ∧
      ∀ ε : ℝ, ε < P.gradientBound/8 → ∀ N : ℕ, N < curvatureChainLength P γ →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : FullJetPolicy (calibratedFrameDimension P γ (curvatureChainLength P γ) N) N Ω),
      ∃ F : Point (calibratedFrameDimension P γ (curvatureChainLength P γ) N) → ℝ,
        Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 ∧
        μ.real {ω | IsSOSP F ε γ (π.outputFor F ω)} ≤ 1/6 := by
  obtain ⟨ηF,hηF,hfixed⟩ := calibrated_curvature_fixed_cap_lower P
  obtain ⟨ηA,hηA,hamp⟩ := curvature_small_amplitude P
  refine ⟨curvatureLengthConstant P, min ηF ηA, curvatureLengthConstant_pos P,
    lt_min hηF hηA, ?_⟩
  intro γ hγ hγη
  have hγF := hγη.trans_le (min_le_left ηF ηA)
  have hγA := hγη.trans_le (min_le_right ηF ηA)
  have hn := curvature_chain_length_bounds P hγ (hamp γ hγ hγA)
  refine ⟨hn.2.2.1, hn.2.2.2, ?_⟩
  intro ε hε N hN Ω _ μ _ π
  generalize hm : curvatureChainLength P γ = m at hn hN π ⊢
  cases m with
  | zero => omega
  | succ T =>
      obtain ⟨U,hU,hprob⟩ := hfixed γ hγ hγF ε hε T N hn.2.1 hN Ω μ π
      exact ⟨_, hU, hprob⟩

end SampleReuse.RandomFrame
