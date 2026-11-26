import SampleReuse.RandomFrameExpectedLower

noncomputable section
namespace SampleReuse.RandomFrame
open MeasureTheory RandomizedFO2003 Rotations

theorem calibrated_curvature_all_dimensions (P : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η → ∀ ε : ℝ, ε < P.gradientBound/8 →
      ∀ T N : ℕ, curvatureAmplitude (curvatureScaleK P) γ*(T+1:ℕ) ≤ P.gap/8 → N < T+1 →
      ∀ d : ℕ, calibratedFrameDimension P γ (T+1) N ≤ d →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : FullJetPolicy d N Ω),
      ∃ F : Point d → ℝ, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 ∧
        μ.real {ω | IsSOSP F ε γ (π.outputFor F ω)} ≤ 1/6 := by
  obtain ⟨ηG,hηG,hglobal⟩ := calibrated_curvature_globalization P
  obtain ⟨ηB,hηB,hbud⟩ := curvature_small_tolerance_budgets P
  refine ⟨min ηG ηB, lt_min hηG hηB, ?_⟩
  intro γ hγ hγη ε hε T N hn hN d hd Ω _ μ _ π
  have hγG := hγη.trans_le (min_le_left ηG ηB)
  have hγB := hγη.trans_le (min_le_right ηG ηB)
  have hbds := hbud γ hγ hγB
  have hscl := calibrated_curvature_scalar_budgets P hγ hε hbds.2.2.2.1 hbds.2.2.2.2 hn
  have hK := curvatureScaleK_pos P
  have hA := (curvatureAmplitude_pos hK hγ).le
  have hβ := curvatureInputDilation_pos hK hγ
  have hb := (curvatureWallSlope_pos P).le
  have hR : 0 < curvatureRadius P γ := div_pos (curvatureRadiusScale_pos P) hγ
  have hh : 0 < curvatureScaleK P*γ := mul_pos hK hγ
  have hβt : curvatureInputDilation (curvatureScaleK P) γ*(curvatureScaleK P*γ/2) ≤ 1/2 := by
    unfold curvatureInputDilation
    have he : (curvatureScaleK P*γ)⁻¹*(curvatureScaleK P*γ/2) = 1/2 := by field_simp
    exact he.le
  have hframe : T+1 ≤ calibratedFrameDimension P γ (T+1) N :=
    hardFrameDimension_ge_frame (T+1) N _ _
  let U₀ := standardEmbedding (hframe.trans hd)
  have hdim : 2*(2*curvatureRadius P γ)^2*
      Real.log (2*((T+1)*(N+1):ℕ)/(1/12)) ≤
      ((calibratedFrameDimension P γ (T+1) N-N:ℕ):ℝ)*(curvatureScaleK P*γ/2)^2 := by
    have hd := hardFrameDimension_budget (T+1) N (curvatureRadius P γ) hh
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hd
  obtain ⟨V,hV⟩ := curvature_radial_exists_hard_frame hN μ π.query π.query_measurable U₀
    hA hβ hb hR hγ (half_pos hh) hβt (by norm_num : (0:ℝ)<1/12)
    (by norm_num : (1/12:ℝ)<1/6) hscl.1 hscl.2.1 hscl.2.2.1 hscl.2.2.2
    (hdim.trans (mul_le_mul_of_nonneg_right (by
      exact_mod_cast Nat.sub_le_sub_right hd N) (sq_nonneg _))) π.output π.output_measurable
  refine ⟨calibratedCurvatureLoss P γ (rotatedEmbedding U₀ V),
    (hglobal γ hγ hγG ε hε _ T (rotatedEmbedding U₀ V) hn).1, ?_⟩
  exact hV


theorem deterministic_curvature_expected_all_dimensions (P : Parameters) :
    ∃ c η : ℝ, 0 < c ∧ 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      ∀ ε : ℝ, ε < P.gradientBound/8 → ∀ d : ℕ,
      calibratedFrameDimension P γ (curvatureChainLength P γ) (curvatureChainLength P γ-1) ≤ d →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : StoppingFullJetPolicy d Ω),
      (∀ F, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 →
        (2/3:ℝ) ≤ μ.real {ω | π.Halts F ω ∧ IsSOSP F ε γ (π.outputFor F ω)}) →
      ∃ F, Admissible (PMF.pure ()).toMeasure P F (fun _ : Unit => F) 0 ∧
        ENNReal.ofReal (c/γ^3) ≤ ∫⁻ ω, π.extendedCost F ω ∂μ := by
  obtain ⟨ηF,hηF,hfixed⟩ := calibrated_curvature_all_dimensions P
  obtain ⟨ηA,hηA,hamp⟩ := curvature_small_amplitude P
  refine ⟨curvatureLengthConstant P/2,min ηF ηA,
    half_pos (curvatureLengthConstant_pos P),lt_min hηF hηA,?_⟩
  intro γ hγ hγη ε hε d hd Ω _ μ _ π hsolve
  have hγF := hγη.trans_le (min_le_left ηF ηA)
  have hγA := hγη.trans_le (min_le_right ηF ηA)
  have hn := curvature_chain_length_bounds P hγ (hamp γ hγ hγA)
  have hN : curvatureChainLength P γ-1 < curvatureChainLength P γ := Nat.sub_lt hn.1 (by decide)
  have hlen : curvatureChainLength P γ-1+1 = curvatureChainLength P γ := Nat.sub_add_cancel hn.1
  have hh := hfixed γ hγ hγF ε hε (curvatureChainLength P γ-1) (curvatureChainLength P γ-1)
  rw [hlen] at hh
  obtain ⟨F,hF,hcap⟩ := hh hn.2.1 hN d hd Ω μ (π.cap (curvatureChainLength P γ-1))
  refine ⟨F,hF,?_⟩
  have hE := π.extended_expected_calls_from_cap hF.population_smooth μ (IsSOSP F ε γ)
    (curvatureChainLength P γ-1) (hsolve F hF) hcap
  rw [hlen] at hE
  have hr : (curvatureLengthConstant P/2)/γ^3 ≤
      (curvatureChainLength P γ:ℝ)*((2/3:ℝ)-1/6) := by
    have he : (curvatureLengthConstant P/2)/γ^3 = (curvatureLengthConstant P/γ^3)/2 := by ring
    rw [he]
    nlinarith only [hn.2.2.1]
  have he : ENNReal.ofReal ((curvatureLengthConstant P/2)/γ^3) ≤
      (curvatureChainLength P γ:ENNReal)*ENNReal.ofReal ((2/3:ℝ)-1/6) := by
    calc
      _ ≤ ENNReal.ofReal ((curvatureChainLength P γ:ℝ)*((2/3:ℝ)-1/6)) :=
        ENNReal.ofReal_le_ofReal hr
      _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact he.trans hE

end SampleReuse.RandomFrame
