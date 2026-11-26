import SampleReuse.RandomFrameHardInstance
import SampleReuse.RandomFrameDimension
import SampleReuse.CurvatureGlobalization

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory RandomizedFO2003 Rotations

/-- Unrestricted measurable full-jet policies, with arbitrary coin space and
arbitrary output after a fixed cap. Earlier replies are retained in full. -/
structure FullJetPolicy (d N : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d
  query_measurable : ∀ n, Measurable
    (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) => query n p.1 p.2)
  output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d
  output_measurable : Measurable
    (fun p : Ω × (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) => output p.1 p.2)

def FullJetPolicy.outputFor {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (π : FullJetPolicy d N Ω) (f : Point d → ℝ) (ω : Ω) : Point d :=
  π.output ω (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () N)

def calibratedFrameDimension (P : Parameters) (γ : ℝ) (m N : ℕ) : ℕ :=
  hardFrameDimension m N (curvatureRadius P γ) (curvatureScaleK P*γ)

/-- For all sufficiently small curvature tolerances, every measurable capped
full-jet algorithm has a fixed, fully admissible deterministic scalar hard
instance. The ambient dimension is explicitly constructed, and the cap may
be zero. No probabilistic or derivative lemma is a hypothesis. -/
theorem calibrated_curvature_fixed_cap_lower (P : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η → ∀ ε : ℝ, ε < P.gradientBound/8 →
      ∀ T N : ℕ, curvatureAmplitude (curvatureScaleK P) γ*(T+1:ℕ) ≤ P.gap/8 → N < T+1 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (π : FullJetPolicy (calibratedFrameDimension P γ (T+1) N) N Ω),
      ∃ U : Point (T+1) →ₗᵢ[ℝ] Point (calibratedFrameDimension P γ (T+1) N),
        Admissible (PMF.pure ()).toMeasure P (calibratedCurvatureLoss P γ U)
          (fun _ : Unit => calibratedCurvatureLoss P γ U) 0 ∧
        μ.real {ω | IsSOSP (calibratedCurvatureLoss P γ U) ε γ
          (π.outputFor (calibratedCurvatureLoss P γ U) ω)} ≤ 1/6 := by
  obtain ⟨ηG,hηG,hglobal⟩ := calibrated_curvature_globalization P
  obtain ⟨ηB,hηB,hbud⟩ := curvature_small_tolerance_budgets P
  refine ⟨min ηG ηB, lt_min hηG hηB, ?_⟩
  intro γ hγ hγη ε hε T N hn hN Ω _ μ _ π
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
  let U₀ := standardEmbedding hframe
  have hdim : 2*(2*curvatureRadius P γ)^2*
      Real.log (2*((T+1)*(N+1):ℕ)/(1/12)) ≤
      ((calibratedFrameDimension P γ (T+1) N-N:ℕ):ℝ)*(curvatureScaleK P*γ/2)^2 := by
    have hd := hardFrameDimension_budget (T+1) N (curvatureRadius P γ) hh
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hd
  obtain ⟨V,hV⟩ := curvature_radial_exists_hard_frame hN μ π.query π.query_measurable U₀
    hA hβ hb hR hγ (half_pos hh) hβt (by norm_num : (0:ℝ)<1/12)
    (by norm_num : (1/12:ℝ)<1/6) hscl.1 hscl.2.1 hscl.2.2.1 hscl.2.2.2
    hdim π.output π.output_measurable
  refine ⟨rotatedEmbedding U₀ V,
    (hglobal γ hγ hγG ε hε _ T (rotatedEmbedding U₀ V) hn).1, ?_⟩
  exact hV

end SampleReuse.RandomFrame
