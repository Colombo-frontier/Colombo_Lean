import Bilevel.ChiUniformProbabilityRate

/-! Actual source lengths and actual full informative radius give the
deterministic-plus-lower-noise rate algebra on the full public window.
This theorem does not identify the count with oracle queries. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths
open ChiCurvatureSchedule ChiExtensionCalibration ChiRecursive ChiBoundedChain

theorem uniform_actual_probability_rate {cS cn η₀ bStar Cb t η CT cold Bs Cf cms : ℝ}
    (hcS : 0<cS) (hcn : 0<cn) (hη₀ : 0<η₀) (hη₀1 : η₀≤1) (hb : 0<bStar)
    (hCb : 0<Cb) (ht : 0<t) (hη : 0<η) (hCT : 1≤CT)
    (hlen : 128≤cn/η^2) (hmacro : bStar^2≤cS/128) (hcold : 0<cold)
    (hBs : 0<Bs) (hCf : 0<Cf) (hcms : 0<cms) :
    ∃ c cRate : ℝ,0<c ∧ c≤1 ∧ c≤cold ∧ 0<cRate ∧ ∃ q : ℕ,
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (L Δ μ κ θ ε σ A Kminus ζ CR : ℝ) (weight : ℕ → ℝ),
        0<L → 0<Δ → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 → 0<ε →
        1≤scale θ CT 6 → ε≤c*min L (Real.sqrt (L*Δ)) →
        let J := chosenDepth θ
        let T := scale θ CT 6
        let b := macroWidth bStar Δ (η₀*L)
        let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
        let N := activationCount cS cn Δ (η₀*L) b h η T J
        64≤macroLength cS Δ (η₀*L) b ∧ 64≤middleLength cn b h ∧
        ∀ (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (b/h) j)) →ₗᵢ[ℝ] F),
        let D := sourceGeometry ⟨η₀*L,b⟩ (sourceRatio T) (resolution η (b/h)) weight A Kminus ζ cn CR V
        let v := fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J
        1≤J → 1≤v →
        let W := ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)
        let B := 4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*(D J []).ell*(D J []).width*W/normalCoefficient L J)
        cRate*(L*(1+θ)*κ^2*Δ/ε^2+L^3*θ^2*(1+θ)*κ^8*σ^2*Δ/ε^6)/
          (Real.log (2+θ))^q≤(N:ℝ)*(BernoulliOracle.probability B σ)⁻¹ := by
  obtain ⟨c,cN,hc,hc1,hcold',hcN,qN,hcount⟩ := uniform_activation_count_certificate hcS hcn hη₀ hη₀1 hb
    hCb ht hη hCT hlen hmacro hcold
  obtain ⟨Cs,hCs,qB,hsignal⟩ := uniform_signal_log_rate hBs hCf ht hCb hcms hη hη₀
  let C := max 1 Cs
  have hC : 1≤C := le_max_left _ _
  have hCp : 0<C := by linarith only [hC]
  refine ⟨c,cN/C^2,hc,hc1,hcold',by positivity,qN+2*qB,?_⟩
  intro F _ _ _ L Δ μ κ θ ε σ A Kminus ζ CR weight hL hΔ hμ hκ hκeq hθ hθκ hε hT hacc
  dsimp only
  let J := chosenDepth θ
  let T := scale θ CT 6
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  obtain ⟨hS,hn,hN⟩ := hcount L Δ κ θ ε hL hΔ hκ hθ hθκ hε hT hacc
  refine ⟨hS,hn,?_⟩
  intro V
  let D : Geometry F := sourceGeometry ⟨η₀*L,b⟩ (sourceRatio T) (resolution η (b/h)) weight A Kminus ζ cn CR V
  let v := fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J
  intro hJ hv
  have hκp : 0<κ := by linarith only [hκ]
  have hbp : 0<b := macroWidth_pos hb hΔ (mul_pos hη₀ hL)
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hp := parentScale_positive (⟨η₀*L,b⟩ : Scale) (sourceRatio T) (resolution η (b/h))
    (mul_pos hη₀ hL) hbp (sourceRatio_ge_one hT) (base_resolution_positive hη (div_pos hbp hhp)) (J+1)
  have hell : 0<(D J []).ell := hp.1
  have hβ : 0<(D J []).width := hp.2
  have hdn := normalCoefficient_pos hL hJ
  have hW := ZeroChainSchedule.width_pos cms (D J []).width v hcms hβ hv (ZeroChainSchedule.levels v)
  have hnormal := SmallGapLiftSupport.C_pos
  have hB : 0<4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*(D J []).ell*(D J []).width*
      ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)/normalCoefficient L J) := by positivity
  have hs := hsignal F L μ κ θ ε b T A Kminus ζ cn CR weight hL hμ hκp hκeq hθ hε hbp hT V hJ hv
  have hCsC : Cs≤C := le_max_right _ _
  have hlog : 0≤Real.log (2+θ) := Real.log_nonneg (by linarith only [hθ])
  have hsignal' := hs.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC (pow_nonneg hlog qB)) (sq_nonneg ε))
    (show 0≤L*θ*κ^3 by positivity))
  exact count_times_inverse_probability hcN hC hL hθ hκp hΔ hε hB hN hsignal'

end Bilevel.ChiIndependentWidths
