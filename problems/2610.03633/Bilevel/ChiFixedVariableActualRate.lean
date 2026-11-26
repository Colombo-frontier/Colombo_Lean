import Bilevel.ChiFixedVariableRate
import Bilevel.ChiUniformEncodedCount

/-! Actual fixed-depth source geometry and actual oracle probability.
The scalar count remains separate from the adaptive information theorem. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiBoundedChain ChiIndependentWidths

set_option maxHeartbeats 500000 in
theorem fixed_variable_actual_probability_rate {Bs Cf t Cb cms η η₀ Cgap cn : ℝ}
    (hBs : 0<Bs) (hCf : 0<Cf) (ht : 0<t) (hCb : 0<Cb) (hcms : 0<cms)
    (hη : 0<η) (hη₀ : 0<η₀) (hCg : 0<Cgap) (hcn : 0<cn) (hlen : 128≤cn/η^2)
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L μ θ κ Δ ε σ b A Kminus ζ CR : ℝ) (weight : ℕ → ℝ)
    (hL : 0<L) (hμ : 0<μ) (hθ : 1≤θ) (hκ : 0<κ) (hκeq : κ=L/μ) (hΔ : 0<Δ) (hε : 0<ε) (hb : 0<b) :
    let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1
    let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
    let N := activationCount (1/(2*Cgap)) cn Δ (η₀*L) b h η 1 1
    cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) →
    let Kg := b/h
    let initial : Scale := ⟨η₀*L,b⟩
    ∀ (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
    let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
    let v := fineParameter (θ*μ) (3*μ/2) (D 1 []).ell (normalCoefficient L 1) Cf 1
    1≤v →
    let W := ZeroChainSchedule.width cms (D 1 []).width v (ZeroChainSchedule.levels v)
    let B := 4*μ*(2*SmallGapLiftSupport.C*Bs^3*(D 1 []).ell*(D 1 []).width*W/normalCoefficient L 1)
    let C := max 1 (fixedSignalCoefficient Bs Cf t Cb cms)
    0<B ∧ B≤C*ε^2/(L*θ*κ^3) ∧
    ((cn^2*η₀*t^2/(576*Cgap*Cb^2))/C^2)*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6)≤
      (N:ℝ)*(BernoulliOracle.probability B σ)⁻¹ := by
  dsimp only
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  intro hstage V hv
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
  let v := fineParameter (θ*μ) (3*μ/2) (D 1 []).ell (normalCoefficient L 1) Cf 1
  let W := ZeroChainSchedule.width cms (D 1 []).width v (ZeroChainSchedule.levels v)
  let B := 4*μ*(2*SmallGapLiftSupport.C*Bs^3*(D 1 []).ell*(D 1 []).width*W/normalCoefficient L 1)
  let C := max 1 (fixedSignalCoefficient Bs Cf t Cb cms)
  have hK : 0<κ/6 := by positivity
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKg : 0<Kg := div_pos hb hhp
  have hp := parentScale_positive initial (sourceRatio 1) (resolution η Kg)
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one le_rfl) (base_resolution_positive hη hKg) 2
  have hell : 0<(D 1 []).ell := hp.1
  have hβ : 0<(D 1 []).width := hp.2
  have hW : 0<W := ZeroChainSchedule.width_pos cms (D 1 []).width v hcms hβ hv _
  have hdn : 0<normalCoefficient L 1 := normalCoefficient_pos hL (by omega)
  have hnormal := SmallGapLiftSupport.C_pos
  have hB : 0<B := by dsimp [B]; positivity
  have hs := fixed_variable_source_signal_rate hBs hCf ht hCb hcms hη hη₀ F L μ θ κ ε b A Kminus ζ cn CR weight
    hL hμ (by linarith only [hθ]) hκ hκeq hε hb V hv
  have hsig : B≤C*ε^2/(L*θ*κ^3) := hs.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ε)) (by positivity))
  have hn := fixed_activation_rate hCg hcn hη₀ hCb ht hη hL hε hκ hlen hstage
  exact ⟨hB,hsig,fixed_variable_probability_rate (by positivity) (le_max_left _ _) hL hθ hκ hΔ hε hB hn hsig⟩

end Bilevel.ChiExtensionCalibration
