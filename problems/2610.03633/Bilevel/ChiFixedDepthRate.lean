import Bilevel.ChiUniformSignalRate
import Bilevel.ChiUniformProbabilityRate

/-! Fixed-depth activation and informative-amplitude bounds. These are
rates for actual finite source lengths and actual Bernoulli samples;
their conversion to oracle-query lower bounds is separate. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiBoundedChain ChiIndependentWidths ChiCurvatureSchedule

def fixedSignalCoefficient (Bs Cf t Cb cms : ℝ) : ℝ :=
  27648*SmallGapLiftSupport.C*Real.exp 2*cms*Bs^3*Cf^2*Cb^2/t^2

theorem fixedSignalCoefficient_pos {Bs Cf t Cb cms : ℝ}
    (hBs : 0<Bs) (hCf : 0<Cf) (ht : 0<t) (hCb : 0<Cb) (hcms : 0<cms) :
    0<fixedSignalCoefficient Bs Cf t Cb cms := by
  have hC := SmallGapLiftSupport.C_pos
  unfold fixedSignalCoefficient
  positivity

theorem fixed_source_signal_rate {Bs Cf t Cb cms η η₀ : ℝ}
    (hBs : 0<Bs) (hCf : 0<Cf) (ht : 0<t) (hCb : 0<Cb) (hcms : 0<cms)
    (hη : 0<η) (hη₀ : 0<η₀)
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L μ κ ε b A Kminus ζ cn CR : ℝ) (weight : ℕ → ℝ)
    (hL : 0<L) (hμ : 0<μ) (hκ : 0<κ) (hκeq : κ=L/μ) (hε : 0<ε) (hb : 0<b) :
    let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1
    let Kg := b/h
    let initial : Scale := ⟨η₀*L,b⟩
    ∀ (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
    let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
    let v := fineParameter μ (3*μ/2) (D 1 []).ell (normalCoefficient L 1) Cf 1
    1≤v →
    let W := ZeroChainSchedule.width cms (D 1 []).width v (ZeroChainSchedule.levels v)
    4*μ*(2*SmallGapLiftSupport.C*Bs^3*(D 1 []).ell*(D 1 []).width*W/normalCoefficient L 1)≤
      fixedSignalCoefficient Bs Cf t Cb cms*ε^2/(L*κ^3) := by
  dsimp only
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  intro V
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
  intro hv
  have hK : 0<κ/6 := by positivity
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKg : 0<Kg := div_pos hb hhp
  have hp := parentScale_positive initial (sourceRatio 1) (resolution η Kg)
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one le_rfl) (base_resolution_positive hη hKg) 2
  have hell : 0<(D 1 []).ell := hp.1
  have hβ : 0<(D 1 []).width := hp.2
  have hforce : (D 1 []).ell*(D 1 []).width=Cb*ε/((κ/6)*t^1) :=
    independent_source_force hK (mul_pos hη₀ hL) ht hη hb le_rfl 1
  have hμeq : μ=L/κ := by
    apply (eq_div_iff hκ.ne').mpr
    rw [hκeq]
    field_simp
  have hh := fine_informative_source_rate hL hμ hκ (by norm_num : (0:ℝ)<1)
    hell hβ hCf hcms hBs.le ht hμeq 1 (by omega) hforce (by simpa only [one_mul] using hv)
  simp only [one_mul] at hh
  apply hh.trans_eq
  unfold fixedSignalCoefficient
  norm_num
  ring

theorem fixed_activation_rate {Cgap cn η₀ Cb t η L Δ κ ε b : ℝ}
    (_hCg : 0<Cgap) (hcn : 0<cn) (hη₀ : 0<η₀) (hCb : 0<Cb)
    (ht : 0<t) (hη : 0<η) (hL : 0<L) (hε : 0<ε) (hκ : 0<κ)
    (hlen : 128≤cn/η^2)
    (hstage : cn*Δ/(8*Cgap*(η₀*L)*(middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1)^2)≤
      ((macroLength (1/(2*Cgap)) Δ (η₀*L) b*
        middleLength cn b (middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1):ℕ):ℝ)) :
    (cn^2*η₀*t^2/(576*Cgap*Cb^2))*L*κ^2*Δ/ε^2≤
      (activationCount (1/(2*Cgap)) cn Δ (η₀*L) b
        (middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1) η 1 1:ℝ) := by
  have hs : (1/(2*Cgap))*cn*Δ/(4*(η₀*L)*(middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1)^2)≤
      ((macroLength (1/(2*Cgap)) Δ (η₀*L) b*
        middleLength cn b (middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1):ℕ):ℝ) := by
    convert hstage using 1
    ring
  have hh := activationCount_from_stage_bound hcn.le (mul_pos hη₀ hL) hCb hε
    (show 0<κ/6 by positivity) ht hη (by norm_num : (1:ℝ)≤1) hlen 1 hs
  apply le_trans _ hh
  simp only [curvature,Real.one_rpow,pow_one,mul_one]
  exact le_of_eq (by ring)

theorem fixed_probability_rate {N : ℕ} {c C L κ Δ ε σ B : ℝ}
    (hc : 0<c) (hC : 1≤C) (hL : 0<L) (hκ : 0<κ) (hΔ : 0<Δ) (hε : 0<ε) (hB : 0<B)
    (hcount : c*L*κ^2*Δ/ε^2≤(N:ℝ)) (hsignal : B≤C*ε^2/(L*κ^3)) :
    (c/C^2)*(L*κ^2*Δ/ε^2+L^3*κ^8*σ^2*Δ/ε^6)≤
      (N:ℝ)*(BernoulliOracle.probability B σ)⁻¹ := by
  have hn : (c/2)*L*(1+(1:ℝ))*κ^2*Δ/(ε^2*(Real.log (2+(1:ℝ)))^0)≤(N:ℝ) := by
    convert hcount using 1
    ring
  have hs : B≤C*(Real.log (2+(1:ℝ)))^0*ε^2/(L*(1:ℝ)*κ^3) := by simpa using hsignal
  have hh := count_times_inverse_probability (σ:=σ) (qN:=0) (qB:=0)
    (show 0<c/2 by positivity) hC hL (by norm_num : (1:ℝ)≤1) hκ hΔ hε hB hn hs
  convert hh using 1
  norm_num
  ring

end Bilevel.ChiExtensionCalibration
