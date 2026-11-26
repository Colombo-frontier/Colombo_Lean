import Bilevel.ChiFixedDepthRate

/-! Fixed-depth variable-theta informative amplitude and probability
arithmetic for the actual conservative source oracle. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiBoundedChain ChiIndependentWidths ChiCurvatureSchedule

theorem fixed_variable_source_signal_rate {Bs Cf t Cb cms η η₀ : ℝ}
    (hBs : 0<Bs) (hCf : 0<Cf) (ht : 0<t) (hCb : 0<Cb) (hcms : 0<cms)
    (hη : 0<η) (hη₀ : 0<η₀)
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L μ θ κ ε b A Kminus ζ cn CR : ℝ) (weight : ℕ → ℝ)
    (hL : 0<L) (hμ : 0<μ) (hθ : 0<θ) (hκ : 0<κ) (hκeq : κ=L/μ) (hε : 0<ε) (hb : 0<b) :
    let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) 1
    let Kg := b/h
    let initial : Scale := ⟨η₀*L,b⟩
    ∀ (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
    let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A Kminus ζ cn CR V
    let v := fineParameter (θ*μ) (3*μ/2) (D 1 []).ell (normalCoefficient L 1) Cf 1
    1≤v →
    let W := ZeroChainSchedule.width cms (D 1 []).width v (ZeroChainSchedule.levels v)
    4*μ*(2*SmallGapLiftSupport.C*Bs^3*(D 1 []).ell*(D 1 []).width*W/normalCoefficient L 1)≤
      fixedSignalCoefficient Bs Cf t Cb cms*ε^2/(L*θ*κ^3) := by
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
  have hh := fine_informative_source_rate hL hμ hκ hθ
    hell hβ hCf hcms hBs.le ht hμeq 1 (by omega) hforce hv
  simp only [one_mul] at hh
  apply hh.trans_eq
  unfold fixedSignalCoefficient
  norm_num
  ring


theorem fixed_variable_probability_rate {N : ℕ} {c C L θ κ Δ ε σ B : ℝ}
    (hc : 0<c) (hC : 1≤C) (hL : 0<L) (hθ : 1≤θ) (hκ : 0<κ)
    (hΔ : 0<Δ) (hε : 0<ε) (hB : 0<B)
    (hcount : c*L*κ^2*Δ/ε^2≤(N:ℝ)) (hsignal : B≤C*ε^2/(L*θ*κ^3)) :
    (c/C^2)*(L*κ^2*Δ/ε^2+L^3*θ^2*κ^8*σ^2*Δ/ε^6)≤
      (N:ℝ)*(BernoulliOracle.probability B σ)⁻¹ := by
  have hpos : 0<1+θ := by linarith
  have hn : (c/(1+θ))*L*(1+θ)*κ^2*Δ/(ε^2*(Real.log (2+θ))^0)≤(N:ℝ) := by
    convert hcount using 1
    field_simp
  have hs : B≤C*(Real.log (2+θ))^0*ε^2/(L*θ*κ^3) := by simpa using hsignal
  have hh := count_times_inverse_probability (σ:=σ) (qN:=0) (qB:=0)
    (div_pos hc hpos) hC hL hθ hκ hΔ hε hB hn hs
  convert hh using 1
  norm_num
  field_simp
  ring

end Bilevel.ChiExtensionCalibration
