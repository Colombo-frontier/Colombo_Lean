import Bilevel.ChiUniformActivationWindow
import Bilevel.EndpointTransportGainCalibration
import Bilevel.ChiRefinementRates

/-! Actual recursive activation lengths at the physical gain, multiplied
by the actual number of transport layers. This is finite-count arithmetic;
the original-SFO information theorem is a separate obligation. -/
noncomputable section
namespace Bilevel.EndpointTransportNormalization
open ChiIndependentWidths ChiCurvatureSchedule

theorem transport_activation_count_certificate {cS cn η₀ bStar Cb t η CT cold : ℝ}
    (hcS : 0<cS) (hcn : 0<cn) (hη₀ : 0<η₀) (hη₀1 : η₀≤1) (hb : 0<bStar)
    (hCb : 0<Cb) (ht : 0<t) (hη : 0<η) (hCT : 1≤CT)
    (hlen : 128≤cn/η^2) (hmacro : bStar^2≤cS/128) (hcold : 0<cold) :
    ∃ c cRate : ℝ,0<c ∧ c≤1 ∧ c≤cold ∧ 0<cRate ∧ ∃ q : ℕ,
      ∀ L Δ κ θ ε : ℝ,0<L → 0<Δ → 3200≤κ → 1≤θ → θ≤κ^2 → 0<ε →
      1≤scale θ CT 6 → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (gain κ) (η₀*L) (t*η) J
      5≤layers κ ∧ 64≤macroLength cS Δ (η₀*L) b ∧ 64≤middleLength cn b h ∧
      cRate*ChiRefinementRates.deterministic L θ κ Δ ε/(Real.log (2+θ))^q≤
        ((layers κ*activationCount cS cn Δ (η₀*L) b h η (scale θ CT 6) J:ℕ):ℝ) := by
  obtain ⟨c,cN,hc,hc1,hccold,hcN,q,hcount⟩ := uniform_activation_count_certificate
    hcS hcn hη₀ hη₀1 hb hCb ht hη hCT hlen hmacro hcold
  have hsqrt : 0<Real.sqrt (128:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨c/32,cN/(2048*Real.sqrt 128),by positivity,by linarith,
    (by linarith),by positivity,q,?_⟩
  intro L Δ κ θ ε hL hΔ hκ hθ hθκ hε hT hacc
  dsimp only
  let J := chosenDepth θ
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth Cb ε (gain κ) (η₀*L) (t*η) J
  let N := activationCount cS cn Δ (η₀*L) b h η (scale θ CT 6) J
  let e := calibrationAccuracy κ ε
  have hep : 0<e := calibrationAccuracy_pos hκ hε
  have hemax : e≤32*ε := (calibrationAccuracy_bounds hκ hε.le).2
  have hlog : 0<Real.log (2+θ) := Real.log_pos (by linarith)
  have hh := hcount L Δ κ θ e hL hΔ (by linarith) hθ hθκ hep hT
    (calibration_accuracy_window hκ hε.le hacc)
  dsimp only at hh
  rw [calibration_middleWidth hκ] at hh
  refine ⟨layers_ge_five hκ,hh.1,hh.2.1,?_⟩
  have hsquare : e^2≤1024*ε^2 := by nlinarith only [hemax,hep,hε]
  have hn : (cN/1024)*L*(1+θ)*κ^2*Δ/(ε^2*(Real.log (2+θ))^q)≤(N:ℝ) := by
    apply le_trans _ hh.2.2
    have hd : e^2*(Real.log (2+θ))^q≤1024*ε^2*(Real.log (2+θ))^q :=
      mul_le_mul_of_nonneg_right hsquare (by positivity)
    have hv := div_le_div_of_nonneg_left
      (show 0≤cN*L*(1+θ)*κ^2*Δ by positivity) (by positivity : 0<e^2*(Real.log (2+θ))^q) hd
    convert hv using 1
    ring
  have hm := mul_le_mul (layers_sqrt_kappa_bounds hκ).1 hn
    (show 0≤(cN/1024)*L*(1+θ)*κ^2*Δ/(ε^2*(Real.log (2+θ))^q) by positivity)
    (Nat.cast_nonneg (layers κ))
  rw [Nat.cast_mul]
  apply le_trans _ hm
  dsimp only [ChiRefinementRates.deterministic]
  apply le_of_eq
  ring

end Bilevel.EndpointTransportNormalization
