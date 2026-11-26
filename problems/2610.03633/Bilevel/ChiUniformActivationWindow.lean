import Bilevel.ChiUniformActivationRate
import Bilevel.ChiUniformEncodedCount

/-! A budget-independent full accuracy window for the actual activation
count, retaining any previously selected accuracy constant. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths
open ChiCurvatureSchedule

theorem uniform_activation_count_certificate {cS cn η₀ bStar Cb t η CT cold : ℝ}
    (hcS : 0<cS) (hcn : 0<cn) (hη₀ : 0<η₀) (hη₀1 : η₀≤1) (hb : 0<bStar)
    (hCb : 0<Cb) (ht : 0<t) (hη : 0<η) (hCT : 1≤CT)
    (hlen : 128≤cn/η^2) (hmacro : bStar^2≤cS/128) (hcold : 0<cold) :
    ∃ c cN : ℝ,0<c ∧ c≤1 ∧ c≤cold ∧ 0<cN ∧ ∃ q : ℕ,
      ∀ L Δ κ θ ε : ℝ,0<L → 0<Δ → 2≤κ → 1≤θ → θ≤κ^2 → 0<ε →
      1≤scale θ CT 6 → ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := chosenDepth θ
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      64≤macroLength cS Δ (η₀*L) b ∧ 64≤middleLength cn b h ∧
      cN*L*(1+θ)*κ^2*Δ/(ε^2*(Real.log (2+θ))^q)≤
        (activationCount cS cn Δ (η₀*L) b h η (scale θ CT 6) J:ℝ) := by
  obtain ⟨cN,hcN,q,hq⟩ := exists_activation_log_rate hcS hcn hη₀ hCb ht hη hCT hlen
  let cFloor := accuracyConstant η₀ bStar cn ((1/6)*depthGain (t*η)) Cb
  let c := min 1 (min cold cFloor)
  have hcf : 0<cFloor := uniform_accuracy_constant_pos hη₀ hb hcn (by norm_num) hCb
  have hc : 0<c := by dsimp [c]; positivity
  have hcle : c≤cFloor := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,cN,hc,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),hcN,q,?_⟩
  intro L Δ κ θ ε hL hΔ hκ hθ hθκ hε hT hacc
  dsimp only
  have hacc' := hacc.trans (mul_le_mul_of_nonneg_right hcle
    (show 0≤min L (Real.sqrt (L*Δ)) by positivity))
  obtain ⟨hS,hn,hstage⟩ := uniform_floor_certificate hL hΔ hη₀ hη₀1 hb hcn
    (by norm_num : (0:ℝ)<1/6) hCb hκ hθ hθκ
    (show (1/6)*κ≤κ/6 by ring_nf; rfl) (mul_pos ht hη) hε hmacro hacc'
  refine ⟨hS,hn,?_⟩
  exact hq L Δ κ θ ε (macroWidth bStar Δ (η₀*L)) hL hΔ (by linarith) hθ hε hT hstage

end Bilevel.ChiIndependentWidths
