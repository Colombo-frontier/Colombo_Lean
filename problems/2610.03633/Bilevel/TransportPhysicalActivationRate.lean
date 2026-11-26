import Bilevel.EndpointTransportActivationRate
import Bilevel.ChiSourceCapacity
import Bilevel.EndpointTransportGainCalibration
import Bilevel.ChiRefinementRates

/-! Actual recursive activation lengths at the physical gain, multiplied
by the actual number of transport layers. This is finite-count arithmetic;
the original-SFO information theorem is a separate obligation. -/
noncomputable section
namespace Bilevel.EndpointTransportNormalization
open ChiIndependentWidths ChiCurvatureSchedule
set_option autoImplicit false

theorem transport_actual_expected_count_certificate {cS cn η₀ bStar Cb t η CT cold : ℝ}
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
        (((interiors κ+1)*ChiTreeProgress.capacity
          (ChiTreeProgress.sourceCounts (macroLength cS Δ (η₀*L) b-1) cn
            (ChiExtensionCalibration.sourceRatio (scale θ CT 6)) (ChiRecursive.resolution η (b/h))) (J+1) 0:ℕ):ℝ)/512 := by
  obtain ⟨c,cRate,hc,hc1,hccold,hcRate,q,hmain⟩ := transport_activation_count_certificate
    hcS hcn hη₀ hη₀1 hb hCb ht hη hCT hlen hmacro hcold
  refine ⟨c,cRate/1024,hc,hc1,hccold,by positivity,q,?_⟩
  intro L Δ κ θ ε hL hΔ hκ hθ hθκ hε hT hacc
  have h := hmain L Δ κ θ ε hL hΔ hκ hθ hθκ hε hT hacc
  dsimp only at h ⊢
  let J := chosenDepth θ
  let b := macroWidth bStar Δ (η₀*L)
  let w := middleWidth Cb ε (gain κ) (η₀*L) (t*η) J
  have hbpos : 0<b := macroWidth_pos hb hΔ (mul_pos hη₀ hL)
  have hgain := gain_pos hκ
  have hwpos : 0<w := by dsimp [w,middleWidth];positivity
  have hcap := ChiTreeProgress.source_capacity_activation hcn.le hbpos hwpos hT hlen
    ((by norm_num : 1≤(64:ℕ)).trans h.2.1) ((by norm_num : 1≤(64:ℕ)).trans h.2.2.1) J
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  rw [hcap]
  let N := activationCount cS cn Δ (η₀*L) b w η (scale θ CT 6) J
  have hlayer : layers κ≤2*(interiors κ+1) := by
    have hi := interiors_add_two hκ
    omega
  have hm : ((layers κ*N:ℕ):ℝ)≤2*(((interiors κ+1)*N:ℕ):ℝ) := by
    exact_mod_cast (show layers κ*N≤2*((interiors κ+1)*N) by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right N hlayer)
  have hd := div_le_div_of_nonneg_right (h.2.2.2.trans hm) (by norm_num : (0:ℝ)≤1024)
  convert hd using 1 <;> ring

end Bilevel.EndpointTransportNormalization
