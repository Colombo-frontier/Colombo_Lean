import Bilevel.ChiUniformActivationLengths
import Bilevel.ChiDepthLogBound

/-! Cancellation of the independent macro width and base resolution in
the actual finite activation count. No oracle query bound is asserted. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths
open ChiCurvatureSchedule ChiExtensionCalibration

theorem resolution_product_cancellation {cn t η : ℝ} (hη : 0<η) (J : ℕ) :
    (t*η)^(2*J)*(cn/(2*η^2))^J=(cn*t^2/2)^J := by
  rw [pow_mul,← mul_pow]
  congr 1
  field_simp
  ring

theorem middle_count_scale_identity {cS cn Δ L₀ Cb ε K t η a : ℝ}
    (hL : 0<L₀) (hCb : 0<Cb) (hε : 0<ε) (_hK : 0<K)
    (_ht : 0<t) (hη : 0<η) (J : ℕ) :
    (cS*cn*Δ/(4*L₀*(middleWidth Cb ε K L₀ (t*η) J)^2))*((cn/(2*η^2))^J*a)=
      (cS*cn/(4*Cb^2))*a*K^2*L₀*Δ/ε^2*(cn*t^2/2)^J := by
  have he : (cS*cn*Δ/(4*L₀*(middleWidth Cb ε K L₀ (t*η) J)^2))*((cn/(2*η^2))^J*a)=
      ((cS*cn/(4*Cb^2))*a*K^2*L₀*Δ/ε^2)*((t*η)^(2*J)*(cn/(2*η^2))^J) := by
    unfold middleWidth
    rw [show (t*η)^(2*J)=((t*η)^J)^2 by rw [Nat.mul_comm 2 J,pow_mul]]
    field_simp
    ring
  rw [he,resolution_product_cancellation hη J]

theorem activationCount_physical_lower {cS cn Δ L₀ b Cb ε K t η T : ℝ}
    (hcn : 0<cn) (hL : 0<L₀) (hb : 0<b) (hCb : 0<Cb) (hε : 0<ε)
    (hK : 0<K) (ht : 0<t) (hη : 0<η) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (J : ℕ)
    (hmacro : 2≤cS*Δ/(L₀*b^2))
    (hmiddle : 2≤cn*b^2/(middleWidth Cb ε K L₀ (t*η) J)^2) :
    (cS*cn/(4*Cb^2))*curvature T J*K^2*L₀*Δ/ε^2*(cn*t^2/2)^J≤
      (activationCount cS cn Δ L₀ b (middleWidth Cb ε K L₀ (t*η) J) η T J:ℝ) := by
  have hh : 0<middleWidth Cb ε K L₀ (t*η) J := by unfold middleWidth; positivity
  have hc := activationCount_lower hcn hL hb hh hT hlen hmacro hmiddle J
  rw [middle_count_scale_identity hL hCb hε hK ht hη J] at hc
  exact hc

end Bilevel.ChiIndependentWidths
