import Bilevel.ChiUniformActivationScales

/-! A fixed logarithmic loss for the actual recursive activation count.
This is finite-length arithmetic, not an information lower bound. -/
noncomputable section
namespace Bilevel.ChiIndependentWidths
open ChiCurvatureSchedule ChiExtensionCalibration

theorem exists_curvature_activation_log_factor {CT β : ℝ} (hCT : 1≤CT) (hβ : 0<β) :
    ∃ c : ℝ,0<c ∧ ∃ q : ℕ,∀ θ : ℝ,1≤θ → 1≤scale θ CT 6 →
      c*(1+θ)≤curvature (scale θ CT 6) (chosenDepth θ)*β^chosenDepth θ*
        (Real.log (2+θ))^q := by
  have hCTp : 0<CT := by linarith
  obtain ⟨q,hq⟩ := exists_depth_polynomial_log_bound (div_pos hCTp hβ).le 6
  refine ⟨Real.exp (-4)/(128*CT),by positivity,q+6,?_⟩
  intro θ hθ hT
  let J := chosenDepth θ
  let a := curvature (scale θ CT 6) J
  let ℓ := (Real.log (2+θ))^(q+6)
  have ha : 0<a := curvature_pos (lt_of_lt_of_le zero_lt_one hT) J
  have hden : 0<CT^(J+1)*((J:ℝ)+1)^6 := by positivity
  have hc := actual_final_curvature hθ hCT 6 hT
  change Real.exp (-4)*(θ/(CT^(J+1)*((J:ℝ)+1)^6))≤a at hc
  have hc' : Real.exp (-4)*θ≤a*(CT^(J+1)*((J:ℝ)+1)^6) := by
    apply (div_le_iff₀ hden).mp
    simpa only [mul_div_assoc] using hc
  have hd := mul_le_mul_of_nonneg_left (hq θ hθ) (show 0≤CT*a*β^J by positivity)
  change (CT*a*β^J)*((CT/β)^J*((J:ℝ)+1)^6)≤
    (CT*a*β^J)*(2^6*ℓ) at hd
  have he : (CT*a*β^J)*((CT/β)^J*((J:ℝ)+1)^6)=
      a*(CT^(J+1)*((J:ℝ)+1)^6) := by
    rw [div_pow,pow_succ]
    field_simp
    ring
  rw [he] at hd
  have hθ' : Real.exp (-4)*(1+θ)≤2*(Real.exp (-4)*θ) := by
    have hp := Real.exp_pos (-4)
    nlinarith only [hθ,hp]
  have hbound : Real.exp (-4)*(1+θ)≤128*CT*(a*β^J*ℓ) := by
    nlinarith only [hc',hd,hθ']
  change (Real.exp (-4)/(128*CT))*(1+θ)≤a*β^J*ℓ
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm (128*CT)] using hbound)

theorem activationCount_from_stage_bound {cS cn Δ L₀ b Cb ε K t η T : ℝ}
    (hcn : 0≤cn) (hL : 0<L₀) (hCb : 0<Cb) (hε : 0<ε)
    (hK : 0<K) (ht : 0<t) (hη : 0<η) (hT : 1≤T)
    (hlen : 128≤cn/η^2) (J : ℕ)
    (hstage : cS*cn*Δ/(4*L₀*(middleWidth Cb ε K L₀ (t*η) J)^2)≤
      ((macroLength cS Δ L₀ b*middleLength cn b (middleWidth Cb ε K L₀ (t*η) J):ℕ):ℝ)) :
    (cS*cn/(4*Cb^2))*curvature T J*K^2*L₀*Δ/ε^2*(cn*t^2/2)^J≤
      (activationCount cS cn Δ L₀ b (middleWidth Cb ε K L₀ (t*η) J) η T J:ℝ) := by
  have hh := higherCount_lower hcn hT hlen J
  have ha := curvature_pos (lt_of_lt_of_le zero_lt_one hT) J
  have hm := mul_le_mul hstage hh (show 0≤(cn/(2*η^2))^J*curvature T J by positivity)
    (Nat.cast_nonneg (macroLength cS Δ L₀ b*middleLength cn b (middleWidth Cb ε K L₀ (t*η) J)))
  rw [middle_count_scale_identity hL hCb hε hK ht hη J] at hm
  simpa only [activationCount,Nat.cast_mul] using hm

theorem exists_activation_log_rate {cS cn η₀ Cb t η CT : ℝ}
    (hcS : 0<cS) (hcn : 0<cn) (hη₀ : 0<η₀) (hCb : 0<Cb)
    (ht : 0<t) (hη : 0<η) (hCT : 1≤CT) (hlen : 128≤cn/η^2) :
    ∃ c : ℝ,0<c ∧ ∃ q : ℕ,
      ∀ L Δ κ θ ε b : ℝ,0<L → 0<Δ → 0<κ → 1≤θ → 0<ε → 1≤scale θ CT 6 →
      let J := chosenDepth θ
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      cS*cn*Δ/(4*(η₀*L)*h^2)≤((macroLength cS Δ (η₀*L) b*middleLength cn b h:ℕ):ℝ) →
      c*L*(1+θ)*κ^2*Δ/(ε^2*(Real.log (2+θ))^q)≤
        (activationCount cS cn Δ (η₀*L) b h η (scale θ CT 6) J:ℝ) := by
  obtain ⟨cd,hcd,q,hq⟩ := exists_curvature_activation_log_factor hCT
    (show 0<cn*t^2/2 by positivity)
  refine ⟨(cS*cn*η₀/(144*Cb^2))*cd,by positivity,q,?_⟩
  intro L Δ κ θ ε b hL hΔ hκ hθ hε hT
  dsimp only
  intro hstage
  let J := chosenDepth θ
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  let N := activationCount cS cn Δ (η₀*L) b h η (scale θ CT 6) J
  have hlog : 0<Real.log (2+θ) := Real.log_pos (by linarith)
  have hn := activationCount_from_stage_bound hcn.le (mul_pos hη₀ hL) hCb hε
    (show 0<κ/6 by positivity) ht hη hT hlen J hstage
  change (cS*cn/(4*Cb^2))*curvature (scale θ CT 6) J*(κ/6)^2*(η₀*L)*Δ/ε^2*
    (cn*t^2/2)^J≤(N:ℝ) at hn
  have hd := mul_le_mul_of_nonneg_left (hq θ hθ hT)
    (show 0≤(cS*cn*η₀/(144*Cb^2))*L*κ^2*Δ/ε^2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hn
    (show 0≤(Real.log (2+θ))^q by positivity)
  have hbound : ((cS*cn*η₀/(144*Cb^2))*cd)*L*(1+θ)*κ^2*Δ/ε^2≤
      (N:ℝ)*(Real.log (2+θ))^q := by
    calc
      _ = ((cS*cn*η₀/(144*Cb^2))*L*κ^2*Δ/ε^2)*(cd*(1+θ)) := by ring
      _ ≤ _ := hd
      _ = ((cS*cn/(4*Cb^2))*curvature (scale θ CT 6) J*(κ/6)^2*(η₀*L)*Δ/ε^2*
        (cn*t^2/2)^J)*(Real.log (2+θ))^q := by ring
      _ ≤ _ := hm
  rw [← div_div]
  exact (div_le_iff₀ (by positivity)).mpr hbound

end Bilevel.ChiIndependentWidths
