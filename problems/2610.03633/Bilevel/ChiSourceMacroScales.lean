import Bilevel.ChiAccuracyCalibration

/-! Exact source margin and energy identities. The gap calculation uses
the sqrt(L*Delta) side of the source accuracy window. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem source_margin_identity {Cb ε η₀ L t η : ℝ}
    (hη₀ : 0 < η₀) (hL : 0 < L) (ht : 0 < t) (hη : 0 < η) (J : ℕ) :
    t^(J+1)*(η^J*((η₀*L)*sourceWidth Cb ε η₀ L t η J))/4 = t*Cb*ε/4 := by
  unfold sourceWidth
  rw [pow_succ,mul_pow]
  field_simp
  ring

theorem source_margin_ge_eight {Cb ε η₀ L t η : ℝ}
    (hη₀ : 0 < η₀) (hL : 0 < L) (ht : 0 < t) (hη : 0 < η)
    (hCb : 32/t ≤ Cb) (hε : 0 ≤ ε) (J : ℕ) :
    8*ε ≤ t^(J+1)*(η^J*((η₀*L)*sourceWidth Cb ε η₀ L t η J))/4 := by
  rw [source_margin_identity hη₀ hL ht hη]
  have hcoef := (div_le_iff₀ ht).mp hCb
  have hh := mul_le_mul_of_nonneg_right hcoef hε
  nlinarith only [hh]

theorem source_energy_formula {Cb ε η₀ L t η : ℝ}
    (hη₀ : 0 < η₀) (hL : 0 < L) (ht : 0 < t) (hη : 0 < η) (J : ℕ) :
    (η₀*L)*(sourceWidth Cb ε η₀ L t η J)^2 = Cb^2*ε^2/(η₀*L*(t*η)^(2*J)) := by
  unfold sourceWidth
  rw [show 2*J=J*2 by omega,pow_mul]
  field_simp
  ring

theorem source_energy_window {Cb ε η₀ L t η c Cacc κ θ Δ : ℝ}
    (_hCb : 0 ≤ Cb) (hε : 0 ≤ ε) (hη₀ : 0 < η₀) (hL : 0 < L)
    (ht : 0 < t) (hη : 0 < η) (hc : 0 ≤ c) (hCacc : 0 < Cacc) (hΔ : 0 ≤ Δ)
    (habsorb : 1 ≤ Cacc*(t*η)) (J q : ℕ)
    (hwindow : ε ≤ accuracyWindow c Cacc L κ θ Δ J q) :
    (η₀*L)*(sourceWidth Cb ε η₀ L t η J)^2 ≤ Cb^2*c^2*Δ/η₀ := by
  have hmin := mul_le_mul_of_nonneg_left (min_le_right (L/(κ*θ)) (Real.sqrt (L*Δ)))
    (show 0 ≤ c/(Cacc^J*((J:ℝ)+1)^q) by positivity)
  have he : ε ≤ c*Real.sqrt (L*Δ)/(Cacc^J*((J:ℝ)+1)^q) :=
    hwindow.trans (hmin.trans_eq (by ring))
  have hdepth : 1 ≤ ((J:ℝ)+1)^q := one_le_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) J; linarith)
  have hden : 1 ≤ Cacc^J*((J:ℝ)+1)^q*(t*η)^J := by
    have hh := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (n:=J) habsorb) hdepth
    convert hh using 1
    ring
  have hscaled : ε/(t*η)^J ≤ c*Real.sqrt (L*Δ) := by
    calc
      _ ≤ (c*Real.sqrt (L*Δ)/(Cacc^J*((J:ℝ)+1)^q))/(t*η)^J :=
        div_le_div_of_nonneg_right he (by positivity)
      _ = c*Real.sqrt (L*Δ)/(Cacc^J*((J:ℝ)+1)^q*(t*η)^J) := by ring
      _ ≤ _ := div_le_self (by positivity) hden
  have hsq := mul_self_le_mul_self (show 0 ≤ ε/(t*η)^J by positivity) hscaled
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ Cb^2/(η₀*L) by positivity)
  have hsqrt : (Real.sqrt (L*Δ))^2 = L*Δ := Real.sq_sqrt (mul_nonneg hL.le hΔ)
  have hsqrt' : Real.sqrt (L*Δ)*Real.sqrt (L*Δ) = L*Δ := by nlinarith only [hsqrt]
  have hh := hm
  rw [show c*Real.sqrt (L*Δ)*(c*Real.sqrt (L*Δ)) = c^2*(Real.sqrt (L*Δ)*Real.sqrt (L*Δ)) by ring,hsqrt'] at hh
  convert hh using 1
  · unfold sourceWidth
    field_simp
    ring
  · field_simp
    ring

end Bilevel.ChiExtensionCalibration
