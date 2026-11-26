import Bilevel.ChiExtensionCalibration

/-! The source accuracy window absorbs the exponential depth constants
and the actual width choice. No desired analytic regularity estimate is
assumed here: the conclusions are numerical budgets for proved ledgers. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

def sourceWidth (Cb ε η₀ L t η : ℝ) (J : ℕ) : ℝ :=
  Cb*ε/((η₀*L)*(t*η)^J)

def accuracyWindow (c Cacc L κ θ Δ : ℝ) (J q : ℕ) : ℝ :=
  c/(Cacc^J*((J:ℝ)+1)^q)*min (L/(κ*θ)) (Real.sqrt (L*Δ))

theorem accuracyWindow_pos {c Cacc L κ θ Δ : ℝ}
    (hc : 0 < c) (hC : 0 < Cacc) (hL : 0 < L) (hκ : 0 < κ)
    (hθ : 0 < θ) (hΔ : 0 < Δ) (J q : ℕ) :
    0 < accuracyWindow c Cacc L κ θ Δ J q := by
  unfold accuracyWindow
  positivity

theorem sourceWidth_pos {Cb ε η₀ L t η : ℝ} (hCb : 0 < Cb) (hε : 0 < ε)
    (hη₀ : 0 < η₀) (hL : 0 < L) (ht : 0 < t) (hη : 0 < η) (J : ℕ) :
    0 < sourceWidth Cb ε η₀ L t η J := by unfold sourceWidth; positivity

theorem accuracyWindow_le_curvature {c Cacc L κ θ Δ : ℝ}
    (hc : 0 ≤ c) (hC : 0 < Cacc) (J q : ℕ) :
    accuracyWindow c Cacc L κ θ Δ J q ≤ c*L/(Cacc^J*((J:ℝ)+1)^q*κ*θ) := by
  have hh := mul_le_mul_of_nonneg_left (min_le_left (L/(κ*θ)) (Real.sqrt (L*Δ)))
    (show 0 ≤ c/(Cacc^J*((J:ℝ)+1)^q) by positivity)
  exact hh.trans_eq (by ring)

theorem sourceWidth_absorption {A Cacc Cb ε η₀ L t η c κ θ Δ : ℝ}
    (hA : 0 ≤ A) (hC : 0 < Cacc) (hCb : 0 ≤ Cb) (hη₀ : 0 < η₀)
    (hL : 0 < L) (ht : 0 < t) (hη : 0 < η) (hc : 0 ≤ c)
    (hκ : 0 < κ) (hθ : 0 < θ) (habsorb : A ≤ Cacc*t*η^2)
    (J q : ℕ) (hε : ε ≤ accuracyWindow c Cacc L κ θ Δ J q) :
    A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J/η^J ≤ A*Cb*c/(η₀*κ*θ) := by
  have he := hε.trans (accuracyWindow_le_curvature hc hC J q)
  have hpow : A^J ≤ Cacc^J*(t*η)^J*η^J := by
    have hh := pow_le_pow_left₀ hA habsorb J
    convert hh using 1
    ring
  have hratio : A^J/(Cacc^J*(t*η)^J*η^J) ≤ 1 :=
    (div_le_one (by positivity)).mpr hpow
  let Z := A^(J+1)*((J:ℝ)+1)^q*Cb/(η₀*L*(t*η)^J*η^J)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  calc
    _ = Z*ε := by dsimp only [sourceWidth,Z]; ring
    _ ≤ Z*(c*L/(Cacc^J*((J:ℝ)+1)^q*κ*θ)) := mul_le_mul_of_nonneg_left he hZ
    _ = (A*Cb*c/(η₀*κ*θ))*(A^J/(Cacc^J*(t*η)^J*η^J)) := by
      dsimp only [Z]
      have hJ : ((J:ℝ)+1) ≠ 0 := by positivity
      field_simp
      ring
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (show 0 ≤ A*Cb*c/(η₀*κ*θ) by positivity)

theorem sourceWidth_hessian_budget {A Cacc Cb ε η₀ L t η c κ θ Δ δ : ℝ}
    (hA : 0 ≤ A) (hC : 0 < Cacc) (hCb : 0 ≤ Cb) (hη₀ : 0 < η₀)
    (hL : 0 < L) (ht : 0 < t) (hη : 0 < η) (hη1 : η ≤ 1) (hc : 0 ≤ c)
    (hκ : 1 ≤ κ) (hθ : 1 ≤ θ) (hδ : 0 ≤ δ) (habsorb : A ≤ Cacc*t*η^2)
    (hsmall : A*Cb*c ≤ δ*η₀) (J q : ℕ)
    (hε : ε ≤ accuracyWindow c Cacc L κ θ Δ J q) :
    A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J ≤ δ := by
  have hb := sourceWidth_absorption hA hC hCb hη₀ hL ht hη hc
    (by linarith) (by linarith) habsorb J q hε
  have hbudget : A*Cb*c/(η₀*κ*θ) ≤ δ := by
    apply (div_le_iff₀ (show 0 < η₀*κ*θ by positivity)).mpr
    have hkt : 1 ≤ κ*θ := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hkt (mul_nonneg hδ hη₀.le)
    nlinarith only [hsmall,hm]
  have hh := (div_le_iff₀ (pow_pos hη J)).mp (hb.trans hbudget)
  have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ hη.le hη1 (n:=J)) hδ
  simpa only [mul_one] using hh.trans hp

theorem sourceWidth_hidden_ratio {A Cacc Cb ε η₀ L t η c κ θ Δ γ : ℝ}
    (hA : 0 ≤ A) (hC : 0 < Cacc) (hCb : 0 ≤ Cb) (hη₀ : 0 < η₀)
    (hL : 0 < L) (ht : 0 < t) (hη : 0 < η) (hc : 0 ≤ c)
    (hκ : 1 ≤ κ) (hθ : 0 < θ) (hγ : 0 ≤ γ) (habsorb : A ≤ Cacc*t*η^2)
    (hsmall : 6*A*Cb*c ≤ γ*η₀) (J q : ℕ)
    (hε : ε ≤ accuracyWindow c Cacc L κ θ Δ J q) :
    A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J*θ/((κ/6)*η^J) ≤ γ := by
  have hκp : 0 < κ := by linarith
  have hb := sourceWidth_absorption hA hC hCb hη₀ hL ht hη hc hκp hθ habsorb J q hε
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ 6*θ/κ by positivity)
  have he : (A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J/η^J)*(6*θ/κ) =
      A^(J+1)*((J:ℝ)+1)^q*sourceWidth Cb ε η₀ L t η J*θ/((κ/6)*η^J) := by ring
  rw [he] at hm
  apply hm.trans
  have he' : (A*Cb*c/(η₀*κ*θ))*(6*θ/κ) = 6*A*Cb*c/(η₀*κ^2) := by field_simp; ring
  rw [he']
  apply (div_le_iff₀ (show 0 < η₀*κ^2 by positivity)).mpr
  have hk2 : 1 ≤ κ^2 := one_le_pow₀ hκ
  have hm' := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hγ hη₀.le)
  nlinarith only [hsmall,hm']

end Bilevel.ChiExtensionCalibration
