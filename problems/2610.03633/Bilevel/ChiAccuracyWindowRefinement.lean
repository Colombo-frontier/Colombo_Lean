import Bilevel.ChiAccuracyConstants

/-! The accuracy window can be tightened without changing any previously
chosen geometric, fine, or curvature constant. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem accuracyWindow_mono {c₁ c₂ A₁ A₂ L κ θ Δ : ℝ}
    (hc₁ : 0 ≤ c₁) (hcc : c₁ ≤ c₂) (hA₂ : 0 < A₂) (hAA : A₂ ≤ A₁)
    (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (J q : ℕ) :
    accuracyWindow c₁ A₁ L κ θ Δ J q ≤ accuracyWindow c₂ A₂ L κ θ Δ J q := by
  have hA₁ : 0 < A₁ := hA₂.trans_le hAA
  have hc₂ : 0 ≤ c₂ := hc₁.trans hcc
  have hp : A₂^J*((J:ℝ)+1)^q ≤ A₁^J*((J:ℝ)+1)^q :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA₂.le hAA J) (by positivity)
  have hfrac : c₁/(A₁^J*((J:ℝ)+1)^q) ≤ c₂/(A₂^J*((J:ℝ)+1)^q) :=
    (div_le_div_of_nonneg_right hcc (by positivity)).trans
      (div_le_div_of_nonneg_left hc₂ (by positivity) hp)
  exact mul_le_mul_of_nonneg_right hfrac (le_min (div_nonneg hL (mul_nonneg hκ hθ)) (Real.sqrt_nonneg _))

theorem exists_refined_hidden_ratio {A Cb η₀ t η γ Cold cold : ℝ}
    (hA : 0 ≤ A) (hCb : 0 ≤ Cb) (hη₀ : 0 < η₀) (ht : 0 < t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hγ : 0 < γ) (hCold : 1 ≤ Cold) (hcold : 0 < cold) :
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ Cold ≤ Cacc ∧ c ≤ cold ∧
      ∀ (L κ θ Δ ε : ℝ) (J : ℕ),0 < L → 1 ≤ κ → 1 ≤ θ →
      ε ≤ accuracyWindow c Cacc L κ θ Δ J 6 →
      ε ≤ accuracyWindow cold Cold L κ θ Δ J 6 ∧
      A^(J+1)*((J:ℝ)+1)^6*sourceWidth Cb ε η₀ L t η J*θ/((κ/6)*η^J) ≤ γ := by
  obtain ⟨Cnew,cnew,hCnew,hcnew,hcnew1,hnew⟩ := exists_uniform_hessian_hidden_budget
    hA hCb hη₀ ht hη hη1 (show (0:ℝ) < 1 by norm_num) hγ
  let Cacc := max Cold Cnew
  let c := min cold cnew
  have hCacc : 1 ≤ Cacc := hCold.trans (le_max_left _ _)
  have hc : 0 < c := lt_min hcold hcnew
  have hc1 : c ≤ 1 := (min_le_right _ _).trans hcnew1
  refine ⟨Cacc,c,hCacc,hc,hc1,le_max_left _ _,min_le_left _ _,?_⟩
  intro L κ θ Δ ε J hL hκ hθ hε
  have hk : 0 ≤ κ := by linarith
  have ht' : 0 ≤ θ := by linarith
  have hold := accuracyWindow_mono (Δ:=Δ) hc.le (show c ≤ cold from min_le_left _ _) (by linarith : 0 < Cold)
    (show Cold ≤ Cacc from le_max_left _ _) hL.le hk ht' J 6
  have hnew' := accuracyWindow_mono (Δ:=Δ) hc.le (show c ≤ cnew from min_le_right _ _) (by linarith : 0 < Cnew)
    (show Cnew ≤ Cacc from le_max_right _ _) hL.le hk ht' J 6
  exact ⟨hε.trans hold,(hnew L κ θ Δ ε J 6 hL hκ hθ (hε.trans hnew')).2⟩

end Bilevel.ChiExtensionCalibration
