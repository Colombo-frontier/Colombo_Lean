import Bilevel.ChiAccuracyWindowRefinement

/-! A further numerical tightening of the same source window bounds the
actual initial width while preserving every older window condition. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem exists_refined_width_budget {Cb η₀ t η W Cold cold : ℝ}
    (hCb : 0 < Cb) (hη₀ : 0 < η₀) (ht : 0 < t) (hη : 0 < η) (hη1 : η ≤ 1)
    (hW : 0 < W) (hCold : 1 ≤ Cold) (hcold : 0 < cold) :
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ Cold ≤ Cacc ∧ c ≤ cold ∧
      ∀ (L κ θ Δ ε : ℝ) (J : ℕ),0 < L → 1 ≤ κ → 1 ≤ θ → 0 < ε →
      ε ≤ accuracyWindow c Cacc L κ θ Δ J 6 →
      ε ≤ accuracyWindow cold Cold L κ θ Δ J 6 ∧ sourceWidth Cb ε η₀ L t η J ≤ W := by
  obtain ⟨Cnew,cnew,hCnew,hcnew,hcnew1,hnew⟩ := exists_uniform_hessian_hidden_budget
    (A:=1) (show (0:ℝ) ≤ 1 by norm_num) hCb.le hη₀ ht hη hη1 hW (show (0:ℝ) < 1 by norm_num)
  let Cacc := max Cold Cnew
  let c := min cold cnew
  have hCacc : 1 ≤ Cacc := hCold.trans (le_max_left _ _)
  have hc : 0 < c := lt_min hcold hcnew
  have hc1 : c ≤ 1 := (min_le_right _ _).trans hcnew1
  refine ⟨Cacc,c,hCacc,hc,hc1,le_max_left _ _,min_le_left _ _,?_⟩
  intro L κ θ Δ ε J hL hκ hθ hε hwindow
  have hk : 0 ≤ κ := by linarith
  have ht' : 0 ≤ θ := by linarith
  have hold := accuracyWindow_mono (Δ:=Δ) hc.le (show c ≤ cold from min_le_left _ _) (by linarith : 0 < Cold)
    (show Cold ≤ Cacc from le_max_left _ _) hL.le hk ht' J 6
  have hnew' := accuracyWindow_mono (Δ:=Δ) hc.le (show c ≤ cnew from min_le_right _ _) (by linarith : 0 < Cnew)
    (show Cnew ≤ Cacc from le_max_right _ _) hL.le hk ht' J 6
  have hb := (sourceWidth_pos hCb hε hη₀ hL ht hη J).le
  have hn := (hnew L κ θ Δ ε J 6 hL hκ hθ (hwindow.trans hnew')).1
  simp only [one_pow,one_mul] at hn
  have hdepth : 1 ≤ ((J:ℝ)+1)^6 := one_le_pow₀ (by have := Nat.cast_nonneg (α:=ℝ) J; linarith)
  exact ⟨hwindow.trans hold,(le_mul_of_one_le_left hb hdepth).trans hn⟩

end Bilevel.ChiExtensionCalibration
