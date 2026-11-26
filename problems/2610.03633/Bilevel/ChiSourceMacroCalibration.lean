import Bilevel.ChiSourceMacroScales
import Bilevel.ChiSourceMacroFloors
import Bilevel.ChiAccuracyWindowRefinement

/-! A source-window refinement selects the actual macro floor and pays
the initial gap, retaining all older construction constants and windows. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

theorem exists_macro_accuracy_refinement {Cb η₀ t η Cgap Cold cold : ℝ}
    (hCb : 0 < Cb) (hη₀ : 0 < η₀) (ht : 0 < t) (hη : 0 < η) (hCgap : 0 < Cgap)
    (hCold : 1 ≤ Cold) (hcold : 0 < cold) :
    ∃ Cacc c : ℝ,1 ≤ Cacc ∧ 0 < c ∧ c ≤ 1 ∧ Cold ≤ Cacc ∧ c ≤ cold ∧
      ∀ (L κ θ Δ ε : ℝ) (J : ℕ),0 < L → 1 ≤ κ → 1 ≤ θ → 0 < Δ → 0 < ε →
      ε ≤ accuracyWindow c Cacc L κ θ Δ J 6 →
      let b := sourceWidth Cb ε η₀ L t η J
      let energy := (η₀*L)*b^2
      let n := macroIndex Δ Cgap energy
      ε ≤ accuracyWindow cold Cold L κ θ Δ J 6 ∧ 128 ≤ n ∧
      Cgap*((n:ℝ)+1)*energy ≤ Δ ∧
      η₀*L*Δ*(t*η)^(2*J)/(4*Cgap*Cb^2*ε^2) ≤ (n:ℝ) ∧
      (n:ℝ) ≤ η₀*L*Δ*(t*η)^(2*J)/(2*Cgap*Cb^2*ε^2) := by
  let Cacc := max Cold (max 1 (1/(t*η)))
  let c := min cold (min 1 (η₀/(256*Cgap*Cb^2)))
  have hCacc : 1 ≤ Cacc := hCold.trans (le_max_left _ _)
  have hCaccp : 0 < Cacc := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hccold : c ≤ cold := min_le_left _ _
  have hcsmall : c ≤ η₀/(256*Cgap*Cb^2) := (min_le_right _ _).trans (min_le_right _ _)
  have hCaccabs : 1 ≤ Cacc*(t*η) := (div_le_iff₀ (mul_pos ht hη)).mp
    ((le_max_right _ _).trans (le_max_right _ _))
  have hcsmall' := (le_div_iff₀ (show 0 < 256*Cgap*Cb^2 by positivity)).mp hcsmall
  have hcsq : c^2 ≤ c := by nlinarith [hc]
  have hconstant : Cgap*Cb^2*c^2 ≤ η₀/256 := by
    have hh := mul_le_mul_of_nonneg_left hcsq (show 0 ≤ Cgap*Cb^2 by positivity)
    nlinarith only [hh,hcsmall']
  refine ⟨Cacc,c,hCacc,hc,hc1,le_max_left _ _,hccold,?_⟩
  intro L κ θ Δ ε J hL hκ hθ hΔ hε hwindow
  dsimp only
  let b := sourceWidth Cb ε η₀ L t η J
  let energy := (η₀*L)*b^2
  have hb : 0 < b := sourceWidth_pos hCb hε hη₀ hL ht hη J
  have he : 0 < energy := by dsimp [energy]; positivity
  have hold := accuracyWindow_mono (κ:=κ) (θ:=θ) (Δ:=Δ) hc.le hccold (by linarith : 0 < Cold)
    (show Cold ≤ Cacc from le_max_left _ _) hL.le (by linarith) (by linarith) J 6
  have henergy := source_energy_window hCb.le hε.le hη₀ hL ht hη hc.le hCaccp hΔ.le hCaccabs J 6 hwindow
  have hsmall : Cgap*energy ≤ Δ/256 := by
    have hh := mul_le_mul_of_nonneg_left henergy hCgap.le
    have hp := mul_le_mul_of_nonneg_right hconstant (div_nonneg hΔ.le hη₀.le)
    apply hh.trans
    convert hp using 1
    · ring
    · field_simp
      ring
  have hfloor := macroIndex_bounds hΔ hCgap he hsmall
  refine ⟨hwindow.trans hold,hfloor.1,hfloor.2.1,?_,?_⟩
  · apply le_trans _ hfloor.2.2.1
    apply le_of_eq
    dsimp only [energy,b]
    rw [source_energy_formula hη₀ hL ht hη]
    field_simp
    ring
  · apply hfloor.2.2.2.trans_eq
    dsimp only [energy,b]
    rw [source_energy_formula hη₀ hL ht hη]
    field_simp
    ring

end Bilevel.ChiExtensionCalibration
