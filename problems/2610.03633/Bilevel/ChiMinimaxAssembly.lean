import Bilevel.ChiRefinementRates
import Bilevel.ChiDepthLogBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Minimax assembly with explicit family lower-bound interfaces.
The three hard-family premises must be supplied by the actual execution
and information certificates; rate arithmetic alone does not supply them. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.ChiMinimax

def complexity {Algorithm Instance : Type*} (cost : Algorithm → Instance → ENNReal)
    (accurate : Algorithm → Prop) : ENNReal :=
  ⨅ A : {A // accurate A}, ⨆ I, cost A.val I

theorem lower_of_hard_instance {Algorithm Instance : Type*}
    (cost : Algorithm → Instance → ENNReal) (accurate : Algorithm → Prop) (R : ENNReal)
    (hhard : ∀ A,accurate A → ∃ I,R≤cost A I) : R≤complexity cost accurate := by
  apply le_iInf
  intro A
  obtain ⟨I,hI⟩ := hhard A.val A.property
  exact hI.trans (le_iSup (fun I => cost A.val I) I)

theorem three_family_lower_real {D U G T cD cU cG ℓ : ℝ} {qD qG : ℕ}
    (hD : 0≤D) (hU : 0≤U) (hG : 0≤G) (hcD : 0<cD) (hcU : 0<cU) (hcG : 0<cG)
    (hℓ : 1≤ℓ) (hdet : cD*D/ℓ^qD≤T) (hupper : cU*U≤T) (hlower : cG*G/ℓ^qG≤T) :
    (min cD (min cU cG)/3)*(U+(D+G)/ℓ^(max qD qG))≤T := by
  let c := min cD (min cU cG)
  have hc : 0<c := lt_min hcD (lt_min hcU hcG)
  have hcd : c≤cD := min_le_left _ _
  have hcu : c≤cU := (min_le_right _ _).trans (min_le_left _ _)
  have hcg : c≤cG := (min_le_right _ _).trans (min_le_right _ _)
  have hℓp : 0<ℓ := by linarith only [hℓ]
  have hd : c*D/ℓ^(max qD qG)≤T := by
    apply le_trans _ hdet
    apply le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcd hD) (by positivity))
    exact div_le_div_of_nonneg_left (mul_nonneg hcD.le hD) (by positivity)
      (pow_le_pow_right₀ hℓ (le_max_left _ _))
  have hu : c*U≤T := (mul_le_mul_of_nonneg_right hcu hU).trans hupper
  have hg : c*G/ℓ^(max qD qG)≤T := by
    apply le_trans _ hlower
    apply le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcg hG) (by positivity))
    exact div_le_div_of_nonneg_left (mul_nonneg hcG.le hG) (by positivity)
      (pow_le_pow_right₀ hℓ (le_max_right _ _))
  change (c/3)*(U+(D+G)/ℓ^(max qD qG))≤T
  calc
    _ = (c*U+c*D/ℓ^(max qD qG)+c*G/ℓ^(max qD qG))/3 := by ring
    _ ≤ T := by linarith only [hd,hu,hg]

theorem three_family_minimax {Algorithm Instance : Type*}
    (cost : Algorithm → Instance → ENNReal) (accurate : Algorithm → Prop)
    {D U G cD cU cG ℓ : ℝ} {qD qG : ℕ}
    (hD : 0≤D) (hU : 0≤U) (hG : 0≤G) (hcD : 0<cD) (hcU : 0<cU) (hcG : 0<cG) (hℓ : 1≤ℓ)
    (hdet : ∀ A,accurate A → ∃ I,ENNReal.ofReal (cD*D/ℓ^qD)≤cost A I)
    (hupper : ∀ A,accurate A → ∃ I,ENNReal.ofReal (cU*U)≤cost A I)
    (hlower : ∀ A,accurate A → ∃ I,ENNReal.ofReal (cG*G/ℓ^qG)≤cost A I) :
    ENNReal.ofReal ((min cD (min cU cG)/3)*(U+(D+G)/ℓ^(max qD qG)))≤complexity cost accurate := by
  apply le_iInf
  intro A
  let T := ⨆ I,cost A.val I
  by_cases htop : T=∞
  · change _≤T
    rw [htop]
    exact le_top
  obtain ⟨Id,hd⟩ := hdet A.val A.property
  obtain ⟨Iu,hu⟩ := hupper A.val A.property
  obtain ⟨Ig,hg⟩ := hlower A.val A.property
  have hd' : ENNReal.ofReal (cD*D/ℓ^qD)≤T := hd.trans (le_iSup (fun I => cost A.val I) Id)
  have hu' : ENNReal.ofReal (cU*U)≤T := hu.trans (le_iSup (fun I => cost A.val I) Iu)
  have hg' : ENNReal.ofReal (cG*G/ℓ^qG)≤T := hg.trans (le_iSup (fun I => cost A.val I) Ig)
  apply ENNReal.ofReal_le_of_le_toReal
  exact three_family_lower_real hD hU hG hcD hcU hcG hℓ
    ((ENNReal.ofReal_le_iff_le_toReal htop).mp hd')
    ((ENNReal.ofReal_le_iff_le_toReal htop).mp hu')
    ((ENNReal.ofReal_le_iff_le_toReal htop).mp hg')

theorem logarithm_ge_one {θ : ℝ} (hθ : 1≤θ) : 1≤Real.log (2+θ) := by
  exact (one_le_pow₀ (by norm_num : (1:ℝ)≤4) : (1:ℝ)≤4^ChiIndependentWidths.chosenDepth θ).trans
    (ChiIndependentWidths.chosenDepth_bound hθ)

end Bilevel.ChiMinimax
