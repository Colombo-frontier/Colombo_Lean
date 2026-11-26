import Bilevel.PrimitiveQueryFamily

/-! Minimax maximum of actual original-query hard families. This lemma keeps
the common admissible instance class and actual solver execution throughout;
the numerical family theorems must still discharge the three premises. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.PrimitiveQuery
set_option autoImplicit false
variable {μ L ρ Δ R₀ σf σg : ℝ}

theorem three_family_minimax (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    {D U G cD cU cG ℓ : ℝ} {qD qG : ℕ}
    (hD : 0≤D) (hU : 0≤U) (hG : 0≤G) (hcD : 0<cD) (hcU : 0<cU) (hcG : 0<cG)
    (hℓ : 1≤ℓ)
    (hd : Hardness C ε (cD*D/ℓ^qD))
    (hu : Hardness C ε (cU*U))
    (hg : Hardness C ε (cG*G/ℓ^qG)) :
    ENNReal.ofReal ((min cD (min cU cG)/3)*(U+(D+G)/ℓ^(max qD qG)))≤Complexity C ε := by
  apply ChiMinimax.three_family_minimax _ _ hD hU hG hcD hcU hcG hℓ
  · intro A hA
    obtain ⟨G,I,hI,hcost⟩ := hd A hA
    exact ⟨⟨⟨G,I⟩,hI⟩,hcost⟩
  · intro A hA
    obtain ⟨G,I,hI,hcost⟩ := hu A hA
    exact ⟨⟨⟨G,I⟩,hI⟩,hcost⟩
  · intro A hA
    obtain ⟨G,I,hI,hcost⟩ := hg A hA
    exact ⟨⟨⟨G,I⟩,hI⟩,hcost⟩

theorem three_family_minimax_no_log (C : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    {D U G cD cU cG : ℝ}
    (hD : 0≤D) (hU : 0≤U) (hG : 0≤G) (hcD : 0<cD) (hcU : 0<cU) (hcG : 0<cG)
    (hd : Hardness C ε (cD*D)) (hu : Hardness C ε (cU*U)) (hg : Hardness C ε (cG*G)) :
    ENNReal.ofReal ((min cD (min cU cG)/3)*(D+U+G))≤Complexity C ε := by
  have h := three_family_minimax C ε (ℓ:=1) (qD:=0) (qG:=0) hD hU hG hcD hcU hcG (le_refl _)
    (by simpa only [one_pow,div_one] using hd) hu (by simpa only [one_pow,div_one] using hg)
  convert h using 1
  congr 1
  simp only [one_pow,div_one]
  ring

end Bilevel.PrimitiveQuery
