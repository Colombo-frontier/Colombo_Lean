import Nonsmooth.AugmentedSupport
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {k n : ℕ} [Nonempty (Fin k)]

abbrev SupportWinningTimes (h : SupportHistory E k n) (i : Fin k) := {j : Fin n // i = (h j).2.1}

def supportWinningMap (h : SupportHistory E k n) (i : Fin k) : E →ₗ[ℝ] (SupportWinningTimes h i → ℝ) where
  toFun b j := ⟪b, (h j.val).1⟫_ℝ
  map_add' b c := by ext j; exact inner_add_left _ _ _
  map_smul' c b := by ext j; exact real_inner_smul_left _ _ _

theorem supportHistoryCell_kernel_difference (h : SupportHistory E k n) (i : Fin k)
    {b c : E} (hb : b ∈ supportHistoryCell n h i) (hc : c ∈ supportHistoryCell n h i) :
    c - b ∈ LinearMap.ker (supportWinningMap h i) := by
  rw [LinearMap.mem_ker]
  ext j
  change ⟪c - b, (h j.val).1⟫_ℝ = 0
  rw [inner_sub_left, supportHistoryCell_winner_equalities n h i c hc j.val j.property,
    supportHistoryCell_winner_equalities n h i b hb j.val j.property, sub_self]

theorem supportHistoryCell_subset_affine_kernel (h : SupportHistory E k n) (i : Fin k)
    {b : E} (hb : b ∈ supportHistoryCell n h i) :
    supportHistoryCell n h i ⊆ {c : E | c - b ∈ LinearMap.ker (supportWinningMap h i)} :=
  fun _ hc => supportHistoryCell_kernel_difference h i hb hc

theorem supportWinningMap_nullity_bound [FiniteDimensional ℝ E]
    (h : SupportHistory E k n) (i : Fin k) :
    Module.finrank ℝ E - Fintype.card (SupportWinningTimes h i) ≤
      Module.finrank ℝ (LinearMap.ker (supportWinningMap h i)) := by
  have he := LinearMap.finrank_range_add_finrank_ker (supportWinningMap h i)
  have hr := Submodule.finrank_le (LinearMap.range (supportWinningMap h i))
  rw [Module.finrank_pi] at hr
  omega

theorem supportWinningTimes_total (h : SupportHistory E k n) :
    (∑ i : Fin k, Fintype.card (SupportWinningTimes h i)) = n := by
  classical
  simp only [SupportWinningTimes, Fintype.card_subtype, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem supportWinningMap_total_codimension [FiniteDimensional ℝ E] (h : SupportHistory E k n) :
    (∑ i : Fin k, (Module.finrank ℝ E - Module.finrank ℝ (LinearMap.ker (supportWinningMap h i)))) ≤ n := by
  apply le_trans ?_ (supportWinningTimes_total h).le
  apply Finset.sum_le_sum
  intro i hi
  have hbound := supportWinningMap_nullity_bound h i
  omega

end
end Nonsmooth
