import Bilevel.ZeroChainFlatteningAnnulus
import Bilevel.ZeroChainFlatteningError

/-! The annular jet localization in the original physical coordinates. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainFlatteningAnnulusScaled
open ZeroChain ZeroChainResidualScaled ZeroChainFlatteningMap ZeroChainFlatteningBounds
  ZeroChainFlatteningError ZeroChainFlatteningAnnulus

theorem scaled_jet_zero_of_zero {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (a β : ℝ) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (hz : iteratedFDeriv ℝ k f (β⁻¹ • z) = 0) : iteratedFDeriv ℝ k (scaled f a β) z = 0 := by
  have hg : ContDiff ℝ 3 (fun w : Space n => f (β⁻¹ • w)) := hf.comp (contDiff_id.const_smul β⁻¹)
  change iteratedFDeriv ℝ k (fun w => a • f (β⁻¹ • w)) z = 0
  rw [iteratedFDeriv_const_smul_apply' (hg.of_le (by exact_mod_cast hk)).contDiffAt]
  have hh := linear_scale_jet_le hf β⁻¹ z k hk
  rw [hz, norm_zero, zero_mul] at hh
  rw [norm_le_zero_iff.mp hh, smul_zero]

theorem scaled_difference_eq (n : ℕ) (a β δ' δ : ℝ) (hβ : 0 < β) (hδ' : 0 < δ')
    (hδ : δ' ≤ δ) (hsmall : δ ≤ β/16) :
    (fun z => flattenedResidual n a β δ' z-flattenedResidual n a β δ z) =
      scaled (differenceRaw n (δ'/β) (δ/β)) a β := by
  have hδpos : 0 < δ := lt_of_lt_of_le hδ' hδ
  have hs : δ/β ≤ 1/16 := (div_le_iff₀ hβ).mpr (by linarith)
  ext z
  change a*ZeroChainResidual.residual n (β⁻¹ • flattenMap n δ' z)-
    a*ZeroChainResidual.residual n (β⁻¹ • flattenMap n δ z) = a*differenceRaw n (δ'/β) (δ/β) (β⁻¹ • z)
  rw [flattenMap_scale_commute n β δ' hβ.ne' hδ'.ne',
    flattenMap_scale_commute n β δ hβ.ne' hδpos.ne', ← mul_sub]
  congr 1
  exact congrFun (normalized_difference_eq (div_pos hδ' hβ)
    (div_le_div_of_nonneg_right hδ hβ.le) hs n) (β⁻¹ • z)

/-- All actual jets through order three of the difference between two
resolutions vanish unless the active child lies in δ'<|z_i|<2δ. -/
theorem source_annular_localization (n : ℕ) (a β δ' δ : ℝ) (hβ : 0 < β) (hδ' : 0 < δ')
    (hδ : δ' ≤ δ) (hsmall : δ ≤ β/16) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (h : iteratedFDeriv ℝ k (fun w => flattenedResidual n a β δ' w-flattenedResidual n a β δ w) z ≠ 0) :
    ∃ i : Fin (n+1), δ' < |z i| ∧ |z i| < 2*δ := by
  rw [scaled_difference_eq n a β δ' δ hβ hδ' hδ hsmall] at h
  have hn : iteratedFDeriv ℝ k (differenceRaw n (δ'/β) (δ/β)) (β⁻¹ • z) ≠ 0 := by
    intro hz
    exact h (scaled_jet_zero_of_zero (differenceRaw_contDiff n (δ'/β) (δ/β)) a β z k hk hz)
  obtain ⟨i,hi,_⟩ := nonzero_difference_jet_annulus (div_pos hδ' hβ)
    (div_le_div_of_nonneg_right hδ hβ.le) n (β⁻¹ • z) k hk hn
  have habs : |(β⁻¹ • z) i| = |z i|/β := by
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hβ), div_eq_inv_mul]
  rw [habs] at hi
  refine ⟨i, (div_lt_div_iff_of_pos_right hβ).mp hi.1, ?_⟩
  apply (div_lt_div_iff_of_pos_right hβ).mp
  convert hi.2 using 1
  ring

end Bilevel.ZeroChainFlatteningAnnulusScaled
