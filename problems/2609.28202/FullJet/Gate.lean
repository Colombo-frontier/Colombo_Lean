import FullJet.Opacity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open scoped ContDiff
open Set

namespace FullJet

/-- Smoothness plus a closed zero plateau implies all-order flatness even at
the endpoint. Restricted derivatives on the half-line handle the endpoint. -/
theorem flatAt_of_zero_on_Iic {G : ℝ → ℝ} {a x : ℝ}
    (hG : ContDiff ℝ ∞ G) (hzero : ∀ t ≤ a, G t = 0) (hx : x ≤ a) :
    FlatAt G x := by
  intro r
  have hGr : ContDiffAt ℝ r G x := hG.contDiffAt.of_le (by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Iic a) hGr hx]
  rw [iteratedFDerivWithin_congr (𝕜 := ℝ) (s := Iic a) (f := fun _ : ℝ => (0 : ℝ))
    (fun t ht => hzero t ht) hx r]
  simp [iteratedFDerivWithin_zero_fun]

noncomputable def gate (a b t : ℝ) : ℝ := Real.smoothTransition ((t - a) / (b - a))

theorem gate_contDiff (a b : ℝ) : ContDiff ℝ ∞ (gate a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem gate_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) : gate a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)

theorem gate_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) : gate a b t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  linarith

theorem gate_range (a b t : ℝ) : 0 ≤ gate a b t ∧ gate a b t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem gate_flat {a b t : ℝ} (hab : a < b) (ht : t ≤ a) : FlatAt (gate a b) t :=
  flatAt_of_zero_on_Iic (gate_contDiff a b) (fun s hs => gate_zero hab hs) ht

/-- A concrete smooth gate with the exact numerical thresholds in the source. -/
theorem explicit_gate_flat {t : ℝ} (ht : t ≤ 5 / 32) :
    FlatAt (gate (5 / 32) (9 / 32)) t := gate_flat (by norm_num) ht

end FullJet
