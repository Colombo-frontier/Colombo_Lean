import Bilevel.ChiAccuracyCalibration

/-! The actual natural macro index pays the initial gap and retains a
quantitative lower bound for subsequent activation counts. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration

def macroIndex (Δ Cgap energy : ℝ) : ℕ := ⌊Δ/(2*Cgap*energy)⌋₊

theorem macroIndex_bounds {Δ Cgap energy : ℝ}
    (hΔ : 0 < Δ) (hCgap : 0 < Cgap) (he : 0 < energy)
    (hsmall : Cgap*energy ≤ Δ/256) :
    128 ≤ macroIndex Δ Cgap energy ∧
    Cgap*((macroIndex Δ Cgap energy:ℝ)+1)*energy ≤ Δ ∧
    Δ/(4*Cgap*energy) ≤ (macroIndex Δ Cgap energy:ℝ) ∧
    (macroIndex Δ Cgap energy:ℝ) ≤ Δ/(2*Cgap*energy) := by
  let x := Δ/(2*Cgap*energy)
  have hx : 128 ≤ x := by
    apply (le_div_iff₀ (show 0 < 2*Cgap*energy by positivity)).mpr
    nlinarith only [hsmall]
  have hx0 : 0 ≤ x := by linarith
  have hn : 128 ≤ macroIndex Δ Cgap energy := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have hup : (macroIndex Δ Cgap energy:ℝ) ≤ x := Nat.floor_le hx0
  have hlo : x < (macroIndex Δ Cgap energy:ℝ)+1 := Nat.lt_floor_add_one x
  have hxmul : x*(2*Cgap*energy)=Δ := by dsimp [x]; field_simp
  refine ⟨hn,?_,?_,hup⟩
  · have hm := mul_le_mul_of_nonneg_right hup (show 0 ≤ Cgap*energy by positivity)
    nlinarith only [hm,hxmul,hsmall,hΔ]
  · have half : x/2 ≤ (macroIndex Δ Cgap energy:ℝ) := by linarith
    convert half using 1
    dsimp only [x]
    ring

end Bilevel.ChiExtensionCalibration
