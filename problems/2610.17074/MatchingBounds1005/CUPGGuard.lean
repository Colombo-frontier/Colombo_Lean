import MatchingBounds1005.CUPGTaylor

/-! # Guarded extrapolation from four actual function evaluations -/
noncomputable section
open scoped ContDiff

namespace MatchingBounds1005.CUPG

/-- Four samples control every momentum extrapolation. This is the source's
cubic guard with exact constants `13` and `1`, specialized to the only case
needed by the algorithm (both stored endpoint values are below baseline). -/
theorem guarded_extrapolation {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {L B θ : ℝ}
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hlip : ∀ x y, |iteratedDeriv 3 h x - iteratedDeriv 3 h y| ≤ L * |x - y|)
    (hzero : h 0 ≤ 0) (hone : h (-1) ≤ 0)
    (hhalf : -B ≤ h (-(1 / 2))) (hthree : -B ≤ h (-3))
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    h θ ≤ h 0 + 13 * B + L := by
  let a := θ / 30 + θ ^ 2 / 10 + θ ^ 3 / 15
  let b := 3 * θ / 2 + 7 * θ ^ 2 / 2 + θ ^ 3
  let c := 24 * θ / 5 + 32 * θ ^ 2 / 5 + 8 * θ ^ 3 / 5
  let d := 10 * θ / 3 + 3 * θ ^ 2 + 2 * θ ^ 3 / 3
  have hθ2 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ hθone
  have hθ3 : θ ^ 3 ≤ 1 := pow_le_one₀ hθ hθone
  have hθ4 : θ ^ 4 ≤ 1 := pow_le_one₀ hθ hθone
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hau : a ≤ 1 / 5 := by dsimp [a]; linarith
  have hbu : b ≤ 6 := by dsimp [b]; linarith
  have hcu : c ≤ 64 / 5 := by dsimp [c]; linarith
  have he : cubicJet h θ = h 0 - a * cubicJet h (-3) + b * cubicJet h (-1) -
      c * cubicJet h (-(1 / 2)) + d * h 0 := by
    unfold cubicJet
    dsimp [a, b, c, d]
    ring
  have et := (abs_le.mp (cubic_jet_error hh hlip θ)).2
  rw [abs_of_nonneg hθ] at et
  have e1 := (abs_le.mp (cubic_jet_error hh hlip (-1))).1
  have ehalf := (abs_le.mp (cubic_jet_error hh hlip (-(1 / 2)))).2
  have e3 := (abs_le.mp (cubic_jet_error hh hlip (-3))).2
  norm_num at e1 ehalf e3
  norm_num [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ehalf
  have hp1 : cubicJet h (-1) ≤ L / 24 := by linarith
  have hphalf : -B - L / 384 ≤ cubicJet h (-(1 / 2)) := by linarith only [hhalf, ehalf]
  have hp3 : -B - 27 * L / 8 ≤ cubicJet h (-3) := by linarith
  have hp1' := mul_le_mul_of_nonneg_left hp1 hb
  have hphalf' := mul_le_mul_of_nonneg_left hphalf hc
  have hp3' := mul_le_mul_of_nonneg_left hp3 ha
  have hz' := mul_nonpos_of_nonneg_of_nonpos hd hzero
  have hnoise : L / 24 * (θ ^ 4 + 81 * a + b + c / 16) ≤ L := by
    have hsum : θ ^ 4 + 81 * a + b + c / 16 ≤ 24 := by
      calc
        _ ≤ 1 + 81 * (1 / 5 : ℝ) + 6 + (64 / 5 : ℝ) / 16 := by gcongr
        _ = 24 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ L / 24 by positivity)
    nlinarith only [hm]
  have hac : a + c ≤ 13 := by
    calc
      a + c ≤ (1 / 5 : ℝ) + 64 / 5 := add_le_add hau hcu
      _ = 13 := by norm_num
  have hbase : (a + c) * B ≤ 13 * B := mul_le_mul_of_nonneg_right hac hB
  rw [he] at et
  linear_combination et + hp1' + hphalf' + hp3' + hz' + hnoise + hbase

end MatchingBounds1005.CUPG
