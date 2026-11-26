import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Explicit information/dimension calibration

Adapted from the pure arithmetic fragment AlignmentArithmetic in the local
0105 formalization. No probability or oracle lower theorem is imported.
-/

namespace NCConcave16991.DenseWeakHiding

theorem informationDimension_contradiction {B D entropy : ℝ} (hB : 1 ≤ B)
    (hD : 512 * Real.log (B + 2) + 2048 ≤ D) (hentropy : entropy ≤ 1) :
    D / 8000 < 25 * D / 16384 - (1 / 8 : ℝ) * Real.log B - entropy := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hB2pos : 0 < B + 2 := by linarith
  have hlog : Real.log B ≤ Real.log (B + 2) :=
    (Real.strictMonoOn_log (by simpa using hBpos) (by simpa using hB2pos) (by linarith)).le
  have hlogNonneg : 0 ≤ Real.log (B + 2) := Real.log_nonneg (by linarith)
  have hcoef : (1 / 1024 : ℝ) < 25 / 16384 - 1 / 8000 := by norm_num
  nlinarith

end NCConcave16991.DenseWeakHiding
