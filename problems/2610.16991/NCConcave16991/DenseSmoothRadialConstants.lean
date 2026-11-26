import NCConcave16991.ConePrimitives
/- Adapted from the proved radial-calculus fragments in ../0105_formalization/Manuscript0105/RadialConstants.lean. No assumed lower bounds are imported. -/
import Mathlib.Analysis.Real.Sqrt

/-!
# Constants in the radial gradient barrier

This file checks the exact rational/square-root estimate at the end of Lemma
`lem:radial-gradient`.
-/

namespace NCConcave16991.DenseSmooth

noncomputable def radialThreshold : ℝ := 9 / 32
noncomputable def radialQuadraticWeight : ℝ := 33 / 16

noncomputable def radialBarrierConstant : ℝ :=
  let b := radialThreshold
  let lam := radialQuadraticWeight
  ((1 - b ^ 2) ^ 2 - lam * b) / Real.sqrt (1 - b ^ 2)

theorem radialBarrierConstant_gt : (5 / 18 : ℝ) < radialBarrierConstant := by
  let b : ℝ := 9 / 32
  let lam : ℝ := 33 / 16
  let A : ℝ := (1 - b ^ 2) ^ 2 - lam * b
  let D : ℝ := Real.sqrt (1 - b ^ 2)
  have hbase : 0 < 1 - b ^ 2 := by norm_num [b]
  have hD : 0 < D := by
    dsimp [D]
    exact Real.sqrt_pos.2 hbase
  have hA : (4 / 15 : ℝ) < A := by norm_num [A, b, lam]
  have hDupper : D < (24 / 25 : ℝ) := by
    dsimp [D]
    apply (Real.sqrt_lt' (by norm_num)).2
    norm_num [b]
  change (5 / 18 : ℝ) < A / D
  apply (lt_div_iff₀ hD).2
  have hleft : (5 / 18 : ℝ) * D < (5 / 18 : ℝ) * (24 / 25) := by
    exact mul_lt_mul_of_pos_left hDupper (by norm_num)
  norm_num at hleft ⊢
  linarith

end NCConcave16991.DenseSmooth
