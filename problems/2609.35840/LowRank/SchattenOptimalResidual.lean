import LowRank.SchattenResidual

/-! Optimal Schatten residuals over rank-exactly-k orthogonal projectors,
matching the compression lemma in the manuscript. The minimum is attained. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

def optimalSchattenPower {d t : ℕ} (p : ℝ) (H : Matrix (Fin d) (Fin t) ℝ) (k : ℕ) : ℝ :=
  sInf {z : ℝ | ∃ P : Matrix (Fin t) (Fin t) ℝ,
    IsOrthogonalProjector P ∧ P.rank = k ∧ z = schattenPower p (H * (1 - P))}

def optimalSchattenNorm {d t : ℕ} (p : ℝ) (H : Matrix (Fin d) (Fin t) ℝ) (k : ℕ) : ℝ :=
  (optimalSchattenPower p H k) ^ (1 / p)

theorem optimalSchattenPower_eq_bottom {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) :
    optimalSchattenPower p H k =
      bottomPowerTrace (rightGram_posSemidef H).isHermitian m (by omega) (p / 2) :=
  (schattenPower_bottom_isLeast hp H).csInf_eq

theorem optimalSchattenPower_isLeast {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) :
    IsLeast {z : ℝ | ∃ P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ,
      IsOrthogonalProjector P ∧ P.rank = k ∧ z = schattenPower p (H * (1 - P))}
      (optimalSchattenPower p H k) := by
  rw [optimalSchattenPower_eq_bottom hp H]
  exact schattenPower_bottom_isLeast hp H

theorem optimalSchattenPower_nonneg {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) : 0 ≤ optimalSchattenPower p H k := by
  obtain ⟨P, _, _, h⟩ := (optimalSchattenPower_isLeast hp H).1
  rw [h]
  exact schattenPower_nonneg _ _

theorem optimalSchattenNorm_isLeast {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) :
    IsLeast {z : ℝ | ∃ P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ,
      IsOrthogonalProjector P ∧ P.rank = k ∧ z = schattenNorm p (H * (1 - P))}
      (optimalSchattenNorm p H k) := by
  have hleast := optimalSchattenPower_isLeast hp H
  constructor
  · obtain ⟨P, hP, hrank, heq⟩ := hleast.1
    exact ⟨P, hP, hrank, congrArg (fun z : ℝ => z ^ (1 / p)) heq⟩
  · intro z hz
    obtain ⟨P, hP, hrank, rfl⟩ := hz
    exact Real.rpow_le_rpow (optimalSchattenPower_nonneg hp H)
      (hleast.2 ⟨P, hP, hrank, rfl⟩) (by positivity)

theorem optimalSchattenNorm_rpow {d k m : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin (k + m)) ℝ) :
    optimalSchattenNorm p H k ^ p = optimalSchattenPower p H k := by
  rw [optimalSchattenNorm, ← Real.rpow_mul (optimalSchattenPower_nonneg hp H),
    one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]

end
end LowRank
