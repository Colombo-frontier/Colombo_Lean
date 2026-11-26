import LowRank.SchattenOptimalResidual
import LowRank.FrobeniusOptimalResidual

/-! The attained rank-exactly-k optimum is also the minimum over all
rank-at-most-k orthogonal projectors, for positive Schatten exponents. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem bottomPowerTrace_mono_length {d a b : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (ha : a ≤ d) (hb : b ≤ d) (hab : a ≤ b) (r : ℝ) :
    bottomPowerTrace hA.isHermitian a ha r ≤ bottomPowerTrace hA.isHermitian b hb r := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  unfold bottomPowerTrace
  rw [Fin.sum_univ_add (fun i : Fin (a + c) =>
    (orderedMatrixSpectrum hA.isHermitian).value (i.castLE hb) ^ r)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
    Real.rpow_nonneg ((orderedMatrixSpectrum hA.isHermitian).value_nonneg hA _) r))

theorem optimalSchattenPower_eq_bottom_of_le {d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) :
    optimalSchattenPower p H k =
      bottomPowerTrace (rightGram_posSemidef H).isHermitian (t - k) (Nat.sub_le t k) (p / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [Nat.add_sub_cancel_left] using optimalSchattenPower_eq_bottom hp H

theorem schattenPower_residual_ge_bottom_of_rank {d t l : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin t) ℝ) {P : Matrix (Fin t) (Fin t) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = l) :
    bottomPowerTrace (rightGram_posSemidef H).isHermitian (t - l) (Nat.sub_le t l) (p / 2) ≤
      schattenPower p (H * (1 - P)) := by
  have hl : l ≤ t := by
    have h := projector_rank_complement hP
    rw [hrank] at h
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  simpa only [Nat.add_sub_cancel_left] using schattenPower_residual_ge_bottom hp H hP hrank

theorem optimalSchattenPower_le_rankBounded {d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) {P : Matrix (Fin t) (Fin t) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank ≤ k) :
    optimalSchattenPower p H k ≤ schattenPower p (H * (1 - P)) := by
  rw [optimalSchattenPower_eq_bottom_of_le hp H hk]
  exact (bottomPowerTrace_mono_length (rightGram_posSemidef H) (Nat.sub_le t k)
    (Nat.sub_le t P.rank) (by omega) (p / 2)).trans
      (schattenPower_residual_ge_bottom_of_rank hp H hP rfl)

theorem optimalSchattenPower_isLeast_rankBounded {d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) :
    IsLeast {z : ℝ | ∃ P : Matrix (Fin t) (Fin t) ℝ,
      IsOrthogonalProjector P ∧ P.rank ≤ k ∧ z = schattenPower p (H * (1 - P))}
      (optimalSchattenPower p H k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  constructor
  · obtain ⟨P, hP, hrank, heq⟩ := (optimalSchattenPower_isLeast hp H).1
    exact ⟨P, hP, hrank.le, heq⟩
  · intro z hz
    obtain ⟨P, hP, hrank, rfl⟩ := hz
    exact optimalSchattenPower_le_rankBounded hp H (by omega) hP hrank

theorem optimalSchattenNorm_isLeast_rankBounded {d t k : ℕ} {p : ℝ} (hp : 0 < p)
    (H : Matrix (Fin d) (Fin t) ℝ) (hk : k ≤ t) :
    IsLeast {z : ℝ | ∃ P : Matrix (Fin t) (Fin t) ℝ,
      IsOrthogonalProjector P ∧ P.rank ≤ k ∧ z = schattenNorm p (H * (1 - P))}
      (optimalSchattenNorm p H k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hleast := optimalSchattenPower_isLeast_rankBounded (k := k) hp H (by omega)
  constructor
  · obtain ⟨P, hP, hrank, heq⟩ := hleast.1
    exact ⟨P, hP, hrank, congrArg (fun z : ℝ => z ^ (1 / p)) heq⟩
  · intro z hz
    obtain ⟨P, hP, hrank, rfl⟩ := hz
    exact Real.rpow_le_rpow (optimalSchattenPower_nonneg hp H)
      (hleast.2 ⟨P, hP, hrank, rfl⟩) (by positivity)

theorem optimalSchattenPower_two_eq_frobenius {d k : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ) (hk : k ≤ d) :
    optimalSchattenPower 2 H k = optimalFrobeniusSq H k := by
  apply le_antisymm
  · apply le_ciInf
    intro P
    simpa only [schattenPower_two] using
      optimalSchattenPower_le_rankBounded (p := 2) (by norm_num) H hk P.2.1 P.2.2
  · obtain ⟨P, hP, hrank, heq⟩ :=
      (optimalSchattenPower_isLeast_rankBounded (p := 2) (by norm_num) H hk).1
    rw [heq, schattenPower_two]
    exact optimalFrobeniusSq_le H hP hrank

end
end LowRank
