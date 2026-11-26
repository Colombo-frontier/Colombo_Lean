import LowRank.TopSpectrum
import LowRank.SchattenRelativeCompression

/-! The manuscript's well-conditioned Schatten compression lemma, including
its relative-error consequence, for every positive real exponent. -/

namespace LowRank
open Matrix
open scoped Matrix
noncomputable section

theorem well_conditioned_schatten_compression {a b p : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ {k m : ℕ} (H : Matrix (Fin (k + m)) (Fin (k + m)) ℝ)
      {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ},
      H.IsHermitian → IsOrthogonalProjector P → P.rank = k →
      LoewnerLE (a • 1) H → LoewnerLE H (b • 1) →
      c * gramCompressionDeficit H k P ≤
        schattenPower p (H * (1 - P)) - optimalSchattenPower p H k := by
  obtain ⟨c, hc, hcomp⟩ := exists_uniform_schatten_compression
    (sq_pos_of_pos ha) (show a ^ 2 ≤ b ^ 2 by nlinarith) hp
  refine ⟨c, hc, ?_⟩
  intro k m H P hH hP hrank hlow hupp
  obtain ⟨hglow, hgupp⟩ := symmetric_gram_spectral_interval hH ha hlow hupp
  exact hcomp H hP hrank hglow hgupp

theorem well_conditioned_relative_schatten_compression {a b p : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k m : ℕ} (H : Matrix (Fin (k + m)) (Fin (k + m)) ℝ)
      {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ} {ε : ℝ},
      H.IsHermitian → IsOrthogonalProjector P → P.rank = k →
      LoewnerLE (a • 1) H → LoewnerLE H (b • 1) →
      0 ≤ ε → ε ≤ 1 →
      schattenNorm p (H * (1 - P)) ≤ (1 + ε) * optimalSchattenNorm p H k →
      gramCompressionDeficit H k P ≤ C * ε * (k + m : ℕ) := by
  obtain ⟨C, hC, hcomp⟩ := exists_uniform_relative_schatten_compression
    (sq_pos_of_pos ha) (show a ^ 2 ≤ b ^ 2 by nlinarith) hp
  refine ⟨C, hC, ?_⟩
  intro k m H P ε hH hP hrank hlow hupp hε hε1 hsuccess
  obtain ⟨hglow, hgupp⟩ := symmetric_gram_spectral_interval hH ha hlow hupp
  exact hcomp H hP hrank hglow hgupp hε hε1 hsuccess

end
end LowRank
