import Bilevel.ChiFinePieceBounds
import Bilevel.ZeroChainScheduleBudgets

/-! Actual revised centered-frontier pieces under the exact logarithmic
resolution schedule. Scalar schedule arithmetic is unchanged by the revision. -/
noncomputable section
namespace Bilevel.ChiFine.Schedule
open ChiBoundedChain ZeroChainSchedule ChiFine.PieceBounds

theorem normalized_piece_budgets : ∃ B : ℝ, 1 ≤ B ∧
    ∀ (n : ℕ) (c θ : ℝ), 0 < c → c ≤ 1/16 → 1 ≤ θ →
    ∀ j, j ≤ levels θ → ∀ z : Space n,
      |ChiFine.piece n (levels θ) (resolution c 1 θ) j z| ≤
        B*θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3, ‖iteratedFDeriv ℝ (k.val+1)
        (ChiFine.piece n (levels θ) (resolution c 1 θ) j) z‖ ≤
          B/(pieceResolution c 1 θ j)^k.val := by
  obtain ⟨B,hB,hb⟩ := normalized_bounds
  refine ⟨2*B,by linarith,fun n c θ hc hcs hθ j hj z => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hpos (i : ℕ) : 0 < resolution c 1 θ i := resolution_pos c 1 θ hc (by norm_num) hθ i
  have hsmall (i : ℕ) : resolution c 1 θ i ≤ 1/16 := by
    simpa using resolution_small c 1 θ hc.le hcs (by norm_num) hθ i
  have hflat (i : ℕ) := (hb n).2 (resolution c 1 θ i) (hpos i) (hsmall i)
  have hbase (w : Space n) : |ChiBoundedChain.centeredResidual n w| ≤ B := by
    simpa only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using (hb n).1 0 w
  constructor
  · by_cases hj0 : j = 0
    · subst j
      have hh := coarse_amplitude_bound B hB0 n (levels θ) (resolution c 1 θ) hbase
        (fun i _ w => (hflat i w).1) z
      have hz : amplitudeExponent 0 = 0 := by simp [amplitudeExponent]
      rw [hz,neg_zero,Real.rpow_zero,mul_one]
      linarith
    · have hh := noncoarse_amplitude_bound B hB0 n (levels θ) (resolution c 1 θ)
        (fun i _ => hpos i) (fun i l hil _ => resolution_antitone c 1 θ hc.le (by norm_num) hθ i l hil)
        (fun i _ w => (hflat i w).2.1) j (by omega) hj z
      rw [amplitudeExponent,if_neg hj0]
      apply hh.trans
      dsimp [resolution]
      have hp : 0 ≤ θ^(-aExponent (j-1)) := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_le_mul_of_nonneg_right (show c ≤ 1 by linarith) (mul_nonneg hB0 hp)]
  · intro k
    apply piece_positive_bound B (pieceResolution c 1 θ j) hB0
      (pieceResolution_pos c 1 θ hc (by norm_num) hθ j)
      (by have hh := pieceResolution_le c 1 θ hc.le (by norm_num) hθ j hj; simpa using hh.trans (by linarith : c*1 ≤ 1))
      n (levels θ) (resolution c 1 θ)
      (fun k w => (hb n).1 ⟨k.val+1,by omega⟩ w)
      (fun i _ k w => (hflat i w).2.2 k) j
      (fun hlt => (pieceResolution_current c 1 θ j hlt).le)
      (fun hj0 _ => pieceResolution_previous c 1 θ hc.le (by norm_num) hθ j hj0 hj) z k

end Bilevel.ChiFine.Schedule
