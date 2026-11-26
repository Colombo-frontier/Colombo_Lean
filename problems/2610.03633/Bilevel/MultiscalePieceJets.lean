import Bilevel.MultiscaleMeanCore
import Bilevel.ZeroChainPieceBounds
import Bilevel.ZeroChainScheduleBudgets

/-! Uniform amplitude and derivative budgets of the actual carried pieces.
The small amplitudes of all noncoarse pieces are retained. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChain ZeroChainSchedule ZeroChainPieceBounds ZeroChainCarry

theorem normalized_piece_budgets : ∃ B : ℝ, 1 ≤ B ∧
    ∀ (n : ℕ) (c θ : ℝ), 0 < c → c ≤ 1/16 → 1 ≤ θ →
    ∀ j, j ≤ levels θ → ∀ z : Space n,
      |ZeroChainMultiscale.piece n (levels θ) (resolution c 1 θ) j z| ≤
        B*θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3, ‖iteratedFDeriv ℝ (k.val+1)
        (ZeroChainMultiscale.piece n (levels θ) (resolution c 1 θ) j) z‖ ≤
          B/(pieceResolution c 1 θ j)^k.val := by
  obtain ⟨B,hB,hb⟩ := normalized_bounds
  refine ⟨2*B,by linarith,fun n c θ hc hcs hθ j hj z => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hpos (i : ℕ) : 0 < resolution c 1 θ i := resolution_pos c 1 θ hc (by norm_num) hθ i
  have hsmall (i : ℕ) : resolution c 1 θ i ≤ 1/16 := by
    simpa using resolution_small c 1 θ hc.le hcs (by norm_num) hθ i
  have hflat (i : ℕ) := (hb n).2 (resolution c 1 θ i) (hpos i) (hsmall i)
  have hbase (w : Space n) : |ZeroChainResidual.residual n w| ≤ B := by
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

theorem actual_piece_budgets : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n), ∀ j, j ≤ levels P.θ → ∀ u : E,
      |P.pieces j u| ≤ C*P.amplitude*P.θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (P.pieces j) u‖ ≤
        C*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ j)^k.val) := by
  obtain ⟨B,hB,hb⟩ := normalized_piece_budgets
  let c : Fin 3 → ℝ := fun k => ((k.val+1).factorial:ℝ)*B*24^(k.val+1)
  have hc (k : Fin 3) : 0 ≤ c k := by dsimp [c]; positivity
  let C := B+∑ k,c k
  have hBC : B ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => hc k))
  have hcC (k : Fin 3) : c k ≤ C := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hc l) (Finset.mem_univ k)
    dsimp [C]
    linarith
  refine ⟨C,hB.trans hBC,fun E _ _ _ n P j hj u => ?_⟩
  let d := pieceResolution P.c 1 P.θ j
  let F := ZeroChainMultiscale.piece n (levels P.θ) (resolution P.c 1 P.θ) j
  let f := ZeroChainResidualScaled.scaled F P.amplitude P.β
  have hF : ContDiff ℝ 3 F := ZeroChainMultiscale.piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j
  have hf : ContDiff ℝ 3 f := contDiff_const.mul (hF.comp (contDiff_id.const_smul P.β⁻¹))
  have hd : 0 < d := pieceResolution_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  have hd1 : d ≤ 1 := by
    have hh := pieceResolution_le P.c 1 P.θ P.c_pos.le (by norm_num) P.θ_ge_one j hj
    dsimp [d]
    linarith [P.c_small]
  have hβ := P.β_pos
  have ha := P.amplitude_nonneg
  have hdphys : 0 < P.β*d := mul_pos hβ hd
  have hdR : P.β*d ≤ P.R := by nlinarith [P.β_le_R]
  have hbF (z : Space n) := hb n P.c P.θ P.c_pos P.c_small P.θ_ge_one j hj z
  have he : P.pieces j = f ∘ WrappedChain.coordinates n P.R P.U := rfl
  constructor
  · change |P.amplitude*F (P.β⁻¹ • WrappedChain.coordinates n P.R P.U u)| ≤ _
    rw [abs_mul,abs_of_nonneg ha]
    have hh := mul_le_mul_of_nonneg_left (hbF (P.β⁻¹ • WrappedChain.coordinates n P.R P.U u)).1 ha
    calc
      _ ≤ P.amplitude*(B*P.θ^(-amplitudeExponent j)) := hh
      _ ≤ C*P.amplitude*P.θ^(-amplitudeExponent j) := by
        have hp := Real.rpow_nonneg (show 0 ≤ P.θ by linarith [P.θ_ge_one]) (-amplitudeExponent j)
        nlinarith [mul_le_mul_of_nonneg_right hBC (mul_nonneg ha hp)]
  · intro k
    have ho (l : ℕ) (hl0 : 1 ≤ l) (hl : l ≤ 3) (z : Space n) :
        ‖iteratedFDeriv ℝ l f z‖ ≤ (B*P.amplitude/P.β)*(P.β*d)/(P.β*d)^l := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
      have hh := ZeroChainResidualScaled.scaled_jet_bound hF P.amplitude P.β (B/d^q) ha hβ
        (q+1) (by omega) (fun w => (hbF w).2 ⟨q,by omega⟩) z
      apply hh.trans_eq
      simp only [pow_succ,mul_pow]
      field_simp
      ring
    have hcomp := positive_composition_jet_bound hf (ZeroChainWrappedResidual.coordinates_contDiff n P.R P.U)
      24 (B*P.amplitude/P.β) (P.β*d) (by norm_num) (by positivity) hdphys ho
      (fun l hl0 hl v => ZeroChainWrappedResidual.coordinates_positive_jet_bound n P.R (P.β*d)
        hdphys hdR P.U v l hl0 hl) u (k.val+1) (by omega) (by omega)
    rw [he]
    have hphys : pieceResolution P.c P.β P.θ j = P.β*d := by dsimp [d,pieceResolution]; ring
    rw [hphys]
    calc
      _ ≤ ((k.val+1).factorial:ℝ)*(B*P.amplitude/P.β)*24^(k.val+1)*(P.β*d)/(P.β*d)^(k.val+1) := hcomp
      _ = c k*P.amplitude/(P.β*(P.β*d)^k.val) := by dsimp [c]; rw [pow_succ]; field_simp; ring
      _ ≤ C*P.amplitude/(P.β*(P.β*d)^k.val) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcC k) ha) (by positivity)

end Bilevel.MultiscaleMean
