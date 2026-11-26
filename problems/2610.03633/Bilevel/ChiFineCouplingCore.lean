import Bilevel.ChiFineSchedule
import Bilevel.ChiFineScaled
import Bilevel.CompensatedMeanJets

/-! Concrete fine coupling from the revised centered chain. The generic
finite-sum jet API is reused; no older lower objective or rate is asserted. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainSchedule ZeroChainResidualScaled

structure Parameters where
  ℓ : ℝ
  β : ℝ
  θ : ℝ
  c : ℝ
  ell_nonneg : 0 ≤ ℓ
  β_pos : 0 < β
  θ_ge_one : 1 ≤ θ
  c_pos : 0 < c
  c_small : c ≤ 1/128

namespace Parameters
variable (P : Parameters)

def amplitude : ℝ := P.ℓ*P.β^2
def pieces (n : ℕ) (j : ℕ) : Space n → ℝ :=
  scaled (piece n (levels P.θ) (resolution P.c 1 P.θ) j) P.amplitude P.β

theorem amplitude_nonneg : 0 ≤ P.amplitude := mul_nonneg P.ell_nonneg (sq_nonneg _)

theorem pieces_contDiff (n j : ℕ) : ContDiff ℝ 3 (P.pieces n j) :=
  contDiff_const.mul ((piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j).comp
    (contDiff_id.const_smul P.β⁻¹))

theorem decomposition (n : ℕ) (z : Space n) :
    (∑ j ∈ Finset.range (levels P.θ+1),P.pieces n j z)=frontier n P.ℓ P.β z := by
  change (∑ j ∈ Finset.range (levels P.θ+1),P.amplitude*
    piece n (levels P.θ) (resolution P.c 1 P.θ) j (P.β⁻¹ • z))=_
  rw [← Finset.mul_sum,sum_piece]
  rfl

/-- Only the finite decomposition and normal-profile fields are used below. -/
def data (n : ℕ) : CompensatedMean.Data (E:=Space n) where
  μ := 1
  L := 1
  J := levels P.θ
  r := frontier n P.ℓ P.β
  A := fun _ => 0
  e := P.pieces n
  w := width P.c P.β P.θ
  r_smooth := frontier_contDiff n P.ℓ P.β
  A_smooth := contDiff_const
  e_smooth := P.pieces_contDiff n
  w_pos := fun j _ => width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j
  decomposition := P.decomposition n

theorem actual_overlap (n : ℕ) (z : Space n) : ((P.data n).activePieces z).card ≤ 3 := by
  classical
  have hsub : (P.data n).activePieces z ⊆
      activePieces n (levels P.θ) (resolution P.c 1 P.θ) (P.β⁻¹ • z) := by
    intro j hj
    obtain ⟨hj,⟨k,hk⟩⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨hj,k,?_⟩
    intro hz
    exact hk (ZeroChainFlatteningAnnulusScaled.scaled_jet_zero_of_zero
      (piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j) P.amplitude P.β z
      k.val (by omega) hz)
  apply (Finset.card_le_card hsub).trans
  apply at_most_three_active_pieces
  · intro j _
    exact resolution_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  · intro i j hij hj
    exact resolutions_separated P.c 1 P.θ P.c_pos.le (by norm_num) P.θ_ge_one i j hij hj

theorem normal_width_small (j : ℕ) : width P.c P.β P.θ j ≤ P.β/128 := by
  have hh : width P.c P.β P.θ j ≤ P.c*P.β := by
    apply mul_le_of_le_one_right (mul_nonneg P.c_pos.le P.β_pos.le)
    exact Real.rpow_le_one_of_one_le_of_nonpos P.θ_ge_one (neg_nonpos.mpr (bExponent_nonneg j))
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right P.c_small P.β_pos.le])

theorem final_normal_width : P.c*P.β/P.θ ≤ width P.c P.β P.θ (levels P.θ) ∧
    width P.c P.β P.θ (levels P.θ) ≤ Real.exp 2*P.c*P.β/P.θ :=
  final_width_bounds P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one

theorem final_normal_width_minimal (j : ℕ) (hj : j ≤ levels P.θ) :
    width P.c P.β P.θ (levels P.θ) ≤ width P.c P.β P.θ j :=
  width_antitone P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one j (levels P.θ) hj

end Parameters

theorem actual_piece_budgets : ∃ B : ℝ,1 ≤ B ∧
    ∀ (P : Parameters) (n j : ℕ),j ≤ levels P.θ → ∀ z : Space n,
      |P.pieces n j z| ≤ B*P.amplitude*P.θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (P.pieces n j) z‖ ≤
        B*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ j)^k.val) := by
  obtain ⟨B,hB,hb⟩ := Schedule.normalized_piece_budgets
  refine ⟨B,hB,fun P n j hj z => ?_⟩
  have hβ := P.β_pos
  have ha := P.amplitude_nonneg
  have hh := hb n P.c P.θ P.c_pos (by linarith [P.c_small]) P.θ_ge_one j hj
  constructor
  · change |P.amplitude*piece n (levels P.θ) (resolution P.c 1 P.θ) j (P.β⁻¹ • z)| ≤ _
    rw [abs_mul,abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hh (P.β⁻¹ • z)).1 ha).trans_eq (by ring)
  · intro k
    have hs := scaled_jet_bound (piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j)
      P.amplitude P.β (B/(pieceResolution P.c 1 P.θ j)^k.val) ha hβ (k.val+1)
      (by omega) (fun w => (hh w).2 k) z
    apply hs.trans_eq
    have he : pieceResolution P.c P.β P.θ j=P.β*pieceResolution P.c 1 P.θ j := by
      dsimp [pieceResolution]
      ring
    rw [he,mul_pow,pow_succ]
    ring

end Bilevel.ChiFine
