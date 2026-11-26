import Bilevel.ChiSplitFineSchedule
import Bilevel.ChiSplitFineScaled
import Bilevel.ChiFineGeneric

/-! Concrete finite fine-extension data for the actual split frontier, with
the manuscript's logarithmic resolutions and at-most-three active jets. -/
noncomputable section
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ZeroChainSchedule

def pieces (P : ChiFine.Parameters) (n j : ℕ) (z : Latent n) : ℝ :=
  P.amplitude*piece n (levels P.θ) (resolution P.c 1 P.θ) j (P.β⁻¹ • z)

theorem pieces_contDiff (P : ChiFine.Parameters) (n j : ℕ) : ContDiff ℝ 3 (pieces P n j) :=
  contDiff_const.mul ((piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j).comp
    (contDiff_id.const_smul P.β⁻¹))

theorem decomposition (P : ChiFine.Parameters) (n : ℕ) (z : Latent n) :
    (∑ j ∈ Finset.range (levels P.θ+1),pieces P n j z)=frontier n P.ℓ P.β z := by
  change (∑ j ∈ Finset.range (levels P.θ+1),P.amplitude*
    piece n (levels P.θ) (resolution P.c 1 P.θ) j (P.β⁻¹ • z))=_
  rw [← Finset.mul_sum,sum_piece]
  rfl

def data (P : ChiFine.Parameters) (n : ℕ) : CompensatedMean.Data (E:=Latent n) where
  μ := 1
  L := 1
  J := levels P.θ
  r := frontier n P.ℓ P.β
  A := fun _ => 0
  e := pieces P n
  w := width P.c P.β P.θ
  r_smooth := frontier_contDiff n P.ℓ P.β
  A_smooth := contDiff_const
  e_smooth := pieces_contDiff P n
  w_pos := fun j _ => width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j
  decomposition := decomposition P n

theorem scaled_jet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 3 f) (a β : ℝ) (z : E) (k : ℕ) (hk : k≤3)
    (hz : iteratedFDeriv ℝ k f (β⁻¹ • z)=0) :
    iteratedFDeriv ℝ k (fun w => a*f (β⁻¹ • w)) z=0 := by
  let L : E →L[ℝ] E := β⁻¹ • ContinuousLinearMap.id ℝ E
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  change iteratedFDeriv ℝ k (fun w => a • (f ∘ L) w) z=0
  rw [iteratedFDeriv_const_smul_apply' (((hf.comp L.contDiff).of_le hk').contDiffAt),
    L.iteratedFDeriv_comp_right hf z hk']
  change a • (iteratedFDeriv ℝ k f (β⁻¹ • z)).compContinuousLinearMap (fun _ => L)=0
  rw [hz]
  ext v
  simp

theorem actual_overlap (P : ChiFine.Parameters) (n : ℕ) (z : Latent n) :
    ((data P n).activePieces z).card≤3 := by
  classical
  have hsub : (data P n).activePieces z⊆
      activePieces n (levels P.θ) (resolution P.c 1 P.θ) (P.β⁻¹ • z) := by
    intro j hj
    obtain ⟨hj,⟨k,hk⟩⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨hj,k,?_⟩
    intro hz
    exact hk (scaled_jet_zero _ (piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j)
      P.amplitude P.β z k.val (by omega) hz)
  apply (Finset.card_le_card hsub).trans
  apply at_most_three_active_pieces
  · intro j _
    exact resolution_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  · intro i j hij hj
    exact resolutions_separated P.c 1 P.θ P.c_pos.le (by norm_num) P.θ_ge_one i j hij hj

theorem actual_piece_budgets : ∃ B : ℝ,1≤B ∧ ∀ (P : ChiFine.Parameters) (n j : ℕ),
    j≤levels P.θ → ∀ z : Latent n,
      |pieces P n j z|≤B*P.amplitude*P.θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (pieces P n j) z‖≤
        B*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ j)^k.val) := by
  obtain ⟨B,hB,hb⟩ := Schedule.normalized_piece_budgets
  refine ⟨B,hB,fun P n j hj z => ?_⟩
  have hβ := P.β_pos
  have ha := P.amplitude_nonneg
  have hh := hb n P.c P.θ P.c_pos (by linarith [P.c_small]) P.θ_ge_one j hj
  constructor
  · change |P.amplitude*piece n (levels P.θ) (resolution P.c 1 P.θ) j (P.β⁻¹ • z)|≤_
    rw [abs_mul,abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hh (P.β⁻¹ • z)).1 ha).trans_eq (by ring)
  · intro k
    have hs := ChiSplitChain.scaled_jet_bound (piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) j)
      P.amplitude P.β (B/(pieceResolution P.c 1 P.θ j)^k.val) ha hβ (k.val+1) (by omega)
      (fun w => (hh w).2 k) z
    apply hs.trans_eq
    have he : pieceResolution P.c P.β P.θ j=P.β*pieceResolution P.c 1 P.θ j := by
      dsimp [pieceResolution]
      ring
    rw [he,mul_pow,pow_succ]
    ring

theorem actual_coupling_budgets : ∃ B : ℝ,1≤B ∧ ∀ (P : ChiFine.Parameters) (n : ℕ)
    (y : CompensatedMean.LowerSpace (Latent n)),
      ‖iteratedFDeriv ℝ 1 (data P n).coupling y‖≤6*SmallGapLiftSupport.C*B*P.ℓ*P.β^2 ∧
      ‖iteratedFDeriv ℝ 2 (data P n).coupling y‖≤12*SmallGapLiftSupport.C*B*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 (data P n).coupling y‖≤24*SmallGapLiftSupport.C*B*P.ℓ*P.θ/P.c^2 := by
  obtain ⟨B,hB,hb⟩ := actual_piece_budgets
  refine ⟨B,hB,fun P n y => ?_⟩
  exact ChiFine.generic_coupling_bounds P (data P n) rfl (fun _ => rfl) B hB
    (fun j hj x => hb P n j hj x) (actual_overlap P n) y

end Bilevel.ChiSplitFine
