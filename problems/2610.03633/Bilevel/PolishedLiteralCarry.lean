import Bilevel.PolishedLiteralMultiscale
import Bilevel.PolishedLiteralSelection
import Bilevel.ZeroChainSchedule

/-! Exact finite decompositions and bounded jet overlap survive the smooth
radial/frame coordinate map. The composition estimate preserves the physical
resolution scale, including the first derivative. -/

noncomputable section
namespace Bilevel.PolishedLiteralCarry

open ChiBoundedChain PolishedLiteralMultiscale ZeroChainResidualJets

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def carriedPiece (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) (H : E → Space n)
    (j : ℕ) (x : E) : ℝ := a * piece n J δ j (H x)

theorem carriedPiece_contDiff (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H) (j : ℕ) : ContDiff ℝ 3 (carriedPiece n J δ a H j) :=
  contDiff_const.mul ((piece_contDiff n J δ j).comp hH)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_carriedPiece (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) (H : E → Space n) (x : E) :
    (∑ j ∈ Finset.range (J+1), carriedPiece n J δ a H j x) =
      a * PolishedLiteral.normalizedResidual n (H x) := by
  simp only [carriedPiece, ← Finset.mul_sum, sum_piece]

theorem carriedPiece_flat (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H) (j : ℕ) (x : E)
    (hj : ¬jetActive n J δ (H x) j) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (carriedPiece n J δ a H j) x = 0 := by
  have hb (l : ℕ) (hl : l ≤ k) : ‖iteratedFDeriv ℝ l (piece n J δ j) (H x)‖ = 0 := by
    have he : iteratedFDeriv ℝ l (piece n J δ j) (H x) = 0 := by
      by_contra hn
      exact hj ⟨⟨l,by omega⟩,hn⟩
    rw [he,norm_zero]
  have hc := ZeroChainResidualJets.flat_jet_comp hH (piece_contDiff n J δ j) x k hk hb
  change iteratedFDeriv ℝ k (fun w => a • (piece n J δ j ∘ H) w) x = 0
  rw [iteratedFDeriv_const_smul_apply' (((piece_contDiff n J δ j).comp hH).of_le
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)).contDiffAt, hc, smul_zero]

def carriedActive (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) (H : E → Space n) (x : E) : Finset ℕ := by
  classical
  exact (Finset.range (J+1)).filter (fun j => ∃ k : Fin 4,
    iteratedFDeriv ℝ k.val (carriedPiece n J δ a H j) x ≠ 0)

theorem carriedActive_subset (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H) (x : E) :
    carriedActive n J δ a H x ⊆ activePieces n J δ (H x) := by
  classical
  intro j hj
  obtain ⟨hj, k, hk⟩ := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  refine ⟨hj, ?_⟩
  by_contra hn
  exact hk (carriedPiece_flat n J δ a hH j x hn k.val (by omega))

theorem at_most_three_carried_pieces (n J : ℕ) (δ : ℕ → ℝ) (a : ℝ) {H : E → Space n}
    (hH : ContDiff ℝ 3 H)
    (hpos : ∀ j, j < J → 0 < δ j) (hsmall : ∀ j, j < J → δ j ≤ 1/16)
    (hsep : ∀ i j, i < j → j < J → 2*δ j ≤ δ i) (x : E) :
    (carriedActive n J δ a H x).card ≤ 3 :=
  (Finset.card_le_card (carriedActive_subset n J δ a hH x)).trans
    (at_most_three_active_pieces n J δ hsmall hpos hsep (H x))


end Bilevel.PolishedLiteralCarry
