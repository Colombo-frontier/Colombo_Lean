import Bilevel.PolishedLiteralScalarWindows
import Bilevel.PolishedLiteralLatentSelection

/-! Exact telescope and at-most-three-jet overlap for the actual revised
centered frontier. Only scalar profiles and finite-set arithmetic are reused
from the older construction; the frontier and all selector jets are revised. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.PolishedLiteralMultiscale
open ChiBoundedChain ZeroChainPotential PolishedLiteralLatent
open PolishedLiteral (normalizedResidual normalizedFlat normalizedResidual_selected normalizedFlat_selected)

def approximation (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) (z : Space n) : ℝ :=
  if j<J then normalizedFlat n (δ j) z else normalizedResidual n z

def piece (n J : ℕ) (δ : ℕ → ℝ) : ℕ → Space n → ℝ
  | 0 => approximation n J δ 0
  | j+1 => fun z => approximation n J δ (j+1) z-approximation n J δ j z

theorem approximation_contDiff (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) :
    ContDiff ℝ 3 (approximation n J δ j) := by
  change ContDiff ℝ 3 (fun z => if j<J then normalizedFlat n (δ j) z else normalizedResidual n z)
  by_cases hj : j<J
  · simpa only [approximation,if_pos hj] using PolishedLiteral.normalizedFlat_contDiff n (δ j)
  · simpa only [approximation,if_neg hj] using PolishedLiteral.normalizedResidual_contDiff n 3

theorem piece_contDiff (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) :
    ContDiff ℝ 3 (piece n J δ j) := by
  cases j with
  | zero => exact approximation_contDiff n J δ 0
  | succ j => exact (approximation_contDiff n J δ (j+1)).sub (approximation_contDiff n J δ j)

theorem sum_piece (n J : ℕ) (δ : ℕ → ℝ) (z : Space n) :
    (∑ j ∈ Finset.range (J+1),piece n J δ j z)=normalizedResidual n z := by
  have hs (N : ℕ) : (∑ j ∈ Finset.range (N+1),piece n J δ j z)=approximation n J δ N z := by
    induction N with
    | zero => simp [piece]
    | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      simp only [piece]
      ring
  simpa only [approximation,if_neg (lt_irrefl J)] using hs J

def pieceProfile (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  -PolishedLiteralScalarWindows.pieceProfile 1 J δ i t

theorem pieceProfile_contDiff (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) :
    ContDiff ℝ 3 (pieceProfile J δ i) :=
  (PolishedLiteralScalarWindows.pieceProfile_contDiff 1 J δ i).neg

theorem piece_eq_selected (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j,j<J → 0<δ j) (hsmall : ∀ j,j<J → δ j≤1/16)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) :
    piece n J δ i=selected n (pieceProfile J δ i) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
  have hl : l<J := by omega
  funext z
  simp only [piece,approximation,if_pos hl]
  by_cases hi : l+1<J
  · rw [if_pos hi,normalizedFlat_selected (hpos _ hi) (hsmall _ hi),
      normalizedFlat_selected (hpos _ hl) (hsmall _ hl),add_sub_add_right_eq_sub,
      PolishedLiteral.latentSelected_sub]
    unfold PolishedLiteral.latentSelected selected
    apply Finset.sum_congr rfl
    intro a _
    unfold PolishedLiteral.latentTerm term
    simp only [pieceProfile,PolishedLiteralScalarWindows.pieceProfile,Nat.succ_eq_add_one,
      if_pos hi,Nat.add_sub_cancel,PolishedLiteralScalarWindows.resolutionDifference,one_mul]
    ring
  · rw [if_neg hi,normalizedResidual_selected,
      normalizedFlat_selected (hpos _ hl) (hsmall _ hl),add_sub_add_right_eq_sub,
      PolishedLiteral.latentSelected_sub]
    unfold PolishedLiteral.latentSelected selected
    apply Finset.sum_congr rfl
    intro a _
    unfold PolishedLiteral.latentTerm term
    simp only [pieceProfile,PolishedLiteralScalarWindows.pieceProfile,Nat.succ_eq_add_one,
      if_neg hi,Nat.add_sub_cancel,PolishedLiteralScalarWindows.remainderProfile,one_mul]
    ring

theorem selected_jet_nonzero_term (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Space n) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (selected n f) z≠0) :
    ∃ i,iteratedFDeriv ℝ k (term n f i) z≠0 := by
  by_contra! hz
  rw [selected_jet_sum n hf z k hk] at hn
  apply hn
  exact Finset.sum_eq_zero (fun i _ => hz i)

theorem pieceProfile_flat_outside (J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j,j<J → 0<δ j) (hmono : ∀ i j,i ≤ j → j<J → δ j ≤ δ i)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) (t : ℝ)
    (ht : ¬PolishedLiteralScalarWindows.pieceWindow J δ i |t|) (k : ℕ) (hk : k ≤ 3) :
    iteratedDeriv k (pieceProfile J δ i) t=0 := by
  change iteratedDeriv k (fun u => -PolishedLiteralScalarWindows.pieceProfile 1 J δ i u) t=0
  rw [iteratedDeriv_neg,
    PolishedLiteralScalarWindows.pieceProfile_flat_outside_window 1 J δ hpos hmono i hi0 hiJ t ht k hk,neg_zero]

theorem term_piece_window (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j,j<J → 0<δ j) (hmono : ∀ i j,i ≤ j → j<J → δ j ≤ δ i)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (c : Fin (n+1)) (hc : iteratedFDeriv ℝ k (term n (pieceProfile J δ i) c) z≠0) :
    PolishedLiteralScalarWindows.pieceWindow J δ i |z c| := by
  by_contra ht
  exact hc (term_flat_profile n (pieceProfile_contDiff J δ i) c z k hk
    (fun l hl => pieceProfile_flat_outside J δ hpos hmono i hi0 hiJ _ ht l (by omega)))

def jetActive (n J : ℕ) (δ : ℕ → ℝ) (z : Space n) (i : ℕ) : Prop :=
  ∃ k : Fin 4,iteratedFDeriv ℝ k.val (piece n J δ i) z≠0

def activePieces (n J : ℕ) (δ : ℕ → ℝ) (z : Space n) : Finset ℕ := by
  classical
  exact (Finset.range (J+1)).filter (jetActive n J δ z)

theorem active_noncoarse_indices_near (n J : ℕ) (δ : ℕ → ℝ)
    (hsmall : ∀ j,j<J → δ j≤1/16)
    (hpos : ∀ j,j<J → 0<δ j)
    (hsep : ∀ i j,i<j → j<J → 2*δ j ≤ δ i)
    (z : Space n) (i j : ℕ) (hi0 : 1 ≤ i) (hjJ : j ≤ J)
    (hi : jetActive n J δ z i) (hj : jetActive n J δ z j) : j ≤ i+1 := by
  have hmono (u v : ℕ) (huv : u ≤ v) (hv : v<J) : δ v ≤ δ u := by
    rcases eq_or_lt_of_le huv with he|hlt
    · rw [he]
    · linarith [hsep u v hlt hv,hpos v hv]
  by_contra! hfar
  obtain ⟨ki,hki⟩ := hi
  obtain ⟨kj,hkj⟩ := hj
  rw [piece_eq_selected n J δ hpos hsmall i hi0 (by omega)] at hki
  rw [piece_eq_selected n J δ hpos hsmall j (by omega) hjJ] at hkj
  obtain ⟨c,hc⟩ := selected_jet_nonzero_term n (pieceProfile_contDiff J δ i) z ki.val (by omega) hki
  obtain ⟨d,hd⟩ := selected_jet_nonzero_term n (pieceProfile_contDiff J δ j) z kj.val (by omega) hkj
  have hcd := term_jets_unique n (pieceProfile_contDiff J δ i) (pieceProfile_contDiff J δ j)
    c d z ki.val kj.val (by omega) (by omega) hc hd
  subst d
  have hwi := term_piece_window n J δ hpos hmono i hi0 (by omega) z ki.val (by omega) c hc
  have hwj := term_piece_window n J δ hpos hmono j (by omega) hjJ z kj.val (by omega) c hd
  have hlo : δ i < |z c| := hwi.2 (by omega)
  have hhi : |z c|<2*δ (j-1) := hwj.1
  linarith [hsep i (j-1) (by omega) (by omega)]

theorem at_most_three_active_pieces (n J : ℕ) (δ : ℕ → ℝ)
    (hsmall : ∀ j,j<J → δ j≤1/16)
    (hpos : ∀ j,j<J → 0<δ j)
    (hsep : ∀ i j,i<j → j<J → 2*δ j ≤ δ i) (z : Space n) :
    (activePieces n J δ z).card ≤ 3 := by
  classical
  let S := activePieces n J δ z
  have htwo : (S.erase 0).card ≤ 2 := by
    apply ZeroChainMultiscale.card_le_two_of_near
    intro i hi j hj _
    have hiS := Finset.mem_of_mem_erase hi
    have hjS := Finset.mem_of_mem_erase hj
    have hi0 : 1 ≤ i := by have := Finset.ne_of_mem_erase hi;omega
    have hmemi : i∈(Finset.range (J+1)).filter (jetActive n J δ z) := hiS
    have hmemj : j∈(Finset.range (J+1)).filter (jetActive n J δ z) := hjS
    exact active_noncoarse_indices_near n J δ hsmall hpos hsep z i j hi0
      (by have := Finset.mem_range.mp (Finset.mem_filter.mp hmemj).1;omega)
      (Finset.mem_filter.mp hmemi).2 (Finset.mem_filter.mp hmemj).2
  have hsub : S⊆insert 0 (S.erase 0) := by intro i hi;by_cases he : i=0 <;> simp [he,hi]
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le 0 (S.erase 0))
  change S.card ≤ 3
  omega

end Bilevel.PolishedLiteralMultiscale
