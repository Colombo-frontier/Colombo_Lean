import Bilevel.ZeroChainFlatteningAnnulusScaled

/-! Exact multiscale residual pieces and bounded overlap of their actual jets. -/

noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainMultiscale
open ZeroChain ZeroChainPotential ZeroChainResidualCutoffs ZeroChainResidual ZeroChainChildProfiles
  ZeroChainFlatteningCutoff ZeroChainFlatteningMap ZeroChainFlatteningAnnulus

def remainderProfile (s δ t : ℝ) : ℝ := phi (s*t)-phi (s*flatten δ t)

theorem remainderProfile_contDiff (s δ : ℝ) : ContDiff ℝ 3 (remainderProfile s δ) :=
  ((phi_contDiff 3).comp (contDiff_const.mul contDiff_id)).sub
    ((phi_contDiff 3).comp (contDiff_const.mul (flatten_contDiff δ)))

theorem remainderProfile_zero_outer (s : ℝ) {δ t : ℝ} (hδ : 0 < δ) (ht : 2*δ ≤ |t|) :
    remainderProfile s δ t = 0 := by rw [remainderProfile, flatten_identity hδ ht, sub_self]

theorem remainderProfile_flat_outer (s : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : 2*δ ≤ |t|) : iteratedDeriv k (remainderProfile s δ) t = 0 := by
  by_cases hk0 : k = 0
  · subst k
    simpa only [iteratedDeriv_zero] using remainderProfile_zero_outer s hδ ht
  · rcases le_total 0 t with hp | hn
    · apply iteratedDeriv_zero_of_constant_on (remainderProfile_contDiff s δ) (uniqueDiffOn_Ici (2*δ))
        (fun u hu => remainderProfile_zero_outer s hδ (by
          change 2*δ ≤ u at hu
          simpa only [abs_of_nonneg (by linarith : 0 ≤ u)] using hu)) k (by omega) hk t
      simpa only [abs_of_nonneg hp] using ht
    · apply iteratedDeriv_zero_of_constant_on (remainderProfile_contDiff s δ) (uniqueDiffOn_Iic (-(2*δ)))
        (fun u hu => remainderProfile_zero_outer s hδ (by
          change u ≤ -(2*δ) at hu
          rw [abs_of_nonpos (by linarith : u ≤ 0)]
          linarith)) k (by omega) hk t
      change t ≤ -(2*δ)
      rw [abs_of_nonpos hn] at ht
      linarith

theorem normalized_remainder_eq {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16) (n : ℕ) :
    (fun z => ZeroChainResidual.residual n z-ZeroChainResidual.residual n (flattenMap n δ z)) =
      rawChild n (remainderProfile 1 δ) (remainderProfile (-1) δ) := by
  ext z
  calc
    _ = rawResidual n z-rawResidual n (flattenMap n δ z) := by dsimp [ZeroChainResidual.residual]; ring
    _ = rawChild n phi (fun t => phi (-t)) z-
        rawChild n (fun t => phi (flatten δ t)) (fun t => phi (-flatten δ t)) z := by
      rw [rawResidual_eq_rawChild, rawResidual_flattenMap_eq hδ hsmall]
    _ = _ := by
      rw [rawChild_sub]
      congr 2 <;> ext t <;> simp [remainderProfile]

def approximation (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) (z : Space n) : ℝ :=
  if j < J then ZeroChainResidual.residual n (flattenMap n (δ j) z) else ZeroChainResidual.residual n z

def piece (n J : ℕ) (δ : ℕ → ℝ) : ℕ → Space n → ℝ
  | 0 => approximation n J δ 0
  | j+1 => fun z => approximation n J δ (j+1) z-approximation n J δ j z

theorem approximation_contDiff (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) : ContDiff ℝ 3 (approximation n J δ j) := by
  change ContDiff ℝ 3 (fun z => if j < J then ZeroChainResidual.residual n (flattenMap n (δ j) z) else ZeroChainResidual.residual n z)
  by_cases hj : j < J
  · simp only [if_pos hj]
    exact (residual_contDiff n).comp (flattenMap_contDiff n (δ j))
  · simpa only [if_neg hj] using residual_contDiff n

theorem piece_contDiff (n J : ℕ) (δ : ℕ → ℝ) (j : ℕ) : ContDiff ℝ 3 (piece n J δ j) := by
  cases j with
  | zero => exact approximation_contDiff n J δ 0
  | succ j => exact (approximation_contDiff n J δ (j+1)).sub (approximation_contDiff n J δ j)

theorem sum_piece (n J : ℕ) (δ : ℕ → ℝ) (z : Space n) :
    (∑ j ∈ Finset.range (J+1), piece n J δ j z) = ZeroChainResidual.residual n z := by
  have hs (N : ℕ) : (∑ j ∈ Finset.range (N+1), piece n J δ j z) = approximation n J δ N z := by
    induction N with
    | zero => simp [piece]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [piece]
      ring
  simpa only [approximation, if_neg (lt_irrefl J)] using hs J

theorem piece_zero_resolution (n : ℕ) (δ : ℕ → ℝ) : piece n 0 δ 0 = ZeroChainResidual.residual n := by
  ext z
  simp [piece, approximation]

def pieceProfile (s : ℝ) (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i < J then resolutionDifference s (δ i) (δ (i-1)) else remainderProfile s (δ (i-1))

theorem pieceProfile_contDiff (s : ℝ) (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) :
    ContDiff ℝ 3 (pieceProfile s J δ i) := by
  unfold pieceProfile
  split_ifs
  · exact resolutionDifference_contDiff _ _ _
  · exact remainderProfile_contDiff _ _

theorem piece_eq_rawChild (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j, j < J → 0 < δ j) (hsmall : ∀ j, j < J → δ j ≤ 1/16)
    (hmono : ∀ i j, i ≤ j → j < J → δ j ≤ δ i)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) :
    piece n J δ i = rawChild n (pieceProfile 1 J δ i) (pieceProfile (-1) J δ i) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
  have hl : l < J := by omega
  by_cases hi : l+1 < J
  · simp only [piece, approximation, if_pos hi, if_pos hl, pieceProfile, Nat.add_sub_cancel]
    exact normalized_difference_eq (hpos (l+1) hi) (hmono l (l+1) (by omega) hi) (hsmall l hl) n
  · simp only [piece, approximation, if_neg hi, if_pos hl, pieceProfile, Nat.add_sub_cancel]
    exact normalized_remainder_eq (hpos l hl) (hsmall l hl) n

def pieceWindow (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) (t : ℝ) : Prop :=
  t < 2*δ (i-1) ∧ (i < J → δ i < t)

theorem pieceProfile_flat_outside_window (s : ℝ) (J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j, j < J → 0 < δ j) (hmono : ∀ i j, i ≤ j → j < J → δ j ≤ δ i)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) (t : ℝ)
    (ht : ¬pieceWindow J δ i |t|) (k : ℕ) (hk : k ≤ 3) :
    iteratedDeriv k (pieceProfile s J δ i) t = 0 := by
  have hprev : i-1 < J := by omega
  by_cases hi : i < J
  · rw [pieceProfile, if_pos hi]
    apply resolutionDifference_flat s (hpos i hi) (hmono (i-1) i (Nat.sub_le _ _) hi) k hk t
    intro hh
    exact ht ⟨hh.2,fun _ => hh.1⟩
  · rw [pieceProfile, if_neg hi]
    apply remainderProfile_flat_outer s (hpos (i-1) hprev) k hk t
    by_contra! hn
    exact ht ⟨hn,fun hh => (hi hh).elim⟩

theorem rawChild_jet_nonzero_term (n : ℕ) {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (z : Space n) (k : ℕ) (hk : k ≤ 3) (h : iteratedFDeriv ℝ k (rawChild n p m) z ≠ 0) :
    ∃ i : Fin (n+1), iteratedFDeriv ℝ k (maskedChild p m i) z ≠ 0 := by
  classical
  by_contra! he
  apply h
  change iteratedFDeriv ℝ k (fun w => ∑ i : Fin (n+1), maskedChild p m i w) z = 0
  rw [iteratedFDeriv_sum (fun i _ => (maskedChild_contDiff hp hm i).of_le
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => he i)

theorem nonzero_child_piece_window (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j, j < J → 0 < δ j) (hmono : ∀ i j, i ≤ j → j < J → δ j ≤ δ i)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) (z : Space n) (k : ℕ) (hk : k ≤ 3)
    (c : Fin (n+1))
    (hc : iteratedFDeriv ℝ k (maskedChild (pieceProfile 1 J δ i) (pieceProfile (-1) J δ i) c) z ≠ 0) :
    pieceWindow J δ i |z c| := by
  by_contra ht
  apply hc
  exact maskedChild_flat_child (pieceProfile_contDiff 1 J δ i) (pieceProfile_contDiff (-1) J δ i) c z k hk
    (fun l hl => pieceProfile_flat_outside_window 1 J δ hpos hmono i hi0 hiJ _ ht l (by omega))
    (fun l hl => pieceProfile_flat_outside_window (-1) J δ hpos hmono i hi0 hiJ _ ht l (by omega))

def jetActive (n J : ℕ) (δ : ℕ → ℝ) (z : Space n) (i : ℕ) : Prop :=
  ∃ k : Fin 4, iteratedFDeriv ℝ k.val (piece n J δ i) z ≠ 0

def activePieces (n J : ℕ) (δ : ℕ → ℝ) (z : Space n) : Finset ℕ := by
  classical
  exact (Finset.range (J+1)).filter (jetActive n J δ z)

theorem active_noncoarse_indices_near (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j, j < J → 0 < δ j) (hsmall : ∀ j, j < J → δ j ≤ 1/16)
    (hsep : ∀ i j, i < j → j < J → 2*δ j ≤ δ i)
    (z : Space n) (i j : ℕ) (hi0 : 1 ≤ i) (hjJ : j ≤ J)
    (hi : jetActive n J δ z i) (hj : jetActive n J δ z j) : j ≤ i+1 := by
  have hmono (u v : ℕ) (huv : u ≤ v) (hv : v < J) : δ v ≤ δ u := by
    rcases eq_or_lt_of_le huv with he | hlt
    · rw [he]
    · linarith [hsep u v hlt hv, hpos v hv]
  by_contra! hfar
  obtain ⟨ki,hki⟩ := hi
  obtain ⟨kj,hkj⟩ := hj
  rw [piece_eq_rawChild n J δ hpos hsmall hmono i hi0 (by omega)] at hki
  rw [piece_eq_rawChild n J δ hpos hsmall hmono j (by omega) hjJ] at hkj
  obtain ⟨c,hc⟩ := rawChild_jet_nonzero_term n (pieceProfile_contDiff 1 J δ i)
    (pieceProfile_contDiff (-1) J δ i) z ki.val (by omega) hki
  obtain ⟨d,hd⟩ := rawChild_jet_nonzero_term n (pieceProfile_contDiff 1 J δ j)
    (pieceProfile_contDiff (-1) J δ j) z kj.val (by omega) hkj
  have hcd : c = d := by
    by_contra hne
    exact hd (maskedChild_cross_jet_exclusive (pieceProfile_contDiff 1 J δ i) (pieceProfile_contDiff (-1) J δ i)
      (pieceProfile_contDiff 1 J δ j) (pieceProfile_contDiff (-1) J δ j) z c d hne ki.val kj.val (by omega) (by omega) hc)
  subst d
  have hwi := nonzero_child_piece_window n J δ hpos hmono i hi0 (by omega) z ki.val (by omega) c hc
  have hwj := nonzero_child_piece_window n J δ hpos hmono j (by omega) hjJ z kj.val (by omega) c hd
  have hlo : δ i < |z c| := hwi.2 (by omega)
  have hhi : |z c| < 2*δ (j-1) := hwj.1
  have hseparation := hsep i (j-1) (by omega) (by omega)
  linarith

theorem card_le_two_of_near (S : Finset ℕ)
    (h : ∀ i ∈ S, ∀ j ∈ S, i < j → j ≤ i+1) : S.card ≤ 2 := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m ∈ S := Finset.min'_mem S hS
    have hsub : S ⊆ Finset.Icc m (m+1) := by
      intro j hj
      have hmj : m ≤ j := Finset.min'_le S j hj
      apply Finset.mem_Icc.mpr
      refine ⟨hmj,?_⟩
      rcases eq_or_lt_of_le hmj with he | hlt
      · omega
      · exact h m hm j hj hlt
    have hc := Finset.card_le_card hsub
    have hi : (Finset.Icc m (m+1)).card = 2 := by simp; omega
    simpa only [hi] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- At every point, at most three multiscale pieces have any nonzero jet
through order three. The proof uses actual annular cancellation, not an
overlap hypothesis on the pieces. -/
theorem at_most_three_active_pieces (n J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j, j < J → 0 < δ j) (hsmall : ∀ j, j < J → δ j ≤ 1/16)
    (hsep : ∀ i j, i < j → j < J → 2*δ j ≤ δ i) (z : Space n) :
    (activePieces n J δ z).card ≤ 3 := by
  classical
  let S := activePieces n J δ z
  have htwo : (S.erase 0).card ≤ 2 := by
    apply card_le_two_of_near
    intro i hi j hj _
    have hiS := Finset.mem_of_mem_erase hi
    have hjS := Finset.mem_of_mem_erase hj
    have hi0 : 1 ≤ i := by have := Finset.ne_of_mem_erase hi; omega
    have hmemi : i ∈ (Finset.range (J+1)).filter (jetActive n J δ z) := hiS
    have hmemj : j ∈ (Finset.range (J+1)).filter (jetActive n J δ z) := hjS
    exact active_noncoarse_indices_near n J δ hpos hsmall hsep z i j hi0
      (by have := Finset.mem_range.mp (Finset.mem_filter.mp hmemj).1; omega)
      (Finset.mem_filter.mp hmemi).2 (Finset.mem_filter.mp hmemj).2
  have hsub : S ⊆ insert 0 (S.erase 0) := by intro i hi; by_cases he : i = 0 <;> simp [he,hi]
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le 0 (S.erase 0))
  change S.card ≤ 3
  omega

end Bilevel.ZeroChainMultiscale
