import FullJet.UniformConditioning
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators ENNReal

namespace FullJet

variable {α : Type*} [DecidableEq α]

/-- Uniform sampling of a fixed number of positive signs from the unseen labels. -/
noncomputable def fixedSizeLaw (U : Finset α) (k : ℕ) (hk : k ≤ U.card) : PMF (Finset α) :=
  PMF.uniformOfFinset (U.powersetCard k) (Finset.powersetCard_nonempty.mpr hk)

theorem powersetCard_filter_absent (U : Finset α) (k : ℕ) (i : α) :
    (U.powersetCard k).filter (fun S => i ∉ S) = (U.erase i).powersetCard k := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_erase]
  tauto

theorem powersetCard_filter_present (U : Finset α) (k : ℕ) (i : α) (hi : i ∈ U) :
    (U.powersetCard (k + 1)).filter (fun S => i ∈ S) =
      ((U.erase i).powersetCard k).image (insert i) := by
  ext S
  constructor
  · intro hS
    obtain ⟨⟨hsub, hcard⟩, hin⟩ := (Finset.mem_filter.mp hS).imp_left Finset.mem_powersetCard.mp
    refine Finset.mem_image.mpr ⟨S.erase i, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.erase_subset_erase i hsub
    · rw [Finset.card_erase_of_mem hin, hcard]; omega
    · exact Finset.insert_erase hin
  · intro hS
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hR
    have hnot : i ∉ R := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset hi (hsub.trans (Finset.erase_subset _ _))
    · rw [Finset.card_insert_of_not_mem hnot, hcard]

theorem insert_injOn_powersetCard_erase (U : Finset α) (k : ℕ) (i : α) :
    Set.InjOn (insert i) ((U.erase i).powersetCard k : Set (Finset α)) := by
  intro S hS R hR heq
  have hS' : i ∉ S := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS).1 h)).1 rfl
  have hR' : i ∉ R := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hR).1 h)).1 rfl
  have h := congrArg (fun A : Finset α => A.erase i) heq
  simpa [hS', hR'] using h

theorem card_powersetCard_filter_present (U : Finset α) (k : ℕ) (i : α) (hi : i ∈ U) :
    ((U.powersetCard (k + 1)).filter (fun S => i ∈ S)).card = (U.card - 1).choose k := by
  rw [powersetCard_filter_present U k i hi,
    Finset.card_image_of_injOn (insert_injOn_powersetCard_erase U k i),
    Finset.card_powersetCard, Finset.card_erase_of_mem hi]

/-- The exact next-sign probability under sampling without replacement. -/
theorem fixedSizeLaw_present_probability_succ (U : Finset α) (k : ℕ) (i : α)
    (hi : i ∈ U) (hk : k + 1 ≤ U.card) :
    ((fixedSizeLaw U (k + 1) hk).toOuterMeasure {S | i ∈ S}).toReal = (k + 1 : ℕ) / (U.card : ℝ) := by
  have hU : 0 < U.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hchoose : 0 < U.card.choose (k + 1) := Nat.choose_pos hk
  have hident : U.card * (U.card - 1).choose k = U.card.choose (k + 1) * (k + 1) := by
    have h := Nat.succ_mul_choose_eq (U.card - 1) k
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hU] using h
  have hident' : (U.card : ℝ) * ((U.card - 1).choose k : ℝ) =
      (U.card.choose (k + 1) : ℝ) * (k + 1 : ℕ) := by exact_mod_cast hident
  have hUn : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
  have hCn : (U.card.choose (k + 1) : ℝ) ≠ 0 := by exact_mod_cast hchoose.ne'
  unfold fixedSizeLaw
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_setOf_eq, card_powersetCard_filter_present U k i hi,
    Finset.card_powersetCard, ENNReal.toReal_div, ENNReal.toReal_natCast]
  apply (div_eq_div_iff hCn hUn).mpr
  convert (by simpa only [mul_comm] using hident' :
    (((U.card - 1).choose k : ℕ) : ℝ) * U.card =
      (k + 1 : ℕ) * (U.card.choose (k + 1) : ℝ)) using 1
  congr 2
  convert card_powersetCard_filter_present U k i hi using 1
  congr 1
  ext S
  simp only [Finset.mem_filter]

theorem fixedSizeLaw_present_probability (U : Finset α) (k : ℕ) (i : α)
    (hi : i ∈ U) (hk : k ≤ U.card) :
    ((fixedSizeLaw U k hk).toOuterMeasure {S | i ∈ S}).toReal = (k : ℝ) / U.card := by
  cases k with
  | zero =>
    simp [fixedSizeLaw]
    ext S
    simp
    rintro rfl
    simp
  | succ k => exact fixedSizeLaw_present_probability_succ U k i hi hk

/-- Exact posterior after observing a positive sign: erase its label and reduce
the remaining positive count by one. Inserting the observed label restores the
original full column. -/
theorem fixedSizeLaw_condition_present (U : Finset α) (k : ℕ) (i : α)
    (hi : i ∈ U) (hk : k + 1 ≤ U.card) (hkr : k ≤ (U.erase i).card)
    (hpos : ∃ S ∈ {S : Finset α | i ∈ S}, S ∈ (fixedSizeLaw U (k + 1) hk).support) :
    (fixedSizeLaw U (k + 1) hk).filter {S | i ∈ S} hpos =
      (fixedSizeLaw (U.erase i) k hkr).map (insert i) := by
  have hR : ((U.erase i).powersetCard k).Nonempty := Finset.powersetCard_nonempty.mpr hkr
  have hA : ((U.powersetCard (k + 1)).filter (fun S => i ∈ S)).Nonempty := by
    rw [powersetCard_filter_present U k i hi]
    exact hR.image (insert i)
  unfold fixedSizeLaw
  rw [uniformOfFinset_filter (U.powersetCard (k + 1))
    (Finset.powersetCard_nonempty.mpr hk) {S : Finset α | i ∈ S} hA hpos]
  trans PMF.uniformOfFinset (((U.erase i).powersetCard k).image (insert i)) (hR.image (insert i))
  · congr 1
    convert powersetCard_filter_present U k i hi using 1
  · exact (uniformOfFinset_map_injOn _ hR (insert i) (insert_injOn_powersetCard_erase U k i)).symm

/-- Exact posterior after observing a negative sign: only the label is erased. -/
theorem fixedSizeLaw_condition_absent (U : Finset α) (k : ℕ) (i : α)
    (hk : k ≤ U.card) (hkr : k ≤ (U.erase i).card)
    (hpos : ∃ S ∈ {S : Finset α | i ∉ S}, S ∈ (fixedSizeLaw U k hk).support) :
    (fixedSizeLaw U k hk).filter {S | i ∉ S} hpos = fixedSizeLaw (U.erase i) k hkr := by
  have hA : ((U.powersetCard k).filter (fun S => i ∉ S)).Nonempty := by
    rw [powersetCard_filter_absent]
    exact Finset.powersetCard_nonempty.mpr hkr
  unfold fixedSizeLaw
  rw [uniformOfFinset_filter (U.powersetCard k)
    (Finset.powersetCard_nonempty.mpr hk) {S : Finset α | i ∉ S} hA hpos]
  congr 1
  convert powersetCard_filter_absent U k i using 1

end FullJet
