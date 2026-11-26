import Bilevel.PolishedLiteralFlattening
import Bilevel.ZeroChainFlatteningAnnulus
import Bilevel.ZeroChainMultiscale

/-! Exact scalar annuli for the manuscript's smooth flattening. -/
noncomputable section
open Set
namespace Bilevel.PolishedLiteralScalarWindows
open ZeroChainPotential ZeroChainResidualCutoffs PolishedLiteralFlattenCutoff
def resolutionDifference (s δ' δ t : ℝ) : ℝ :=
  phi (s*flatten δ' t)-phi (s*flatten δ t)

theorem resolutionDifference_contDiff (s δ' δ : ℝ) : ContDiff ℝ 3 (resolutionDifference s δ' δ) :=
  ((phi_contDiff 3).comp (contDiff_const.mul (flatten_contDiff δ'))).sub
    ((phi_contDiff 3).comp (contDiff_const.mul (flatten_contDiff δ)))

theorem resolutionDifference_zero_inner (s : ℝ) {δ' δ t : ℝ}
    (hδ' : 0 < δ') (hδ : δ' ≤ δ) (ht : |t| ≤ δ') : resolutionDifference s δ' δ t = 0 := by
  rw [resolutionDifference, flatten_zero hδ' ht, flatten_zero (lt_of_lt_of_le hδ' hδ) (ht.trans hδ), sub_self]

theorem resolutionDifference_zero_outer (s : ℝ) {δ' δ t : ℝ}
    (hδ' : 0 < δ') (hδ : δ' ≤ δ) (ht : 2*δ ≤ |t|) : resolutionDifference s δ' δ t = 0 := by
  rw [resolutionDifference, flatten_identity hδ' (by linarith),
    flatten_identity (lt_of_lt_of_le hδ' hδ) ht, sub_self]

theorem resolutionDifference_flat (s : ℝ) {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : ¬(δ' < |t| ∧ |t| < 2*δ)) :
    iteratedDeriv k (resolutionDifference s δ' δ) t = 0 := by
  have he (u : ℝ) (hu : |u| ≤ δ') := resolutionDifference_zero_inner s hδ' hδ hu
  have ho (u : ℝ) (hu : 2*δ ≤ |u|) := resolutionDifference_zero_outer s hδ' hδ hu
  by_cases hk0 : k = 0
  · subst k
    simp only [iteratedDeriv_zero]
    by_cases hsmall : |t| ≤ δ'
    · exact he t hsmall
    · exact ho t (by by_contra! hh; exact ht ⟨lt_of_not_ge hsmall,hh⟩)
  · by_cases hsmall : |t| ≤ δ'
    · exact iteratedDeriv_zero_of_constant_on (resolutionDifference_contDiff s δ' δ)
        (uniqueDiffOn_Icc (show -δ' < δ' by linarith)) (fun u hu => he u (abs_le.mpr hu))
        k (by omega) hk t (abs_le.mp hsmall)
    · have hout : 2*δ ≤ |t| := by by_contra! hh; exact ht ⟨lt_of_not_ge hsmall,hh⟩
      rcases le_total 0 t with hp | hn
      · apply iteratedDeriv_zero_of_constant_on (resolutionDifference_contDiff s δ' δ)
          (uniqueDiffOn_Ici (2*δ)) (fun u hu => ho u (by
            change 2*δ ≤ u at hu
            rw [abs_of_nonneg (by linarith : 0 ≤ u)]
            exact hu)) k (by omega) hk t
        simpa only [abs_of_nonneg hp] using hout
      · apply iteratedDeriv_zero_of_constant_on (resolutionDifference_contDiff s δ' δ)
          (uniqueDiffOn_Iic (-(2*δ))) (fun u hu => ho u (by
            change u ≤ -(2*δ) at hu
            rw [abs_of_nonpos (by linarith : u ≤ 0)]
            linarith)) k (by omega) hk t
        change t ≤ -(2*δ)
        rw [abs_of_nonpos hn] at hout
        linarith

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

def pieceProfile (s : ℝ) (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i < J then resolutionDifference s (δ i) (δ (i-1)) else remainderProfile s (δ (i-1))

theorem pieceProfile_contDiff (s : ℝ) (J : ℕ) (δ : ℕ → ℝ) (i : ℕ) :
    ContDiff ℝ 3 (pieceProfile s J δ i) := by
  unfold pieceProfile
  split_ifs
  · exact resolutionDifference_contDiff _ _ _
  · exact remainderProfile_contDiff _ _

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


end Bilevel.PolishedLiteralScalarWindows
