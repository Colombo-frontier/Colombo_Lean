import MatchingBounds1005.Primitive
import MatchingBounds1005.OrthogonalReadouts

/-! The exact taper correction vanishes, together with its first derivative,
throughout the closed quartic core. -/
noncomputable section
open scoped ContDiff InnerProductSpace BigOperators

namespace MatchingBounds1005.Primitive

def correction (r u : ℝ) : ℝ := potential r u - quarticCore u

theorem quartic_smooth : ContDiff ℝ ∞ quarticCore := by
  unfold quarticCore
  fun_prop

theorem correction_smooth (r : ℝ) : ContDiff ℝ ∞ (correction r) :=
  (potential_smooth r).sub quartic_smooth

theorem correction_hasDerivAt (r u : ℝ) :
    HasDerivAt (correction r) (slope r u - 120 * u ^ 2 * (u - 1)) u :=
  (potential_hasDerivAt r u).sub (quartic_hasDerivAt u)

theorem correction_core {r u : ℝ} (hr : 1 ≤ r) (hu : |u| ≤ r) :
    correction r u = 0 := by
  simp only [correction, potential_core hr hu, sub_self]

theorem correction_deriv_core {r u : ℝ} (hr : 1 ≤ r) (hu : |u| ≤ r) :
    HasDerivAt (correction r) 0 u := by
  convert correction_hasDerivAt r u using 1
  rw [slope_core (zero_lt_one.trans_le hr) hu, sub_self]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem correction_readout_core {r A : ℝ} (hr : 1 ≤ r) (b x : E)
    (hx : |A * ⟪b, x⟫_ℝ| ≤ r) :
    (fun y => correction r (A * ⟪b, y⟫_ℝ)) x = 0 ∧
    HasFDerivAt (fun y => correction r (A * ⟪b, y⟫_ℝ)) (0 : E →L[ℝ] ℝ) x := by
  refine ⟨correction_core hr hx, ?_⟩
  let L : E →L[ℝ] ℝ := A • innerSL ℝ b
  have h := (correction_deriv_core hr hx).comp_hasFDerivAt x L.hasFDerivAt
  simpa only [zero_smul] using h

/-- Censoring taper corrections changes neither value nor derivative while
every hidden readout remains in its actual closed quartic core. -/
theorem disclosed_corrections {ι : Type*} [Fintype ι] (b : ι → E)
    (S : Finset ι) {r A : ℝ} (hr : 1 ≤ r) (x : E)
    (hx : ∀ i, i ∉ S → |A * ⟪b i, x⟫_ℝ| ≤ r) :
    (∑ i, correction r (A * ⟪b i, x⟫_ℝ)) =
      ∑ i ∈ S, correction r (A * ⟪b i, x⟫_ℝ) ∧
    fderiv ℝ (fun y => ∑ i, correction r (A * ⟪b i, y⟫_ℝ)) x =
      fderiv ℝ (fun y => ∑ i ∈ S, correction r (A * ⟪b i, y⟫_ℝ)) x := by
  classical
  have hs (i : ι) : ContDiff ℝ ∞ (fun y : E => correction r (A * ⟪b i, y⟫_ℝ)) :=
    (correction_smooth r).comp (scaledReadout b A i).contDiff
  have hdiff (i : ι) : DifferentiableAt ℝ (fun y : E => correction r (A * ⟪b i, y⟫_ℝ)) x :=
    (hs i).differentiable (by norm_num) x
  refine ⟨?_, ?_⟩
  · exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => correction_core hr (hx i hi)) |>.symm
  · rw [fderiv_sum (fun i _ => hdiff i), fderiv_sum (fun i _ => hdiff i)]
    exact Finset.sum_subset (Finset.subset_univ S)
      (fun i _ hi => (correction_readout_core hr (b i) x (hx i hi)).2.fderiv) |>.symm

end MatchingBounds1005.Primitive
