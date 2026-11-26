import Geode.Candidates

/-! Every residual candidate sphere has a candidate at least its radius away
from an arbitrary output, including outputs outside the public subspace. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem candidate_far_of_nonpositive_pairing {W : Submodule ℝ (Ambient E)}
    {c : Point E} (hc : c.val ∈ W) {v : Ambient E}
    (hv : IsResidual W v) (hv1 : form E v v = 1) {S : ℝ} (hS : 0 ≤ S)
    (x : Point E) (hxv : form E x.val v ≤ 0) :
    ∃ p ∈ candidateSet W c S, S ≤ dist x p := by
  refine ⟨unitGeodesic c v (residual_tangent hc hv) hv1 S,
    candidate_from_residual hc hv hv1 S, (le_dist_iff hS).mpr ?_⟩
  change Real.cosh S ≤ -form E x.val (Real.cosh S • c.val + Real.sinh S • v)
  simp only [form_add_right, form_smul_right]
  have hs : Real.sinh S * form E x.val v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.sinh_nonneg_iff.mpr hS) hxv
  have hcauchy := mul_le_mul_of_nonneg_left (reverse_cauchy x c) (Real.cosh_pos S).le
  nlinarith only [hs, hcauchy]

theorem candidate_far_of_residual_unit {W : Submodule ℝ (Ambient E)}
    {c : Point E} (hc : c.val ∈ W) {v : Ambient E}
    (hv : IsResidual W v) (hv1 : form E v v = 1) {S : ℝ} (hS : 0 ≤ S)
    (x : Point E) : ∃ p ∈ candidateSet W c S, S ≤ dist x p := by
  by_cases h : form E x.val v ≤ 0
  · exact candidate_far_of_nonpositive_pairing hc hv hv1 hS x h
  · have hvneg : IsResidual W (-v) := by intro w hw; simp [hv w hw]
    have hvneg1 : form E (-v) (-v) = 1 := by simpa using hv1
    apply candidate_far_of_nonpositive_pairing hc hvneg hvneg1 hS x
    simpa only [form_neg_right, neg_nonpos] using (not_le.mp h).le

theorem candidate_far_of_nonempty {W : Submodule ℝ (Ambient E)}
    {c : Point E} (hc : c.val ∈ W) {S : ℝ} (hS : 0 ≤ S)
    (hne : (candidateSet W c S).Nonempty) (x : Point E) :
    ∃ p ∈ candidateSet W c S, S ≤ dist x p := by
  obtain ⟨_, v, hv, hv1, _⟩ := hne
  exact candidate_far_of_residual_unit hc hv hv1 hS x

end Geode.Lorentz
