import Nonsmooth.GrunbaumApplication
import Mathlib.Analysis.Convex.Combination

open Set
open scoped BigOperators
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_sum_mem_of_sum_le_one {ι : Type} [Fintype ι] {S : Set E}
    (hconv : Convex ℝ S) (hzero : (0 : E) ∈ S) (w : ι → ℝ) (v : ι → E)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) (hv : ∀ i, v i ∈ S) :
    (∑ i, w i • v i) ∈ S := by
  classical
  have hq : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  by_cases hz : ∑ i, w i = 0
  · have hwi : ∀ i, w i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp hz i (Finset.mem_univ i)
    simpa [hwi] using hzero
  · have hpos : 0 < ∑ i, w i := lt_of_le_of_ne hq (Ne.symm hz)
    have hmass := hconv.centerMass_mem (t := Finset.univ) (w := w) (z := v)
      (fun i _ => hw i) hpos (fun i _ => hv i)
    have h := hconv.smul_mem_of_zero_mem hzero hmass ⟨hq, hsum⟩
    simpa [Finset.centerMass, smul_smul, hz] using h

theorem symmetric_convex_signed_sum_mem {ι : Type} [Fintype ι] {S : Set E}
    (hconv : Convex ℝ S) (hzero : (0 : E) ∈ S)
    (hsym : ∀ x ∈ S, -x ∈ S) (c : ι → ℝ) (v : ι → E)
    (hsum : ∑ i, |c i| ≤ 1) (hv : ∀ i, v i ∈ S) :
    (∑ i, c i • v i) ∈ S := by
  classical
  let w : ι → E := fun i => if 0 ≤ c i then v i else -v i
  have hw : ∀ i, w i ∈ S := by
    intro i
    dsimp only [w]
    split_ifs
    · exact hv i
    · exact hsym _ (hv i)
  have h := convex_sum_mem_of_sum_le_one hconv hzero (fun i => |c i|) w
    (fun i => abs_nonneg _) hsum hw
  have heq : ∀ i, |c i| • w i = c i • v i := by
    intro i
    by_cases hi : 0 ≤ c i
    · simp [w, hi, abs_of_nonneg hi]
    · simp [w, hi, abs_of_neg (lt_of_not_ge hi)]
  simpa only [heq] using h

end
end Nonsmooth
