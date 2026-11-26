import SampleReuse.CurvatureNegative
import SecondOrder.ScalarJetEquality

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem curvatureGate_zeroJet {u : ℝ} (hu : |u| ≤ 1/2) :
    ScalarJetEq curvatureGate (fun _ => 0) u := by
  obtain ⟨hv, hg, hH⟩ := curvatureGate_flat hu
  apply scalarJetEq_zero_of_flat (curvatureGate_contDiff 2) u hv
  · simpa only [gradient_eq_deriv'] using hg
  · have he : gradient curvatureGate = deriv curvatureGate :=
      funext (fun x => gradient_eq_deriv' (g := curvatureGate) (u := x))
    apply ContinuousLinearMap.ext
    intro v
    rw [he, fderiv_eq_deriv_mul, hH]
    simp

/-- The prefix chain embedded in the original coordinate space; k is the
number of retained coordinates (k>=1 for the manuscript's q_k). -/
def truncatedCurvatureChain (T k : ℕ) (x : Point (T+1)) : ℝ :=
  curvatureGate 1*curvaturePotential (x 0) +
    ∑ i : Fin T, if i.val+1 < k then
      curvatureGate (x i.castSucc)*curvaturePotential (x i.succ) else 0

/-- Exact order-two jet truncation, including points on the flat boundary. -/
theorem deterministicCurvatureChain_truncate (T k : ℕ) (x : Point (T+1))
    (htail : ∀ i : Fin (T+1), k ≤ i.val+1 → |x i| ≤ 1/2) :
    ScalarJetEq (deterministicCurvatureChain T) (truncatedCurvatureChain T k) x := by
  apply ScalarJetEq.add
  · exact ScalarJetEq.refl (contDiff_const.mul ((curvaturePotential_contDiff 2).comp
      (blockProj (E := ℝ) (0 : Fin (T+1))).contDiff)) x
  · apply ScalarJetEq.sum
    intro i _
    by_cases hi : i.val+1 < k
    · simp only [if_pos hi]
      exact ScalarJetEq.refl
        (((curvatureGate_contDiff 2).comp (blockProj (E := ℝ) i.castSucc).contDiff).mul
          ((curvaturePotential_contDiff 2).comp (blockProj (E := ℝ) i.succ).contDiff)) x
    · have hflat := (curvatureGate_zeroJet (htail i.castSucc (by simpa using le_of_not_gt hi))).comp_linear
        (blockProj (E := ℝ) i.castSucc)
      have hp := ScalarJetEq.refl ((curvaturePotential_contDiff 2).comp
        (blockProj (E := ℝ) i.succ).contDiff) x
      simpa only [Function.comp_def, blockProj_apply, zero_mul, if_neg hi] using hflat.mul hp

theorem deterministicCurvatureChain_full_reply_truncate (T k : ℕ) (x : Point (T+1))
    (htail : ∀ i : Fin (T+1), k ≤ i.val+1 → |x i| ≤ 1/2) :
    (deterministicCurvatureChain T x, gradient (deterministicCurvatureChain T) x,
      hessian (deterministicCurvatureChain T) x) =
    (truncatedCurvatureChain T k x, gradient (truncatedCurvatureChain T k) x,
      hessian (truncatedCurvatureChain T k) x) := by
  have h := deterministicCurvatureChain_truncate T k x htail
  exact Prod.ext h.value (Prod.ext h.gradient_eq h.hessian_eq)

end
end SampleReuse
