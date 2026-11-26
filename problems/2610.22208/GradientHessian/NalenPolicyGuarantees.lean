import GradientHessian.NalenPolicyCounts
import GradientHessian.NalenPolicyOutput
import GradientHessian.NalenTuning

/-! Actual Algorithm.Guarantees from the literal policy execution and
the proved NALEN convergence theorem. No convergence or trajectory
correctness premise is supplied by the algorithm or its caller. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen MeasureTheory
open scoped ENNReal

variable {d m q K N : ℕ} {T : ℝ}

theorem machine_output_stationary (hm : 1≤m) (hq : 1≤q) (hK : 1≤K)
    (hmq : m≤q^3) (hKq : K*q≤N) (hTK : 256*T≤(K:ℝ))
    (f : Point d → ℝ) (hf : Admissible T f) (seed : PUnit) :
    ‖gradient f ((policy d (stepRadius_pos hq).le (stepSize m q) m q N).output
      ((policy d (stepRadius_pos hq).le (stepSize m q) m q N).run
        (ordinaryOracle f) (richOracle f) (1+4*N) seed))‖≤1 := by
  exact Nalen.output_stationary
    (actualIterates_valid (stepRadius_pos hq).le (stepSize m q) m q f N)
    hf.smooth hf.hessianLip hm hq hK hmq hKq
    (fun n _ x y => actualIterates_symmetric (stepRadius_pos hq).le (stepSize m q) m q f (by omega) hf.smooth n x y)
    (fun n _ => actualIterates_snapshot_error (stepRadius_pos hq).le (stepSize m q) m q f (by omega) n)
    _ (fun k hk => output_gradient_le_candidate (stepRadius_pos hq).le (stepSize m q) m q f
      (by omega) N k ((Nat.mul_le_mul_right q (Nat.succ_le_of_lt hk)).trans hKq) seed)
    hf.boundedBelow (by simpa only [actualIterates_initial] using hf.gap) hTK

theorem algorithm_guarantees (hm : 1≤m) (hq : 1≤q) (hK : 1≤K)
    (hmq : m≤q^3) (hKq : K*q≤N) (hTK : 256*T≤(K:ℝ)) :
    (algorithm d (stepRadius_pos hq).le (stepSize m q) m q N).Guarantees T (3*N+1) (N ⌈/⌉ m) := by
  intro f hf
  refine ⟨?_,?_,?_⟩
  · exact (policy d (stepRadius_pos hq).le (stepSize m q) m q N).terminatesAlmostSurely_of_terminates
      (ordinaryOracle f) (richOracle f) (Measure.dirac PUnit.unit)
      (policy_terminates d (stepRadius_pos hq).le (stepSize m q) m q N _ _)
  · exact policy_source_caps d (stepRadius_pos hq).le (stepSize m q) m q N (by omega) _ _
  · have hs : (policy d (stepRadius_pos hq).le (stepSize m q) m q N).success
        (ordinaryOracle f) (richOracle f) (stationary f)=Set.univ := by
      apply Set.eq_univ_of_forall
      intro seed
      refine ⟨1+4*N,?_,?_⟩
      · exact (program d (stepRadius_pos hq).le (stepSize m q) m q N).halt _ _ seed
      · exact (stationary_iff_gradient f _).2 (machine_output_stationary hm hq hK hmq hKq hTK f hf seed)
    change (2/3:ℝ≥0∞)≤(Measure.dirac PUnit.unit)
      ((policy d (stepRadius_pos hq).le (stepSize m q) m q N).success (ordinaryOracle f) (richOracle f) (stationary f))
    rw [hs]
    simp only [MeasureTheory.measure_univ]
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).2 (by norm_num)

end GradientHessian.NalenPolicy
