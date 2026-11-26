import SecondOrder.ComparisonSamplingLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- Include the output point in the progress test without drawing another
response. The output is the policy query at the final time. -/
def curvatureComparisonOutputProgress (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (N : ℕ) : ℕ :=
  max (curvatureComparisonRun P Θ A β z N).1 (curvatureComparisonIndex P Θ A β z N)

theorem curvatureComparisonOutputProgress_le (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (N : ℕ) :
    curvatureComparisonOutputProgress P Θ A β z N≤T+1 :=
  max_le (curvatureComparisonRun_progress_le P Θ A β z N) (curvatureLimitedProgress_le Θ β _ _).1

theorem curvatureComparisonOutputProgress_tape_congr (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → CurvatureCoefficients m T R) (N : ℕ) (hz : ∀ t, t<N → z t=z' t) :
    curvatureComparisonOutputProgress P Θ A β z N=curvatureComparisonOutputProgress P Θ A β z' N := by
  unfold curvatureComparisonOutputProgress
  rw [curvatureComparisonIndex_tape_congr P Θ A β z z' N hz,
    curvatureComparisonRun_tape_congr P Θ A β z z' N hz]

/-- If a successful output requires all gates to have opened, then successful
actual execution either makes a far jump or finishes the comparison chain. -/
theorem curvatureComparison_success_transfer (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (N : ℕ)
    (success : Point (CurvatureDimension m T) → Prop)
    (hcomplete : ∀ x, success x → curvatureProgress Θ (curvatureDilation m T β x)=T+1)
    (hs : success (P.query N (queryPolicyRun P (fun x a => richReply (scaledCurvatureSample Θ A β) a x) z N))) :
    ¬curvatureNoFarJump P Θ A β z (N+1) ∨ curvatureComparisonOutputProgress P Θ A β z N=T+1 := by
  by_cases hfar : curvatureNoFarJump P Θ A β z (N+1)
  · right
    have hc := curvatureComparisonRun_coupling P Θ A β z N (fun n hn => hfar n (by omega))
    rw [hc] at hs
    have hi : curvatureComparisonIndex P Θ A β z N=T+1 := by
      unfold curvatureComparisonIndex
      rw [curvatureLimitedProgress_no_far Θ β _ _ (hfar N (by omega))]
      exact hcomplete _ hs
    unfold curvatureComparisonOutputProgress
    rw [hi, max_eq_right (curvatureComparisonRun_progress_le P Θ A β z N)]
  · exact Or.inl hfar

theorem curvatureHardFamily_sosp_comparison (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (N : ℕ)
    (hs : IsSOSP (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
      (curvatureInputScale L γ)) ε γ
      (P.query N (queryPolicyRun P (fun x a => richReply
        (scaledCurvatureSample Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ)) a x) z N))) :
    ¬curvatureNoFarJump P Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ) (curvatureInputScale L γ) z (N+1) ∨
    curvatureComparisonOutputProgress P Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
      (curvatureInputScale L γ) z N=T+1 :=
  curvatureComparison_success_transfer P Θ _ _ z N _
    (fun _ hx => curvatureHardFamily_sosp_progress Θ hm hL hγ hx) hs

end
end SecondOrder
