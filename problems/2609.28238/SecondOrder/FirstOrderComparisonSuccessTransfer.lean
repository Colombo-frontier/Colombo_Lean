import SecondOrder.FirstOrderComparisonSamplingLaw

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Include the output point in the progress test without drawing another
response. The output is the policy query at the final time. -/
def firstOrderComparisonOutputProgress (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (N : ℕ) : ℕ :=
  max (firstOrderComparisonRun P Θ A β z N).1 (firstOrderComparisonIndex P Θ A β z N)

theorem firstOrderComparisonOutputProgress_le (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (N : ℕ) :
    firstOrderComparisonOutputProgress P Θ A β z N≤T+1 :=
  max_le (firstOrderComparisonRun_progress_le P Θ A β z N) (firstOrderLimitedProgress_le Θ β _ _).1

theorem firstOrderComparisonOutputProgress_tape_congr (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z z' : ℕ → FirstOrderCoefficients d T R) (N : ℕ) (hz : ∀ t, t<N → z t=z' t) :
    firstOrderComparisonOutputProgress P Θ A β z N=firstOrderComparisonOutputProgress P Θ A β z' N := by
  unfold firstOrderComparisonOutputProgress
  rw [firstOrderComparisonIndex_tape_congr P Θ A β z z' N hz,
    firstOrderComparisonRun_tape_congr P Θ A β z z' N hz]

/-- If a successful output requires all gates to have opened, then successful
actual execution either makes a far jump or finishes the comparison chain. -/
theorem firstOrderComparison_success_transfer (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (N : ℕ)
    (success : Point (FirstOrderDimension d T) → Prop)
    (hcomplete : ∀ x, success x → firstOrderProgress Θ (firstOrderDilation d T β x)=T+1)
    (hs : success (P.query N (queryPolicyRun P (fun x a => richReply (scaledFirstOrderSample Θ A β) a x) z N))) :
    ¬firstOrderNoFarJump P Θ A β z (N+1) ∨ firstOrderComparisonOutputProgress P Θ A β z N=T+1 := by
  by_cases hfar : firstOrderNoFarJump P Θ A β z (N+1)
  · right
    have hc := firstOrderComparisonRun_coupling P Θ A β z N (fun n hn => hfar n (by omega))
    rw [hc] at hs
    have hi : firstOrderComparisonIndex P Θ A β z N=T+1 := by
      unfold firstOrderComparisonIndex
      rw [firstOrderLimitedProgress_no_far Θ β _ _ (hfar N (by omega))]
      exact hcomplete _ hs
    unfold firstOrderComparisonOutputProgress
    rw [hi, max_eq_right (firstOrderComparisonRun_progress_le P Θ A β z N)]
  · exact Or.inl hfar

end
end SecondOrder

