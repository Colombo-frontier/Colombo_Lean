import SecondOrder.FiniteFirstExitTape

open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

def curvatureRestartTransition (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (start p : ℕ) (s₀ : S) (a₀ : CurvatureCoefficients m T R)
    (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n) :=
  curvaturePrefixCoefficientLaw Θ R hR
    (curvatureRestartIndex P Θ A β start p s₀ (finiteHistoryTape a₀ n h) n+1)

theorem curvatureRestartSamplingLaw_adaptive (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R) (start p : ℕ)
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (n : ℕ) :
    curvatureRestartSamplingLaw P Θ A β R hR start p s₀ n=
      finiteAdaptiveLaw (PMF.pure ()) (curvatureRestartTransition P Θ A β R hR start p s₀ a₀) n := by
  have hk : finiteStateTransition (p,s₀) (fun t => curvatureComparisonStep P Θ A β (start+t))
      (fun t s => curvaturePrefixCoefficientLaw Θ R hR
        (curvatureLimitedProgress Θ β (P.query (start+t) s.2) (s.1+1)+1))=
      curvatureRestartTransition P Θ A β R hR start p s₀ a₀ := by
    funext t h
    unfold finiteStateTransition curvatureRestartTransition curvatureRestartIndex curvatureRestartRun
    rw [finiteStateRun_eq_tape _ _ a₀ t h]
  exact congrArg (fun K => finiteAdaptiveLaw (PMF.pure ()) K n) hk

def curvatureContinuationKernel (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β R : ℝ) (hR : 2≤R) (start stage cap : ℕ)
    (dummy : RichReply (CurvatureDimension m T)) (s₀ : S) :=
  cappedTransition
    (curvatureStageSelected (curvatureContinuationIndex P Θ A β start stage cap dummy s₀) stage) cap
    (fun n h => curvaturePrefixCoefficientLaw Θ R hR
      (curvatureContinuationIndex P Θ A β start stage cap dummy s₀ n h+1))
    (fun _ _ => curvaturePrefixCoefficientLaw Θ R hR 0)

/-- The two actual sampling kernels agree until target activation or the
response cap. No agreement is required after either stopping condition. -/
theorem curvatureRestartTransition_before_exit (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (CurvatureDimension m T))
    (s₀ : S) (a₀ : CurvatureCoefficients m T R) (hp : p+1=i.val ∨ p=i.val)
    (n : ℕ) (h : FiniteHistory Unit (CurvatureCoefficients m T R) n)
    (hbefore : ¬finiteHistorySeen
      (fun t h => curvatureRestartExit P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ t h)) n h) :
    curvatureRestartTransition P Θ A β R hR start p s₀ a₀ n h=
      curvatureContinuationKernel P Θ A β R hR start i.val cap dummy s₀ n h := by
  have hn (t : ℕ) (ht : t≤n) :
      ¬curvatureRestartExit P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ n h) := by
    intro he
    exact hbefore ((finiteHistorySeen_tape_iff a₀ _
      (curvatureRestartExit_tape_congr P Θ A β start p i cap s₀) n h).mpr ⟨t,ht,he⟩)
  have hc : curvatureRestartCount P Θ A β start p i.val s₀ (finiteHistoryTape a₀ n h) n<cap :=
    lt_of_not_ge (fun hh => hn n le_rfl (Or.inr hh))
  obtain ⟨hp',hs,hcount⟩ := curvatureContinuation_coupling P Θ A β start p i cap dummy s₀
    (finiteHistoryTape a₀ n h) hp n (fun t ht hh => hn t (by omega) (Or.inl hh)) hc
  have hcapped : cappedHistoryCount
      (curvatureStageSelected (curvatureContinuationIndex P Θ A β start i.val cap dummy s₀) i.val) cap n h<cap := by
    rw [←curvatureContinuation_count, finiteStateRun_eq_tape _ _ a₀ n h, hcount]
    exact hc
  have hindex : curvatureRestartIndex P Θ A β start p s₀ (finiteHistoryTape a₀ n h) n=
      curvatureContinuationIndex P Θ A β start i.val cap dummy s₀ n h := by
    unfold curvatureRestartIndex curvatureContinuationIndex
    dsimp only
    rw [curvatureLimitedProgress_stage_agree Θ β _ i _ hp' (fun hh => hn n le_rfl (Or.inl hh)),
      hs, finiteStateRun_eq_tape _ _ a₀ n h]
  unfold curvatureRestartTransition curvatureContinuationKernel cappedTransition
  rw [if_pos hcapped, hindex]

end
end SecondOrder
