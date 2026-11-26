import SecondOrder.FirstOrderRestartLocality
import SecondOrder.FiniteFirstExitTape

open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

def firstOrderRestartTransition (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (start p : ℕ) (s₀ : S) (a₀ : FirstOrderCoefficients d T R)
    (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n) :=
  firstOrderPrefixCoefficientLaw Θ R hR
    (firstOrderRestartIndex P Θ A β start p s₀ (finiteHistoryTape a₀ n h) n+1)

theorem firstOrderRestartSamplingLaw_adaptive (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R) (start p : ℕ)
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (n : ℕ) :
    firstOrderRestartSamplingLaw P Θ A β R hR start p s₀ n=
      finiteAdaptiveLaw (PMF.pure ()) (firstOrderRestartTransition P Θ A β R hR start p s₀ a₀) n := by
  have hk : finiteStateTransition (p,s₀) (fun t => firstOrderComparisonStep P Θ A β (start+t))
      (fun t s => firstOrderPrefixCoefficientLaw Θ R hR
        (firstOrderLimitedProgress Θ β (P.query (start+t) s.2) (s.1+1)+1))=
      firstOrderRestartTransition P Θ A β R hR start p s₀ a₀ := by
    funext t h
    unfold finiteStateTransition firstOrderRestartTransition firstOrderRestartIndex firstOrderRestartRun
    rw [finiteStateRun_eq_tape _ _ a₀ t h]
  exact congrArg (fun K => finiteAdaptiveLaw (PMF.pure ()) K n) hk

def firstOrderContinuationKernel (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β R : ℝ) (hR : 2≤R) (start stage cap : ℕ)
    (dummy : RichReply (FirstOrderDimension d T)) (s₀ : S) :=
  cappedTransition
    (firstOrderStageSelected (firstOrderContinuationIndex P Θ A β start stage cap dummy s₀) stage) cap
    (fun n h => firstOrderPrefixCoefficientLaw Θ R hR
      (firstOrderContinuationIndex P Θ A β start stage cap dummy s₀ n h+1))
    (fun _ _ => firstOrderPrefixCoefficientLaw Θ R hR 0)

/-- The two actual sampling kernels agree until target activation or the
response cap. No agreement is required after either stopping condition. -/
theorem firstOrderRestartTransition_before_exit (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (start p : ℕ) (i : Fin (T+1)) (cap : ℕ) (dummy : RichReply (FirstOrderDimension d T))
    (s₀ : S) (a₀ : FirstOrderCoefficients d T R) (hp : p+1=i.val ∨ p=i.val)
    (n : ℕ) (h : FiniteHistory Unit (FirstOrderCoefficients d T R) n)
    (hbefore : ¬finiteHistorySeen
      (fun t h => firstOrderRestartExit P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ t h)) n h) :
    firstOrderRestartTransition P Θ A β R hR start p s₀ a₀ n h=
      firstOrderContinuationKernel P Θ A β R hR start i.val cap dummy s₀ n h := by
  have hn (t : ℕ) (ht : t≤n) :
      ¬firstOrderRestartExit P Θ A β start p i cap s₀ t (finiteHistoryTape a₀ n h) := by
    intro he
    exact hbefore ((finiteHistorySeen_tape_iff a₀ _
      (firstOrderRestartExit_tape_congr P Θ A β start p i cap s₀) n h).mpr ⟨t,ht,he⟩)
  have hc : firstOrderRestartCount P Θ A β start p i.val s₀ (finiteHistoryTape a₀ n h) n<cap :=
    lt_of_not_ge (fun hh => hn n le_rfl (Or.inr hh))
  obtain ⟨hp',hs,hcount⟩ := firstOrderContinuation_coupling P Θ A β start p i cap dummy s₀
    (finiteHistoryTape a₀ n h) hp n (fun t ht hh => hn t (by omega) (Or.inl hh)) hc
  have hcapped : cappedHistoryCount
      (firstOrderStageSelected (firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀) i.val) cap n h<cap := by
    rw [←firstOrderContinuation_count, finiteStateRun_eq_tape _ _ a₀ n h, hcount]
    exact hc
  have hindex : firstOrderRestartIndex P Θ A β start p s₀ (finiteHistoryTape a₀ n h) n=
      firstOrderContinuationIndex P Θ A β start i.val cap dummy s₀ n h := by
    unfold firstOrderRestartIndex firstOrderContinuationIndex
    dsimp only
    rw [firstOrderLimitedProgress_stage_agree Θ β _ i _ hp' (fun hh => hn n le_rfl (Or.inl hh)),
      hs, finiteStateRun_eq_tape _ _ a₀ n h]
  unfold firstOrderRestartTransition firstOrderContinuationKernel cappedTransition
  rw [if_pos hcapped, hindex]

end
end SecondOrder
