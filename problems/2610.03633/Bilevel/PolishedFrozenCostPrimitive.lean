import Bilevel.PolishedFrozenProcedure
import Bilevel.PolishedFrozenCalls

/-! Actual conditional-kernel call counters and support for the frozen
algorithm. These are structural procedure proofs, not a fresh-seed shortcut. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenProcedure
open Stateful PrimitiveGeometry CachedOuterProcedure
variable {X Y : Type} {History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query:=X×Y) (History:=History) (X:=X) (Y:=Y) σf σg)

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseEstimator_calls (μ Lg t D r δ : ℝ) (q : ℕ) [NeZero q] :
    (reuseEstimator O μ Lg t D r δ q).CallsEq (fun _ => PolishedFrozenCode.reuseCalls μ Lg σg D r δ q) := by
  have hpair := Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (CachedEstimatorProcedure.tilted_calls O μ Lg t D r q)
      Prod.fst measurable_fst)
    (fun z : (CachedEstimatorProcedure.Input X Y×Y)×Y => (z.1.2,z.2)) (by fun_prop)
  have hfirst := Procedure.CallsEq.reparam _ _ (CachedEstimatorProcedure.firstGradient_calls O δ q)
    (fun z : (CachedEstimatorProcedure.Input X Y×Y)×(Y×Y) => (z.1.1,z.2)) (by fun_prop)
  have hlast := Procedure.CallsEq.reparam _ _ (CachedEstimatorProcedure.lastGradient_calls O δ q)
    (fun z : (CachedEstimatorProcedure.Input X Y×Y)×((Y×Y)×X) => (z.1.1,z.2)) (by fun_prop)
  have h1 := Procedure.CallsEq.bind (reusePair O μ Lg t D r q) (reuseFirst O δ q)
    (fun _ => q*StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (r/12))
    (fun _ => q*FreshBatchKernel.count σg (δ/12)) hpair hfirst
  have h2 := Procedure.CallsEq.bind ((reusePair O μ Lg t D r q).bind (reuseFirst O δ q))
    (reuseLast O δ q) _ (fun _ => q*FreshBatchKernel.count σg (δ/12)) h1 hlast
  have h3 := Procedure.CallsEq.map _ _ h2
    (fun z : (CachedEstimatorProcedure.Input X Y×Y)×CachedEstimatorProcedure.Transcript X Y =>
      CachedEstimatorProcedure.estimate t z.1.1 z.2) (by unfold CachedEstimatorProcedure.estimate;fun_prop)
  simpa only [PolishedFrozenCode.reuseCalls,Nat.add_assoc] using h3

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseEstimateStep_calls (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    (reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).CallsEq
      (fun _ => PolishedFrozenCode.reuseCalls μ Lg σg D r δ q) := by
  unfold reuseEstimateStep
  exact Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ (reuseEstimator_calls O μ Lg t D r δ q) _ _) _ _

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem reuseEstimateStep_support (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (s,h),
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2=s.2 := by
  have hp : MeasurableSet {z : Outcome (State X Y) History | z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2=s.2} := by
    apply MeasurableSet.inter
    · apply measurableSet_eq_fun (by fun_prop)
      exact (put_measurable n).comp (measurable_const.prodMk (by fun_prop))
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
  rw [reuseEstimateStep,Procedure.map_law]
  have hm : Measurable (fun z : Outcome X History => ((put s.1 n z.1,s.2),z.2)) :=
    (((put_measurable n).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_const).prodMk measurable_snd
  apply (ae_map_iff hm.aemeasurable hp).mpr
  filter_upwards with z
  exact ⟨by simp only [put,ite_true],rfl⟩

theorem refreshIteration_calls (μ Lg Cf t D r rA δ η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    (refreshIteration O μ Lg Cf t D r rA δ η Λ cap q x₀ yinit n).CallsEq
      (fun _ => anchorCalls μ Lg σf σg D rA η q+PolishedFrozenCode.reuseCalls μ Lg σg D r δ q) := by
  unfold refreshIteration
  exact Procedure.CallsEq.bind _ _ _ _ (CachedOuterProcedure.refreshAt_calls O μ Lg Cf D rA η Λ cap q x₀ yinit n)
    (Procedure.CallsEq.reparam _ _ (reuseEstimateStep_calls O μ Lg Cf t D r δ Λ cap q x₀ yinit n) _ _)

theorem refreshIteration_support (μ Lg Cf t D r rA δ η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(refreshIteration O μ Lg Cf t D r rA δ η Λ cap q x₀ yinit n).law (s,h),
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=current Λ cap x₀ n s := by
  have hp : MeasurableSet {z : Outcome (State X Y) History |
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=current Λ cap x₀ n s} := by
    apply MeasurableSet.inter
    · apply measurableSet_eq_fun (by fun_prop)
      exact (put_measurable n).comp (measurable_const.prodMk (by fun_prop))
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
  unfold refreshIteration
  apply (Procedure.ae_bind_iff _ _ s h _ hp).mpr
  filter_upwards [CachedOuterProcedure.refreshAt_support O μ Lg Cf D rA η Λ cap q x₀ yinit n s h] with z hz
  change ∀ᵐ w ∂(reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (z.1,z.2.1),_
  filter_upwards [reuseEstimateStep_support O μ Lg Cf t D r δ Λ cap q x₀ yinit n z.1 z.2.1] with w hw
  exact ⟨by simpa only [hz.1] using hw.1,by
    change w.1.2.1=current Λ cap x₀ n s
    rw [hw.2]
    exact hz.2⟩

theorem liveIteration_calls_le (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(liveIteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h),
      z.2.2≤estimatorCalls μ Lg σg D r δ q+refreshIndex Λ cap radius x₀ n s*anchorCalls μ Lg σf σg D rA η q := by
  rw [liveIteration,Procedure.choose_law]
  rcases refreshIndex_cases Λ cap radius x₀ n s with hi|hi
  · simp only [hi,if_pos rfl,Nat.zero_mul,Nat.add_zero]
    exact (CachedOuterProcedure.estimateStep_calls O μ Lg Cf t D r δ Λ cap q x₀ yinit n s h).mono (fun _ hz => hz.le)
  · simp only [hi,Nat.one_ne_zero,if_false,Nat.one_mul]
    filter_upwards [refreshIteration_calls O μ Lg Cf t D r rA δ η Λ cap q x₀ yinit n s h] with z hz
    rw [hz]
    have hb := PolishedFrozenCode.reuseCalls_le_estimatorCalls μ Lg σg D r δ q
    omega

theorem liveIteration_support (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(liveIteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h),
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  rw [liveIteration,Procedure.choose_law]
  by_cases hc : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · simpa only [refreshIndex,if_pos hc,one_ne_zero,if_false,nextAnchor] using
      refreshIteration_support O μ Lg Cf t D r rA δ η Λ cap q x₀ yinit n s h
  · simp only [refreshIndex,if_neg hc,if_pos rfl,nextAnchor]
    exact (CachedOuterProcedure.estimateStep_support O μ Lg Cf t D r δ Λ cap q x₀ yinit n s h).mono
      (fun _ hz => ⟨hz.1,congrArg Prod.fst hz.2⟩)

theorem iteration_calls_le (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h),
      z.2.2≤estimatorCalls μ Lg σg D r δ q+refreshIndex Λ cap radius x₀ n s*anchorCalls μ Lg σf σg D rA η q := by
  rw [iteration,Procedure.choose_law]
  cases hh : (CappedExecution.run Λ cap x₀ s.1 n).stopped with
  | true =>
      simp only [PolishedFrozenCode.liveIndex,hh,if_true,if_pos rfl]
      exact (Procedure.calls_pure id measurable_id s h).mono (fun _ hz => hz ▸ Nat.zero_le _)
  | false => simpa only [PolishedFrozenCode.liveIndex,hh,Bool.false_eq_true,if_false,one_ne_zero] using
      liveIteration_calls_le O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n s h

theorem iteration_support (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (hr : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (hs : s.2.1=if n=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) (n-1)).point) (h : History) :
    ∀ᵐ z ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h),
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  rw [iteration,Procedure.choose_law]
  cases hh : (CappedExecution.run Λ cap x₀ s.1 n).stopped with
  | true =>
      simp only [PolishedFrozenCode.liveIndex,hh,if_true,if_pos rfl,Procedure.pure_law]
      have hp : MeasurableSet {z : Outcome (State X Y) History |
          z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s} := by
        apply MeasurableSet.inter
        · apply measurableSet_eq_fun (by fun_prop)
          exact (put_measurable n).comp (measurable_const.prodMk (by fun_prop))
        · exact measurableSet_eq_fun (by fun_prop) measurable_const
      apply (ae_dirac_iff hp).mpr
      constructor
      · funext i
        simp only [put]
        split_ifs with hi
        · exact congrArg s.1 hi
        · rfl
      · exact (PolishedFrozenCode.stopped_nextAnchor_eq Λ cap radius hr x₀ n s hs hh).symm
  | false => simpa only [PolishedFrozenCode.liveIndex,hh,Bool.false_eq_true,if_false,one_ne_zero] using
      liveIteration_support O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n s h

end Bilevel.PolishedFrozenProcedure
