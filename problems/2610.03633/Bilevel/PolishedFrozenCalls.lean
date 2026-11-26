import Bilevel.PolishedFrozenCallsPrimitive

/-! All-reply-stream control and sharp La-dependent call budgets for the
literal frozen-anchor code, including immediate normalization on abort. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedFrozenCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedOracleCode CachedBudgetCalibration

section Deterministic
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem stopped_point_previous (Λ cap : ℝ) (x₀ : X) (G : ℕ → X) (n : ℕ)
    (hs : (CappedExecution.run Λ cap x₀ G (n+1)).stopped=true) :
    (CappedExecution.run Λ cap x₀ G (n+1)).point=(CappedExecution.run Λ cap x₀ G n).point := by
  cases hh : (CappedExecution.run Λ cap x₀ G n).stopped with
  | true => simp [CappedExecution.run,CappedExecution.step,hh]
  | false =>
      by_cases he : (CappedExecution.run Λ cap x₀ G n).energy+‖G n‖^2≤cap
      · simp [CappedExecution.run,CappedExecution.step,hh,he] at hs
      · simp [CappedExecution.run,CappedExecution.step,hh,he]

theorem stopped_nextAnchor_eq (Λ cap radius : ℝ) (hr : 0≤radius) (x₀ : X)
    (n : ℕ) (s : State X Y)
    (hs : s.2.1=if n=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) (n-1)).point)
    (hstop : (CappedExecution.run Λ cap x₀ s.1 n).stopped=true) :
    nextAnchor Λ cap radius x₀ n s=s.2.1 := by
  cases n with
  | zero => cases hstop
  | succ n =>
      simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel] at hs
      have hp := stopped_point_previous Λ cap x₀ s.1 n hstop
      have hd : ‖current Λ cap x₀ (n+1) s-s.2.1‖≤radius := by
        rw [current,hp,hs]
        exact CachedAnchorCount.current_within_radius (E:=X) hr
          (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) n
      simp only [nextAnchor,Nat.add_eq_zero_iff,one_ne_zero,and_false,false_or,not_lt.mpr hd,if_false]

end Deterministic

variable {X Y Seed : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  (response : (X×Y) → Seed → FullResponse X Y)

theorem liveIteration_support (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (liveIteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (s,stream)
    w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  by_cases hc : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · simpa only [liveIteration,eval,refreshIndex,if_pos hc,one_ne_zero,if_false,nextAnchor] using
      refreshIteration_support response μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n s stream
  · have hh := estimateStep_support_pointwise response μ Lg Cf σg t D r δ Λ cap q x₀ yinit n s stream
    simp only [liveIteration,eval,refreshIndex,if_neg hc,if_pos rfl,nextAnchor]
    exact ⟨hh.1,congrArg Prod.fst hh.2⟩

theorem liveIteration_calls_le (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    (eval response (liveIteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (s,stream)).1.2.2≤
      estimatorCalls μ Lg σg D r δ q+refreshIndex Λ cap radius x₀ n s*anchorCalls μ Lg σf σg D rA η q := by
  by_cases hc : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · simp only [liveIteration,eval,refreshIndex,if_pos hc,one_ne_zero,if_false,one_mul]
    have hh := refreshIteration_exactCalls response μ Lg Cf σf σg t D r rA δ η Λ cap q x₀ yinit n (s,stream)
    rw [hh]
    have hb := reuseCalls_le_estimatorCalls μ Lg σg D r δ q
    omega
  · simp only [liveIteration,eval,refreshIndex,if_neg hc,if_pos rfl,zero_mul,add_zero]
    exact (estimateStep_exactCalls response μ Lg Cf σg t D r δ Λ cap q x₀ yinit n (s,stream)).le

theorem iteration_calls_le (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    (eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (s,stream)).1.2.2≤
      estimatorCalls μ Lg σg D r δ q+refreshIndex Λ cap radius x₀ n s*anchorCalls μ Lg σf σg D rA η q := by
  cases hh : (CappedExecution.run Λ cap x₀ s.1 n).stopped with
  | true => simp only [iteration,eval,liveIndex,hh,if_true,if_pos rfl];exact Nat.zero_le _
  | false => simpa only [iteration,eval,liveIndex,hh,Bool.false_eq_true,if_false,one_ne_zero] using
      liveIteration_calls_le response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n s stream

theorem iteration_support (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (hr : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (hs : s.2.1=if n=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) (n-1)).point)
    (stream : ℕ → Seed) :
    let w := eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (s,stream)
    w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  cases hh : (CappedExecution.run Λ cap x₀ s.1 n).stopped with
  | true =>
      simp only [iteration,eval,liveIndex,hh,if_true,if_pos rfl]
      constructor
      · funext i
        simp only [put]
        split_ifs with hi
        · exact congrArg s.1 hi
        · rfl
      · exact (stopped_nextAnchor_eq Λ cap radius hr x₀ n s hs hh).symm
  | false => simpa only [iteration,eval,liveIndex,hh,Bool.false_eq_true,if_false,one_ne_zero] using
      liveIteration_support response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n s stream

theorem run_anchor_pointwise (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (hr : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (stream : ℕ → Seed) :
    let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
    z.1.1.2.1=if n=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ z.1.1.1 i).point) (n-1)).point := by
  induction n generalizing stream with
  | zero => rfl
  | succ n ih =>
    let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
    let w := eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (z.1.1,z.2)
    have hz := ih stream
    have hw := iteration_support response μ Lg Cf σf σg t D r rA δ η Λ cap radius hr q x₀ yinit n z.1.1 hz z.2
    change w.1.1.2.1=if n+1=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ w.1.1.1 i).point) (n+1-1)).point
    simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
    have hprefix : ∀ i,i<n → w.1.1.1 i=z.1.1.1 i := by
      intro i hi
      calc
        _=put z.1.1.1 n (w.1.1.1 n) i := congrFun hw.1 i
        _=_ := if_neg (ne_of_lt hi)
    rw [track_run_prefix_congr Λ cap radius x₀ w.1.1.1 z.1.1.1 n hprefix,hw.2]
    exact nextAnchor_eq_track Λ cap radius x₀ n z.1.1 hz

theorem run_calls_pointwise_le (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ) (hr : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (stream : ℕ → Seed) :
    let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
    z.1.2.2≤n*estimatorCalls μ Lg σg D r δ q+
      refreshCount Λ cap radius x₀ n z.1.1.1*anchorCalls μ Lg σf σg D rA η q := by
  induction n generalizing stream with
  | zero => simp [run,eval,refreshCount]
  | succ n ih =>
    let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
    let w := eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (z.1.1,z.2)
    have hz := ih stream
    have hanc := run_anchor_pointwise response μ Lg Cf σf σg t D r rA δ η Λ cap radius hr q x₀ yinit n stream
    have hw := iteration_calls_le response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n z.1.1 z.2
    have hs := iteration_support response μ Lg Cf σf σg t D r rA δ η Λ cap radius hr q x₀ yinit n z.1.1 hanc z.2
    change z.1.2.2+w.1.2.2≤(n+1)*estimatorCalls μ Lg σg D r δ q+
      refreshCount Λ cap radius x₀ (n+1) w.1.1.1*anchorCalls μ Lg σf σg D rA η q
    have hprefix : ∀ i,i<n → w.1.1.1 i=z.1.1.1 i := by
      intro i hi
      calc
        _=put z.1.1.1 n (w.1.1.1 n) i := congrFun hs.1 i
        _=_ := if_neg (ne_of_lt hi)
    rw [refreshCount_succ_congr Λ cap radius x₀ w.1.1.1 z.1.1.1 n hprefix,
      refreshCount_next Λ cap radius x₀ n z.1.1 hanc]
    convert add_le_add hz hw using 1; ring

/-- Abort normalization consumes no response and leaves the trace, cache,
call count and unconsumed stream exactly unchanged. -/
theorem iteration_aborted (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed)
    (hstop : (CappedExecution.run Λ cap x₀ s.1 n).stopped=true) :
    eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (s,stream)=
      ((s,(),0),stream) := by
  simp only [iteration,eval,liveIndex,hstop,if_true,if_pos rfl]
  rfl

/-- The original La-sensitive deterministic budget holds on every reply
stream for the actual early-abort, reused-untilted algorithm. -/
theorem publicRun_calls_pointwise (μ Lg Cf σf σg t D r rA δ η Λ La Δ ε : ℝ)
    (q : ℕ) [NeZero q] (hΛ : 0<Λ) (hLa : 0≤La) (hLaΛ : La≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (stream : ℕ → Seed) :
    ((eval response (run μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
      (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε)) ((),stream)).1.2.2:ℝ)≤
      publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q := by
  let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε)) ((),stream)
  have hz := run_calls_pointwise_le response μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) (refreshRadius_pos hΛ hLa hΔ hε).le q x₀ yinit (outerCount Λ Δ ε) stream
  have hN := outerCount_pos Λ Δ ε
  have hc := capped_anchor_budget hΛ hLa hLaΛ hΔ hε x₀ z.1.1.1
    (outerCount Λ Δ ε-1) (Nat.sub_le _ _)
  have hr : (refreshCount Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
      x₀ (outerCount Λ Δ ε) z.1.1.1:ℝ)≤2560*(1+La*Δ/ε^2) := by
    simp only [refreshCount,if_neg (Nat.ne_of_gt hN),Nat.cast_add,Nat.cast_one]
    simpa only [add_comm] using hc
  change (z.1.2.2:ℝ)≤_
  have hb : ((outerCount Λ Δ ε*estimatorCalls μ Lg σg D r δ q+
      refreshCount Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε) x₀ (outerCount Λ Δ ε) z.1.1.1*
        anchorCalls μ Lg σf σg D rA η q:ℕ):ℝ)≤publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q := by
    push_cast
    exact add_le_add_left (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) _
  exact (Nat.cast_le.mpr hz).trans hb

theorem algorithm_calls_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (stream : ℕ → Seed) :
    ((eval response (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) ((),stream)).1.2.2:ℝ)≤
      CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  dsimp only [algorithm,CachedUpper.cost]
  exact publicRun_calls_pointwise response _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hΛ (CachedParameterChoice.anchorSmoothness_nonneg hLf) hLaΛ hΔ hε x₀ yinit stream

theorem selectedAlgorithm_calls_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y)
    (i : Fin (outerCount Λ Δ ε)) (stream : ℕ → Seed) :
    ((eval response (selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) (i,stream)).1.2.2:ℝ)≤
      CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  simpa only [selectedAlgorithm,OracleCode.map,eval,Procedure.combine,Nat.add_zero] using
    algorithm_calls_pointwise response μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ hLf hΛ hLaΛ hΔ hε x₀ yinit stream

theorem selectedAlgorithm_calls_rate_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hμ : 0<μ) (hμg : μ≤Lg) (hLf : 0≤Lf) (hρ : 0≤ρ)
    (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y)
    (i : Fin (outerCount Λ Δ ε)) (stream : ℕ → Seed) :
    ((eval response (selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) (i,stream)).1.2.2:ℝ)≤
      CachedUpper.rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ :=
  (selectedAlgorithm_calls_pointwise response μ Lf Lg Cf ρ σf σg Λ Δ ε R₀
    hLf hΛ hLaΛ hΔ hε x₀ yinit i stream).trans
      (CachedUpper.cost_le_rateBound hμ hμg hLf hρ hΛ hLaΛ hΔ hε)

theorem compiled_selectedAlgorithm_calls_rate_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hμ : 0<μ) (hμg : μ≤Lg) (hLf : 0≤Lf) (hρ : 0≤ρ)
    (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y)
    (q₀ : X×Y) (o₀ : FullResponse X Y) (i : Fin (outerCount Λ Δ ε)) (stream : ℕ → Seed) :
    let c := selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    BorelAdaptive.totalCalls m.program (fun _ : Unit => response) ((),m.start i,stream)≤
      ENNReal.ofReal (CachedUpper.rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  let c := selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
  let m := compile q₀ o₀ c
  change BorelAdaptive.totalCalls m.program (fun _ : Unit => response) ((),m.start i,stream)≤_
  rw [Machine.totalCalls_eq m c (compile_correct q₀ o₀ c) response i stream,←ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (selectedAlgorithm_calls_rate_pointwise response μ Lf Lg Cf ρ σf σg Λ Δ ε R₀
      hμ hμg hLf hρ hΛ hLaΛ hΔ hε x₀ yinit i stream)

end Bilevel.PolishedFrozenCode
