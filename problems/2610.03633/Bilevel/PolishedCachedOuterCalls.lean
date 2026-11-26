import Bilevel.PolishedCachedPrimitiveCalls
import Bilevel.CachedOuterCostBound
import Bilevel.OracleCompiler
import Bilevel.CachedUpperRateTheorem

/-! Pathwise exact counters and sharp budgets for the cached public code.
Every response function and every response stream is allowed. No oracle law,
probability-one event, error estimate or conditional moment assumption enters. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.CachedOracleCode
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure CachedBudgetCalibration
variable {X Y Seed : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  (response : (X × Y) → Seed → FullResponse X Y)

theorem refreshAt_exactCalls (μ Lg Cf σf σg D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    ExactCalls response (refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n)
      (anchorCalls μ Lg σf σg D rA η q) := by
  unfold refreshAt
  exact ((anchorRefresh_exactCalls response μ Lg Cf σf σg D rA η q).reparam _ _).map _ _

omit [MeasurableSpace (Joint X Y)]
  [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem estimateStep_exactCalls (μ Lg Cf σg t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    ExactCalls response (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n)
      (estimatorCalls μ Lg σg D r δ q) := by
  unfold estimateStep
  exact ((estimator_exactCalls response μ Lg σg t D r δ q).reparam _ _).map _ _

theorem refreshAt_support_pointwise (μ Lg Cf σf σg D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n) (s,stream)
    w.1.1.1=s.1 ∧ w.1.1.2.1=current Λ cap x₀ n s := ⟨rfl,rfl⟩

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
  [SecondCountableTopology (Joint X Y)] in
theorem estimateStep_support_pointwise (μ Lg Cf σg t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n) (s,stream)
    w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2=s.2 := by
  constructor
  · simp only [estimateStep,OracleCode.map,eval,Procedure.combine,put,ite_true]
  · rfl

 theorem maybeRefresh_support_pointwise (μ Lg Cf σf σg D rA η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n) (s,stream)
    w.1.1.1=s.1 ∧ w.1.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  by_cases hc : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · simpa only [maybeRefresh,eval,refreshIndex,if_pos hc,one_ne_zero,if_false,
      nextAnchor] using refreshAt_support_pointwise response μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n s stream
  · simp [maybeRefresh,eval,refreshIndex,hc,nextAnchor]

 theorem maybeRefresh_calls_pointwise (μ Lg Cf σf σg D rA η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    (eval response (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n)
      (s,stream)).1.2.2=refreshIndex Λ cap radius x₀ n s*anchorCalls μ Lg σf σg D rA η q := by
  by_cases hc : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · simpa only [maybeRefresh,eval,refreshIndex,if_pos hc,one_ne_zero,if_false,one_mul] using
      refreshAt_exactCalls response μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n (s,stream)
  · simp only [maybeRefresh,eval,refreshIndex,if_neg hc,ite_true,zero_mul]

 theorem iteration_support_pointwise (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    let w := eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (s,stream)
    w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  let z := eval response (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n) (s,stream)
  let w := eval response (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n) (z.1.1,z.2)
  have hz := maybeRefresh_support_pointwise response μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n s stream
  have hw := estimateStep_support_pointwise response μ Lg Cf σg t D r δ Λ cap q x₀ yinit n z.1.1 z.2
  change w.1.1.1=put s.1 n (w.1.1.1 n) ∧ w.1.1.2.1=nextAnchor Λ cap radius x₀ n s
  change z.1.1.1=s.1 ∧ z.1.1.2.1=nextAnchor Λ cap radius x₀ n s at hz
  change w.1.1.1=put z.1.1.1 n (w.1.1.1 n) ∧ w.1.1.2=z.1.1.2 at hw
  exact ⟨hw.1.trans (congrArg (fun G => put G n (w.1.1.1 n)) hz.1),by rw [hw.2];exact hz.2⟩

 theorem iteration_calls_pointwise (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (stream : ℕ → Seed) :
    (eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)
      (s,stream)).1.2.2=refreshIndex Λ cap radius x₀ n s*anchorCalls μ Lg σf σg D rA η q+
        estimatorCalls μ Lg σg D r δ q := by
  let z := eval response (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n) (s,stream)
  change z.1.2.2+(eval response (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n)
    (z.1.1,z.2)).1.2.2=_
  rw [estimateStep_exactCalls response μ Lg Cf σg t D r δ Λ cap q x₀ yinit n]
  exact congrArg (fun k => k+estimatorCalls μ Lg σg D r δ q)
    (maybeRefresh_calls_pointwise response μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n s stream)

/-- The actual pointwise returned anchor is the deterministic tracker of
its returned vector prefix, even for zero-probability response sequences. -/
theorem run_anchor_pointwise (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
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
    have hw := iteration_support_pointwise response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n z.1.1 z.2
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

/-- Exact original-call count for every response stream, expressed using
its actual returned trace. No moment or accuracy hypothesis is present. -/
theorem run_calls_pointwise (μ Lg Cf σf σg t D r rA δ η Λ cap radius : ℝ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (stream : ℕ → Seed) :
    let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
    z.1.2.2=n*estimatorCalls μ Lg σg D r δ q+
      refreshCount Λ cap radius x₀ n z.1.1.1*anchorCalls μ Lg σf σg D rA η q := by
  induction n generalizing stream with
  | zero => simp [run,eval,refreshCount]
  | succ n ih =>
    let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) ((),stream)
    let w := eval response (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n) (z.1.1,z.2)
    have hz := ih stream
    have hanc := run_anchor_pointwise response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n stream
    have hw := iteration_calls_pointwise response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n z.1.1 z.2
    have hs := iteration_support_pointwise response μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n z.1.1 z.2
    change z.1.2.2+w.1.2.2=(n+1)*estimatorCalls μ Lg σg D r δ q+
      refreshCount Λ cap radius x₀ (n+1) w.1.1.1*anchorCalls μ Lg σf σg D rA η q
    have hprefix : ∀ i,i<n → w.1.1.1 i=z.1.1.1 i := by
      intro i hi
      calc
        _=put z.1.1.1 n (w.1.1.1 n) i := congrFun hs.1 i
        _=_ := if_neg (ne_of_lt hi)
    rw [hz,hw,refreshCount_succ_congr Λ cap radius x₀ w.1.1.1 z.1.1.1 n hprefix,
      refreshCount_next Λ cap radius x₀ n z.1.1 hanc]
    ring

/-- Sharp deterministic budget for all actual syntactic executions. The
refresh term uses La, rather than paying an anchor on every outer step. -/
theorem publicRun_calls_pointwise (μ Lg Cf σf σg t D r rA δ η Λ La Δ ε : ℝ)
    (q : ℕ) [NeZero q] (hΛ : 0<Λ) (hLa : 0≤La) (hLaΛ : La≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (stream : ℕ → Seed) :
    ((eval response (run μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
      (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε)) ((),stream)).1.2.2:ℝ) ≤
      publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q := by
  let z := eval response (run μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε)) ((),stream)
  have hz := run_calls_pointwise response μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε) stream
  have hN := outerCount_pos Λ Δ ε
  have hc := capped_anchor_budget hΛ hLa hLaΛ hΔ hε x₀ z.1.1.1
    (outerCount Λ Δ ε-1) (Nat.sub_le _ _)
  have hr : (refreshCount Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
      x₀ (outerCount Λ Δ ε) z.1.1.1:ℝ) ≤ 2560*(1+La*Δ/ε^2) := by
    simp only [refreshCount,if_neg (Nat.ne_of_gt hN),Nat.cast_add,Nat.cast_one]
    simpa only [add_comm] using hc
  change (z.1.2.2:ℝ) ≤ _
  rw [hz]
  push_cast
  exact add_le_add_left (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) _

/-- The same all-reply-stream budget applies to the actual stopped program,
via the pathwise compiler certificate and its exact original-call counter. -/
theorem compiled_publicRun_calls_pointwise (μ Lg Cf σf σg t D r rA δ η Λ La Δ ε : ℝ)
    (q : ℕ) [NeZero q] (hΛ : 0<Λ) (hLa : 0≤La) (hLaΛ : La≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y)
    (q₀ : X × Y) (o₀ : FullResponse X Y) (stream : ℕ → Seed) :
    let c := run μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
      (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε)
    let m := compile q₀ o₀ c
    BorelAdaptive.totalCalls m.program (fun _ : Unit => response) ((),m.start (),stream) ≤
      ENNReal.ofReal (publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q) := by
  let c := run μ Lg Cf σf σg t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) q x₀ yinit (outerCount Λ Δ ε)
  let m := compile q₀ o₀ c
  change BorelAdaptive.totalCalls m.program (fun _ : Unit => response) ((),m.start (),stream)≤_
  rw [Machine.totalCalls_eq m c (compile_correct q₀ o₀ c) response () stream]
  rw [←ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (publicRun_calls_pointwise response μ Lg Cf σf σg t D r rA δ η Λ La Δ ε
      q hΛ hLa hLaΛ hΔ hε x₀ yinit stream)

/-- The actual calibrated cached code obeys its sharp public cost on every
stream; the bound uses only public numerical-budget conditions. -/
theorem algorithm_calls_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (stream : ℕ → Seed) :
    ((eval response (algorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) ((),stream)).1.2.2:ℝ)≤
      CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  dsimp only [algorithm,CachedUpper.cost]
  apply publicRun_calls_pointwise response
  · exact hΛ
  · exact CachedParameterChoice.anchorSmoothness_nonneg hLf
  · exact hLaΛ
  · exact hΔ
  · exact hε

/-- Choosing the output index and returning the selected point are pure
operations, so the same sharp budget holds for the exact public output code. -/
theorem selectedAlgorithm_calls_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y)
    (i : Fin (outerCount Λ Δ ε)) (stream : ℕ → Seed) :
    ((eval response (selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit) (i,stream)).1.2.2:ℝ)≤
      CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  simpa only [selectedAlgorithm,OracleCode.map,eval,Procedure.combine,Nat.add_zero] using
    algorithm_calls_pointwise response μ Lf Lg Cf ρ σf σg Λ Δ ε R₀
      hLf hΛ hLaΛ hΔ hε x₀ yinit stream

/-- The full explicit source rate, including the actual initialization and
confidence logarithms, holds pathwise for every possible reply stream. -/
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

/-- The compiled selected-output public program obeys the same sharp source
rate on every stream. The compiler preserves actual stopping and original
calls, not merely an output-law equivalence. -/
theorem compiled_selectedAlgorithm_calls_rate_pointwise (μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ : ℝ)
    (hμ : 0<μ) (hμg : μ≤Lg) (hLf : 0≤Lf) (hρ : 0≤ρ)
    (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y)
    (q₀ : X × Y) (o₀ : FullResponse X Y) (i : Fin (outerCount Λ Δ ε)) (stream : ℕ → Seed) :
    let c := selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
    let m := compile q₀ o₀ c
    BorelAdaptive.totalCalls m.program (fun _ : Unit => response) ((),m.start i,stream)≤
      ENNReal.ofReal (CachedUpper.rateBound μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  let c := selectedAlgorithm μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ x₀ yinit
  let m := compile q₀ o₀ c
  change BorelAdaptive.totalCalls m.program (fun _ : Unit => response) ((),m.start i,stream)≤_
  rw [Machine.totalCalls_eq m c (compile_correct q₀ o₀ c) response i stream]
  rw [←ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (selectedAlgorithm_calls_rate_pointwise response μ Lf Lg Cf ρ σf σg Λ Δ ε R₀
      hμ hμg hLf hρ hΛ hLaΛ hΔ hε x₀ yinit i stream)

end Bilevel.CachedOracleCode
