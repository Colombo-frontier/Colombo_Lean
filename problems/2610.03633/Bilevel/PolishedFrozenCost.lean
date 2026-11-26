import Bilevel.PolishedFrozenCostPrimitive

/-! Sharp all-history original-call cost of the literal frozen algorithm.
The proof uses actual procedure support, trace tracker, and call counters. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedFrozenProcedure
open Stateful PrimitiveGeometry CachedOuterProcedure CachedBudgetCalibration
variable {X Y : Type} {History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query:=X×Y) (History:=History) (X:=X) (Y:=Y) σf σg)

theorem run_anchor (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (hr : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (h : History) :
    ∀ᵐ z ∂(run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law ((),h),
      z.1.2.1=if n=0 then x₀ else
        (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ z.1.1 i).point) (n-1)).point := by
  have hp (m : ℕ) : MeasurableSet {z : Outcome (State X Y) History |
      z.1.2.1=if m=0 then x₀ else
        (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ z.1.1 i).point) (m-1)).point} := by
    apply measurableSet_eq_fun (by fun_prop)
    by_cases hm : m=0
    · simp only [hm,if_pos rfl]
      exact measurable_const
    · simp only [if_neg hm]
      exact (track_run_measurable Λ cap radius x₀ (m-1)).1.comp (by fun_prop)
  induction n with
  | zero =>
      rw [run,Procedure.pure_law]
      exact (ae_dirac_iff (hp 0)).mpr rfl
  | succ n ih =>
      rw [run]
      apply (Procedure.ae_bind_iff _ _ () h _ (hp (n+1))).mpr
      filter_upwards [ih] with z hz
      change ∀ᵐ w ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (z.1,z.2.1),_
      filter_upwards [iteration_support O μ Lg Cf t D r rA δ η Λ cap radius hr q x₀ yinit n z.1 hz z.2.1] with w hw
      simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
      have hprefix : ∀ i,i<n → w.1.1 i=z.1.1 i := by
        intro i hi
        calc
          _=put z.1.1 n (w.1.1 n) i := congrFun hw.1 i
          _=_ := if_neg (ne_of_lt hi)
      change w.1.2.1=(CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ w.1.1 i).point) n).point
      rw [track_run_prefix_congr Λ cap radius x₀ w.1.1 z.1.1 n hprefix,hw.2]
      exact nextAnchor_eq_track Λ cap radius x₀ n z.1 hz

theorem run_calls_actual_le (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (hr : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (h : History) :
    ∀ᵐ z ∂(run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law ((),h),
      z.2.2≤n*estimatorCalls μ Lg σg D r δ q+
        refreshCount Λ cap radius x₀ n z.1.1*anchorCalls μ Lg σf σg D rA η q := by
  have hp (m : ℕ) : MeasurableSet {z : Outcome (State X Y) History |
      z.2.2≤m*estimatorCalls μ Lg σg D r δ q+
        refreshCount Λ cap radius x₀ m z.1.1*anchorCalls μ Lg σf σg D rA η q} := by
    apply measurableSet_le (by fun_prop)
    exact (((refreshCount_measurable Λ cap radius x₀ m).comp
      (measurable_fst.comp measurable_fst)).mul_const _).const_add _
  induction n with
  | zero =>
      rw [run,Procedure.pure_law]
      apply (ae_dirac_iff (hp 0)).mpr
      simp [refreshCount]
  | succ n ih =>
      rw [run]
      apply (Procedure.ae_bind_iff _ _ () h _ (hp (n+1))).mpr
      filter_upwards [ih,run_anchor O μ Lg Cf t D r rA δ η Λ cap radius hr q x₀ yinit n h] with z hz hanc
      change ∀ᵐ w ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (z.1,z.2.1),
        z.2.2+w.2.2≤(n+1)*estimatorCalls μ Lg σg D r δ q+
          refreshCount Λ cap radius x₀ (n+1) w.1.1*anchorCalls μ Lg σf σg D rA η q
      filter_upwards [iteration_calls_le O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n z.1 z.2.1,
        iteration_support O μ Lg Cf t D r rA δ η Λ cap radius hr q x₀ yinit n z.1 hanc z.2.1] with w hw hs
      have hprefix : ∀ i,i<n → w.1.1 i=z.1.1 i := by
        intro i hi
        calc
          _=put z.1.1 n (w.1.1 n) i := congrFun hs.1 i
          _=_ := if_neg (ne_of_lt hi)
      rw [refreshCount_succ_congr Λ cap radius x₀ w.1.1 z.1.1 n hprefix,
        refreshCount_next Λ cap radius x₀ n z.1 hanc]
      convert add_le_add hz hw using 1;ring

theorem publicRun_calls_bound (μ Lg Cf t D r rA δ η Λ La Δ ε : ℝ) (q : ℕ) [NeZero q]
    (hΛ : 0<Λ) (hLa : 0≤La) (hLaΛ : La≤Λ) (hΔ : 0≤Δ) (hε : 0<ε)
    (x₀ : X) (yinit : Y) (h : History) :
    ∀ᵐ z ∂(run O μ Lg Cf t D r rA δ η Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
      q x₀ yinit (outerCount Λ Δ ε)).law ((),h),
      (z.2.2:ℝ)≤publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q := by
  have hN := outerCount_pos Λ Δ ε
  filter_upwards [run_calls_actual_le O μ Lg Cf t D r rA δ η Λ (energyCap Λ Δ ε)
    (refreshRadius Λ La Δ ε) (refreshRadius_pos hΛ hLa hΔ hε).le q x₀ yinit (outerCount Λ Δ ε) h] with z hz
  have hc := capped_anchor_budget hΛ hLa hLaΛ hΔ hε x₀ z.1.1 (outerCount Λ Δ ε-1) (Nat.sub_le _ _)
  have hr : (refreshCount Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
      x₀ (outerCount Λ Δ ε) z.1.1:ℝ)≤2560*(1+La*Δ/ε^2) := by
    simp only [refreshCount,if_neg (Nat.ne_of_gt hN),Nat.cast_add,Nat.cast_one]
    simpa only [add_comm] using hc
  have hb : ((outerCount Λ Δ ε*estimatorCalls μ Lg σg D r δ q+
      refreshCount Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε) x₀ (outerCount Λ Δ ε) z.1.1*
        anchorCalls μ Lg σf σg D rA η q:ℕ):ℝ)≤publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q := by
    push_cast
    exact add_le_add_left (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) _
  exact (Nat.cast_le.mpr hz).trans hb

theorem publicRun_costBound (μ Lg Cf t D r rA δ η Λ La Δ ε : ℝ) (q : ℕ) [NeZero q]
    (hΛ : 0<Λ) (hLa : 0≤La) (hLaΛ : La≤Λ) (hΔ : 0≤Δ) (hε : 0<ε)
    (x₀ : X) (yinit : Y) :
    (run O μ Lg Cf t D r rA δ η Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
      q x₀ yinit (outerCount Λ Δ ε)).CostBound
      (fun _ => publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q) := by
  intro p h
  cases p
  let B := publicCost μ Lg σf σg D r rA δ η Λ La Δ ε q
  have hb := publicRun_calls_bound O μ Lg Cf t D r rA δ η Λ La Δ ε q hΛ hLa hLaΛ hΔ hε x₀ yinit h
  have hi : Integrable (fun z : Outcome (State X Y) History => (z.2.2:ℝ))
      ((run O μ Lg Cf t D r rA δ η Λ (energyCap Λ Δ ε) (refreshRadius Λ La Δ ε)
        q x₀ yinit (outerCount Λ Δ ε)).law ((),h)) := by
    have hm : Measurable (fun z : Outcome (State X Y) History => (z.2.2:ℝ)) :=
      (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_snd.comp measurable_snd)
    apply (integrable_const B).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with z hz
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using hz
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi (integrable_const B) hb
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using hh

theorem algorithm_calls_bound (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (h : History) :
    ∀ᵐ z ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h),
      (z.2.2:ℝ)≤CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀ := by
  dsimp only [algorithm,CachedUpper.cost]
  exact publicRun_calls_bound O _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hΛ (CachedParameterChoice.anchorSmoothness_nonneg hLf) hLaΛ hΔ hε x₀ yinit h

theorem algorithm_costBound (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) :
    (algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).CostBound
      (fun _ => CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  dsimp only [algorithm,CachedUpper.cost]
  exact publicRun_costBound O _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hΛ (CachedParameterChoice.anchorSmoothness_nonneg hLf) hLaΛ hΔ hε x₀ yinit

theorem algorithm_cost_lintegral (μ Lf Lg Cf ρ Λ Δ ε R₀ : ℝ)
    (hLf : 0≤Lf) (hΛ : 0<Λ) (hLaΛ : CachedParameterChoice.anchorSmoothness Lf (Lg/μ)≤Λ)
    (hΔ : 0≤Δ) (hε : 0<ε) (x₀ : X) (yinit : Y) (h : History) :
    (∫⁻ z,(z.2.2:ℝ≥0∞) ∂(algorithm O μ Lf Lg Cf ρ Λ Δ ε R₀ x₀ yinit).law ((),h))≤
      ENNReal.ofReal (CachedUpper.cost μ Lf Lg Cf ρ σf σg Λ Δ ε R₀) := by
  have hb := algorithm_costBound O μ Lf Lg Cf ρ Λ Δ ε R₀ hLf hΛ hLaΛ hΔ hε x₀ yinit () h
  have he := ofReal_integral_eq_lintegral_ofReal hb.1
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
  simp only [ENNReal.ofReal_natCast] at he
  rw [←he]
  exact ENNReal.ofReal_le_ofReal hb.2

end Bilevel.PolishedFrozenProcedure
