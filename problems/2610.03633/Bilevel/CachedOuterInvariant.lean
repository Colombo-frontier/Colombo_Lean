import Bilevel.CachedOuterProcedure

/-! Almost-sure trace and anchor invariants of the actual cached procedure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOuterProcedure
open Stateful

section Deterministic
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem run_prefix_congr (Λ cap : ℝ) (x₀ : X) (G H : ℕ → X) (n : ℕ)
    (hGH : ∀ i, i < n → G i = H i) :
    CappedExecution.run Λ cap x₀ G n = CappedExecution.run Λ cap x₀ H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CappedExecution.run,CappedExecution.run,ih (fun i hi => hGH i (by omega)),hGH n (by omega)]

omit [InnerProductSpace ℝ X] in
theorem track_prefix_congr (radius : ℝ) (x y : ℕ → X) (n : ℕ)
    (hxy : ∀ i, i ≤ n → x i = y i) :
    CachedAnchorCount.track radius x n = CachedAnchorCount.track radius y n := by
  induction n with
  | zero => simp only [CachedAnchorCount.track,hxy 0 le_rfl]
  | succ n ih =>
    simp only [CachedAnchorCount.track,ih (fun i hi => hxy i (by omega)),hxy (n+1) le_rfl]

theorem track_run_prefix_congr (Λ cap radius : ℝ) (x₀ : X) (G H : ℕ → X) (n : ℕ)
    (hGH : ∀ i, i < n → G i = H i) :
    CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ G i).point) n =
      CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ H i).point) n := by
  apply track_prefix_congr
  intro i hi
  rw [run_prefix_congr Λ cap x₀ G H i (fun j hj => hGH j (by omega))]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [InnerProductSpace ℝ X] in
theorem track_measurable {S : Type*} [MeasurableSpace S] (radius : ℝ)
    (x : ℕ → S → X) (hx : ∀ i, Measurable (x i)) (n : ℕ) :
    Measurable (fun s => (CachedAnchorCount.track radius (fun i => x i s) n).point) ∧
      Measurable (fun s => (CachedAnchorCount.track radius (fun i => x i s) n).refreshes) := by
  induction n with
  | zero => exact ⟨hx 0,measurable_const⟩
  | succ n ih =>
    have hs : MeasurableSet {s | radius < ‖x (n+1) s-(CachedAnchorCount.track radius (fun i => x i s) n).point‖} :=
      measurableSet_lt measurable_const ((hx (n+1)).sub ih.1).norm
    constructor
    · simpa only [CachedAnchorCount.track,apply_ite] using (hx (n+1)).ite hs ih.1
    · simpa only [CachedAnchorCount.track,apply_ite] using (ih.2.add_const 1).ite hs ih.2

theorem track_run_measurable (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) :
    Measurable (fun G : ℕ → X =>
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ G i).point) n).point) ∧
    Measurable (fun G : ℕ → X =>
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ G i).point) n).refreshes) :=
  track_measurable radius _
    (fun i => (CappedExecution.run_measurable Λ cap x₀ (fun j (G : ℕ → X) => G j)
      (fun j => measurable_pi_apply j) i).1) n

end Deterministic

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

def nextAnchor (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) (s : State X Y) : X :=
  if n = 0 ∨ radius < ‖current Λ cap x₀ n s-s.2.1‖ then current Λ cap x₀ n s else s.2.1

theorem refreshAt_support (μ Lg Cf D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n).law (s,h),
      z.1.1=s.1 ∧ z.1.2.1=current Λ cap x₀ n s := by
  have hp : MeasurableSet {z : Outcome (State X Y) History |
      z.1.1=s.1 ∧ z.1.2.1=current Λ cap x₀ n s} := by
    apply MeasurableSet.inter <;> exact measurableSet_eq_fun (by fun_prop) measurable_const
  rw [refreshAt,Procedure.map_law]
  have hm : Measurable (fun z : Outcome (CachedAnchorProcedure.Stored X Y) History =>
      ((s.1,current Λ cap x₀ n s,z.1),z.2)) :=
    (measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
  apply (ae_map_iff hm.aemeasurable hp).mpr
  filter_upwards with z
  exact ⟨rfl,rfl⟩

theorem maybeRefresh_support (μ Lg Cf D rA η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n).law (s,h),
      z.1.1=s.1 ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  rw [maybeRefresh,Procedure.choose_law]
  by_cases hc : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · simpa only [refreshIndex,if_pos hc,one_ne_zero,if_false,nextAnchor] using
      refreshAt_support O μ Lg Cf D rA η Λ cap q x₀ yinit n s h
  · simp only [refreshIndex,if_neg hc,if_pos rfl,Procedure.pure_law]
    have hp : MeasurableSet {z : Outcome (State X Y) History |
        z.1.1=s.1 ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s} := by
      apply MeasurableSet.inter <;> exact measurableSet_eq_fun (by fun_prop) measurable_const
    apply (ae_dirac_iff hp).mpr
    exact ⟨rfl,by simp only [nextAnchor,if_neg hc,id_eq]⟩

omit [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem estimateStep_support (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (s,h),
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2=s.2 := by
  have hp : MeasurableSet {z : Outcome (State X Y) History |
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2=s.2} := by
    apply MeasurableSet.inter
    · apply measurableSet_eq_fun (by fun_prop)
      exact (put_measurable n).comp (measurable_const.prodMk (by fun_prop))
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
  rw [estimateStep,Procedure.map_law]
  have hm : Measurable (fun z : Outcome X History => ((put s.1 n z.1,s.2),z.2)) :=
    (((put_measurable n).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_const).prodMk measurable_snd
  apply (ae_map_iff hm.aemeasurable hp).mpr
  filter_upwards with z
  exact ⟨by simp only [put,ite_true],rfl⟩

theorem iteration_support (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y) (h : History) :
    ∀ᵐ z ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h),
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s := by
  have hp : MeasurableSet {z : Outcome (State X Y) History |
      z.1.1=put s.1 n (z.1.1 n) ∧ z.1.2.1=nextAnchor Λ cap radius x₀ n s} := by
    apply MeasurableSet.inter
    · apply measurableSet_eq_fun (by fun_prop)
      exact (put_measurable n).comp (measurable_const.prodMk (by fun_prop))
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
  unfold iteration
  apply (Procedure.ae_bind_iff _ _ s h _ hp).mpr
  filter_upwards [maybeRefresh_support O μ Lg Cf D rA η Λ cap radius q x₀ yinit n s h] with z hz
  change ∀ᵐ w ∂(estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (z.1,z.2.1),
    w.1.1=put s.1 n (w.1.1 n) ∧ w.1.2.1=nextAnchor Λ cap radius x₀ n s
  filter_upwards [estimateStep_support O μ Lg Cf t D r δ Λ cap q x₀ yinit n z.1 z.2.1] with w hw
  exact ⟨by simpa only [hz.1] using hw.1,by rw [hw.2]; exact hz.2⟩

omit [CompleteSpace X] [CompleteSpace Y] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem nextAnchor_eq_track (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) (s : State X Y)
    (hs : s.2.1 = if n=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) (n-1)).point) :
    nextAnchor Λ cap radius x₀ n s =
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) n).point := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel] at hs
    simp only [nextAnchor,Nat.succ_ne_zero,false_or,hs,CachedAnchorCount.track,current]
    split <;> rfl

theorem run_anchor (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (h : History) :
    ∀ᵐ z ∂(run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law ((),h),
      z.1.2.1 = if n=0 then x₀ else
        (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ z.1.1 i).point) (n-1)).point := by
  have hp (m : ℕ) : MeasurableSet {z : Outcome (State X Y) History |
      z.1.2.1 = if m=0 then x₀ else
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
    change ∀ᵐ w ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (z.1,z.2.1),
      w.1.2.1 = if n+1=0 then x₀ else
        (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ w.1.1 i).point) (n+1-1)).point
    filter_upwards [iteration_support O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n z.1 z.2.1] with w hw
    simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
    have hprefix : ∀ i, i<n → w.1.1 i=z.1.1 i := by
      intro i hi
      calc
        _ = put z.1.1 n (w.1.1 n) i := congrFun hw.1 i
        _ = _ := if_neg (ne_of_lt hi)
    rw [track_run_prefix_congr Λ cap radius x₀ w.1.1 z.1.1 n hprefix,hw.2]
    exact nextAnchor_eq_track Λ cap radius x₀ n z.1 hz

theorem run_anchor_of_pos (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (hn : 0<n) (h : History) :
    ∀ᵐ z ∂(run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law ((),h),
      z.1.2.1 =
        (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ z.1.1 i).point) (n-1)).point := by
  simpa only [if_neg (Nat.ne_of_gt hn)] using
    run_anchor O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n h

end Bilevel.CachedOuterProcedure
