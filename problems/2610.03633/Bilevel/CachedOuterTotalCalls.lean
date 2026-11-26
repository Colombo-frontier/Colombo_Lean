import Bilevel.CachedOuterCalls
import Bilevel.CachedOuterInvariant
import Bilevel.CachedRefreshBudget

/-! Exact total query count as a function of the actual returned trace.
The all-history refresh bound therefore bounds original calls, not a
surrogate invocation count or an expectation on a good event. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOuterProcedure
open Stateful

section Count
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def refreshCount (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) (G : ℕ → X) : ℕ :=
  if n=0 then 0 else 1+
    (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ G i).point) (n-1)).refreshes

theorem refreshCount_succ_congr (Λ cap radius : ℝ) (x₀ : X) (G H : ℕ → X) (n : ℕ)
    (hGH : ∀ i, i<n → G i=H i) :
    refreshCount Λ cap radius x₀ (n+1) G = refreshCount Λ cap radius x₀ (n+1) H := by
  simp only [refreshCount,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
  rw [track_run_prefix_congr Λ cap radius x₀ G H n hGH]

theorem refreshCount_next (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) (s : State X Y)
    (hs : s.2.1 = if n=0 then x₀ else
      (CachedAnchorCount.track radius (fun i => (CappedExecution.run Λ cap x₀ s.1 i).point) (n-1)).point) :
    refreshCount Λ cap radius x₀ (n+1) s.1 =
      refreshCount Λ cap radius x₀ n s.1 + refreshIndex Λ cap radius x₀ n s := by
  cases n with
  | zero => simp [refreshCount,refreshIndex,CachedAnchorCount.track]
  | succ n =>
    simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel] at hs
    simp only [refreshCount,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel,
      refreshIndex,Nat.succ_ne_zero,false_or,hs,CachedAnchorCount.track,current]
    split_ifs <;> rfl

theorem refreshCount_le (Λ cap radius : ℝ) (x₀ : X) (G : ℕ → X) (n : ℕ) :
    refreshCount Λ cap radius x₀ n G ≤ n := by
  cases n with
  | zero => simp [refreshCount]
  | succ n =>
    simp only [refreshCount,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,Nat.add_sub_cancel]
    have hh := CachedAnchorCount.refreshes_le_steps radius
      (fun i => (CappedExecution.run Λ cap x₀ G i).point) n
    omega

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

theorem refreshCount_measurable (Λ cap radius : ℝ) (x₀ : X) (n : ℕ) :
    Measurable (refreshCount Λ cap radius x₀ n) := by
  unfold refreshCount
  split_ifs
  · exact measurable_const
  · exact ((track_run_measurable Λ cap radius x₀ (n-1)).2).const_add 1

end Count

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)]
  [MeasurableSpace History] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

theorem run_calls_actual (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (h : History) :
    ∀ᵐ z ∂(run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law ((),h),
      z.2.2 = n*estimatorCalls μ Lg σg D r δ q +
        refreshCount Λ cap radius x₀ n z.1.1 * anchorCalls μ Lg σf σg D rA η q := by
  have hp (m : ℕ) : MeasurableSet {z : Outcome (State X Y) History |
      z.2.2 = m*estimatorCalls μ Lg σg D r δ q +
        refreshCount Λ cap radius x₀ m z.1.1 * anchorCalls μ Lg σf σg D rA η q} := by
    apply measurableSet_eq_fun_of_countable (by fun_prop)
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
    filter_upwards [ih,run_anchor O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n h] with z hz hanc
    change ∀ᵐ w ∂(iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (z.1,z.2.1),
      z.2.2+w.2.2 = (n+1)*estimatorCalls μ Lg σg D r δ q +
        refreshCount Λ cap radius x₀ (n+1) w.1.1 * anchorCalls μ Lg σf σg D rA η q
    filter_upwards [iteration_calls O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n z.1 z.2.1,
      iteration_support O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n z.1 z.2.1] with w hw hs
    have hprefix : ∀ i, i<n → w.1.1 i=z.1.1 i := by
      intro i hi
      calc
        _ = put z.1.1 n (w.1.1 n) i := congrFun hs.1 i
        _ = _ := if_neg (ne_of_lt hi)
    rw [hz,hw,refreshCount_succ_congr Λ cap radius x₀ w.1.1 z.1.1 n hprefix,
      refreshCount_next Λ cap radius x₀ n z.1 hanc]
    ring

end Bilevel.CachedOuterProcedure
