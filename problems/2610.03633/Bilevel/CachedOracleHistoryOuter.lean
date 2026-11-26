import Bilevel.CachedOracleCodeOuter
import Bilevel.CachedOracleHistoryEstimator
import Bilevel.CachedOracleHistoryAnchor
import Bilevel.CachedUpperAccuracy

/-! Public causal code for the actual capped cached outer loop. The refresh
test dispatches before reading a new oracle reply and all actual calls are
those already counted by CachedOuterProcedure. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOracleCode.History
open Stateful PrimitiveGeometry OracleCode CachedOuterProcedure
variable {X Y : Type} {H : OracleCode.Space}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

variable {σf σg : ℝ}
  (O : HistorySFO (Query:=X × Y) (History:=H) (X:=X) (Y:=Y) σf σg)

theorem denote_refreshAt (μ Lg Cf D rA η Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (refreshAt μ Lg Cf σf σg D rA η Λ cap q x₀ yinit n)=
      CachedOuterProcedure.refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n := by
  simp only [refreshAt,OracleCode.History.denote_map,OracleCode.History.denote,denote_anchorRefresh O,CachedOuterProcedure.refreshAt]

theorem denote_maybeRefresh (μ Lg Cf D rA η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (maybeRefresh μ Lg Cf σf σg D rA η Λ cap radius q x₀ yinit n)=
      CachedOuterProcedure.maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n := by
  simp only [maybeRefresh,OracleCode.History.denote,apply_ite,denote_refreshAt O,CachedOuterProcedure.maybeRefresh]

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] in
theorem denote_estimateStep (μ Lg Cf t D r δ Λ cap : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (estimateStep μ Lg Cf σg t D r δ Λ cap q x₀ yinit n)=
      CachedOuterProcedure.estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n := by
  simp only [estimateStep,OracleCode.History.denote_map,OracleCode.History.denote,denote_estimator O,CachedOuterProcedure.estimateStep]

theorem denote_iteration (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (iteration μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)=
      CachedOuterProcedure.iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n := by
  simp only [iteration,OracleCode.History.denote,denote_maybeRefresh O,denote_estimateStep O,CachedOuterProcedure.iteration]

theorem denote_run (μ Lg Cf t D r rA δ η Λ cap radius : ℝ) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) :
    OracleCode.History.denote (H:=H) O.law O.update O.update_measurable (run μ Lg Cf σf σg t D r rA δ η Λ cap radius q x₀ yinit n)=
      CachedOuterProcedure.run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,OracleCode.History.denote,ih,denote_iteration O,CachedOuterProcedure.run]

end Bilevel.CachedOracleCode.History
