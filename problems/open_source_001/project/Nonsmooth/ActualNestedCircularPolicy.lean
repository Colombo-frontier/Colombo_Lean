import Nonsmooth.AdaptiveCyclicPolicy
import Nonsmooth.CircularGeometryState

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

structure CircularHistory where
  entries : List ℤ
  deriving Encodable

instance circularHistoryMeasurableSpace : MeasurableSpace CircularHistory := ⊤
instance circularHistoryDiscreteMeasurableSpace : DiscreteMeasurableSpace CircularHistory :=
  inferInstanceAs (@DiscreteMeasurableSpace CircularHistory ⊤)

def circularHistoryNext (c : CircularHistory) (j : ℤ) : CircularHistory := ⟨j :: c.entries⟩

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def nestedCircularQuery (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : CircularHistory) (j : ℤ) : Feasible E R :=
  ⟨circularGeometryQuery R ε N c.entries j, circularGeometryQuery_feasible hR hε hε1 N c.entries j⟩

def nestedCircularOutput (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : CircularHistory) : Feasible E R :=
  ⟨(circularGeometryState R ε N c.entries).1,
    (circularGeometryState_norm_le_half hR hε hε1 N c.entries).trans (by linarith)⟩

theorem nestedCircularQuery_periodic (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : CircularHistory) :
    Function.Periodic (nestedCircularQuery (E := E) R ε N hR hε hε1 c) (4 * 2 ^ N) := by
  intro j
  exact Subtype.ext (circularGeometryQuery_periodic R ε N c.entries j)

theorem nestedCircularQuery_anchor (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : CircularHistory) :
    nestedCircularQuery (E := E) R ε N hR hε hε1 c 0 = nestedCircularOutput R ε N hR hε hε1 c :=
  Subtype.ext (circularGeometryQuery_anchor R ε N c.entries)

theorem nestedCircularOutput_next (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : CircularHistory) (j : ℤ) :
    nestedCircularOutput (E := E) R ε N hR hε hε1 (circularHistoryNext c j) =
      nestedCircularQuery R ε N hR hε hε1 c j := rfl

def nestedCircularPolicy (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Policy Unit (CircularHistory × CyclicPeakState) (Feasible E R) :=
  adaptiveBlockPolicy (cyclicPeakPolicy N) (3 * N + 4) (nestedCircularQuery R ε N hR hε hε1)
    circularHistoryNext (nestedCircularOutput R ε N hR hε hε1) ⟨[]⟩

def nestedCircularController (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) : ℕ → CircularHistory :=
  adaptiveBlockController (cyclicPeakPolicy N) (3 * N + 4) (nestedCircularQuery R ε N hR hε hε1)
    circularHistoryNext (fun x => f x.val) ⟨[]⟩

theorem nestedCircularPolicy_measurable (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (nestedCircularPolicy (E := E) R ε N hR hε hε1).IsMeasurable :=
  adaptiveBlockPolicy_measurable _ (cyclicPeakPolicy_measurable N) _ _ _ _ _

theorem nestedCircularController_length (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) : (nestedCircularController R ε N hR hε hε1 f m).entries.length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (circularHistoryNext (nestedCircularController R ε N hR hε hε1 f m) _).entries.length = m + 1
    simpa only [circularHistoryNext, List.length_cons] using congrArg (fun k : ℕ => k + 1) ih

theorem nestedCircularPolicy_result_exact (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    (nestedCircularPolicy R ε N hR hε hε1).result (fun x => f x.val) () (m * (3 * N + 4)) =
      nestedCircularOutput R ε N hR hε hε1 (nestedCircularController R ε N hR hε hε1 f m) :=
  adaptiveBlockPolicy_result_exact _ (by omega) _ _ _ _ _ _

theorem nestedCircularPolicy_value_monotone (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) :
    Monotone (fun m => f ((nestedCircularPolicy R ε N hR hε hε1).result
      (fun x => f x.val) () (m * (3 * N + 4))).val) := by
  simp only [nestedCircularPolicy_result_exact]
  exact adaptive_cyclic_controller_value_monotone N _ circularHistoryNext _
    (nestedCircularQuery_periodic R ε N hR hε hε1) (nestedCircularQuery_anchor R ε N hR hε hε1)
    (nestedCircularOutput_next R ε N hR hε hε1) (fun x => f x.val) ⟨[]⟩

end
end Nonsmooth
