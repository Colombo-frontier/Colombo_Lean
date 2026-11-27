import Nonsmooth.NestedCircularNeighborGeometry

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def circularGeometryDirection (R ε : ℝ) (N : ℕ) : List ℤ → E
  | [] => 0
  | j :: h =>
    let K := (circularGeometryState (E := E) R ε N h).2
    circleArc (subspaceCircularFrame K).1 (subspaceCircularFrame K).2
      (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))

def nestedCircularDirection (R ε : ℝ) (N : ℕ) (st : CircularHistory × CyclicPeakState) : E :=
  circularGeometryDirection R ε N st.1.entries

omit [BorelSpace E] [Nontrivial E] in
theorem nestedCircularDirection_measurable (R ε : ℝ) (N : ℕ) :
    Measurable (nestedCircularDirection (E := E) R ε N) := by
  have hm : Measurable (fun c : CircularHistory => circularGeometryDirection (E := E) R ε N c.entries) :=
    measurable_of_countable _
  exact hm.comp measurable_fst

theorem nestedCircularDirection_run_succ (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    nestedCircularDirection R ε N ((nestedCircularPolicy R ε N hR hε hε1).run
      (fun z => f z.val) () ((m + 1) * (3 * N + 4))) = nestedCircularRadial R ε N hR hε hε1 f m := by
  unfold nestedCircularPolicy
  rw [adaptiveBlockPolicy_run_exact _ (by omega)]
  change circularGeometryDirection R ε N
    (nestedCircularController R ε N hR hε hε1 f (m + 1)).entries = _
  rw [nestedCircularController_succ]
  rfl

theorem nestedCircularDirection_run_exact (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (D : ℕ) (hD : 0 < D) :
    nestedCircularDirection R ε N ((nestedCircularPolicy R ε N hR hε hε1).run
      (fun z => f z.val) () (D * (3 * N + 4))) = nestedCircularRadial R ε N hR hε hε1 f (D - 1) := by
  have h := nestedCircularDirection_run_succ R ε N hR hε hε1 f (D - 1)
  simpa only [Nat.sub_add_cancel (show 1 ≤ D by omega)] using h

end
end Nonsmooth
