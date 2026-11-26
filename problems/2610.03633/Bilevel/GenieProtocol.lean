import Bilevel.ProjectionPosterior

/-! Finite adaptive projection protocols with genuine observation-dependent branches. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Bilevel.GenieProtocol
open EuclideanGaussian ProjectionPosterior

/-- A query observes every column's scalar projection; a revelation observes an
entire chosen column. Both continuations may depend arbitrarily on that observation.
The indices are remaining upper bounds, not a preselected nonadaptive schedule. -/
inductive Protocol (d T : ℕ) : ℕ → ℕ → Type
  | halt {m r : ℕ} : Protocol d T m r
  | query {m r : ℕ} (w : Space d) (next : (Fin T → ℝ) → Protocol d T m r) : Protocol d T (m+1) r
  | reveal {m r : ℕ} (i : Fin T) (next : Space d → Protocol d T m r) : Protocol d T m (r+1)

def bad {d T : ℕ} (b : ℝ) : {m r : ℕ} → Protocol d T m r → Frame d T → Prop
  | _, _, .halt, _ => False
  | _, _, .query w next, U => (∃ i : Fin T, b ≤ ⟪w,U i⟫ ^ 2) ∨
      bad b (next (queryObservation d T w U)) U
  | _, _, .reveal i next, U => bad b (next (U i)) U

/-- Borel execution, expressed on the joint next-observation/latent-frame space.
This is a measurability requirement only; it includes no probability estimate. -/
def Regular {d T : ℕ} (b : ℝ) : {m r : ℕ} → Protocol d T m r → Prop
  | _, _, .halt => True
  | _, _, .query _ next =>
      MeasurableSet {p : (Fin T → ℝ) × Frame d T | bad b (next p.1) p.2} ∧
      ∀ y, Regular b (next y)
  | _, _, .reveal _ next =>
      MeasurableSet {p : Space d × Frame d T | bad b (next p.1) p.2} ∧
      ∀ y, Regular b (next y)

/-- Normalized residual queries, including padded directions, add one dimension.
Full revelation branches enlarge the known space by the actual revealed vector. -/
def Valid {d T : ℕ} : {m r : ℕ} → Protocol d T m r → Submodule ℝ (Space d) → Prop
  | _, _, .halt, _ => True
  | _, _, .query w next, V => w ∈ Vᗮ ∧ ‖w‖ = 1 ∧
      ∀ y, Valid (next y) (V ⊔ Submodule.span ℝ {w})
  | _, _, .reveal _ next, V => ∀ y, Valid (next y) (V ⊔ Submodule.span ℝ {y})

theorem bad_measurable {d T m r : ℕ} (b : ℝ) (P : Protocol d T m r) (hP : Regular b P) :
    MeasurableSet {U : Frame d T | bad b P U} := by
  cases P with
  | halt => exact MeasurableSet.empty
  | query w next =>
    have hq : MeasurableSet {U : Frame d T | ∃ i : Fin T, b ≤ ⟪w,U i⟫ ^ 2} := by
      simp only [Set.setOf_exists]
      exact MeasurableSet.iUnion (fun i : Fin T => measurableSet_le measurable_const
        ((continuous_const.inner (continuous_apply i)).measurable.pow_const 2))
    exact hq.union ((query_measurable d T w).prodMk measurable_id hP.1)
  | reveal i next =>
    exact ((reveal_measurable d T i).prodMk measurable_id) hP.1

end Bilevel.GenieProtocol
