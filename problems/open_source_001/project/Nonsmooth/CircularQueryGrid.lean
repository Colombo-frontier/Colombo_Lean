import Nonsmooth.CyclicPeakLegality
import Nonsmooth.PlaneRotation
import Nonsmooth.Minimax

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def circularQueryPoint (o u v : E) (r : ℝ) (N : ℕ) (j : ℤ) : E :=
  o + r • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))

theorem circularQueryPoint_periodic (o u v : E) (r : ℝ) (N : ℕ) :
    Function.Periodic (circularQueryPoint o u v r N) (4 * 2 ^ N) := by
  intro j
  have he : 2 * Real.pi * ((j + 4 * 2 ^ N : ℤ) : ℝ) / (4 * 2 ^ N) =
      2 * Real.pi * (j : ℝ) / (4 * 2 ^ N) + 2 * Real.pi := by
    push_cast
    field_simp
  simp only [circularQueryPoint, he, circleArc, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem circularQueryPoint_feasible {o u v : E} {r R : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 ≤ r) (hR : ‖o‖ + r ≤ R) (N : ℕ) (j : ℤ) :
    ‖circularQueryPoint o u v r N j‖ ≤ R := by
  calc
    ‖circularQueryPoint o u v r N j‖ ≤ ‖o‖ +
        ‖r • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))‖ := norm_add_le _ _
    _ = ‖o‖ + r := by
      rw [norm_smul, circleArc_norm hu hv huv, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
    _ ≤ R := hR

def feasibleCircularQuery (o u v : E) (r R : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 ≤ r) (hR : ‖o‖ + r ≤ R) (N : ℕ) (j : ℤ) : Feasible E R :=
  ⟨circularQueryPoint o u v r N j, circularQueryPoint_feasible hu hv huv hr hR N j⟩

theorem feasibleCircularQuery_periodic (o u v : E) (r R : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 ≤ r) (hR : ‖o‖ + r ≤ R) (N : ℕ) :
    Function.Periodic (feasibleCircularQuery o u v r R hu hv huv hr hR N) (4 * 2 ^ N) := by
  intro j
  exact Subtype.ext (circularQueryPoint_periodic o u v r N j)

/-- The actual circular grid policy uses 3N+4 scalar responses, uniformly over f. -/
theorem circular_grid_local_max_policy (o u v : E) (r R : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 ≤ r) (hR : ‖o‖ + r ≤ R) (N : ℕ) :
    ∃ p : Policy Unit CyclicPeakState (Feasible E R), p.IsMeasurable ∧
      ∀ f : E → ℝ, ∃ j : ℤ,
        (p.result (fun x => f x.val) () (3 * N + 4)).val = circularQueryPoint o u v r N j ∧
        f (circularQueryPoint o u v r N (j - 1)) ≤ f (circularQueryPoint o u v r N j) ∧
        f (circularQueryPoint o u v r N (j + 1)) ≤ f (circularQueryPoint o u v r N j) := by
  let q := feasibleCircularQuery o u v r R hu hv huv hr hR N
  obtain ⟨hpm, hresult⟩ := cyclicPeakPolicy_on_periodic_points N q
    (feasibleCircularQuery_periodic o u v r R hu hv huv hr hR N)
  refine ⟨(cyclicPeakPolicy N).simulate q (fun _ y => y), hpm, ?_⟩
  intro f
  obtain ⟨j, hj, hl, hr'⟩ := hresult (fun x => f x.val)
  exact ⟨j, congrArg Subtype.val hj, hl, hr'⟩

end
end Nonsmooth
