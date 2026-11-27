import Nonsmooth.PeakValueMonotonicity
import Nonsmooth.CircularQueryGrid

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem cyclicPeakPolicy_on_periodic_points_value_ge {X : Type} [MeasurableSpace X]
    (N : ℕ) (q : ℤ → X) (hq : Function.Periodic q (4 * 2 ^ N)) :
    ((cyclicPeakPolicy N).simulate q (fun _ y => y)).IsMeasurable ∧
      ∀ f : X → ℝ, ∃ j : ℤ,
        ((cyclicPeakPolicy N).simulate q (fun _ y => y)).result f () (3 * N + 4) = q j ∧
        f (q 0) ≤ f (q j) ∧ f (q (j - 1)) ≤ f (q j) ∧ f (q (j + 1)) ≤ f (q j) := by
  refine ⟨(cyclicPeakPolicy_on_periodic_points N q hq).1, ?_⟩
  intro f
  let j := (cyclicPeakPolicy N).result (fun i => f (q i)) () (3 * N + 4)
  have hm := cyclicPeakPolicy_local_max N (fun i => f (q i)) (fun i => congrArg f (hq i))
  exact ⟨j, simulation_output_exact (cyclicPeakPolicy N) q (fun _ y => y) f
    (fun i => f (q i)) (fun _ => rfl) () (3 * N + 4),
    cyclicPeakPolicy_value_ge_zero (fun i => f (q i)) N, hm.1, hm.2⟩

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
theorem circularQueryPoint_anchor (y u v : E) (r : ℝ) (N : ℕ) :
    circularQueryPoint (y - r • u) u v r N 0 = y := by
  simp [circularQueryPoint, circleArc]

theorem circularQueryPoint_anchor_displacement {y u v : E} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 ≤ r) (N : ℕ) (j : ℤ) :
    ‖circularQueryPoint (y - r • u) u v r N j - y‖ ≤ 2 * r := by
  have he : circularQueryPoint (y - r • u) u v r N j - y =
      r • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) - r • u := by
    dsimp only [circularQueryPoint]
    module
  rw [he]
  calc
    _ ≤ ‖r • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))‖ + ‖r • u‖ := norm_sub_le _ _
    _ = 2 * r := by
      rw [norm_smul, norm_smul, circleArc_norm hu hv huv, hu, Real.norm_eq_abs, abs_of_nonneg hr]
      ring

/-- The preceding apex is a sampled grid vertex, and all movements are bounded by twice the radius. -/
theorem anchored_circular_peak_policy (y u v : E) (r R : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 ≤ r) (hR : ‖y - r • u‖ + r ≤ R) (N : ℕ) :
    ∃ p : Policy Unit CyclicPeakState (Feasible E R), p.IsMeasurable ∧
      ∀ f : E → ℝ, ∃ j : ℤ,
        (p.result (fun x => f x.val) () (3 * N + 4)).val =
          circularQueryPoint (y - r • u) u v r N j ∧
        f y ≤ f (circularQueryPoint (y - r • u) u v r N j) ∧
        f (circularQueryPoint (y - r • u) u v r N (j - 1)) ≤
          f (circularQueryPoint (y - r • u) u v r N j) ∧
        f (circularQueryPoint (y - r • u) u v r N (j + 1)) ≤
          f (circularQueryPoint (y - r • u) u v r N j) ∧
        ‖circularQueryPoint (y - r • u) u v r N j - y‖ ≤ 2 * r := by
  let q := feasibleCircularQuery (y - r • u) u v r R hu hv huv hr hR N
  obtain ⟨hpm, hres⟩ := cyclicPeakPolicy_on_periodic_points_value_ge N q
    (feasibleCircularQuery_periodic (y - r • u) u v r R hu hv huv hr hR N)
  refine ⟨(cyclicPeakPolicy N).simulate q (fun _ z => z), hpm, ?_⟩
  intro f
  obtain ⟨j, hout, hzero, hl, hright⟩ := hres (fun x => f x.val)
  have hstart : f y ≤ f (circularQueryPoint (y - r • u) u v r N j) := by
    simpa only [q, feasibleCircularQuery, circularQueryPoint_anchor] using hzero
  exact ⟨j, congrArg Subtype.val hout, hstart, hl, hright,
    circularQueryPoint_anchor_displacement hu hv huv hr N j⟩

end
end Nonsmooth
