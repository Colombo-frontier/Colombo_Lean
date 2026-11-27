import Mathlib

namespace Task003Integration
open Set

/-- Change coordinates between the Euclidean ambient space used by the
known-body algorithm and the exact l1 point space of the manuscript. -/
noncomputable def protasovCoordinates (d : ℕ) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] PiLp 1 (fun _ : Fin d => ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).trans
    (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin d => ℝ)).symm

/-- The l1 unit ball, viewed as a known convex body in Euclidean coordinates. -/
def protasovBody (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  protasovCoordinates d ⁻¹' Metric.closedBall 0 1

theorem mem_protasovBody {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ protasovBody d ↔ ‖protasovCoordinates d x‖ ≤ 1 := by
  simp [protasovBody, Metric.mem_closedBall, dist_zero_right]

theorem protasovBody_convex (d : ℕ) : Convex ℝ (protasovBody d) :=
  (convex_closedBall (0 : PiLp 1 (fun _ : Fin d => ℝ)) 1).linear_preimage
    (protasovCoordinates d).toLinearMap

theorem protasovBody_compact (d : ℕ) : IsCompact (protasovBody d) :=
  (protasovCoordinates d).toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 1)

theorem protasovBody_interior_nonempty (d : ℕ) : (interior (protasovBody d)).Nonempty := by
  refine ⟨0, ?_⟩
  change 0 ∈ interior ((protasovCoordinates d).toHomeomorph ⁻¹' Metric.closedBall 0 1)
  rw [← (protasovCoordinates d).toHomeomorph.preimage_interior]
  change protasovCoordinates d 0 ∈ interior (Metric.closedBall 0 1)
  rw [map_zero]
  exact mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds 0 (by norm_num))

theorem protasovBody_image (d : ℕ) :
    protasovCoordinates d '' protasovBody d = Metric.closedBall 0 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨(protasovCoordinates d).symm x, ?_, by simp⟩
    change protasovCoordinates d ((protasovCoordinates d).symm x) ∈ Metric.closedBall 0 1
    simpa using hx

theorem protasovBody_value_image (d : ℕ) (f : PiLp 1 (fun _ : Fin d => ℝ) → ℝ) :
    (fun x => f (protasovCoordinates d x)) '' protasovBody d =
      f '' Metric.closedBall 0 1 := by
  rw [← Set.image_image, protasovBody_image]

theorem protasovBody_objective_convex (d : ℕ)
    (f : PiLp 1 (fun _ : Fin d => ℝ) → ℝ) (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ (protasovBody d) (fun x => f (protasovCoordinates d x)) := by
  exact (hf.comp_linearMap (protasovCoordinates d).toLinearMap).subset
    (by intro x hx; trivial) (protasovBody_convex d)

end Task003Integration
