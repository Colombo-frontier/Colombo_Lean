import Nonsmooth.NestedCircularDimension

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def nestedCircularApex (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) : E :=
  (circularGeometryState R ε N (nestedCircularController R ε N hR hε hε1 f m).entries).1

def nestedCircularSpace (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) : Submodule ℝ E :=
  (circularGeometryState R ε N (nestedCircularController R ε N hR hε hε1 f m).entries).2

def nestedCircularIndex (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) : ℤ :=
  (cyclicPeakPolicy N).result
    (fun j => f (circularGeometryQuery R ε N (nestedCircularController R ε N hR hε hε1 f m).entries j))
    () (3 * N + 4)

theorem nestedCircularController_succ (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    nestedCircularController R ε N hR hε hε1 f (m + 1) =
      circularHistoryNext (nestedCircularController R ε N hR hε hε1 f m)
        (nestedCircularIndex R ε N hR hε hε1 f m) := rfl

theorem nestedCircularQuery_at_stage (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) (j : ℤ) :
    circularGeometryQuery R ε N (nestedCircularController R ε N hR hε hε1 f m).entries j =
      subspaceCircularPoint (nestedCircularSpace R ε N hR hε hε1 f m)
        (nestedCircularApex R ε N hR hε hε1 f m) (shrinkingCircularRadius R ε N m) N j := by
  dsimp only [circularGeometryQuery, nestedCircularSpace, nestedCircularApex]
  rw [nestedCircularController_length]

theorem nestedCircularApex_succ (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    nestedCircularApex R ε N hR hε hε1 f (m + 1) =
      subspaceCircularPoint (nestedCircularSpace R ε N hR hε hε1 f m)
        (nestedCircularApex R ε N hR hε hε1 f m) (shrinkingCircularRadius R ε N m) N
          (nestedCircularIndex R ε N hR hε hε1 f m) := by
  unfold nestedCircularApex
  rw [nestedCircularController_succ]
  change circularGeometryQuery R ε N (nestedCircularController R ε N hR hε hε1 f m).entries _ = _
  exact nestedCircularQuery_at_stage R ε N hR hε hε1 f m _

theorem nestedCircularSpace_succ (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    nestedCircularSpace R ε N hR hε hε1 f (m + 1) =
      subspaceCircularSection (nestedCircularSpace R ε N hR hε hε1 f m) N
        (nestedCircularIndex R ε N hR hε hε1 f m) := rfl

theorem nestedCircularApex_step_mem (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    nestedCircularApex R ε N hR hε hε1 f (m + 1) - nestedCircularApex R ε N hR hε hε1 f m ∈
      nestedCircularSpace R ε N hR hε hε1 f m := by
  rw [nestedCircularApex_succ]
  exact subspaceCircularPoint_mem_plane _ _ _ _ _

theorem nestedCircularApex_step_norm (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    ‖nestedCircularApex R ε N hR hε hε1 f (m + 1) - nestedCircularApex R ε N hR hε hε1 f m‖ ≤
      2 * shrinkingCircularRadius R ε N m := by
  rw [nestedCircularApex_succ]
  apply subspaceCircularPoint_displacement
  exact mul_nonneg (div_nonneg hR (by norm_num)) (pow_nonneg (circularRadiusRatio_pos hε N).le m)

theorem nestedCircularApex_value_monotone (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) : Monotone (fun m => f (nestedCircularApex R ε N hR hε hε1 f m)) := by
  have h := nestedCircularPolicy_value_monotone R ε N hR hε hε1 f
  simpa only [nestedCircularPolicy_result_exact, nestedCircularOutput, nestedCircularApex] using h

theorem nestedCircular_stage_neighbors (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    let K := nestedCircularSpace R ε N hR hε hε1 f m
    let y := nestedCircularApex R ε N hR hε hε1 f m
    let j := nestedCircularIndex R ε N hR hε hε1 f m
    let r := shrinkingCircularRadius R ε N m
    f (subspaceCircularPoint K y r N (j - 1)) ≤ f (nestedCircularApex R ε N hR hε hε1 f (m + 1)) ∧
    f (subspaceCircularPoint K y r N (j + 1)) ≤ f (nestedCircularApex R ε N hR hε hε1 f (m + 1)) := by
  let c := nestedCircularController R ε N hR hε hε1 f m
  have hp : Function.Periodic (fun j => f (circularGeometryQuery R ε N c.entries j)) (4 * 2 ^ N) :=
    fun j => congrArg f (circularGeometryQuery_periodic R ε N c.entries j)
  have h := cyclicPeakPolicy_local_max N (fun j => f (circularGeometryQuery R ε N c.entries j)) hp
  change _ at h
  dsimp only
  rw [nestedCircularApex_succ]
  simpa only [c, nestedCircularQuery_at_stage, nestedCircularIndex] using h

end
end Nonsmooth
