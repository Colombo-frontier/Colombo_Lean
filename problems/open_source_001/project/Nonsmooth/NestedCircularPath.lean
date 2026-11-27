import Nonsmooth.NestedCircularStepData

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem nestedCircular_initial_geometry (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) : nestedCircularApex R ε N hR hε hε1 f 0 = 0 ∧
      nestedCircularSpace R ε N hR hε hε1 f 0 = ⊤ := ⟨rfl, rfl⟩

theorem nestedCircularSpace_antitone (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) : Antitone (nestedCircularSpace R ε N hR hε hε1 f) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [nestedCircularSpace_succ]
  exact subspaceCircularSection_le _ _ _

theorem nestedCircularApex_displacement_mem (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (i j : ℕ) (hij : i ≤ j) :
    nestedCircularApex R ε N hR hε hε1 f j - nestedCircularApex R ε N hR hε hε1 f i ∈
      nestedCircularSpace R ε N hR hε hε1 f i := by
  induction j, hij using Nat.le_induction with
  | base => simp only [sub_self, Submodule.zero_mem]
  | succ j hij ih =>
    have hstep := (nestedCircularSpace_antitone R ε N hR hε hε1 f hij)
      (nestedCircularApex_step_mem R ε N hR hε hε1 f j)
    have heq : nestedCircularApex R ε N hR hε hε1 f (j + 1) - nestedCircularApex R ε N hR hε hε1 f i =
        (nestedCircularApex R ε N hR hε hε1 f (j + 1) - nestedCircularApex R ε N hR hε hε1 f j) +
        (nestedCircularApex R ε N hR hε hε1 f j - nestedCircularApex R ε N hR hε hε1 f i) := by abel
    rw [heq]
    exact (nestedCircularSpace R ε N hR hε hε1 f i).add_mem hstep ih

theorem nestedCircularApex_tail_norm (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (D i : ℕ) (hi : i < D) :
    ‖nestedCircularApex R ε N hR hε hε1 f D - nestedCircularApex R ε N hR hε hε1 f (i + 1)‖ ≤
      (shrinkingCircularRadius R ε N i * Real.sin (circularGridAngle N)) * (ε / 2) :=
  shrinkingCircularRadius_tail (nestedCircularApex R ε N hR hε hε1 f) hR hε hε1 N D i hi
    (fun j _ => nestedCircularApex_step_norm R ε N hR hε hε1 f j)

theorem nestedCircular_stage_query_feasible (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) (j : ℤ) :
    ‖subspaceCircularPoint (nestedCircularSpace R ε N hR hε hε1 f m)
      (nestedCircularApex R ε N hR hε hε1 f m) (shrinkingCircularRadius R ε N m) N j‖ ≤ R := by
  rw [← nestedCircularQuery_at_stage]
  exact circularGeometryQuery_feasible hR hε hε1 N _ j

theorem nestedCircularSpace_dimension (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    Module.finrank ℝ (nestedCircularSpace R ε N hR hε hε1 f m) = max 1 (Module.finrank ℝ E - m) := by
  have hh := circularGeometryState_dimension (E := E) R ε N
    (nestedCircularController R ε N hR hε hε1 f m).entries
  rw [nestedCircularController_length] at hh
  convert! hh using 1

end
end Nonsmooth
