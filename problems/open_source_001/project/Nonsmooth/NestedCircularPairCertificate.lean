import Nonsmooth.NestedCircularNeighborGeometry

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) (f : E → ℝ)

theorem nestedCircularOffset_mem_next (D i : ℕ) (hi : i < D) (hD : D ≤ Module.finrank ℝ E - 1) :
    nestedCircularOffset R ε N hR hε hε1 f D i ∈ nestedCircularSpace R ε N hR hε hε1 f (i + 1) := by
  let K := nestedCircularSpace R ε N hR hε hε1 f (i + 1)
  have htail := nestedCircularApex_displacement_mem R ε N hR hε hε1 f (i + 1) D (by omega)
  have hback : nestedCircularApex R ε N hR hε hε1 f (i + 1) -
      nestedCircularApex R ε N hR hε hε1 f D ∈ K := by
    simpa only [neg_sub] using K.neg_mem htail
  exact K.sub_mem hback (K.smul_mem _ (nestedCircularRadial_mem_next R ε N hR hε hε1 f i (lt_of_lt_of_le hi hD)))

theorem nestedCircularOffset_norm_small (D i : ℕ) (hi : i < D) (hD : D ≤ Module.finrank ℝ E - 1)
    (hθ : 2 / (2 : ℝ) ^ N ≤ ε / 2) :
    ‖nestedCircularOffset R ε N hR hε hε1 f D i‖ ≤
      (shrinkingCircularRadius R ε N i * Real.sin (circularGridAngle N)) * ε := by
  obtain ⟨_, _, hu, hv, huv⟩ := subspaceCircularFrame_spec _
    (nestedCircularSpace_at_least_two R ε N hR hε hε1 f i (lt_of_lt_of_le hi hD))
  have hr : 0 ≤ shrinkingCircularRadius R ε N i :=
    mul_nonneg (div_nonneg hR (by norm_num)) (pow_nonneg (circularRadiusRatio_pos hε N).le i)
  rw [nestedCircularOffset_eq_grid_offset]
  apply circularNeighborOffset_small_of_small_tail hu hv huv hr N _ hθ
  have ht := nestedCircularApex_tail_norm R ε N hR hε hε1 f D i hi
  rw [nestedCircularApex_succ] at ht
  simpa only [subspaceCircularPoint, norm_sub_rev] using ht

/-- Every earlier pair has all geometric and value bounds required by the cone-lifting argument. -/
theorem nestedCircular_pair_certificate (hRpos : 0 < R) (D i : ℕ) (hi : i < D)
    (hD : D ≤ Module.finrank ℝ E - 1) (hθ : 2 / (2 : ℝ) ^ N ≤ ε / 2) :
    let x := nestedCircularApex R ε N hR hε hε1 f D
    let w := nestedCircularOffset R ε N hR hε hε1 f D i
    let n := nestedCircularNormal R ε N hR hε hε1 f i
    let a := shrinkingCircularRadius R ε N i * Real.sin (circularGridAngle N)
    0 < a ∧ n ∈ nestedCircularSpace R ε N hR hε hε1 f i ∧ ‖n‖ = 1 ∧
      w ∈ nestedCircularSpace R ε N hR hε hε1 f (i + 1) ∧ ‖w‖ ≤ a * ε ∧
      ‖x + w - a • n‖ ≤ R ∧ ‖x + w + a • n‖ ≤ R ∧
      f (x + w - a • n) ≤ f x ∧ f (x + w + a • n) ≤ f x := by
  dsimp only
  have hiDim := lt_of_lt_of_le hi hD
  have ha := mul_pos (shrinkingCircularRadius_pos hRpos hε N i) (circularGridAngle_sin_pos N)
  have hrep := nestedCircular_neighbors_representation R ε N hR hε hε1 f D i
  have hval := nestedCircular_stage_neighbors R ε N hR hε hε1 f i
  have hmono := nestedCircularApex_value_monotone R ε N hR hε hε1 f (show i + 1 ≤ D by omega)
  refine ⟨ha, nestedCircularNormal_mem R ε N hR hε hε1 f i,
    nestedCircularNormal_unit R ε N hR hε hε1 f i hiDim,
    nestedCircularOffset_mem_next R ε N hR hε hε1 f D i hi hD,
    nestedCircularOffset_norm_small R ε N hR hε hε1 f D i hi hD hθ, ?_, ?_, ?_, ?_⟩
  · rw [← hrep.1]
    exact nestedCircular_stage_query_feasible R ε N hR hε hε1 f i _
  · rw [← hrep.2]
    exact nestedCircular_stage_query_feasible R ε N hR hε hε1 f i _
  · rw [← hrep.1]
    exact hval.1.trans hmono
  · rw [← hrep.2]
    exact hval.2.trans hmono

end
end Nonsmooth
