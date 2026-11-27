import Nonsmooth.NestedCircularPairCertificate
import Nonsmooth.RecursiveConeCertificate

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) (f : E → ℝ)

theorem nestedCircularRadial_spans_final (D : ℕ) (hD : 0 < D) (hDim : D ≤ Module.finrank ℝ E - 1)
    (hline : Module.finrank ℝ (nestedCircularSpace R ε N hR hε hε1 f D) = 1) :
    (ℝ ∙ nestedCircularRadial R ε N hR hε hε1 f (D - 1)) =
      nestedCircularSpace R ε N hR hε hε1 f D := by
  have hi : D - 1 < Module.finrank ℝ E - 1 := by omega
  have hu := nestedCircularRadial_unit R ε N hR hε hε1 f (D - 1) hi
  have hm := nestedCircularRadial_mem_next R ε N hR hε hε1 f (D - 1) hi
  rw [Nat.sub_add_cancel (show 1 ≤ D by omega)] at hm
  have hu0 : nestedCircularRadial R ε N hR hε hε1 f (D - 1) ≠ 0 := by
    intro hz
    simp [hz] at hu
  apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hm)
  rw [finrank_span_singleton hu0, hline]

theorem nestedCircular_last_offset (D : ℕ) (hD : 0 < D) :
    nestedCircularOffset R ε N hR hε hε1 f D (D - 1) =
      -((shrinkingCircularRadius R ε N (D - 1) * (1 - Real.cos (circularGridAngle N))) •
        nestedCircularRadial R ε N hR hε hε1 f (D - 1)) := by
  simp only [nestedCircularOffset, Nat.sub_add_cancel (show 1 ≤ D by omega), sub_self, zero_sub]

theorem nestedCircular_final_positive_ray (hRpos : 0 < R)
    (G : Set E) (hballG : Metric.closedBall (0 : E) R ⊆ G)
    (hf : ConvexOn ℝ G f) (D : ℕ) (hD : 0 < D)
    (h : ℝ) (hh : 0 ≤ h)
    (hz : nestedCircularApex R ε N hR hε hε1 f D +
      h • nestedCircularRadial R ε N hR hε hε1 f (D - 1) ∈ G) :
    f (nestedCircularApex R ε N hR hε hε1 f D) ≤
      f (nestedCircularApex R ε N hR hε hε1 f D +
        h • nestedCircularRadial R ε N hR hε hε1 f (D - 1)) := by
  let i := D - 1
  let x := nestedCircularApex R ε N hR hε hε1 f D
  let e := nestedCircularRadial R ε N hR hε hε1 f i
  let n := nestedCircularNormal R ε N hR hε hε1 f i
  let r := shrinkingCircularRadius R ε N i
  let b := r * (1 - Real.cos (circularGridAngle N))
  let a := r * Real.sin (circularGridAngle N)
  have hb : 0 < b := mul_pos (shrinkingCircularRadius_pos hRpos hε N i) (circularGridAngle_cos_gap_pos N)
  have hrep := nestedCircular_neighbors_representation R ε N hR hε hε1 f D (D - 1)
  rw [nestedCircular_last_offset R ε N hR hε hε1 f D hD] at hrep
  simp only [← sub_eq_add_neg] at hrep
  have hval := nestedCircular_stage_neighbors R ε N hR hε hε1 f (D - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ D by omega)] at hval
  have hmG : x - b • e - a • n ∈ Metric.closedBall (0 : E) R := by
    have hp := nestedCircular_stage_query_feasible R ε N hR hε hε1 f i
      (nestedCircularIndex R ε N hR hε hε1 f i - 1)
    rw [hrep.1] at hp
    simpa only [x, b, e, a, n, r, i, Metric.mem_closedBall, dist_zero_right] using hp
  have hpG : x - b • e + a • n ∈ Metric.closedBall (0 : E) R := by
    have hp := nestedCircular_stage_query_feasible R ε N hR hε hε1 f i
      (nestedCircularIndex R ε N hR hε hε1 f i + 1)
    rw [hrep.2] at hp
    simpa only [x, b, e, a, n, r, i, Metric.mem_closedBall, dist_zero_right] using hp
  have hmB : f (x - b • e - a • n) ≤ f x := by rw [← hrep.1]; exact hval.1
  have hpB : f (x - b • e + a • n) ≤ f x := by rw [← hrep.2]; exact hval.2
  exact symmetric_queries_positive_ray hf x e n hb hh (hballG hmG) (hballG hpG) hmB hpB hz

theorem nestedCircular_final_line_cone (hRpos : 0 < R)
    (G : Set E) (hballG : Metric.closedBall (0 : E) R ⊆ G)
    (hf : ConvexOn ℝ G f) (D : ℕ) (hD : 0 < D)
    (hDim : D ≤ Module.finrank ℝ E - 1)
    (hline : Module.finrank ℝ (nestedCircularSpace R ε N hR hε hε1 f D) = 1) :
    comparisonConeExcluded G f (nestedCircularSpace R ε N hR hε hε1 f D)
      (nestedCircularApex R ε N hR hε hε1 f D) (nestedCircularRadial R ε N hR hε hε1 f (D - 1))
      0 (f (nestedCircularApex R ε N hR hε hε1 f D)) := by
  rw [← nestedCircularRadial_spans_final R ε N hR hε hε1 f D hD hDim hline]
  apply comparisonConeExcluded_of_positive_ray
    (nestedCircularRadial_unit R ε N hR hε hε1 f (D - 1) (by omega))
  intro h hh hz
  exact nestedCircular_final_positive_ray R ε N hR hε hε1 f hRpos G hballG hf D hD h hh hz

end
end Nonsmooth
