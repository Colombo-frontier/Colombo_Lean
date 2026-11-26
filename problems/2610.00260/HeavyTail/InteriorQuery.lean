import HeavyTail.ProximalMeasurability
import Mathlib.Analysis.Convex.Topology

/-! An explicit continuous interior query near any feasible point, and the
bounded-subgradient fact used after reducing to the affine hull. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace Topology
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def interiorQueryWeight (ε : ℝ) (anchor y : E) : ℝ :=
  min (1 / 2) (ε / (2 * (1 + ‖anchor - y‖)))

def interiorQuery (ε : ℝ) (anchor y : E) : E :=
  y + interiorQueryWeight ε anchor y • (anchor - y)

theorem interiorQueryWeight_mem {ε : ℝ} (hε : 0 < ε) (anchor y : E) :
    interiorQueryWeight ε anchor y ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · unfold interiorQueryWeight
    apply lt_min <;> positivity
  · exact (min_le_left _ _).trans (by norm_num)

theorem interiorQuery_mem {X : Set E} (hX : Convex ℝ X) {anchor y : E}
    (ha : anchor ∈ interior X) (hy : y ∈ X) {ε : ℝ} (hε : 0 < ε) :
    interiorQuery ε anchor y ∈ interior X :=
  hX.add_smul_sub_mem_interior hy ha (interiorQueryWeight_mem hε anchor y)

theorem interiorQuery_near {ε : ℝ} (hε : 0 < ε) (anchor y : E) :
    ‖interiorQuery ε anchor y - y‖ ≤ ε := by
  have ht := (interiorQueryWeight_mem hε anchor y).1.le
  have heq : interiorQuery ε anchor y - y = interiorQueryWeight ε anchor y • (anchor - y) := by
    unfold interiorQuery
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  calc
    _ ≤ ε / (2 * (1 + ‖anchor - y‖)) * ‖anchor - y‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
    _ ≤ ε := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + ‖anchor - y‖))).mpr
      nlinarith [mul_nonneg hε.le (norm_nonneg (anchor - y))]

theorem interiorQueryWeight_continuous (ε : ℝ) (anchor : E) :
    Continuous (interiorQueryWeight ε anchor) := by
  exact continuous_const.min (continuous_const.div
    (continuous_const.mul (continuous_const.add (continuous_const.sub continuous_id).norm))
      (fun y => ne_of_gt (by positivity : 0 < 2 * (1 + ‖anchor - y‖))))

theorem interiorQuery_continuous (ε : ℝ) (anchor : E) :
    Continuous (interiorQuery ε anchor) :=
  continuous_id.add ((interiorQueryWeight_continuous ε anchor).smul (continuous_const.sub continuous_id))

/-- Every subgradient at an interior query is bounded by the Lipschitz constant.
In the affine-hull coordinates this applies to the tangent projected mean. -/
theorem interior_subgradient_norm_bound {X : Set E} {f : E → ℝ} {w g : E} {G : ℝ}
    (hG : 0 ≤ G) (hw : w ∈ interior X)
    (hsub : ∀ u ∈ X, ⟪g, u - w⟫_ℝ ≤ f u - f w)
    (hlip : ∀ u ∈ X, f u - f w ≤ G * ‖u - w‖) : ‖g‖ ≤ G := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  let t := ε / (2 * (1 + ‖g‖))
  have ht : 0 < t := by dsimp [t]; positivity
  let u := w + t • g
  have hueq : u - w = t • g := by dsimp [u]; abel
  have hdist : ‖u - w‖ = t * ‖g‖ := by
    rw [hueq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hnear : ‖u - w‖ < ε := by
    rw [hdist]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + ‖g‖))).mpr
    nlinarith [mul_nonneg hε.le (norm_nonneg g)]
  have hu : u ∈ X := hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hnear)
  have h := (hsub u hu).trans (hlip u hu)
  rw [hueq, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h
  have h' : t * ‖g‖ ^ 2 ≤ t * (G * ‖g‖) := by nlinarith only [h]
  have hs := (mul_le_mul_left ht).mp h'
  by_contra hn
  have hgt : G < ‖g‖ := lt_of_not_ge hn
  have hprod := mul_pos (sub_pos.mpr hgt) (hG.trans_lt hgt)
  nlinarith only [hs, hprod]

end HeavyTail
