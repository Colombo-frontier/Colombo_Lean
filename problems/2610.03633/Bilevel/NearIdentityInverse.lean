import Bilevel.FrozenTilt
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Actual continuous homotopy inverse of `z ↦ z + t G(z)`, constructed by
Banach contraction. The small Lipschitz bound is a verifiable derivative-budget
premise, not a presumed inverse, minimizer, or locality conclusion. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.NearIdentityInverse

abbrev Time := Set.Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def iteration (G : E → E) (u : E) (t : Time) (z : E) : E := u - (t:ℝ) • G z

omit [CompleteSpace E] in
theorem iteration_contracting {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) (t : Time) :
    ContractingWith δ (iteration G u t) := by
  refine ⟨hδ, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simp only [iteration, dist_eq_norm, sub_sub_sub_cancel_left, norm_neg, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  rw [norm_sub_rev (G y) (G x)]
  have h := hG.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h
  calc
    (t:ℝ) * ‖G x-G y‖ ≤ ‖G x-G y‖ :=
      mul_le_of_le_one_left (norm_nonneg _) t.property.2
    _ ≤ (δ:ℝ) * ‖x-y‖ := h

def inverse {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) (t : Time) : E :=
  (iteration_contracting hδ hG u t).fixedPoint (iteration G u t)

theorem inverse_equation {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) (t : Time) :
    inverse hδ hG u t + (t:ℝ) • G (inverse hδ hG u t) = u := by
  have h := (iteration_contracting hδ hG u t).fixedPoint_isFixedPt
  change u-(t:ℝ) • G (inverse hδ hG u t) = inverse hδ hG u t at h
  exact (eq_sub_iff_add_eq.mp h.symm)

theorem inverse_unique {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u z : E) (t : Time)
    (hz : z+(t:ℝ) • G z=u) : z=inverse hδ hG u t := by
  apply (iteration_contracting hδ hG u t).fixedPoint_unique
  change u-(t:ℝ) • G z=z
  rw [← hz]
  abel

theorem inverse_zero {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) :
    inverse hδ hG u ⟨0, by constructor <;> norm_num⟩ = u := by
  simpa using inverse_equation hδ hG u ⟨0, by constructor <;> norm_num⟩

theorem inverse_gradient_bound {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) (t : Time) :
    ‖G (inverse hδ hG u t)‖ ≤ ‖G u‖ / (1-(δ:ℝ)) := by
  let z := inverse hδ hG u t
  have he : z-u = -(t:ℝ) • G z := by
    have h := inverse_equation hδ hG u t
    change z+(t:ℝ) • G z=u at h
    rw [← h]
    module
  have hd : ‖z-u‖ ≤ ‖G z‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg _) t.property.2
  have hg := hG.dist_le_mul z u
  rw [dist_eq_norm, dist_eq_norm] at hg
  have hb := norm_add_le (G z-G u) (G u)
  rw [sub_add_cancel] at hb
  have hm := mul_le_mul_of_nonneg_left hd δ.coe_nonneg
  have hp : 0 < 1-(δ:ℝ) := sub_pos.mpr hδ
  apply (le_div_iff₀ hp).mpr
  change ‖G z‖ * (1-(δ:ℝ)) ≤ ‖G u‖
  nlinarith

theorem inverse_time_bound {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) (s t : Time) :
    ‖inverse hδ hG u s-inverse hδ hG u t‖ ≤
      (‖G u‖/(1-(δ:ℝ))^2) * |(s:ℝ)-(t:ℝ)| := by
  have h := (iteration_contracting hδ hG u s).dist_le_of_fixedPoint
    (inverse hδ hG u t) (iteration_contracting hδ hG u s).fixedPoint_isFixedPt
  have he : inverse hδ hG u t - iteration G u s (inverse hδ hG u t) =
      ((s:ℝ)-(t:ℝ)) • G (inverse hδ hG u t) := by
    let z := inverse hδ hG u t
    have ht : z+(t:ℝ) • G z=u := inverse_equation hδ hG u t
    change z-(u-(s:ℝ) • G z)=((s:ℝ)-(t:ℝ)) • G z
    rw [← ht]
    module
  rw [dist_eq_norm, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, norm_sub_rev] at h
  have hp : 0 < 1-(δ:ℝ) := sub_pos.mpr hδ
  calc
    _ ≤ |(s:ℝ)-(t:ℝ)| * ‖G (inverse hδ hG u t)‖ / (1-(δ:ℝ)) := h
    _ ≤ |(s:ℝ)-(t:ℝ)| * (‖G u‖ / (1-(δ:ℝ))) / (1-(δ:ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (inverse_gradient_bound hδ hG u t) (abs_nonneg _)) hp.le
    _ = _ := by field_simp; ring

theorem inverse_continuous {δ : NNReal} (hδ : δ < 1) {G : E → E}
    (hG : LipschitzWith δ G) (u : E) : Continuous (inverse hδ hG u) := by
  have hc : 0 ≤ ‖G u‖ / (1-(δ:ℝ))^2 := by positivity
  have hl : LipschitzWith ⟨‖G u‖/(1-(δ:ℝ))^2,hc⟩ (inverse hδ hG u) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, NNReal.coe_mk]
      using inverse_time_bound hδ hG u s t
  exact hl.continuous

end Bilevel.NearIdentityInverse

