import Bilevel.TransportEdgePosterior
import Bilevel.TransportEdgeMoment

/-! Actual paired-action histories. Their source/range spans and support are
computed from disclosed vector pairs. Perpendicular fresh-image support is
derived from the real orthogonal map's constraints, not posited as a moment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportEdgePosterior
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

abbrev Pairs (D : ℕ) := List (Space D × Space D)

def domain {D : ℕ} : Pairs D → Submodule ℝ (Space D)
  | [] => ⊥
  | (a,_)::L => domain L ⊔ Submodule.span ℝ {a}

def range {D : ℕ} : Pairs D → Submodule ℝ (Space D)
  | [] => ⊥
  | (_,b)::L => range L ⊔ Submodule.span ℝ {b}

def Supports {D : ℕ} : Pairs D → OrthogonalHaar.Group D → Prop
  | [],_ => True
  | (a,b)::L,O => (O • a = b) ∧ Supports L O

theorem support_measurable {D : ℕ} (L : Pairs D) : MeasurableSet {O | Supports L O} := by
  induction L with
  | nil => exact MeasurableSet.univ
  | cons p L ih =>
    exact (measurableSet_eq_fun (forward_measurable p.1) measurable_const).inter ih

theorem map_domain_eq_range {D : ℕ} (L : Pairs D) (O : OrthogonalHaar.Group D)
    (hO : Supports L O) :
    (domain L).map (isometry D O).toLinearEquiv.toLinearMap = range L := by
  induction L with
  | nil => simp only [domain,range,Submodule.map_bot]
  | cons p L ih =>
    rcases p with ⟨a,b⟩
    change (domain L ⊔ Submodule.span ℝ {a}).map (isometry D O).toLinearEquiv.toLinearMap =
      range L ⊔ Submodule.span ℝ {b}
    rw [Submodule.map_sup,ih hO.2,Submodule.map_span]
    have hh : (isometry D O).toLinearEquiv.toLinearMap a = b := hO.1
    rw [Set.image_singleton,hh]

theorem image_perpendicular {D : ℕ} (L : Pairs D) (O : OrthogonalHaar.Group D)
    (hO : Supports L O) (x : Space D) (hx : x ∈ (domain L)ᗮ) : O • x ∈ (range L)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← map_domain_eq_range L O hO] at hy
  obtain ⟨a,ha,hya⟩ := hy
  change (isometry D O) a = y at hya
  rw [← hya]
  exact ((isometry D O).inner_map_map x a).trans (hx a ha)

theorem forward_posterior_pairs {D : ℕ} (L : Pairs D)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O) (q : Space D) :
    ∀ᵐ y ∂μ.map (forward q),
      Invariant (range ((q,y)::L)) (condDistrib id (forward q) μ y) ∧
      (∀ᵐ O ∂condDistrib id (forward q) μ y, Supports ((q,y)::L) O) := by
  have hold := ConditionalSupport.support μ (forward q) (forward_measurable q)
    _ (support_measurable L) hL
  filter_upwards [forward_posterior_invariant (range L) μ hμ q,forward_fiber μ q,hold] with y hy hf ho
  refine ⟨hy,?_⟩
  filter_upwards [hf,ho] with O hO hOld
  exact ⟨hO,hOld⟩

theorem reverse_posterior_pairs {D : ℕ} (L : Pairs D)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O) (q : Space D) :
    ∀ᵐ x ∂μ.map (reverse q),
      Invariant (range ((x,q)::L)) (condDistrib id (reverse q) μ x) ∧
      (∀ᵐ O ∂condDistrib id (reverse q) μ x, Supports ((x,q)::L) O) := by
  have hold := ConditionalSupport.support μ (reverse q) (reverse_measurable q)
    _ (support_measurable L) hL
  filter_upwards [reverse_posterior_invariant (range L) μ hμ q,reverse_fiber μ q,hold] with x hx hf ho
  refine ⟨hx,?_⟩
  filter_upwards [hf,ho] with O hO hOld
  exact ⟨hO,hOld⟩

/-- The required fresh-image perpendicular support follows from actual paired
constraints. The resulting Frobenius probability bound contains no supplied
support or moment conclusion for the fresh image. -/
theorem paired_images_projection_failure {D r : ℕ} (L : Pairs D)
    (W : Submodule ℝ (Space D)) (hd : 0 < Module.finrank ℝ (range L)ᗮ)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O)
    (v : Fin r → Space D) (hv : ∀ i, ‖v i‖ = 1) (hp : ∀ i, v i ∈ (domain L)ᗮ) :
    μ.real {O | (1:ℝ)/64 < TransportObserver.frameEnergy W (images v O) Finset.univ} ≤
      64*((r:ℝ)*Module.finrank ℝ W/(Module.finrank ℝ (range L)ᗮ : ℝ)) := by
  apply images_projection_failure (range L) W hd μ hμ v hv
  filter_upwards [hL] with O hO
  exact fun i => image_perpendicular L O hO (v i) (hp i)

end Bilevel.TransportEdgePosterior
