import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Topology.Algebra.Support

/-!
# Exact local oracle identities

The jets below contain the actual first and iterated second Fréchet
derivatives. They are not independent fields supplied by an oracle model.
On a Euclidean space the first derivative represents the gradient covector
and the iterated derivative represents the Hessian as a curried bilinear map.

These results justify local replacements once neighborhood equality has
been established. They do not establish the manuscript's adaptive shadow
process, visibility invariants, or a complete comparison-oracle simulation.
-/

namespace GradientHessian.JetLocality

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The value and actual first Fréchet derivative. -/
noncomputable def ordinaryJet (f : E → ℝ) (x : E) : ℝ × (E →L[ℝ] ℝ) :=
  (f x, fderiv ℝ f x)

/-- The complete second jet, using the actual iterated Fréchet derivative. -/
noncomputable def richJet (f : E → ℝ) (x : E) :
    ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  (f x, fderiv ℝ f x, fderiv ℝ (fderiv ℝ f) x)

theorem ordinaryJet_congr_of_eventuallyEq {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : ordinaryJet f x = ordinaryJet g x := by
  exact Prod.ext h.self_of_nhds h.fderiv_eq

theorem richJet_congr_of_eventuallyEq {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : richJet f x = richJet g x := by
  have hfirst : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := h.fderiv
  exact Prod.ext h.self_of_nhds (Prod.ext h.fderiv_eq hfirst.fderiv_eq)

@[simp] theorem richJet_zero (x : E) : richJet (fun _ : E => (0 : ℝ)) x = 0 := by
  simp [richJet, fderiv_const, fderiv_zero]

/-- A gate that vanishes on a neighborhood annihilates an arbitrary
coefficient, including an unbounded or noncompactly supported coefficient. -/
theorem richJet_mul_zero_of_gate_zero_near
    (coefficient : E → ℝ) {gate : E → ℝ} {x : E}
    (hgate : gate =ᶠ[𝓝 x] fun _ => 0) :
    richJet (fun y => coefficient y * gate y) x = 0 := by
  have hzero : (fun y => coefficient y * gate y) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hgate] with y hy
    simp [hy]
  exact (richJet_congr_of_eventuallyEq hzero).trans (richJet_zero x)

/-- Consequently a locally zero gate permits replacement of its hidden
coefficient by any other coefficient without changing the literal jet. -/
theorem richJet_replace_coefficient_of_gate_zero_near
    (baseline coefficient replacement : E → ℝ) {gate : E → ℝ} {x : E}
    (hgate : gate =ᶠ[𝓝 x] fun _ => 0) :
    richJet (fun y => baseline y + coefficient y * gate y) x =
      richJet (fun y => baseline y + replacement y * gate y) x := by
  apply richJet_congr_of_eventuallyEq
  filter_upwards [hgate] with y hy
  simp [hy]

/-- Removing a locally zero gated term preserves the entire second jet. -/
theorem richJet_remove_gated_term
    (baseline coefficient : E → ℝ) {gate : E → ℝ} {x : E}
    (hgate : gate =ᶠ[𝓝 x] fun _ => 0) :
    richJet (fun y => baseline y + coefficient y * gate y) x = richJet baseline x := by
  apply richJet_congr_of_eventuallyEq
  filter_upwards [hgate] with y hy
  simp [hy]

omit [NormedSpace ℝ E] in
/-- A perturbation supported in a closed set vanishes on a neighborhood
of every point outside that set. -/
theorem zero_near_of_support_subset_closed
    {perturbation : E → ℝ} {K : Set E} (hK : IsClosed K)
    (hsupport : Function.support perturbation ⊆ K) {x : E} (hx : x ∉ K) :
    perturbation =ᶠ[𝓝 x] fun _ => 0 := by
  have houtside : ∀ᶠ y in 𝓝 x, y ∈ Kᶜ := hK.isOpen_compl.mem_nhds hx
  filter_upwards [houtside] with y hy
  by_contra hne
  exact hy (hsupport hne)

/-- Exact second-jet replacement outside a closed support enclosure. -/
theorem richJet_add_eq_outside_closed_support
    (baseline : E → ℝ) {perturbation : E → ℝ} {K : Set E} (hK : IsClosed K)
    (hsupport : Function.support perturbation ⊆ K) {x : E} (hx : x ∉ K) :
    richJet (fun y => baseline y + perturbation y) x = richJet baseline x := by
  have hzero := zero_near_of_support_subset_closed hK hsupport hx
  apply richJet_congr_of_eventuallyEq
  filter_upwards [hzero] with y hy
  simp [hy]

/-- Compact support is one sufficient enclosure for the preceding identity. -/
theorem richJet_add_eq_outside_compact_support
    (baseline : E → ℝ) {perturbation : E → ℝ} {K : Set E} (hK : IsCompact K)
    (hsupport : Function.support perturbation ⊆ K) {x : E} (hx : x ∉ K) :
    richJet (fun y => baseline y + perturbation y) x = richJet baseline x :=
  richJet_add_eq_outside_closed_support baseline hK.isClosed hsupport hx

end GradientHessian.JetLocality
