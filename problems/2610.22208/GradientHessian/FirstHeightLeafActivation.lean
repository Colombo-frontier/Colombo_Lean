import GradientHessian.FirstHeightLeafData
import GradientHessian.FirstHeightActivation
import GradientHessian.LeafLocalization

/-! Actual first-height numerical localization and activation, instantiated
with the literal capped leaves and their genuine coefficient assumptions. -/

noncomputable section
namespace GradientHessian.FirstHeight
open InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceWeights (d : Data Y E m) (Z : SourceSpace Y E m) : Fin 8 → ℝ :=
  InnerSelector.weight (Inner.ports d.outerDirections Z)
def sourceTerminal (d : Data Y E m) (Z : SourceSpace Y E m) : ℝ :=
  ∏ i, Inner.ports d.outerDirections Z i

theorem sourceWeights_nonneg (d : Data Y E m) (Z : SourceSpace Y E m) (i : Fin 8) :
    0 ≤ sourceWeights d Z i :=
  SelectorPayloadBounds.finite_weight_nonneg _ (Inner.ports_bounds d.outerDirections Z) i
theorem sourceTerminal_nonneg (d : Data Y E m) (Z : SourceSpace Y E m) : 0 ≤ sourceTerminal d Z :=
  Finset.prod_nonneg (fun i _ => (Inner.ports_bounds d.outerDirections Z i).1)
theorem sourceWeights_partition (d : Data Y E m) (Z : SourceSpace Y E m) :
    sourceTerminal d Z + ∑ i, sourceWeights d Z i = 1 := by
  rw [add_comm]
  exact SelectorPayloadBounds.finite_weight_partition 8 _

theorem sourceDriven_numerical_slice (d : Data Y E m) (l : ℝ) (Z : SourceSpace Y E m) :
    let z := numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z
    ∃ c : ℝ, ∀ y,
      sourceDriven d l (replaceNumerical Z (replaceNumerical z y)) =
        Leaf.mixture (sourceTerminal d Z) (sourceWeights d Z) d.A d.b d.a d.innerDirections
          (replaceNumerical z y) + c := by
  dsimp only
  let z := numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z
  let w := sourceWeights d Z
  let q := sourceTerminal d Z
  let B := fun i => Inner.input (d.outerDirections i)
    (tasks (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z i)
  let c := -(∑ i, w i * ((i.val : ℝ) * spacing m + B i * childPorts d i z)) -
    8 * spacing m * q + Inner.selfSum d.outerDirections Z - l * Inner.outgoing d.outerDirections Z
  refine ⟨c, fun y => ?_⟩
  have hout : Inner.outgoing d.outerDirections (replaceNumerical Z (replaceNumerical z y)) =
      Inner.outgoing d.outerDirections Z := by simp [Inner.outgoing, Inner.ports]
  unfold sourceDriven driven
  rw [node_lower_slice, hout]
  simp only [childPorts, Leaf.outgoing, Inner.outgoing, Inner.ports, tasks_replaceNumerical]
  change q * Leaf.publicQuadratic (m + 1) (replaceNumerical z y) +
      (∑ i, w i * children d i (replaceNumerical z y)) -
      (∑ i, w i * ((i.val : ℝ) * spacing m + B i * childPorts d i z)) - 8 * spacing m * q +
      Inner.selfSum d.outerDirections Z - l * Inner.outgoing d.outerDirections Z = _
  change _ = q * Leaf.publicQuadratic (m + 1) (replaceNumerical z y) +
    ∑ i, w i * children d i (replaceNumerical z y) + c
  dsimp only [c]
  ring

variable [CompleteSpace Y] [CompleteSpace E]

theorem sourceDriven_localization (d : Data Y E m) (hd : Valid d) (l : ℝ) (Z : SourceSpace Y E m)
    (hg : ‖gradient (sourceDriven d l) Z‖ ≤ 1) :
    ‖numerical Y E (m + 1) (Inner.absoluteDepth + 2)
      (numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z)‖ ≤ Leaf.numericalRadius := by
  let z := numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z
  let f := fun W : Leaf.Space Y E (m + 1) => sourceDriven d l (replaceNumerical Z W)
  have hf : ContDiff ℝ 3 f := (sourceDriven_contDiff d l).comp
    (contDiff_const.add ((insertNumerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2)).contDiff.comp
      (contDiff_id.sub contDiff_const)))
  have hfg := (numerical_slice_gradient_norm_le Z (sourceDriven d l)
    ((sourceDriven_contDiff d l).differentiable (by norm_num) Z)).trans hg
  obtain ⟨c, hc⟩ := sourceDriven_numerical_slice d l Z
  apply Leaf.mixture_localization (m := m + 1) (by omega)
    (sourceTerminal d Z) (sourceWeights d Z) (sourceTerminal_nonneg d Z)
    (sourceWeights_nonneg d Z) (sourceWeights_partition d Z) d.A hd.lower
    (fun i => by simpa using hd.opNorm i) hd.symmetric d.b d.a d.innerDirections
    hd.b_norm hd.a_norm f z (hf.differentiable (by norm_num) z) c hc hfg

/-- Assertion (ii) of `lem:first-height`, for the literal eight-child node.
All child properties are discharged by the proved capped-leaf construction. -/
theorem source_activation (d : Data Y E m) (hd : Valid d) {l : ℝ} (hl : 0 ≤ l)
    (Z : SourceSpace Y E m) (hg : ‖gradient (sourceDriven d l) Z‖ ≤ 1) :
    ∀ i, Inner.ports d.outerDirections Z i = 1 := by
  have hZ := sourceDriven_localization d hd l Z hg
  apply activation_at_bounded_lower (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d)
    (mul_nonneg leafValueConstant_pos.le (by positivity)) d.outerDirections hl
    (Leaf.publicQuadratic_contDiff _) (children_contDiff d) (childPorts_contDiff d) hd.outer_unit
    ?_ Z ?_ (fun i => childPorts_bounds d i _) hg
  · intro i s hs z hgrad
    exact (Leaf.activation (d.A i) (hd.lower i) (hd.opNorm i) (hd.symmetric i)
      (d.b i) (d.a i) (d.innerDirections i) (hd.b_norm i) (hd.a_norm i) (hd.certificate i)
      (hd.inner_unit i) hs z hgrad).1
  · intro i
    rw [children_relative]
    simpa only [leafValueConstant, Nat.cast_add, Nat.cast_one, neg_mul] using
      Leaf.bounded_correction (d.A i) (by simpa using hd.opNorm i) (d.b i) (d.a i)
        (d.innerDirections i) _ hZ

end GradientHessian.FirstHeight
