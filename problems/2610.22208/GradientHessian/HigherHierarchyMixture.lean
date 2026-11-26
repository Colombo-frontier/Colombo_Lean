import GradientHessian.HigherHierarchyLeafSlice
import GradientHessian.HigherHierarchyLeafData

/-! The exact convex mixture of literal leaf objectives along the shared
numerical slice. No small-gradient or analytic assumption is used here. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open InnerCoordinates

section Node
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem nodePorts_replaceLower (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) (x : F) :
    nodePorts w c (replaceLower Z x) = nodePorts w c Z := by
  funext i
  simp only [nodePorts, parent_replaceLower]
theorem nodeWeights_replaceLower (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) (x : F) :
    nodeWeights w c (replaceLower Z x) = nodeWeights w c Z := by
  rw [nodeWeights, nodePorts_replaceLower]
  rfl
theorem nodeTerminal_replaceLower (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) (x : F) :
    nodeTerminal w c (replaceLower Z x) = nodeTerminal w c Z := by
  simp only [nodeTerminal, nodePorts, parent_replaceLower]

theorem nodeScalar_eq_mixture (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (S R w : ℝ) (c : Fin 8 → G) (Z : Layer F G) :
    nodeScalar Q child childPort S R w c Z = nodeTerminal w c Z * Q (lower F G Z) +
      (∑ i, nodeWeights w c Z i * child i (lower F G Z)) -
      (∑ i, nodeWeights w c Z i * ((i.val:ℝ)*S+nodeIncoming R w c Z i*childPort i (lower F G Z))) -
      8*S*nodeTerminal w c Z + nodeSelf R w c Z := by
  have he : nodePayload Q child childPort S R w c Z = fun i =>
      child i (lower F G Z)-Q (lower F G Z)-((i.val:ℝ)*S+nodeIncoming R w c Z i*childPort i (lower F G Z)) := by
    funext i
    unfold nodePayload
    ring
  rw [nodeScalar, nodeSelected, he, FirstHeightSelector.select_sub_baseline]
  unfold nodeWeights nodeTerminal
  ring
end Node

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def leafMixture (K : ℝ) (t : ℕ) (d : Data Y E H m t) (Z : Space Y E H m t)
    (z : Leaf.Space Y E (m+1)) : ℝ :=
  Leaf.mixture (resetWeight K t d Z) (leafWeights K t d Z)
    (fun i => (leafData t d i).A) (fun i => (leafData t d i).b)
    (fun i => (leafData t d i).a) (fun i => (leafData t d i).v) z

theorem leafMixture_succ (K : ℝ) (t : ℕ) (d : Data Y E H m (t+1)) (Z : Space Y E H m (t+1))
    (z : Leaf.Space Y E (m+1)) :
    leafMixture K (t+1) d Z z = nodeTerminal (width m t) (centers K d) Z * Leaf.publicQuadratic (m+1) z +
      ∑ i, nodeWeights (width m t) (centers K d) Z i * leafMixture K t (d.children i) (lower _ _ Z) z := by
  change (nodeTerminal (width m t) (centers K d) Z +
      ∑ i, nodeWeights (width m t) (centers K d) Z i * resetWeight K t (d.children i) (lower _ _ Z)) *
      Leaf.publicQuadratic (m+1) z +
    (∑ a : Fin 8 × LeafSlot t, (nodeWeights (width m t) (centers K d) Z a.1 *
      leafWeights K t (d.children a.1) (lower _ _ Z) a.2) *
      Leaf.objective (leafData t (d.children a.1) a.2).A (leafData t (d.children a.1) a.2).b
        (leafData t (d.children a.1) a.2).a (leafData t (d.children a.1) a.2).v z) = _
  rw [Fintype.sum_prod_type]
  simp only [leafMixture, Leaf.mixture, add_mul, Finset.sum_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

theorem scalar_numerical_slice (K : ℝ) : ∀ t (d : Data Y E H m t) (Z : Space Y E H m t),
    ∃ c : ℝ, ∀ y, scalar K t d (replaceLeaf t Z (replaceNumerical (leafProjection t Z) y)) =
      leafMixture K t d Z (replaceNumerical (leafProjection t Z) y) + c := by
  intro t
  induction t with
  | zero =>
    intro d Z
    simpa only [scalar, replaceLeaf_zero, leafProjection, leafMixture, resetWeight, leafWeights,
      leafData, FirstHeight.sourceDriven, FirstHeight.driven, zero_mul, sub_zero] using
      FirstHeight.sourceDriven_numerical_slice d 0 Z
  | succ t ih =>
    intro d Z
    let z := leafProjection t (lower _ _ Z)
    let α := nodeWeights (width m t) (centers K d) Z
    let τ := nodeTerminal (width m t) (centers K d) Z
    let cost := ∑ i, α i * ((i.val:ℝ)*spacing m K t + nodeIncoming (radius m K t) (width m t)
      (centers K d) Z i * outgoing K t (d.children i) (lower _ _ Z))
    choose c hc using fun i : Fin 8 => ih (d.children i) (lower _ _ Z)
    refine ⟨τ*(baseline K t (lower _ _ Z)-Leaf.publicQuadratic (m+1) z)+
      (∑ i, α i*c i)-cost-8*spacing m K t*τ+nodeSelf (radius m K t) (width m t) (centers K d) Z, ?_⟩
    intro y
    have he : scalar K (t+1) d (replaceLeaf (t+1) Z (replaceNumerical z y)) =
        τ*baseline K t (replaceLeaf t (lower _ _ Z) (replaceNumerical z y)) +
        (∑ i, α i*scalar K t (d.children i) (replaceLeaf t (lower _ _ Z) (replaceNumerical z y))) -
        cost-8*spacing m K t*τ+nodeSelf (radius m K t) (width m t) (centers K d) Z := by
      rw [scalar, nodeScalar_eq_mixture, replaceLeaf_succ]
      simp only [α, τ, cost, nodeWeights_replaceLower, nodeTerminal_replaceLower,
        nodeIncoming, nodeSelf, parent_replaceLower, lower_replaceLower, outgoing_replaceLeaf]
    have hs : (∑ i, α i*scalar K t (d.children i) (replaceLeaf t (lower _ _ Z) (replaceNumerical z y))) =
        (∑ i, α i*leafMixture K t (d.children i) (lower _ _ Z) (replaceNumerical z y)) + ∑ i, α i*c i := by
      calc
        _ = ∑ i, α i*(leafMixture K t (d.children i) (lower _ _ Z) (replaceNumerical z y)+c i) :=
          Finset.sum_congr rfl (fun i _ => congrArg (fun r => α i*r) (hc i y))
        _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]
    change scalar K (t+1) d (replaceLeaf (t+1) Z (replaceNumerical z y)) = _
    rw [he, hs, baseline_replaceLeaf, leafMixture_succ]
    have algebra (a b c d e f g h i : ℝ) :
        a*(b+(c-d))+(e+f)-g-h+i = a*b+e+(a*(c-d)+f-g-h+i) := by ring
    exact algebra _ _ _ _ _ _ _ _ _

theorem driven_numerical_slice (K : ℝ) (t : ℕ) (d : Data Y E H m t) (l : ℝ) (Z : Space Y E H m t) :
    ∃ c : ℝ, ∀ y, driven K t d l (replaceLeaf t Z (replaceNumerical (leafProjection t Z) y)) =
      leafMixture K t d Z (replaceNumerical (leafProjection t Z) y)+c := by
  obtain ⟨c,hc⟩ := scalar_numerical_slice K t d Z
  refine ⟨c-l*outgoing K t d Z, fun y => ?_⟩
  rw [driven, hc, outgoing_replaceLeaf]
  ring

end GradientHessian.HigherHierarchy
