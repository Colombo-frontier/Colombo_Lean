import GradientHessian.HigherHierarchyCoordinates

/-! The literal localized node on one shared lower space and eight new
physical parent vectors. Centers label coefficients, not coordinates. -/

noncomputable section
namespace GradientHessian.HigherHierarchy

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def nodePorts (w : ℝ) (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) : ℝ :=
  Localized.port w (c i) (parent F E Z i)
def nodeIncoming (R w : ℝ) (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) : ℝ :=
  Localized.incoming R w (c i) (parent F E Z i)
def nodeSelf (R w : ℝ) (c : Fin 8 → E) (Z : Layer F E) : ℝ :=
  ∑ i, Localized.potential R w (c i) (parent F E Z i)
def nodePerturbation (R w : ℝ) (c : Fin 8 → E) (Z : Layer F E) : ℝ :=
  ∑ i, Localized.perturbation R w (c i) (parent F E Z i)

def nodePayload (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) : ℝ :=
  child i (lower F E Z) - Q (lower F E Z) - (i.val : ℝ) * S -
    nodeIncoming R w c Z i * childPort i (lower F E Z)
def nodeSelected (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) : ℝ :=
  FirstHeightSelector.select 8 (nodePorts w c Z) (nodePayload Q child childPort S R w c Z) (-8 * S)
def nodeScalar (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) : ℝ :=
  Q (lower F E Z) + nodeSelected Q child childPort S R w c Z + nodeSelf R w c Z
def nodeBaseline (Q : F → ℝ) (R : ℝ) (Z : Layer F E) : ℝ :=
  Q (lower F E Z) + ∑ i, Localized.publicPotential R (parent F E Z i)
def nodeResidual (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) : ℝ :=
  nodeScalar Q child childPort S R w c Z - nodeBaseline Q R Z

theorem nodeScalar_eq_source (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) :
    nodeScalar Q child childPort S R w c Z = Q (lower F E Z) +
      (∑ i, InnerSelector.weight (nodePorts w c Z) i * nodePayload Q child childPort S R w c Z i) -
      8 * S * (∏ i, nodePorts w c Z i) + nodeSelf R w c Z := by
  simp only [nodeScalar, nodeSelected, FirstHeightSelector.select_eq_inner,
    InnerSelector.select_eq_weighted_sum]
  ring

theorem nodeResidual_eq (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) :
    nodeResidual Q child childPort S R w c Z =
      nodeSelected Q child childPort S R w c Z + nodePerturbation R w c Z := by
  simp only [nodeResidual, nodeScalar, nodeBaseline, nodeSelf, nodePerturbation,
    Localized.potential, Finset.sum_add_distrib]
  ring

theorem nodePorts_bounds (w : ℝ) (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) :
    nodePorts w c Z i ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Profiles.step_bounds ((‖parent F E Z i - c i‖ ^ 2 - w ^ 2) / (3 * w ^ 2))
  unfold nodePorts Localized.port
  constructor <;> linarith [h.1, h.2]

theorem nodePorts_contDiff {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (i : Fin 8) :
    ContDiff ℝ 3 (fun Z : Layer F E => nodePorts w c Z i) :=
  ((Localized.localized_contDiff hR hw (c i)).2.2).comp (parentAt F E i).contDiff
theorem nodeIncoming_contDiff {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (i : Fin 8) :
    ContDiff ℝ 3 (fun Z : Layer F E => nodeIncoming R w c Z i) :=
  ((Localized.localized_contDiff hR hw (c i)).2.1).comp (parentAt F E i).contDiff
theorem nodeSelf_contDiff {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) :
    ContDiff ℝ 3 (nodeSelf R w c : Layer F E → ℝ) := by
  apply ContDiff.sum
  intro i _
  exact ((Localized.localized_contDiff hR hw (c i)).1).comp (parentAt F E i).contDiff
theorem nodeBaseline_contDiff (Q : F → ℝ) {R : ℝ} (hR : 0 < R) (hQ : ContDiff ℝ 3 Q) :
    ContDiff ℝ 3 (nodeBaseline Q R : Layer F E → ℝ) := by
  apply (hQ.comp (lower F E).contDiff).add
  apply ContDiff.sum
  intro i _
  exact (Localized.publicPotential_contDiff hR 3).comp (parentAt F E i).contDiff

theorem nodePayload_contDiff (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (hQ : ContDiff ℝ 3 Q)
    (hf : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) (i : Fin 8) :
    ContDiff ℝ 3 (fun Z => nodePayload Q child childPort S R w c Z i) := by
  have hl : ContDiff ℝ 3 (lower F E) := (lower F E).contDiff
  exact ((((hf i).comp hl).sub (hQ.comp hl)).sub contDiff_const).sub
    ((nodeIncoming_contDiff hR hw c i).mul ((ho i).comp hl))

theorem nodeScalar_contDiff (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (hQ : ContDiff ℝ 3 Q)
    (hf : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) :
    ContDiff ℝ 3 (nodeScalar Q child childPort S R w c) := by
  apply ((hQ.comp (lower F E).contDiff).add ?_).add (nodeSelf_contDiff hR hw c)
  exact FirstHeightSelector.select_contDiff 8 _ _ _ (nodePorts_contDiff hR hw c)
    (nodePayload_contDiff Q child childPort S hR hw c hQ hf ho) contDiff_const

end GradientHessian.HigherHierarchy
