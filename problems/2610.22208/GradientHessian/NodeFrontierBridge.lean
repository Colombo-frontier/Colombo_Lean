import GradientHessian.FiniteFrontierBridge

/-! The general finite frontier identities instantiated with the literal
localized and first-height nodes, on their actual physical Hilbert spaces. -/

noncomputable section
namespace GradientHessian.NodeFrontierBridge

open FiniteFrontierBridge SecondJetAlgebra JetLocality
open InnerCoordinates

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def higherFrontier (k : Fin 8) (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (S R w : ℝ) (c : Fin 8 → E) : HigherHierarchy.Layer F E → ℝ :=
  frontier k (Q ∘ HigherHierarchy.lower F E) S
    (fun i => child i ∘ HigherHierarchy.lower F E)
    (fun i => childPort i ∘ HigherHierarchy.lower F E)
    (fun i Z => Localized.potential R w (c i) (HigherHierarchy.parent F E Z i))
    (fun i Z => HigherHierarchy.nodeIncoming R w c Z i)
    (fun i Z => HigherHierarchy.nodePorts w c Z i)

def higherWithoutIncoming (k : Fin 8) (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (S R w : ℝ) (c : Fin 8 → E) : HigherHierarchy.Layer F E → ℝ :=
  withoutIncoming k (Q ∘ HigherHierarchy.lower F E) S
    (fun i => child i ∘ HigherHierarchy.lower F E)
    (fun i => childPort i ∘ HigherHierarchy.lower F E)
    (fun i Z => Localized.potential R w (c i) (HigherHierarchy.parent F E Z i))
    (fun i Z => HigherHierarchy.nodeIncoming R w c Z i)
    (fun i Z => HigherHierarchy.nodePorts w c Z i)

theorem higher_node_eq (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (S R w : ℝ) (c : Fin 8 → E) :
    HigherHierarchy.nodeScalar Q child childPort S R w c =
      node (Q ∘ HigherHierarchy.lower F E) S
        (fun i => child i ∘ HigherHierarchy.lower F E)
        (fun i => childPort i ∘ HigherHierarchy.lower F E)
        (fun i Z => Localized.potential R w (c i) (HigherHierarchy.parent F E Z i))
        (fun i Z => HigherHierarchy.nodeIncoming R w c Z i)
        (fun i Z => HigherHierarchy.nodePorts w c Z i) := by
  funext Z
  rw [HigherHierarchy.nodeScalar_eq_source]
  rfl

theorem higher_frontier_richJet (k : Fin 8) (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (S : ℝ) {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E)
    (hQ : ContDiff ℝ 3 Q) (hf : ∀ i,ContDiff ℝ 3 (child i))
    (ho : ∀ i,ContDiff ℝ 3 (childPort i)) (Z : HigherHierarchy.Layer F E)
    (hz : ZeroSecondJet (fun V => HigherHierarchy.nodePorts w c V k) Z) :
    richJet (HigherHierarchy.nodeScalar Q child childPort S R w c) Z =
      richJet (higherFrontier k Q child childPort S R w c) Z := by
  rw [higher_node_eq]
  exact node_frontier_richJet k _ S _ _ _ _ _ Z
    ((hQ.comp (HigherHierarchy.lower F E).contDiff).of_le (by decide))
    (fun i => ((hf i).comp (HigherHierarchy.lower F E).contDiff).of_le (by decide))
    (fun i => ((ho i).comp (HigherHierarchy.lower F E).contDiff).of_le (by decide))
    (fun i => (((Localized.localized_contDiff hR hw (c i)).1).comp
      (HigherHierarchy.parentAt F E i).contDiff).of_le (by decide))
    (fun i => (HigherHierarchy.nodeIncoming_contDiff hR hw c i).of_le (by decide))
    (fun i => (HigherHierarchy.nodePorts_contDiff hR hw c i).of_le (by decide)) hz

theorem higher_withoutIncoming_richJet (k : Fin 8) (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    (S : ℝ) {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E)
    (hQ : ContDiff ℝ 3 Q) (hf : ∀ i,ContDiff ℝ 3 (child i))
    (ho : ∀ i,ContDiff ℝ 3 (childPort i)) (Z : HigherHierarchy.Layer F E)
    (hz : ZeroSecondJet (fun V => HigherHierarchy.nodePorts w c V k) Z)
    (hzChild : ZeroSecondJet (childPort k) (HigherHierarchy.lower F E Z)) :
    richJet (HigherHierarchy.nodeScalar Q child childPort S R w c) Z =
      richJet (higherWithoutIncoming k Q child childPort S R w c) Z := by
  rw [higher_node_eq]
  exact node_withoutIncoming_richJet k _ S _ _ _ _ _ Z
    ((hQ.comp (HigherHierarchy.lower F E).contDiff).of_le (by decide))
    (fun i => ((hf i).comp (HigherHierarchy.lower F E).contDiff).of_le (by decide))
    (fun i => ((ho i).comp (HigherHierarchy.lower F E).contDiff).of_le (by decide))
    (fun i => (((Localized.localized_contDiff hR hw (c i)).1).comp
      (HigherHierarchy.parentAt F E i).contDiff).of_le (by decide))
    (fun i => (HigherHierarchy.nodeIncoming_contDiff hR hw c i).of_le (by decide))
    (fun i => (HigherHierarchy.nodePorts_contDiff hR hw c i).of_le (by decide)) hz
    (hzChild.comp_linear ((ho k).of_le (by decide)) (HigherHierarchy.lower F E))

variable {b depth : ℕ}

def firstFrontier (j : Fin b) (Q : F → ℝ) (child childPort : Fin b → F → ℝ)
    (S : ℝ) (v : Fin b → Fin (depth+2) → E) : FirstHeight.Space F E b depth → ℝ :=
  frontier j (Q ∘ numerical F E b (depth+2)) S
    (fun i => child i ∘ numerical F E b (depth+2))
    (fun i => childPort i ∘ numerical F E b (depth+2))
    (fun i Z => Inner.block (v i) (tasks F E b (depth+2) Z i))
    (fun i Z => Inner.input (v i) (tasks F E b (depth+2) Z i))
    (fun i Z => Inner.ports v Z i)

def firstWithoutIncoming (j : Fin b) (Q : F → ℝ) (child childPort : Fin b → F → ℝ)
    (S : ℝ) (v : Fin b → Fin (depth+2) → E) : FirstHeight.Space F E b depth → ℝ :=
  withoutIncoming j (Q ∘ numerical F E b (depth+2)) S
    (fun i => child i ∘ numerical F E b (depth+2))
    (fun i => childPort i ∘ numerical F E b (depth+2))
    (fun i Z => Inner.block (v i) (tasks F E b (depth+2) Z i))
    (fun i Z => Inner.input (v i) (tasks F E b (depth+2) Z i))
    (fun i Z => Inner.ports v Z i)

theorem first_node_eq (Q : F → ℝ) (child childPort : Fin b → F → ℝ)
    (S : ℝ) (v : Fin b → Fin (depth+2) → E) :
    FirstHeight.node Q child childPort S v =
      node (Q ∘ numerical F E b (depth+2)) S
        (fun i => child i ∘ numerical F E b (depth+2))
        (fun i => childPort i ∘ numerical F E b (depth+2))
        (fun i Z => Inner.block (v i) (tasks F E b (depth+2) Z i))
        (fun i Z => Inner.input (v i) (tasks F E b (depth+2) Z i))
        (fun i Z => Inner.ports v Z i) := by
  funext Z
  rw [FirstHeight.node_eq_source]
  rfl

theorem first_frontier_richJet (j : Fin b) (Q : F → ℝ) (child childPort : Fin b → F → ℝ)
    (S : ℝ) (v : Fin b → Fin (depth+2) → E)
    (hQ : ContDiff ℝ 3 Q) (hf : ∀ i,ContDiff ℝ 3 (child i))
    (ho : ∀ i,ContDiff ℝ 3 (childPort i)) (Z : FirstHeight.Space F E b depth)
    (hz : ZeroSecondJet (fun V => Inner.ports v V j) Z) :
    richJet (FirstHeight.node Q child childPort S v) Z =
      richJet (firstFrontier j Q child childPort S v) Z := by
  rw [first_node_eq]
  exact node_frontier_richJet j _ S _ _ _ _ _ Z
    ((hQ.comp (numerical F E b (depth+2)).contDiff).of_le (by decide))
    (fun i => ((hf i).comp (numerical F E b (depth+2)).contDiff).of_le (by decide))
    (fun i => ((ho i).comp (numerical F E b (depth+2)).contDiff).of_le (by decide))
    (fun i => ((Inner.block_contDiff (v i)).comp (Inner.taskProjection (Y := F) (E := E) b depth i).contDiff).of_le (by decide))
    (fun i => ((Inner.input_contDiff (v i)).comp (Inner.taskProjection (Y := F) (E := E) b depth i).contDiff).of_le (by decide))
    (fun i => (Inner.ports_contDiff v i).of_le (by decide)) hz

theorem first_withoutIncoming_richJet (j : Fin b) (Q : F → ℝ) (child childPort : Fin b → F → ℝ)
    (S : ℝ) (v : Fin b → Fin (depth+2) → E)
    (hQ : ContDiff ℝ 3 Q) (hf : ∀ i,ContDiff ℝ 3 (child i))
    (ho : ∀ i,ContDiff ℝ 3 (childPort i)) (Z : FirstHeight.Space F E b depth)
    (hz : ZeroSecondJet (fun V => Inner.ports v V j) Z)
    (hzChild : ZeroSecondJet (childPort j) (numerical F E b (depth+2) Z)) :
    richJet (FirstHeight.node Q child childPort S v) Z =
      richJet (firstWithoutIncoming j Q child childPort S v) Z := by
  rw [first_node_eq]
  exact node_withoutIncoming_richJet j _ S _ _ _ _ _ Z
    ((hQ.comp (numerical F E b (depth+2)).contDiff).of_le (by decide))
    (fun i => ((hf i).comp (numerical F E b (depth+2)).contDiff).of_le (by decide))
    (fun i => ((ho i).comp (numerical F E b (depth+2)).contDiff).of_le (by decide))
    (fun i => ((Inner.block_contDiff (v i)).comp (Inner.taskProjection (Y := F) (E := E) b depth i).contDiff).of_le (by decide))
    (fun i => ((Inner.input_contDiff (v i)).comp (Inner.taskProjection (Y := F) (E := E) b depth i).contDiff).of_le (by decide))
    (fun i => (Inner.ports_contDiff v i).of_le (by decide)) hz
    (hzChild.comp_linear ((ho j).of_le (by decide)) (numerical F E b (depth+2)))

end GradientHessian.NodeFrontierBridge
