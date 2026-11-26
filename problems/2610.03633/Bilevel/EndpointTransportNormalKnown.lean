import Bilevel.EndpointTransportKnownSpace
import Bilevel.EndpointTransportHybridOperators
import Bilevel.ChiExtensionRestrictedInverse

/-! Heterogeneous known spaces for the actual lower variables: ordinary
blocks, separate physical layers, and all public normal coordinates. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiCarrier ChiExtension

def physicalTangentKnown {m n D : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D)) :
    Submodule ℝ (HybridTangent (Blocks m (Block D)) n D) :=
  jointKnown (knownSpace W) (knownSpace Z)

def physicalNormalKnown {m n D : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D)) (s : ℕ) :
    Submodule ℝ (HybridVariables (Blocks m (Block D)) (Normals s) n D) :=
  jointKnown (physicalTangentKnown W Z) ⊤

theorem mem_physicalTangentKnown {m n D : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    (z : HybridTangent (Blocks m (Block D)) n D) :
    z∈physicalTangentKnown W Z ↔ (∀ i,z.fst i∈W i) ∧ (∀ i,z.snd i∈Z i) := Iff.rfl

theorem mem_physicalNormalKnown {m n D s : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    (z : HybridVariables (Blocks m (Block D)) (Normals s) n D) :
    z∈physicalNormalKnown W Z s ↔ (∀ i,z.fst.fst i∈W i) ∧ (∀ i,z.fst.snd i∈Z i) := by
  change ((_ ∧ _) ∧ z.snd∈(⊤:Submodule ℝ (Normals s))) ↔ _
  simp only [Submodule.mem_top,and_true]
  rfl

theorem physicalTangentKnown_isClosed {m n D : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D)) :
    IsClosed (physicalTangentKnown W Z : Set (HybridTangent (Blocks m (Block D)) n D)) :=
  jointKnown_isClosed _ _ (knownSpace_isClosed W (fun i => (W i).closed_of_finiteDimensional))
    (knownSpace_isClosed Z (fun i => (Z i).closed_of_finiteDimensional))

theorem physicalNormalKnown_isClosed {m n D : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D)) (s : ℕ) :
    IsClosed (physicalNormalKnown W Z s : Set (HybridVariables (Blocks m (Block D)) (Normals s) n D)) :=
  jointKnown_isClosed _ _ (physicalTangentKnown_isClosed W Z) isClosed_univ

theorem gradient_physicalNormalKnown_iff {m n D s : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    {f : HybridVariables (Blocks m (Block D)) (Normals s) n D → ℝ}
    (z : HybridVariables (Blocks m (Block D)) (Normals s) n D)
    (hf : ContDiff ℝ 3 f) :
    gradient f z∈physicalNormalKnown W Z s ↔
      gradient (fun t => f (pack t z.snd)) z.fst∈physicalTangentKnown W Z := by
  rw [physicalNormalKnown,gradient_jointKnown_iff _ _ z (hf.differentiable (by norm_num) z)]
  simp only [Submodule.mem_top,and_true]

theorem gradient_physicalTangentKnown_iff {m n D : ℕ} (W : Fin m → Submodule ℝ (Block D))
    (Z : EndpointTransportMatrix.Index n → Submodule ℝ (Block D))
    {f : HybridTangent (Blocks m (Block D)) n D → ℝ}
    (z : HybridTangent (Blocks m (Block D)) n D) (hf : ContDiff ℝ 3 f) :
    gradient f z∈physicalTangentKnown W Z ↔
      gradient (fun u => f (pack u z.snd)) z.fst∈knownSpace W ∧
      gradient (fun Y => f (pack z.fst Y)) z.snd∈knownSpace Z :=
  gradient_jointKnown_iff _ _ z (hf.differentiable (by norm_num) z)

end Bilevel.EndpointTransportResponse
