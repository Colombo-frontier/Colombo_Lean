import Bilevel.EndpointTransportParentSupport
import Bilevel.EndpointTransportSelectedLedger
import Bilevel.ChiLiftedSupportAlgebra

/-! Actual selected nonterminal physical carriers. Before the last parent
the closed carrier is ordinary; at the last parent every physical release
is included. No prospective source endpoint column is required. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre

theorem physical_parent_selected_support {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (t j : ℕ) (I : List ℕ) (hm : j+t<m)
    (W : Fin m → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (x : HybridTangent (Blocks m (Block D)) n D) (r : ℕ → List ℕ → ℕ)
    (hancestor : ∀ k A,j≤k → ∀ hkt : k≤j+t,BlindNode W x.fst ⟨k,by omega⟩ (G k A) (r k A))
    (hh : ∀ A,0<(G (j+t+1) A).width) (hR : ∀ A,0<(G (j+t+1) A).radius)
    (hhp : ∀ A,0<(G (j+t+1) A).parentWidth)
    (hw : ∀ A,(G (j+t+1) A).width≤(G (j+t+1) A).parentWidth)
    (ht : ∀ A,∀ k : Fin ((G (j+t+1) A).n+1),k.val<r (j+t+1) A →
      Q (Fin.last (n+1)) ((G (j+t+1) A).frame (basis k))∈Z (Fin.last (n+1)))
    (hp : ∀ A,∀ k : Fin ((G (j+t+1) A).n+1),r (j+t+1) A≤k.val →
      (gamma n*(G (j+t+1) A).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G (j+t+1) A).frame (basis k)))‖≤(G (j+t+1) A).width/8)
    (hY : x.snd∈knownSpace Z)
    (hfuture : ∀ A,∀ i : Fin ((G (j+t) A).n+1),r (j+t) A≤ i.val →
      r (j+t+1) (child A i.val)≤(G (j+t+1) (child A i.val)).n) :
    gradient (physicalCarrier m Q G jointFstLinear jointSndLinear (t+1) j I t) x∈physicalTangentKnown W Z := by
  have he := physicalCarrier_selectFamily m Q G
    (jointFstLinear : HybridTangent (Blocks m (Block D)) n D →L[ℝ] Blocks m (Block D)) jointSndLinear 1 t j I
  rw [Nat.add_comm 1 t] at he
  rw [he]
  apply ChiLiftedCarrier.selectFamily_gradient_mem G jointFstLinear
    (fun k A => physicalCarrier (X:=HybridTangent (Blocks m (Block D)) n D) m Q G jointFstLinear jointSndLinear 1 k A 0)
    (fun k A => physicalCarrier_contDiff (X:=HybridTangent (Blocks m (Block D)) n D) m Q G jointFstLinear jointSndLinear 1 k A 0)
    t j I (physicalTangentKnown W Z) x
  · intro k A hk hkt i
    exact fst_composition_gradient_mem (knownSpace W) (knownSpace Z)
      (jointSelector_contDiff m k (G k A) i 3) x ((hancestor k A hk (by omega)).selector_mem i)
  · intro A
    have hleaf : physicalCarrier (X:=HybridTangent (Blocks m (Block D)) n D) m Q G jointFstLinear jointSndLinear 1 (j+t) A 0 =
        lastParentCarrier m (j+t) (G (j+t) A)
          (fun i => G (j+t+1) (child A i.val)) jointFstLinear jointSndLinear Q := by
      funext y
      simp only [physicalCarrier, if_pos rfl, if_true]
    rw [hleaf]
    exact lastParentCarrier_support hm Q (G (j+t) A) (fun i => G (j+t+1) (child A i.val)) W Z x
      (r (j+t) A) (hancestor (j+t) A (by omega) le_rfl) (fun i => r (j+t+1) (child A i.val))
      (fun i => hh _) (fun i => hR _) (fun i => hhp _) (fun i => hw _)
      (fun i => ht _) (fun i => hp _) hY (hfuture A)

theorem physical_ordinary_selected_support {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (d t j : ℕ) (I : List ℕ) (hm : j+t+1<m)
    (W : Fin m → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (x : HybridTangent (Blocks m (Block D)) n D) (r : ℕ → List ℕ → ℕ)
    (hancestor : ∀ k A,j≤k → ∀ hkt : k≤j+t+1,BlindNode W x.fst ⟨k,by omega⟩ (G k A) (r k A))
    (hhp : ∀ A,0<(G (j+t+1) A).parentWidth)
    (hw : ∀ A,(G (j+t+1) A).width≤(G (j+t+1) A).parentWidth)
    (hfuture : ∀ A,∀ i : Fin ((G (j+t) A).n+1),r (j+t) A≤ i.val →
      r (j+t+1) (child A i.val)≤(G (j+t+1) (child A i.val)).n) :
    gradient (physicalCarrier m Q G jointFstLinear jointSndLinear (d+2+t) j I t) x∈physicalTangentKnown W Z := by
  rw [physicalCarrier_selectFamily]
  apply ChiLiftedCarrier.selectFamily_gradient_mem G jointFstLinear
    (fun k A => physicalCarrier (X:=HybridTangent (Blocks m (Block D)) n D) m Q G jointFstLinear jointSndLinear (d+2) k A 0)
    (fun k A => physicalCarrier_contDiff (X:=HybridTangent (Blocks m (Block D)) n D) m Q G jointFstLinear jointSndLinear (d+2) k A 0)
    t j I (physicalTangentKnown W Z) x
  · intro k A hk hkt i
    exact fst_composition_gradient_mem (knownSpace W) (knownSpace Z)
      (jointSelector_contDiff m k (G k A) i 3) x ((hancestor k A hk (by omega)).selector_mem i)
  · intro A
    have he : physicalCarrier m Q G jointFstLinear jointSndLinear (d+2) (j+t) A 0=
        jointCarrier m G (d+2) (j+t) A 0 ∘
          (jointFstLinear : HybridTangent (Blocks m (Block D)) n D →L[ℝ] Blocks m (Block D)) := by
      funext y
      simp only [physicalCarrier,show ¬(d+1=0) by omega,if_false,Function.comp_apply]
    rw [he]
    apply fst_composition_gradient_mem (knownSpace W) (knownSpace Z) (jointCarrier_contDiff m G (d+2) (j+t) A 0 3) x
    exact jointClosed_gradient_mem G (d+1) (j+t) A hm W x.fst (r (j+t) A)
      (hancestor (j+t) A (by omega) (by omega)) (fun i => r (j+t+1) (child A i.val))
      (fun i => hancestor (j+t+1) (child A i.val) (by omega) le_rfl)
      (fun i => hhp _) (fun i => hw _) (hfuture A)

end Bilevel.EndpointTransportResponse


