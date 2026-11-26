import Bilevel.EndpointTransportDeepestSupport
import Bilevel.EndpointTransportNonterminalSupport

/-! Every actual physical coarse carrier has old-prefix support. The
proof distinguishes ordinary closed carriers, the last physical parent,
and the deepest centered payload, without assuming their gradients. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre

theorem physicalCoarseCarrier_support {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (P : ChiFine.Parameters) (J t : ℕ) (I : List ℕ) (hm : J≤m) (ht : t≤J)
    (W : Fin m → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (x : HybridTangent (Blocks m (Block D)) n D) (r : ℕ → List ℕ → ℕ)
    (hancestor : ∀ k A,∀ hk : k<J,BlindNode W x.fst ⟨k,by omega⟩ (G k A) (r k A))
    (hh : ∀ A,0<(G J A).width) (hR : ∀ A,0<(G J A).radius)
    (hhp : ∀ k A,k≤J → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤J → (G k A).width≤(G k A).parentWidth)
    (hℓ : ∀ A,P.ℓ=(G J A).ell) (hβ : ∀ A,P.β=(G J A).width)
    (hs : ∀ A,∀ k : Fin ((G J A).n+1),k.val<r J A → Q 0 ((G J A).frame (basis k))∈Z 0)
    (htarget : ∀ A,∀ k : Fin ((G J A).n+1),k.val<r J A →
      Q (Fin.last (n+1)) ((G J A).frame (basis k))∈Z (Fin.last (n+1)))
    (hp : ∀ A,∀ k : Fin ((G J A).n+1),r J A≤k.val →
      (gamma n*(G J A).radius)*‖(Z (Fin.last (n+1))).orthogonalProjection
        (Q (Fin.last (n+1)) ((G J A).frame (basis k)))‖≤(G J A).width/8)
    (hY : x.snd∈knownSpace Z)
    (hfuture : ∀ k,k<J → ∀ A,∀ i : Fin ((G k A).n+1),r k A≤ i.val →
      r (k+1) (child A i.val)≤(G (k+1) (child A i.val)).n) :
    gradient (physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P J 0 I t) x∈physicalTangentKnown W Z := by
  by_cases he : t=J
  · subst t
    exact physical_deepest_support Q G P J 0 I (by omega) W Z x r
      (fun k A _ hk => hancestor k A (by omega))
      (by rw [Nat.zero_add]; exact hh) (by rw [Nat.zero_add]; exact hR)
      (by rw [Nat.zero_add]; exact hℓ) (by rw [Nat.zero_add]; exact hβ)
      (by rw [Nat.zero_add]; exact hs) (by rw [Nat.zero_add]; exact htarget)
      (by rw [Nat.zero_add]; exact hp) hY
  · have hfun : physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P J 0 I t=
        physicalCarrier (X:=HybridTangent (Blocks m (Block D)) n D) m Q G jointFstLinear jointSndLinear J 0 I t := by
      funext y
      simp only [physicalCoarseCarrier,if_neg he,sub_zero]
    rw [hfun]
    by_cases hlast : J=t+1
    · subst J
      exact physical_parent_selected_support Q G t 0 I (by omega) W Z x r
        (fun k A _ hk => hancestor k A (by omega))
        (by rw [Nat.zero_add]; exact hh) (by rw [Nat.zero_add]; exact hR)
        (by rw [Nat.zero_add]; exact hhp (t+1) · le_rfl)
        (by rw [Nat.zero_add]; exact hw (t+1) · le_rfl)
        (by rw [Nat.zero_add]; exact htarget) (by rw [Nat.zero_add]; exact hp)
        hY (by rw [Nat.zero_add]; exact hfuture t (by omega))
    · have hgap : t+2≤J := by omega
      have hj : J=J-(t+2)+2+t := by omega
      rw [hj]
      exact physical_ordinary_selected_support Q G (J-(t+2)) t 0 I (by omega) W Z x r
        (fun k A _ hk => hancestor k A (by omega))
        (fun A => by rw [Nat.zero_add]; exact hhp (t+1) A (by omega))
        (fun A => by rw [Nat.zero_add]; exact hw (t+1) A (by omega))
        (by rw [Nat.zero_add]; exact hfuture t (by omega))

end Bilevel.EndpointTransportResponse


