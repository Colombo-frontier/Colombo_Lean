import Bilevel.ChiHierarchyInactiveLocality
import Bilevel.NearIdentityConfinement

/-! Actual column-projection geometry implies blind coordinates at every
restricted point, without any displacement or hidden-force assumption.
This is the inactive inverse mechanism in both the rec and waI branches. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiRecursive.Node
open ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinate_eq_inner (D : Node E) (u : E) (k : Fin (D.n+1)) :
    D.coordinates u k=⟪D.frame (basis k),RadialWrapper.compress D.radius u⟫ := by
  have hh := D.frame.toContinuousLinearMap.adjoint_inner_right (basis k)
    (RadialWrapper.compress D.radius u)
  simpa only [basis,EuclideanSpace.inner_single_left,one_mul,conj_trivial] using hh

theorem coordinate_projection_bound (D : Node E) (hR : 0<D.radius)
    (W : Submodule ℝ E) [CompleteSpace W] (u : W) (k : Fin (D.n+1)) :
    |D.coordinates (u:E) k|≤D.radius*‖W.orthogonalProjection (D.frame (basis k))‖ := by
  rw [D.coordinate_eq_inner]
  exact NearIdentityConfinement.undisclosed_readout_bound W D.radius hR (D.frame (basis k)) u le_rfl

end Bilevel.ChiRecursive.Node

namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Point-independent geometric information about one actual node. -/
structure ProjectedBlindNode {m : ℕ} (W : Fin m → Submodule ℝ E) (j : Fin m)
    [CompleteSpace (W j)] (D : Node E) (r : ℕ) : Prop where
  width_pos : 0<D.width
  radius_pos : 0<D.radius
  columns_mem : ∀ k : Fin (D.n+1),k.val < r → D.frame (basis k)∈W j
  blind_projection : ∀ k : Fin (D.n+1),r ≤ k.val →
    D.radius*‖(W j).orthogonalProjection (D.frame (basis k))‖≤D.width/4

theorem ProjectedBlindNode.at_point {m : ℕ} {W : Fin m → Submodule ℝ E} {j : Fin m}
    [CompleteSpace (W j)] {D : Node E} {r : ℕ} (h : ProjectedBlindNode W j D r)
    (x : Blocks m E) (hx : x j∈W j) : BlindNode W x j D r := by
  refine ⟨h.width_pos,h.radius_pos,hx,h.columns_mem,?_⟩
  intro k hk
  exact (D.coordinate_projection_bound h.radius_pos (W j) ⟨x j,hx⟩ k).trans (h.blind_projection k hk)

def TreeProjection {m : ℕ} (D : Geometry E) (j d : ℕ) (hm : j+d < m)
    (W : Fin m → Submodule ℝ E) [∀ i,CompleteSpace (W i)] (r : ℕ → List ℕ → ℕ) : Prop :=
  ∀ k P (_hk : j ≤ k) (hkt : k ≤ j+d),ProjectedBlindNode W ⟨k,by omega⟩ (D k P) (r k P)

theorem TreeProjection.at_point {m : ℕ} {D : Geometry E} {j d : ℕ} {hm : j+d < m}
    {W : Fin m → Submodule ℝ E} [∀ i,CompleteSpace (W i)] {r : ℕ → List ℕ → ℕ}
    (h : TreeProjection D j d hm W r) (x : Blocks m E) (hx : x∈knownSpace W) :
    TreeBlind D j d hm W x r :=
  fun k P hk hkt => (h k P hk hkt).at_point x (hx _)

theorem inactive_tail_of_projection {m : ℕ} (D : Geometry E) (t : Fin m)
    (W : Fin m → Submodule ℝ E) [CompleteSpace (W t)] (r : List ℕ → ℕ) (τ : ℝ)
    (hR : ∀ P,0<(D t.val P).radius)
    (hp : ∀ P,∀ k : Fin ((D t.val P).n+1),r P ≤ k.val →
      (D t.val P).radius*‖(W t).orthogonalProjection ((D t.val P).frame (basis k))‖≤τ)
    (x : Blocks m E) (hx : x t∈W t) :
    ∀ P,∀ k : Fin ((D t.val P).n+1),r P ≤ k.val → |(D t.val P).coordinates (x t) k|≤τ := by
  intro P k hk
  exact ((D t.val P).coordinate_projection_bound (hR P) (W t) ⟨x t,hx⟩ k).trans (hp P k hk)

end Bilevel.ChiCarrier
