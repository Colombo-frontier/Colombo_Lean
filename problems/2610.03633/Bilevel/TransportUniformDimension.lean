import Bilevel.TransportAugmentedDimension

/-! One fixed public dimension works for every truncation cap in a fixed
finite range. Neither the algorithm nor its random seed enters the choice. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.TransportAugmented
set_option autoImplicit false

def ObserverBudget (n p Tnet k T B D N : ℕ) (networkCap cap δ : ℝ) : Prop :=
  ∃ r : ℕ, ∃ e : ℝ,
    TransportRound.observerDimension n p Tnet (N+1) networkCap (δ/2)≤D ∧
    (2*(N*B)+1)+(N*B)+(r+1)≤D ∧ 0<r ∧ 0<e ∧ e≤2 ∧
    ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*e)≤1/2 ∧
    2*((2*(N*B)+1:ℕ):ℝ)*e≤cap ∧
    ENNReal.ofReal (δ/2)+(k:ℝ≥0∞)*
      (((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e)≤ENNReal.ofReal δ

theorem ObserverBudget.dimension_mono {n p Tnet k T B D D' N : ℕ}
    {networkCap cap δ : ℝ} (hD : D≤D')
    (h : ObserverBudget n p Tnet k T B D N networkCap cap δ) :
    ObserverBudget n p Tnet k T B D' N networkCap cap δ := by
  rcases h with ⟨r,e,hn,ha,hr,he,he2,hs,hc,hp⟩
  exact ⟨r,e,hn.trans hD,ha.trans hD,hr,he,he2,hs,hc,hp⟩

theorem exists_uniform_joint_dimension (D₀ n p Tnet k T H B : ℕ) (networkCap cap δ : ℝ)
    (hk : 0<k) (hc : 0<cap) (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ D : ℕ,D₀≤D ∧ Tnet≤D ∧ T+1≤D ∧
      ∀ N : ℕ,N≤H → ObserverBudget n p Tnet k T B D N networkCap cap δ := by
  classical
  have hone (N : ℕ) : ∃ D : ℕ,D₀≤D ∧ Tnet≤D ∧ T+1≤D ∧
      ObserverBudget n p Tnet k T B D N networkCap cap δ := by
    cases k with
    | zero => omega
    | succ j =>
      obtain ⟨D,r,e,hD,hnet,hT,hn,ha,hr,he,he2,hs,hc',hp⟩ :=
        exists_joint_dimension D₀ n p Tnet j T N B networkCap cap δ hc hδ hδ1
      exact ⟨D,hD,hnet,hT,r,e,hn,ha,hr,he,he2,hs,hc',hp.le⟩
  choose dims hdims using hone
  let D := Finset.univ.sup (fun i : Fin (H+1) => dims i.val)
  have hle (N : ℕ) (hN : N≤H) : dims N≤D :=
    Finset.le_sup (f:=fun i : Fin (H+1) => dims i.val) (Finset.mem_univ ⟨N,by omega⟩)
  refine ⟨D,(hdims 0).1.trans (hle 0 (Nat.zero_le H)),
    (hdims 0).2.1.trans (hle 0 (Nat.zero_le H)),
    (hdims 0).2.2.1.trans (hle 0 (Nat.zero_le H)),?_⟩
  intro N hN
  exact (hdims N).2.2.2.dimension_mono (hle N hN)

end Bilevel.TransportAugmented
