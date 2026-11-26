import Bilevel.TransportRoundPrefix

/-! The three source phases are kept distinct: query-augmented frozen input,
post-one-hop output before next-source disclosure, and the next round state.
The edge-local old protected union differs across an edge by at most one
column. Global post-one-hop future sets are subsets of its complement. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction

def PostProtected {n T : ℕ} (t : ℕ) (v : Vertex n) (i : Fin T) : Prop :=
  Protected (t+1) v i ∧ i.val*n≤t

theorem frozen_prefix {n D m p : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (q : Queries n D p) (z : Latent n D)
    (hg : ∀ v i, Protected t v i → frame T hT z v i∈known g v) :
    ∀ v i, Protected t v i → frame T hT z v i∈known (augment g q) v := by
  intro v i hi
  rw [augment_span]
  exact (show known g v≤_ from le_sup_left) (hg v i hi)

theorem postBatch_prefix {n D m p : ℕ} (T : ℕ) (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (q : Queries n D p) (z : Latent n D)
    (hg : ∀ v i, Protected t v i → frame T hT z v i∈known g v) :
    ∀ v i, PostProtected t v i → frame T hT z v i∈known (execute (augment g q) z) v := by
  intro v i hi
  cases v using Fin.cases with
  | zero =>
    apply keeps_old (augment g q) z 0
    exact frozen_prefix T hT t g q z hg 0 i hi.2
  | succ v =>
    have hp : Protected t (src v) i := by
      have hh := hi.1
      dsimp [Protected,src] at hh ⊢
      omega
    have hmem := frozen_prefix T hT t g q z hg (src v) i hp
    have hh := forward_whole_space (augment g q) z v
      (show z.2 v • frame T hT z (src v) i ∈
        (known (augment g q) (src v)).map (isometry D (z.2 v)).toLinearEquiv.toLinearMap from
        ⟨frame T hT z (src v) i,hmem,rfl⟩)
    simpa only [edge_frame] using hh

theorem protected_downward {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T) :
    Protected t (dst e) i → Protected t (src e) i := by
  dsimp [Protected,src,dst]
  omega

theorem edge_crossing_iff {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T) :
    Protected t (src e) i ∧ ¬Protected t (dst e) i ↔ i.val*n+e.val=t := by
  dsimp [Protected,src,dst]
  omega

theorem edge_crossing_unique {n T : ℕ} (hn : 0<n) (t : ℕ) (e : Edge n) (i j : Fin T)
    (hi : Protected t (src e) i ∧ ¬Protected t (dst e) i)
    (hj : Protected t (src e) j ∧ ¬Protected t (dst e) j) : i=j := by
  have h1 := (edge_crossing_iff t e i).mp hi
  have h2 := (edge_crossing_iff t e j).mp hj
  apply Fin.ext
  nlinarith

theorem paired_src_post {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T)
    (hi : Protected t (src e) i) : PostProtected t (src e) i := by
  dsimp [PostProtected,Protected,src] at hi ⊢
  constructor <;> omega

theorem paired_dst_post {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T)
    (hi : Protected t (src e) i) : PostProtected t (dst e) i := by
  dsimp [PostProtected,Protected,src,dst] at hi ⊢
  constructor <;> omega

theorem global_future_src {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T)
    (hi : ¬PostProtected t (src e) i) : ¬Protected t (src e) i :=
  fun h => hi (paired_src_post t e i h)

theorem global_future_dst {n T : ℕ} (t : ℕ) (e : Edge n) (i : Fin T)
    (hi : ¬PostProtected t (dst e) i) : ¬Protected t (src e) i :=
  fun h => hi (paired_dst_post t e i h)

theorem new_source_only_after_completion {n T : ℕ} (hn : 0<n) (t : ℕ) (i : Fin T)
    (hi : Protected (t+1) (0 : Vertex n) i) (hold : ¬PostProtected t (0 : Vertex n) i) :
    i.val*n=t+1 ∧ (t+1)%n=0 ∧ i.val=(t+1)/n := by
  have he : i.val*n=t+1 := by
    have hnot : ¬i.val*n≤t := fun h => hold ⟨hi,h⟩
    dsimp [Protected] at hi
    omega
  refine ⟨he,?_,?_⟩
  · rw [← he]; simp
  · rw [← he,Nat.mul_div_left _ hn]

end Bilevel.TransportRound
