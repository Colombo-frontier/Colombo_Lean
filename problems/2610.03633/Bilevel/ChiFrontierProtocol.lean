import Bilevel.ChiCarrierPathLocality

/-! Finite prefix-tree bookkeeping for one unfinished frontier. Earlier
children may be completed; no columns are requested from future children.
This is a deterministic protocol certificate, separate from the observer. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def CompletedLeaves (D : Geometry E) (r : ℕ → List ℕ → ℕ) : ℕ → ℕ → List ℕ → Prop
  | 0,j,I => (D j I).n<r j I
  | d+1,j,I => ∀ i : Fin ((D j I).n+1),CompletedLeaves D r d (j+1) (child I i.val)

def FrontierKnown (D : Geometry E) (r : ℕ → List ℕ → ℕ) (V : Submodule ℝ E) : ℕ → ℕ → List ℕ → Prop
  | 0,j,I => ∀ k : Fin ((D j I).n+1),k.val=r j I → (D j I).frame (basis k)∈V
  | d+1,j,I => ∀ i : Fin ((D j I).n+1),i.val≤r j I → FrontierKnown D r V d (j+1) (child I i.val)

omit [CompleteSpace E] in
theorem CompletedLeaves.frontierKnown {D : Geometry E} {r : ℕ → List ℕ → ℕ}
    (V : Submodule ℝ E) {d j : ℕ} {I : List ℕ} (h : CompletedLeaves D r d j I) :
    FrontierKnown D r V d j I := by
  induction d generalizing j I with
  | zero =>
    intro k hk
    have hi := k.isLt
    change (D j I).n<r j I at h
    omega
  | succ d ih =>
    intro i _
    exact ih (h i)

omit [CompleteSpace E] in
theorem frontierKnown_of_completed_children (D : Geometry E) (r : ℕ → List ℕ → ℕ)
    (V : Submodule ℝ E) (d j : ℕ) (I : List ℕ)
    (hold : ∀ i : Fin ((D j I).n+1),i.val<r j I → CompletedLeaves D r d (j+1) (child I i.val))
    (hcurrent : ∀ i : Fin ((D j I).n+1),i.val=r j I → FrontierKnown D r V d (j+1) (child I i.val)) :
    FrontierKnown D r V (d+1) j I := by
  intro i hi
  rcases lt_or_eq_of_le hi with hi|hi
  · exact (hold i hi).frontierKnown V
  · exact hcurrent i hi

theorem selector_future_zero {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤1/4) (i : Fin (n+1)) (hi : r < i.val) :
    ChiBoundedChain.selector n i z=0 := by
  revert hi
  refine Fin.cases (by intro h;change r<0 at h;omega) (fun k => ?_) i
  intro hk
  have hs := hz k.castSucc (by simpa using Nat.le_of_lt_succ hk)
  simp only [ChiBoundedChain.selector,Fin.cases_succ,evenGate_zero (by linarith : |z k.castSucc|≤1/2),zero_mul]

theorem BlindNode.selector_future_zero {m : ℕ} {W : Fin m → Submodule ℝ E} {x : Blocks m E}
    {j : Fin m} {D : Node E} {r : ℕ} (h : BlindNode W x j D r)
    (i : Fin (D.n+1)) (hi : r < i.val) : jointSelector m j.val D i x=0 := by
  apply ChiCarrier.selector_future_zero r _ _ i hi
  intro k hk
  simpa only [block,dif_pos j.isLt,PiLp.proj_apply] using
    ZeroChainResidualScaled.scaled_coordinate_small D.width h.width_pos (D.coordinates (x j)) k (h.blind k hk)

end Bilevel.ChiCarrier
