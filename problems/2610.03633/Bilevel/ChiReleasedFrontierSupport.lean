import Bilevel.ChiFrontierAdvance
import Bilevel.ChiOuterFrontierSupport
import Bilevel.ChiVirtualOuterFineValues

/-! The actual paired-prefix advance implies the support certificate used
by the nonlinear inverse. It consumes only the newly disclosed terminal
prefix, and only macro branches reachable from the old prefix. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiPrefixEvaluation
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem FrontierAdvance.frontierKnown {D : Geometry F} {old new : ℕ → List ℕ → ℕ}
    {d j : ℕ} {I : List ℕ} (V : Submodule ℝ F) (h : FrontierAdvance D old new d j I)
    (hcols : ∀ P,∀ k : Fin ((D (j+d) P).n+1),k.val<new (j+d) P →
      (D (j+d) P).frame (basis k)∈V) : FrontierKnown D old V d j I := by
  induction d generalizing j I with
  | zero =>
    intro k hk
    change (D j I).n<old j I ∨ old j I<new j I at h
    rcases h with h|h
    · have hlt := k.isLt
      omega
    · exact hcols I k (by simpa only [Nat.add_zero] using (show k.val<new j I by omega))
  | succ d ih =>
    intro i hi
    apply ih (h i hi)
    convert hcols using 1
    rw [show j+1+d=j+(d+1) by omega]

omit [CompleteSpace F] in
theorem outerValueStage_le_prefix (M : Node E) (x : E) (rM : ℕ) (hmw : 0<M.width)
    (hblind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x k|≤M.width/8) :
    (outerValueStage M x).val≤rM := by
  classical
  unfold outerValueStage
  split_ifs with h
  · by_contra hn
    have hz : wrappedSelector M (Classical.choose h) x=0 := by
      apply outer_selector_future_zero M.n rM _ _ _ (by omega)
      intro k hk
      apply ZeroChainResidualScaled.scaled_coordinate_small M.width hmw (M.coordinates x) k
      have hh := hblind k hk
      linarith
    exact Classical.choose_spec h hz
  · exact Nat.zero_le _

omit [CompleteSpace F] in
theorem released_frontierKnown (M : Node E) (D : Geometry F) (J : ℕ)
    (old new : ℕ → List ℕ → ℕ) (V : Submodule ℝ F) (rM : ℕ) (x : E)
    (hmw : 0<M.width)
    (hblind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x k|≤M.width/8)
    (hadvance : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance D old new J 0 [i.val])
    (hcols : ∀ P,∀ k : Fin ((D J P).n+1),k.val<new J P → (D J P).frame (basis k)∈V) :
    FrontierKnown D old V J 0 [(outerValueStage M x).val] := by
  apply (hadvance (outerValueStage M x) (outerValueStage_le_prefix M x rM hmw hblind)).frontierKnown V
  convert hcols using 1
  rw [Nat.zero_add]

end Bilevel.ChiTreeProgress
