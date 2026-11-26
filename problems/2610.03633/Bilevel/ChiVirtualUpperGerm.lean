import Bilevel.ChiVirtualUpperValues
import Bilevel.ChiUniformBlindNeighborhood
import Bilevel.ChiUpperRegularity

/-! Exact full upper-oracle gradient from OLD disclosed columns. The proof
uses an actual common scalar germ, including all macro derivatives. -/
noncomputable section
open scoped Topology RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem actual_upperBase_eventuallyEq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (J : ℕ) (hJ : 0<J) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
    (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
    (hhp : ∀ j I,j≤1 → 0<(D j I).parentWidth)
    (hw : ∀ j I,j≤1 → (D j I).width≤(D j I).parentWidth)
    (hmfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(D 0 [i.val]).n)
    (hfuture : ∀ I,∀ i : Fin ((D 0 I).n+1),r 0 I≤ i.val →
      r 1 (child I i.val)≤(D 1 (child I i.val)).n)
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤3*M.width/16)
    (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
      |(D j I).coordinates (block m j z.snd) k|≤3*(D j I).width/16)
    (hmR : 0<M.radius) (hDR : ∀ j I,j≤J → 0<(D j I).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδD : ∀ j I,j≤J → δ≤(D j I).width/16) :
    upperBase m M ν D J ρ R =ᶠ[𝓝 z]
      virtualUpperBase m M ν D J ρ R rM r macroColumns columns := by
  have hm := eventually_blind_uniform (fun _ : Unit => M) (fun _ => hmR)
    (fun _ => outerProjection (E:=E) (F:=F) m) (fun _ => outerProjection_norm_le m)
    (fun _ => rM) (fun _ => M.width/4) δ hδ z (by
      intro _ k hk
      change |M.coordinates z.fst k|≤M.width/4-δ
      have hb := hmBlind k hk
      linarith)
  have hn := eventually_blind_uniform
    (fun i : Fin (J+1) × List ℕ => D i.1.val i.2)
    (fun i => hDR _ _ (by have := i.1.isLt;omega))
    (fun i => hierarchyBlock (E:=E) (F:=F) m i.1.val) (fun i => hierarchyBlock_norm_le m i.1.val)
    (fun i => r i.1.val i.2) (fun i => (D i.1.val i.2).width/4) δ hδ z (by
      intro i k hk
      change |(D i.1.val i.2).coordinates (block m i.1.val z.snd) k|≤(D i.1.val i.2).width/4-δ
      have hi : i.1.val≤J := by have := i.1.isLt;omega
      have hb := hblind i.1.val i.2 hi k hk
      have hd := hδD i.1.val i.2 hi
      linarith)
  filter_upwards [hm,hn] with y hym hyn
  exact actual_upperBase_eq_virtual m M ν D J hJ ρ R rM r macroColumns columns hmPrefix hprefix
    hmw hh hhp hw hmfuture hfuture y (hym ()) (fun j I hj k hk => hyn (⟨j,by omega⟩,I) k hk)

theorem fullUpper_gradient_eq_of_base_germ {X U V : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {f g : Joint X U → ℝ} (b : V) (q : PartialLegendre.FullNormalVariables X U V)
    (he : f =ᶠ[𝓝 (ChiUpper.baseProjection q)] g) :
    gradient (ChiUpper.fullUpper f b) q=gradient (ChiUpper.fullUpper g b) q := by
  have hp : (fun y => f (ChiUpper.baseProjection y)) =ᶠ[𝓝 q]
      (fun y => g (ChiUpper.baseProjection y)) :=
    he.comp_tendsto (ChiUpper.baseProjection (X:=X) (U:=U) (V:=V)).continuous.continuousAt
  have hh : ChiUpper.fullUpper f b =ᶠ[𝓝 q] ChiUpper.fullUpper g b := by
    filter_upwards [hp] with y hy
    exact congrArg (fun t => t+⟪b,y.snd.snd⟫) hy
  exact hh.gradient_eq

end Bilevel.ChiPrefixEvaluation
