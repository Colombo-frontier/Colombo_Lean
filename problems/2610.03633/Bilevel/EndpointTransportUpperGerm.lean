import Bilevel.EndpointTransportUpperPrefix
import Bilevel.EndpointTransportVirtualNeighborhood
import Bilevel.ChiVirtualUpperGerm
import Bilevel.EndpointTransportUpperReadout

/-! A full ambient old-prefix germ for the actual physical upper objective.
This includes the first physical target release and all macro derivatives. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped Topology RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physicalUpperBase_eventuallyEq_prefix {n D : ℕ} (Q : Rotations n D) (M : Node E)
    (ν : ℝ) (G : Geometry (Block D)) (J : ℕ) (hJ : 0<J) (ρ R : ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (hmp : ∀ a : Fin (M.n+1),a.val<rM → macroColumns a=M.frame (basis a))
    (hp : ∀ k A,∀ a : Fin ((G k A).n+1),a.val<r k A → columns k A a=(G k A).frame (basis a))
    (hmw : 0<M.width) (hh : ∀ A,0<(G 0 A).width)
    (hhp : ∀ k A,k≤1 → 0<(G k A).parentWidth)
    (hw : ∀ k A,k≤1 → (G k A).width≤(G k A).parentWidth)
    (ht : ∀ A,∀ a : Fin ((G J A).n+1),a.val<r J A → T J A a=endpointFrame Q (G J A).frame (Fin.last (n+1)) (basis a))
    (hmfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(G 0 [i.val]).n)
    (hfuture : ∀ A,∀ i : Fin ((G 0 A).n+1),r 0 A ≤ i.val →
      r 1 (child A i.val)≤(G 1 (child A i.val)).n)
    (z : PhysicalBase E J n D)
    (hmb : ∀ a : Fin (M.n+1),rM≤a.val → |M.coordinates z.fst a|≤M.width/8)
    (hb : ∀ k A,k<J → ∀ a : Fin ((G k A).n+1),r k A≤a.val →
      |(G k A).coordinates (block J k z.snd.fst) a|≤(G k A).width/8)
    (hbt : ∀ A,∀ a : Fin ((G J A).n+1),r J A≤a.val →
      |(physicalCoordinates Q (G J A) z.snd.snd).snd a|≤(G J A).width/8)
    (hmR : 0<M.radius) (hR : ∀ k A,k≤J → 0<(G k A).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδG : ∀ k A,k≤J → δ≤(G k A).width/16) :
    physicalUpperBase J Q M ν G J ρ R =ᶠ[𝓝 z]
      prefixPhysicalUpperBase J M ν G J ρ R rM r macroColumns columns T := by
  have hn := physical_eventually_blind_uniform (s:=0) Q M G rM r hmR hR δ hδ hδM hδG
    (pack z 0) hmb hb hbt
  have hcont : Continuous (fun y : PhysicalBase E J n D => pack y (0:Normals 0)) :=
    packLinear.continuous.comp (continuous_id.prodMk continuous_const)
  have hn' := (hcont.tendsto z).eventually hn
  filter_upwards [hn'] with y hy
  apply physicalUpperBase_eq_prefix Q M ν G J hJ ρ R rM r macroColumns columns T hmp hp hmw hh
    hhp hw ht hmfuture hfuture y hy.1 hy.2.1
  intro A a ha
  have hwidth : 0<(G J A).width := by have := hδG J A le_rfl;linarith
  have hx := hy.2.2 A a ha
  change |(physicalCoordinates Q (G J A) y.snd.snd).snd a|≤3*(G J A).width/16 at hx
  linarith

theorem physicalUpper_gradient_eq_of_base_germ {U T V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {D : ℕ} {f g : Joint E T → ℝ} (b : V)
    (z : Joint (HybridOuter E U D) (Joint T V))
    (he : f =ᶠ[𝓝 (pack z.fst.fst.fst z.snd.fst)] g) :
    gradient (physicalUpper (U:=U) (D:=D) f b) z=
      gradient (physicalUpper (U:=U) (D:=D) g b) z := by
  let A : Joint (HybridOuter E U D) (Joint T V) →L[ℝ] Joint E T :=
    jointFstLinear.comp normalCoordinates
  have hp : (fun y => f (A y)) =ᶠ[𝓝 z] (fun y => g (A y)) :=
    he.comp_tendsto A.continuous.continuousAt
  have hh : physicalUpper (U:=U) (D:=D) f b =ᶠ[𝓝 z] physicalUpper (U:=U) (D:=D) g b := by
    filter_upwards [hp] with y hy
    exact congrArg (fun t => t+⟪b,y.snd.snd⟫) hy
  exact hh.gradient_eq

end Bilevel.EndpointTransportResponse
