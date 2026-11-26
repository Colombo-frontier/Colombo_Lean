import Bilevel.ChiUpperNoisePrefixValues
import Bilevel.ChiUniformBlindNeighborhood
import Bilevel.ChiVirtualReplyEquality

/-! Common scalar germs for the actual direct upper active/inactive branches.
The full conservative reply is pulled back to every original query block. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Topology
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem direct_blind_neighborhood (m : ℕ) (M : Node E) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (τM : ℝ) (τ : List ℕ → ℝ) (δ : ℝ) (hδ : 0<δ)
    (hmR : 0<M.radius) (hR : ∀ I,0<(D 0 I).radius) (z : Joint E (Blocks m F))
    (hm : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤τM-δ)
    (hn : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤τ I-δ) :
    ∀ᶠ y in 𝓝 z,
      (∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates y.fst k|≤τM) ∧
      (∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
        |(D 0 I).coordinates (block m 0 y.snd) k|≤τ I) := by
  have hmacro := eventually_blind_uniform (fun _ : Unit => M) (fun _ => hmR)
    (fun _ => outerProjection (E:=E) (F:=F) m) (fun _ => outerProjection_norm_le m)
    (fun _ => rM) (fun _ => τM) δ hδ z (fun _ => hm)
  have hnode := eventually_blind_uniform (fun I => D 0 I) hR
    (fun _ => hierarchyBlock (E:=E) (F:=F) m 0) (fun _ => hierarchyBlock_norm_le m 0)
    (r 0) τ δ hδ z hn
  filter_upwards [hmacro,hnode] with y hym hyn
  exact ⟨hym (),hyn⟩

theorem direct_core_eventuallyEq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (rM sM : ℕ) (r a : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hm : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hp : ∀ I,∀ k : Fin ((D 0 I).n+1),k.val<a 0 I → columns 0 I k=(D 0 I).frame (basis k))
    (hms : rM≤sM) (hra : ∀ I,r 0 I≤a 0 I)
    (hmw : 0<M.width) (hh : ∀ I,0<(D 0 I).width)
    (hhp : ∀ I,0<(D 0 I).parentWidth) (hw : ∀ I,(D 0 I).width≤(D 0 I).parentWidth)
    (hfuture : ∀ i : Fin (M.n+1),sM≤ i.val → a 0 [i.val]≤(D 0 [i.val]).n)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → (D 0 [i.val]).n<r 0 [i.val] ∨ r 0 [i.val]<a 0 [i.val])
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤3*M.width/16)
    (hblind : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤3*(D 0 I).width/16)
    (hmR : 0<M.radius) (hR : ∀ I,0<(D 0 I).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδD : ∀ I,δ≤(D 0 I).width/16) :
    ChiUpperNoise.core m M ν D ρ R =ᶠ[𝓝 z]
      virtualUpperBase m M ν D 0 (ρ 0) (R 0) sM a macroColumns columns := by
  have hlocal := direct_blind_neighborhood m M D rM r (M.width/4)
    (fun I => (D 0 I).width/4) δ hδ hmR hR z (by
      intro k hk
      have hb := hmBlind k hk
      linarith) (by
      intro I k hk
      have hb := hblind I k hk
      have hd := hδD I
      linarith)
  filter_upwards [hlocal] with y hy
  exact direct_core_eq_virtual m M ν D ρ R rM sM r a macroColumns columns hm hp hms hra
    hmw hh hhp hw hfuture hfront y hy.1 hy.2

theorem direct_inactive_core_eventuallyEq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hm : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hp : ∀ I,∀ k : Fin ((D 0 I).n+1),k.val<r 0 I → columns 0 I k=(D 0 I).frame (basis k))
    (hmw : 0<M.width) (hh : ∀ I,0<(D 0 I).width)
    (hhp : ∀ I,0<(D 0 I).parentWidth) (hw : ∀ I,(D 0 I).width≤(D 0 I).parentWidth)
    (hwidth : ∀ I,(D 0 I).width=(D 0 []).width)
    (hfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(D 0 [i.val]).n)
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤3*M.width/16)
    (hblind : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤(D 0 []).width/32)
    (hmR : 0<M.radius) (hR : ∀ I,0<(D 0 I).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδD : δ≤(D 0 []).width/32) :
    ChiUpperNoise.inactiveCore m M ν D ρ R =ᶠ[𝓝 z]
      virtualDirectInactive m M ν D ρ R rM r macroColumns columns := by
  have hlocal := direct_blind_neighborhood m M D rM r (M.width/4)
    (fun _ => (D 0 []).width/16) δ hδ hmR hR z (by
      intro k hk
      have hb := hmBlind k hk
      linarith) (by
      intro I k hk
      have hb := hblind I k hk
      linarith)
  filter_upwards [hlocal] with y hy
  exact direct_inactive_core_eq_virtual m M ν D ρ R rM r macroColumns columns hm hp
    hmw hh hhp hw hwidth hfuture y hy.1 hy.2

theorem direct_full_sample_eq_of_germs (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (active inactive : Joint E (Blocks m F) → ℝ)
    (π : ℝ) (coin : Bool) (q : ChiUpperNoise.Queries E (Blocks m F))
    (hi : ChiUpperNoise.inactiveCore m M ν D ρ R =ᶠ[𝓝 (ChiUpperNoise.queryProjection q)] inactive)
    (ha : coin=true → ChiUpperNoise.core m M ν D ρ R =ᶠ[𝓝 (ChiUpperNoise.queryProjection q)] active) :
    ChiConservative.sampleGradient (ChiUpperNoise.fullCore m M ν D ρ R)
      (ChiUpperNoise.fullInactiveCore m M ν D ρ R) π coin q=
      ChiConservative.sampleGradient (active ∘ ChiUpperNoise.queryProjection)
        (inactive ∘ ChiUpperNoise.queryProjection) π coin q := by
  apply sampleGradient_eq_of_branch_replies
  · exact (hi.comp_tendsto
      (ChiUpperNoise.queryProjection (E:=E) (U:=Blocks m F)).continuous.continuousAt).gradient_eq
  · intro hc
    exact ((ha hc).comp_tendsto
      (ChiUpperNoise.queryProjection (E:=E) (U:=Blocks m F)).continuous.continuousAt).gradient_eq

end Bilevel.ChiPrefixEvaluation
