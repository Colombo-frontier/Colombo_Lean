import Bilevel.ChiHierarchyInactiveInverse

/-! Actual fixed inactive inverse locality from column-projection geometry.
The numeric blind conditions hold at every restricted point, hence in
particular at the constructed unique restricted inverse. There is no
assumption of small total hidden force relative to the finest width. -/
noncomputable section
set_option maxHeartbeats 600000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ) (hm : J < m)
  (W : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)] (r : ℕ → List ℕ → ℕ)
  (htree : TreeProjection D 0 J (by simpa using hm) W r)
  (hhp : ∀ t,t < J → ∀ P,0<(D (t+1) P).parentWidth)
  (hw : ∀ t,t < J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
  (hfuture : ∀ t,t < J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
    r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
  (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (hell : ∀ P,0≤(D J P).ell) (hwidth : ∀ P,(D J P).width=(D J []).width)
  (hfinest : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
    (D J P).radius*‖(W ⟨J,hm⟩).orthogonalProjection ((D J P).frame (basis k))‖≤
      width c (D J []).width θ (levels θ)/16)
  (s : ℕ) (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))

include hm htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchy_inactive_inverse_strict_blind [CompleteSpace (normalKnown W s)]
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (δ : NNReal)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(δ:ℝ))
    (hδ : δ<1) (a : E) (u : normalKnown W s) :
    let hf := hierarchyInactiveExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    let z := PartialLegendre.jointSolution (reassociated_gradient_lipschitz hf δ hb) hδ a (u:Full (Blocks m F) s)
    (∀ j P,j≤J → ∀ k : Fin ((D j P).n+1),r j P≤k.val →
      |(D j P).coordinates (block m j z.fst) k|≤(D j P).width/8) ∧
    (∀ P,∀ k : Fin ((D J P).n+1),r J P≤k.val →
      |(D J P).coordinates (block m J z.fst) k|≤width c (D J []).width θ (levels θ)/16) := by
  dsimp only
  let hf := hierarchyInactiveExtension_contDiff m M D J c θ hc hβ hθ s coarseIndex radialIndex fineIndex ρ R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  let p := NearIdentityInverse.restrictedInverse (normalKnown W s) hδ
    (lowerSlice_gradient_lipschitz hf δ hb a) u ⟨1,by norm_num⟩
  have hWpos := width_pos c (D J []).width θ hc hβ hθ (levels θ)
  have hweak : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
      (D J P).radius*‖(W ⟨J,hm⟩).orthogonalProjection ((D J P).frame (basis k))‖≤
        width c (D J []).width θ (levels θ)/8 := by
    intro P k hk
    have hh := hfinest P k hk
    linarith
  have he := hierarchyInactive_restricted_inverse_eq M D J hm W r htree hhp hw hfuture c θ hc hcs hβ hθ
    hell hwidth hweak s coarseIndex radialIndex fineIndex ρ R dn hR δ hb hδ a u
  change (p:Full (Blocks m F) s)=_ at he
  rw [← he]
  have hpoint (j : ℕ) (P : List ℕ) (hj : j≤J) (k : Fin ((D j P).n+1)) :
      |(D j P).coordinates (block m j (p:Full (Blocks m F) s).fst) k|≤
        (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖ := by
    let ij : Fin m := ⟨j,by omega⟩
    have hblock : block m j (p:Full (Blocks m F) s).fst=(p:Full (Blocks m F) s).fst ij := by
      have hjm : j<m := by omega
      simp only [block,dif_pos hjm,PiLp.proj_apply]
      rfl
    rw [hblock]
    exact (D j P).coordinate_projection_bound (htree j P (by omega) (by omega)).radius_pos
      (W ij) ⟨(p:Full (Blocks m F) s).fst ij,p.property ij⟩ k
  exact ⟨fun j P hj k hk => (hpoint j P hj k).trans (hmargin j P hj k hk),
    fun P k hk => (hpoint J P le_rfl k).trans (hfinest P k hk)⟩

end Bilevel.ChiOuter
