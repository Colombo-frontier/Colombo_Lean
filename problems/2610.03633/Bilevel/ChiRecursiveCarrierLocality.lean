import Bilevel.ChiRecursiveNodeLocality
import Bilevel.GradientJetBounds

/-! Exact support for actual recursive carrier slices. Child release
coefficients are discharged from the actual terminal intervals, and ancestor
selectors have no nonradial derivative in any blind coordinate. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiRecursive
open ChiBoundedChain ZeroChainResidualScaled
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem own_selectedCarrier_eq_closed (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    (fun v => selectedCarrier D (d+1) j I 0 (Function.update u j v))=
      (D j I).closed (fun i => (D (j+1) (child I i.val)).release (u (j+1))) := by
  funext v
  simp only [selectedCarrier,Node.closed,Function.update_self,
    Function.update_of_ne (show j+1≠j by omega)]

theorem own_selectedCarrier_gradient_mem (D : Geometry E) (d j r : ℕ) (I : List ℕ) (u : ℕ → E)
    (hh : 0<(D j I).width) (hR : 0<(D j I).radius)
    (hchildWidth : ∀ i : Fin ((D j I).n+1),r ≤ i.val →
      (D (j+1) (child I i.val)).width≤(D (j+1) (child I i.val)).parentWidth)
    (hchildParent : ∀ i : Fin ((D j I).n+1),r ≤ i.val → 0<(D (j+1) (child I i.val)).parentWidth)
    (hchildTerminal : ∀ i : Fin ((D j I).n+1),r ≤ i.val →
      |(D (j+1) (child I i.val)).coordinates (u (j+1)) (Fin.last (D (j+1) (child I i.val)).n)|≤
        (D (j+1) (child I i.val)).width/4)
    (W : Submodule ℝ E) (hu : u j∈W)
    (hU : ∀ k : Fin ((D j I).n+1),k.val<r → (D j I).frame (basis k)∈W)
    (hz : ∀ k : Fin ((D j I).n+1),r≤k.val → |(D j I).coordinates (u j) k|≤(D j I).width/4) :
    gradient (fun v => selectedCarrier D (d+1) j I 0 (Function.update u j v)) (u j)∈W := by
  rw [own_selectedCarrier_eq_closed]
  apply Node.closed_gradient_mem _ r hh hR _ _ (u j) W hu hU hz
  intro i hi
  exact ((D (j+1) (child I i.val)).release_flat_of_blind_terminal
    (hchildParent i hi) (hchildWidth i hi) (u (j+1)) (hchildTerminal i hi)).1

theorem normalized_selector_gradient_small (n : ℕ) (h : ℝ) (hh : 0<h)
    (i j : Fin (n+1)) (z : Space n) (hj : |z j|≤h/4) :
    gradient (fun x => ChiBoundedChain.selector n i (h⁻¹ • x)) z j=0 := by
  have he : (fun x => ChiBoundedChain.selector n i (h⁻¹ • x))=scaled (ChiBoundedChain.selector n i) 1 h := by
    funext x
    simp only [scaled,one_mul]
  rw [he,scaled_gradient ((ChiBoundedChain.selector_contDiff n 3 i).differentiable (by norm_num)),PiLp.smul_apply]
  have hz := scaled_coordinate_small h hh z j hj
  have hg : gradient (ChiBoundedChain.selector n i) (h⁻¹ • z) j=0 := by
    rw [ZeroChainResidualLocality.gradient_coordinate_eq (ChiBoundedChain.selector_hasFDerivAt n i _)]
    exact selectorDerivative_basis_small i j _ hz
  rw [hg,smul_zero]

theorem Node.selector_gradient_mem (D : Node E) (r : ℕ) (hh : 0<D.width) (hR : 0<D.radius)
    (i : Fin (D.n+1)) (u : E) (W : Submodule ℝ E) (hu : u∈W)
    (hU : ∀ k : Fin (D.n+1),k.val<r → D.frame (basis k)∈W)
    (hz : ∀ k : Fin (D.n+1),r≤k.val → |D.coordinates u k|≤D.width/4) :
    gradient (D.selector i) u∈W :=
  WrappedPrefixLocality.carried_gradient_mem D.n r D.radius hR D.frame
    (fun x => ChiBoundedChain.selector D.n i (D.width⁻¹ • x))
    (((ChiBoundedChain.selector_contDiff D.n 3 i).comp (contDiff_id.const_smul D.width⁻¹)).differentiable (by norm_num))
    u W hu hU (fun k hk => normalized_selector_gradient_small D.n D.width hh i k _ (hz k hk))

theorem Node.release_gradient_zero_of_blind (D : Node E) (hhp : 0<D.parentWidth) (hwidth : D.width≤D.parentWidth)
    (u : E) (ht : |D.coordinates u (Fin.last D.n)|≤D.width/4) : gradient D.release u=0 := by
  apply norm_eq_zero.mp
  rw [GradientJetBounds.gradient_norm_eq,(D.release_flat_of_blind_terminal hhp hwidth u ht).2,norm_zero]

end Bilevel.ChiRecursive
