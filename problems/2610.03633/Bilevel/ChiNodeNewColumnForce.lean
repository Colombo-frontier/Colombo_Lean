import Bilevel.ChiCarrierDeepestLocality
import Bilevel.ChiCarrierRadialForce

/-! Construction-specific pre-wrapper cancellation on newly disclosed
columns. The closed carrier uses actual child release gates; the centered
deepest carrier and all ancestor selectors have zero new-column force. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiRecursive.Node
open ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def latentForce (D : Node E) (f : Space D.n → ℝ) (u : E) : E :=
  D.frame (gradient f (D.coordinates u))

theorem latentForce_coordinate (D : Node E) (f : Space D.n → ℝ) (u : E) (k : Fin (D.n+1)) :
    ⟪D.frame (basis k),D.latentForce f u⟫=gradient f (D.coordinates u) k := by
  rw [latentForce,D.frame.inner_map_map]
  exact ZeroChain.inner_basis k _

theorem carried_gradient_latentForce (D : Node E) (f : Space D.n → ℝ)
    (hf : ContDiff ℝ 3 f) (hR : 0<D.radius) (u : E) :
    gradient (f ∘ D.coordinates) u=RadialWrapper.compressDerivative D.radius u (D.latentForce f u) := by
  exact (WrappedPrefixLocality.carried_gradient D.n D.radius hR D.frame f
    (hf.differentiable (by norm_num)) u).trans (ChiCarrier.wrappedGradient_zero_eq _ _ _)

theorem closed_new_force_zero (D : Node E) (r : ℕ) (hh : 0<D.width)
    (q : Fin (D.n+1) → ℝ) (hq : ∀ i,r ≤ i.val → q i=0) (u : E)
    (hz : ∀ k : Fin (D.n+1),r≤k.val → |D.coordinates u k|≤D.width/4)
    (k : Fin (D.n+1)) (hk : r≤k.val) :
    ⟪D.frame (basis k),D.latentForce
      (closedCarrier D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius q) u⟫=0 := by
  rw [D.latentForce_coordinate]
  exact closedCarrier_gradient_support D.n r D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    hh q hq (D.coordinates u) hz k hk

theorem actual_child_closed_new_force_zero (D : Node E) (r : ℕ) (hh : 0<D.width)
    (children : Fin (D.n+1) → Node E) (v : Fin (D.n+1) → E)
    (hp : ∀ i,0<(children i).parentWidth) (hw : ∀ i,(children i).width≤(children i).parentWidth)
    (hchild : ∀ i,r ≤ i.val → |(children i).coordinates (v i) (Fin.last (children i).n)|≤(children i).width/4)
    (u : E) (hz : ∀ k : Fin (D.n+1),r≤k.val → |D.coordinates u k|≤D.width/4)
    (k : Fin (D.n+1)) (hk : r≤k.val) :
    ⟪D.frame (basis k),D.latentForce
      (closedCarrier D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
        (fun i => (children i).release (v i))) u⟫=0 := by
  apply D.closed_new_force_zero r hh _ _ u hz k hk
  intro i hi
  apply ((children i).release_flat (hp i) (v i) _).1
  have hz' := (le_abs_self ((children i).coordinates (v i) (Fin.last (children i).n))).trans (hchild i hi)
  have hp' := hp i
  have hw' := hw i
  linarith

theorem centered_new_force_zero (D : Node E) (r : ℕ) (hh : 0<D.width) (u : E)
    (hz : ∀ k : Fin (D.n+1),r≤k.val → |D.coordinates u k|≤D.width/4)
    (k : Fin (D.n+1)) (hk : r≤k.val) :
    ⟪D.frame (basis k),D.latentForce (fun z =>
      payload D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius z-
      ChiFine.frontier D.n D.ell D.width z) u⟫=0 := by
  rw [D.latentForce_coordinate]
  exact centeredPayload_gradient_support D.n r D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
    hh (D.coordinates u) hz k hk

theorem selector_new_force_zero (D : Node E) (hh : 0<D.width) (i k : Fin (D.n+1)) (u : E)
    (hk : |D.coordinates u k|≤D.width/4) :
    ⟪D.frame (basis k),D.latentForce (fun z => ChiBoundedChain.selector D.n i (D.width⁻¹ • z)) u⟫=0 := by
  rw [D.latentForce_coordinate]
  have hd := (ChiBoundedChain.selector_hasFDerivAt D.n i (D.width⁻¹ • D.coordinates u)).comp (D.coordinates u)
    ((hasFDerivAt_id (D.coordinates u)).const_smul D.width⁻¹)
  change HasFDerivAt (fun z : Space D.n => ChiBoundedChain.selector D.n i (D.width⁻¹ • z)) _ _ at hd
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hd]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul]
  change D.width⁻¹ • (selectorDerivative D.n i (D.width⁻¹ • D.coordinates u)) (basis k)=0
  rw [selectorDerivative_basis_small i k (D.width⁻¹ • D.coordinates u)
    (ZeroChainResidualScaled.scaled_coordinate_small D.width hh (D.coordinates u) k hk),smul_zero]

end Bilevel.ChiRecursive.Node
