import Bilevel.ChiFineTangentLocality
import Bilevel.ChiRecursiveSlice

/-! Construction-specific closed-carrier and release support. Unreleased
incoming sources cancel in the actual carrier; their actual child gates
are flat when the child terminal remains in its blind interval. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential ZeroChainResidualScaled

theorem residualTerm_contDiff (n k : ℕ) (i : Fin (n+1)) : ContDiff ℝ k (residualTerm n i) :=
  (selector_contDiff n k i).neg.mul ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

theorem Rterm_contDiff (n : ℕ) (ℓ h : ℝ) (i : Fin (n+1)) (k : ℕ) :
    ContDiff ℝ k (Rterm n ℓ h i) :=
  contDiff_const.mul ((residualTerm_contDiff n k i).comp (contDiff_id.const_smul h⁻¹))

theorem residualTerm_gradient_small_ne {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hj : |z j|≤1/4) (hij : i≠j) : gradient (residualTerm n i) z j=0 := by
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (residualTerm_hasFDerivAt n i z)]
  have hs : selectorDerivative n i z (ZeroChain.basis j)=0 := selectorDerivative_basis_small i j z hj
  change selectorDerivative n i z (EuclideanSpace.single j 1)=0 at hs
  simp [residualTermDerivative,hs,ZeroChain.basis,EuclideanSpace.single_apply,hij,hij.symm]

theorem Rterm_gradient_small_ne {n : ℕ} (ℓ h : ℝ) (hh : 0<h) (i j : Fin (n+1)) (z : Space n)
    (hj : |z j|≤h/4) (hij : i≠j) : gradient (Rterm n ℓ h i) z j=0 := by
  rw [Rterm,scaled_gradient ((residualTerm_contDiff n 3 i).differentiable (by norm_num)),
    PiLp.smul_apply,residualTerm_gradient_small_ne i j (h⁻¹ • z)
      (scaled_coordinate_small h hh z j hj) hij,smul_zero]

def closedCarrier (n : ℕ) (ℓ h A ν g hp T : ℝ) (q : Fin (n+1) → ℝ) (z : Space n) : ℝ :=
  payloadCarrier n ℓ h A ν g hp T z+∑ i : Fin (n+1),Rterm n ℓ h i z*q i

theorem closedCarrier_contDiff (n : ℕ) (ℓ h A ν g hp T : ℝ) (q : Fin (n+1) → ℝ) :
    ContDiff ℝ 3 (closedCarrier n ℓ h A ν g hp T q) :=
  ((payload_contDiff n ℓ h A ν g hp T 3).sub (scaled_contDiff (residual_contDiff n 3) (ℓ*h^2) h)).add
    (ContDiff.sum (fun i _ => (Rterm_contDiff n ℓ h i 3).mul contDiff_const))

theorem closedCarrier_gradient_support (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (q : Fin (n+1) → ℝ) (hq : ∀ i,r ≤ i.val → q i=0)
    (z : Space n) (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤h/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (closedCarrier n ℓ h A ν g hp T q) z j=0 := by
  have hc : ContDiff ℝ 3 (payloadCarrier n ℓ h A ν g hp T) :=
    (payload_contDiff n ℓ h A ν g hp T 3).sub (scaled_contDiff (residual_contDiff n 3) (ℓ*h^2) h)
  have hd := (hc.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt
  have hr (i : Fin (n+1)) := ((Rterm_contDiff n ℓ h i 3).differentiable (by norm_num) z).hasGradientAt.hasFDerivAt
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun i _ => (hr i).mul_const (q i))
  have ht := hd.add hs
  change HasFDerivAt (closedCarrier n ℓ h A ν g hp T q) _ z at ht
  rw [ZeroChainResidualLocality.gradient_coordinate_eq ht,ContinuousLinearMap.add_apply,
    ← ZeroChainResidualLocality.gradient_coordinate_eq hd,payloadCarrier_gradient_support n r ℓ h A ν g hp T hh z hz j hj,
    zero_add,ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [ContinuousLinearMap.smul_apply,← ZeroChainResidualLocality.gradient_coordinate_eq (hr i)]
  by_cases hi : r ≤ i.val
  · rw [hq i hi,zero_smul]
  · rw [Rterm_gradient_small_ne ℓ h hh i j z (hz j hj)
      (by intro he;have he' := congrArg Fin.val he;omega),smul_zero]

end Bilevel.ChiBoundedChain

namespace Bilevel.ChiRecursive.Node
open ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def closed (D : Node E) (q : Fin (D.n+1) → ℝ) (u : E) : ℝ :=
  D.H u-(∑ i : Fin (D.n+1),D.residual i u)+∑ i : Fin (D.n+1),D.residual i u*q i

theorem closed_formula (D : Node E) (q : Fin (D.n+1) → ℝ) :
    D.closed q=closedCarrier D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius q ∘ D.coordinates := by
  funext u
  simp only [closed,Function.comp_apply,closedCarrier,payloadCarrier,H,residual,← R_eq_sum]

theorem closed_gradient_mem (D : Node E) (r : ℕ) (hh : 0<D.width) (hR : 0<D.radius)
    (q : Fin (D.n+1) → ℝ) (hq : ∀ i,r ≤ i.val → q i=0)
    (u : E) (W : Submodule ℝ E) (hu : u∈W)
    (hU : ∀ j : Fin (D.n+1),j.val<r → D.frame (basis j)∈W)
    (hz : ∀ j : Fin (D.n+1),r≤j.val → |D.coordinates u j|≤D.width/4) :
    gradient (D.closed q) u∈W := by
  rw [D.closed_formula]
  exact WrappedPrefixLocality.carried_gradient_mem D.n r D.radius hR D.frame _
    ((closedCarrier_contDiff D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius q).differentiable (by norm_num))
    u W hu hU (fun j hj => closedCarrier_gradient_support D.n r D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius
      hh q hq _ hz j hj)

theorem release_flat (D : Node E) (hhp : 0<D.parentWidth) (u : E)
    (ht : D.coordinates u (Fin.last D.n)≤D.parentWidth) :
    D.release u=0 ∧ fderiv ℝ D.release u=0 := by
  have hz : D.release u=0 := releaseGate_zero ((div_le_one hhp).mpr ht)
  have hm : IsLocalMin D.release u := by
    apply Filter.Eventually.of_forall
    intro v
    rw [hz]
    exact Real.smoothTransition.nonneg _
  exact ⟨hz,hm.hasFDerivAt_eq_zero (((D.release_contDiff 1).differentiable (by norm_num) u).hasFDerivAt)⟩

theorem release_flat_of_blind_terminal (D : Node E) (hhp : 0<D.parentWidth) (hwidth : D.width≤D.parentWidth)
    (u : E) (ht : |D.coordinates u (Fin.last D.n)|≤D.width/4) :
    D.release u=0 ∧ fderiv ℝ D.release u=0 :=
  D.release_flat hhp u (by linarith [(abs_le.mp ht).2])

end Bilevel.ChiRecursive.Node
