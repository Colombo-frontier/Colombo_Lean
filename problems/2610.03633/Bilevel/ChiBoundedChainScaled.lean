import Bilevel.ChiBoundedChainCentered
import Bilevel.WrappedPrefixLocality

/-! The revised source normalization e=ell*h^2, including actual radial
wrapper support. The ambient support explicitly includes the query direction. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

theorem selector_contDiff (n k : ℕ) (i : Fin (n+1)) : ContDiff ℝ k (selector n i) := by
  refine Fin.cases (tailMask_contDiff 0 k) (fun j => ?_) i
  exact ((evenGate_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff).mul
    (tailMask_contDiff j.succ k)

theorem residual_contDiff (n k : ℕ) : ContDiff ℝ k (residual n) := by
  apply ContDiff.sum
  intro i _
  exact (selector_contDiff n k i).neg.mul
    ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

theorem carrier_contDiff (n k : ℕ) : ContDiff ℝ k (carrier n) :=
  (value_contDiff n k).sub (residual_contDiff n k)

theorem centeredResidual_contDiff (n k : ℕ) : ContDiff ℝ k (centeredResidual n) := by
  apply ContDiff.sum
  intro i _
  exact (selector_contDiff n k i).neg.mul
    (((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff).sub contDiff_const)

theorem centeredCarrier_contDiff (n k : ℕ) : ContDiff ℝ k (centeredCarrier n) :=
  (value_contDiff n k).sub (centeredResidual_contDiff n k)

def Rterm (n : ℕ) (ℓ h : ℝ) (i : Fin (n+1)) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (residualTerm n i) (ℓ*h^2) h
def R (n : ℕ) (ℓ h : ℝ) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (residual n) (ℓ*h^2) h
def A (n : ℕ) (ℓ h : ℝ) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (carrier n) (ℓ*h^2) h
def Rcentered (n : ℕ) (ℓ h : ℝ) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (centeredResidual n) (ℓ*h^2) h
def Acentered (n : ℕ) (ℓ h : ℝ) : Space n → ℝ :=
  ZeroChainResidualScaled.scaled (centeredCarrier n) (ℓ*h^2) h

theorem Rterm_formula (n : ℕ) (ℓ h : ℝ) (i : Fin (n+1)) (z : Space n) :
    Rterm n ℓ h i z=-(ℓ*h^2)*selector n i (h⁻¹ • z)*phi (z i/h) := by
  simp only [Rterm,ZeroChainResidualScaled.scaled,residualTerm,PiLp.smul_apply,smul_eq_mul,
    div_eq_inv_mul]
  ring

theorem R_eq_sum (n : ℕ) (ℓ h : ℝ) (z : Space n) :
    R n ℓ h z=∑ i : Fin (n+1),Rterm n ℓ h i z := by
  simp only [R,Rterm,ZeroChainResidualScaled.scaled,residual,Finset.mul_sum]

theorem Rterm_nonpos (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (i : Fin (n+1)) (z : Space n) :
    Rterm n ℓ h i z≤0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) (residualTerm_nonpos n i _)

theorem R_nonpos (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (z : Space n) : R n ℓ h z≤0 :=
  mul_nonpos_of_nonneg_of_nonpos (by positivity) (residual_nonpos n _)

theorem scaled_exact_split (n : ℕ) (ℓ h : ℝ) (z : Space n) :
    A n ℓ h z+R n ℓ h z=chain n ℓ h z := by
  simp [A,R,chain,ZeroChainResidualScaled.scaled,carrier,mul_sub]

theorem scaled_centered_exact_split (n : ℕ) (ℓ h : ℝ) (z : Space n) :
    Acentered n ℓ h z+Rcentered n ℓ h z=chain n ℓ h z := by
  simp [Acentered,Rcentered,chain,ZeroChainResidualScaled.scaled,centeredCarrier,mul_sub]

theorem Rcentered_zero (n : ℕ) (ℓ h : ℝ) : Rcentered n ℓ h 0=0 := by
  simp [Rcentered,ZeroChainResidualScaled.scaled,centeredResidual_zero]

theorem A_gradient_support (n r : ℕ) (ℓ h : ℝ) (hh : 0<h) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤h/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (A n ℓ h) z j=0 := by
  rw [A,ZeroChainResidualScaled.scaled_gradient
    ((carrier_contDiff n 1).differentiable (by norm_num)),PiLp.smul_apply,
    carrier_gradient_support r (h⁻¹ • z) (fun k hk =>
      ZeroChainResidualScaled.scaled_coordinate_small h hh z k (hz k hk)) j hj,smul_zero]

theorem R_gradient_support (n r : ℕ) (ℓ h : ℝ) (hh : 0<h) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤h/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (R n ℓ h) z j=0 := by
  rw [R,ZeroChainResidualScaled.scaled_gradient
    ((residual_contDiff n 1).differentiable (by norm_num)),PiLp.smul_apply,
    residual_gradient_support r (h⁻¹ • z) (fun k hk =>
      ZeroChainResidualScaled.scaled_coordinate_small h hh z k (hz k hk)) j hj,smul_zero]

theorem Acentered_gradient_support (n r : ℕ) (ℓ h : ℝ) (hh : 0<h) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤h/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (Acentered n ℓ h) z j=0 := by
  rw [Acentered,ZeroChainResidualScaled.scaled_gradient
    ((centeredCarrier_contDiff n 1).differentiable (by norm_num)),PiLp.smul_apply,
    centeredCarrier_gradient_support r (h⁻¹ • z) (fun k hk =>
      ZeroChainResidualScaled.scaled_coordinate_small h hh z k (hz k hk)) j hj,smul_zero]

theorem Rcentered_gradient_support (n r : ℕ) (ℓ h : ℝ) (hh : 0<h) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤h/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (Rcentered n ℓ h) z j=0 := by
  rw [Rcentered,ZeroChainResidualScaled.scaled_gradient
    ((centeredResidual_contDiff n 1).differentiable (by norm_num)),PiLp.smul_apply,
    centeredResidual_gradient_support r (h⁻¹ • z) (fun k hk =>
      ZeroChainResidualScaled.scaled_coordinate_small h hh z k (hz k hk)) j hj,smul_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem wrapped_carrier_gradient_mem (n r : ℕ) (ℓ h radius : ℝ) (hh : 0<h) (hR : 0<radius)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (V : Submodule ℝ E) (hu : u∈V)
    (hU : ∀ j : Fin (n+1),j.val<r → U (basis j)∈V)
    (hz : ∀ j : Fin (n+1),r≤j.val → |WrappedChain.coordinates n radius U u j|≤h/4) :
    gradient (A n ℓ h ∘ WrappedChain.coordinates n radius U) u∈V := by
  exact WrappedPrefixLocality.carried_gradient_mem n r radius hR U _
    ((ZeroChainResidualScaled.scaled_contDiff (carrier_contDiff n 3) _ _).differentiable (by norm_num))
    u V hu hU (fun j hj => A_gradient_support n r ℓ h hh _ hz j hj)

theorem wrapped_residual_gradient_mem (n r : ℕ) (ℓ h radius : ℝ) (hh : 0<h) (hR : 0<radius)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (V : Submodule ℝ E) (hu : u∈V)
    (hU : ∀ j : Fin (n+1),j.val<r+1 → U (basis j)∈V)
    (hz : ∀ j : Fin (n+1),r≤j.val → |WrappedChain.coordinates n radius U u j|≤h/4) :
    gradient (R n ℓ h ∘ WrappedChain.coordinates n radius U) u∈V := by
  exact WrappedPrefixLocality.carried_gradient_mem n (r+1) radius hR U _
    ((ZeroChainResidualScaled.scaled_contDiff (residual_contDiff n 3) _ _).differentiable (by norm_num))
    u V hu hU (fun j hj => R_gradient_support n r ℓ h hh _ hz j hj)

end Bilevel.ChiBoundedChain
