import Bilevel.ChiBoundedChainLocality

/-! Centering the revised deepest frontier adds a predecessor-only compensation
on a blind tail. Its actual derivative support is preserved. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

def selectorDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  Fin.cases (maskDerivative 0 z) (fun j =>
    ((deriv psi (z j.castSucc)-deriv psi (-z j.castSucc))*tailMask j.succ z) •
      EuclideanSpace.proj (𝕜:=ℝ) j.castSucc + evenGate (z j.castSucc) • maskDerivative j.succ z) i

theorem selector_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (selector n i) (selectorDerivative n i z) z := by
  refine Fin.cases (tailMask_hasFDerivAt 0 z) (fun j => ?_) i
  have he := (evenGate_hasDerivAt (z j.castSucc)).hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).hasFDerivAt
  convert he.mul (tailMask_hasFDerivAt j.succ z) using 1
  ext v
  simp [selectorDerivative,ContinuousLinearMap.comp_apply]
  ring

theorem selectorDerivative_basis_small {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hj : |z j|≤1/4) : selectorDerivative n i z (basis j)=0 := by
  refine Fin.cases (maskDerivative_basis_small 0 j z hj) (fun k => ?_) i
  simp only [selectorDerivative,Fin.cases_succ,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,maskDerivative_basis_small k.succ j z hj,smul_zero,add_zero]
  by_cases he : j=k.castSucc
  · have h0 : deriv psi (z k.castSucc)=0 := by
      rw [← he]
      exact psi_deriv_zero (by linarith [(abs_le.mp hj).2])
    have h1 : deriv psi (-z k.castSucc)=0 := by
      rw [← he]
      exact psi_deriv_zero (by linarith [(abs_le.mp hj).1])
    simp [h0,h1]
  · simp [basis,he,Ne.symm he]

def centeredResidual (n : ℕ) (z : Space n) : ℝ :=
  ∑ i : Fin (n+1),-selector n i z*(phi (z i)-phi 0)

def centeredCarrier (n : ℕ) (z : Space n) : ℝ := value n z-centeredResidual n z

theorem centeredResidual_formula (n : ℕ) (z : Space n) :
    centeredResidual n z=residual n z+phi 0*(∑ i : Fin (n+1),selector n i z) := by
  unfold centeredResidual residual residualTerm
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem centeredResidual_zero (n : ℕ) : centeredResidual n 0=0 := by
  simp [centeredResidual]

def centeredResidualDerivative (n : ℕ) (z : Space n) : Space n →L[ℝ] ℝ :=
  residualDerivative n z+phi 0 • ∑ i : Fin (n+1),selectorDerivative n i z

theorem centeredResidual_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (centeredResidual n) (centeredResidualDerivative n z) z := by
  convert (residual_hasFDerivAt n z).add
    ((HasFDerivAt.sum (fun i (_ : i∈Finset.univ) => selector_hasFDerivAt n i z)).const_mul (phi 0)) using 1
  exact funext (centeredResidual_formula n)

theorem centeredResidual_gradient_support {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (centeredResidual n) z j=0 := by
  have hs (i : Fin (n+1)) : selectorDerivative n i z (ZeroChain.basis j)=0 :=
    selectorDerivative_basis_small i j z (hz j (by omega))
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (centeredResidual_hasFDerivAt n z)]
  simp only [centeredResidualDerivative,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    hs,Finset.sum_const_zero,smul_zero,add_zero]
  rw [← ZeroChainResidualLocality.gradient_coordinate_eq (residual_hasFDerivAt n z)]
  exact residual_gradient_support r z hz j hj

theorem centeredCarrier_gradient_support {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (centeredCarrier n) z j=0 := by
  have hs (i : Fin (n+1)) : selectorDerivative n i z (ZeroChain.basis j)=0 :=
    selectorDerivative_basis_small i j z (hz j hj)
  have hc := (value_hasFDerivAt_parts n z).sub (centeredResidual_hasFDerivAt n z)
  change HasFDerivAt (centeredCarrier n) _ z at hc
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hc]
  simp only [ContinuousLinearMap.sub_apply,centeredResidualDerivative,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    hs,Finset.sum_const_zero,smul_zero,add_zero]
  have hr := carrier_gradient_support r z hz j hj
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (carrier_hasFDerivAt n z),
    ContinuousLinearMap.sub_apply] at hr
  simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply] using hr

end Bilevel.ChiBoundedChain
