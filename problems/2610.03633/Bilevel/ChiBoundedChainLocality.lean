import Bilevel.ChiBoundedChainResidual

/-! Exact actual-gradient prefix cancellation for the revised incoming-only
nonpositive residual. The support conclusions follow from the concrete cutoffs
and signed-edge identity, rather than being protocol hypotheses. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

theorem incomingDerivative_basis_late {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i<j) : incomingDerivative n i z (basis j)=0 := by
  revert hij
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hj
    have hj0 : j≠0 := ne_of_gt hj
    simp [incomingDerivative,basis,hj0,hj0.symm]
  · intro hk
    have hj0 : j≠k.castSucc := by
      intro he
      rw [he] at hk
      change k.val+1<k.val at hk
      omega
    have hj1 : j≠k.succ := ne_of_gt hk
    simp [incomingDerivative,basis,hj0,hj1,hj0.symm,hj1.symm]

theorem incomingDerivative_succ_inactive {n : ℕ} (i : Fin n) (z : Space n)
    (hi : |z i.castSucc|≤1/2) : incomingDerivative n i.succ z=0 := by
  have hp : deriv psi (z i.castSucc)=0 := psi_deriv_zero (abs_le.mp hi).2
  have hn : deriv psi (-z i.castSucc)=0 := psi_deriv_zero (by linarith [(abs_le.mp hi).1])
  simp [incomingDerivative,hp,hn,evenGate_zero hi]

theorem predecessorDerivative_basis_small {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hj : |z j|≤1/4) : predecessorDerivative n i z (basis j)=0 := by
  refine Fin.cases (by simp [predecessorDerivative]) (fun k => ?_) i
  by_cases he : j=k.castSucc
  · have hz : deriv psi (-z k.castSucc)=0 := by
      rw [← he]
      exact psi_deriv_zero (by linarith [(abs_le.mp hj).1])
    simp [predecessorDerivative,hz]
  · simp [predecessorDerivative,basis,he,Ne.symm he]

theorem residualDerivative_tail_eq_incoming {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r≤j.val) :
    residualDerivative n z (basis j)=(∑ i : Fin (n+1),incomingDerivative n i z) (basis j) := by
  simp only [residualDerivative,ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,maskDerivative_basis_small i j z (hz j hj),smul_zero,add_zero]
  by_cases hi : i.val<r
  · rw [incomingDerivative_basis_late i j z (by change i.val<j.val;omega),smul_zero]
  · rw [tailMask_one_of_small i z (fun k hik => hz k (by
      have hik' : i.val≤k.val := hik
      omega)),one_smul]

theorem carrier_gradient_support {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (carrier n) z j=0 := by
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (carrier_hasFDerivAt n z),
    ContinuousLinearMap.sub_apply]
  change (∑ i : Fin (n+1),(incomingDerivative n i z+predecessorDerivative n i z)) (basis j)-
    residualDerivative n z (basis j)=0
  rw [residualDerivative_tail_eq_incoming r z hz j hj]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    predecessorDerivative_basis_small _ j z (hz j hj),add_zero,sub_self]

theorem residual_gradient_support {n : ℕ} (r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤1/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (residual n) z j=0 := by
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (residual_hasFDerivAt n z)]
  change residualDerivative n z (basis j)=0
  rw [residualDerivative_tail_eq_incoming r z hz j (by omega),ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val≤r
  · exact incomingDerivative_basis_late i j z (by change i.val<j.val;omega)
  · revert hi
    refine Fin.cases (by simp) (fun k hk => ?_) i
    have hp := hz k.castSucc (by change r≤k.val;simp only [Fin.val_succ] at hk;omega)
    rw [incomingDerivative_succ_inactive k z (by linarith)]
    rfl

theorem carrier_gradient_zero (n : ℕ) : gradient (carrier n) 0=0 := by
  ext j
  exact carrier_gradient_support 0 0 (by intro j _;simp) j (Nat.zero_le _)

end Bilevel.ChiBoundedChain
