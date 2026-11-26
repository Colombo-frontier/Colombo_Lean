import Bilevel.ChiBoundedChainMasks

/-! The revised nonpositive frontier residual, defined from incoming sources
and even predecessor gates. This differs from masking the entire signed edge. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

def incoming (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases (-phi (z 0)) (fun j => -evenGate (z j.castSucc)*phi (z j.succ)) i

def predecessor (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases 0 (fun j => (2*phi 0)*psi (-z j.castSucc)) i

def selector (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases (tailMask 0 z) (fun j => evenGate (z j.castSucc)*tailMask j.succ z) i

def residualTerm (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  -selector n i z*phi (z i)

def residual (n : ℕ) (z : Space n) : ℝ := ∑ i : Fin (n+1),residualTerm n i z
def carrier (n : ℕ) (z : Space n) : ℝ := value n z-residual n z

theorem selector_range (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    0≤selector n i z ∧ selector n i z≤1 := by
  refine Fin.cases (tailMask_range 0 z) (fun j => ?_) i
  exact ⟨mul_nonneg (evenGate_range _).1 (tailMask_range _ _).1,
    mul_le_one₀ (evenGate_range _).2 (tailMask_range _ _).1 (tailMask_range _ _).2⟩

theorem residualTerm_nonpos (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    residualTerm n i z≤0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (selector_range n i z).1) (phi_nonneg _)

theorem residual_nonpos (n : ℕ) (z : Space n) : residual n z≤0 :=
  Finset.sum_nonpos (fun i _ => residualTerm_nonpos n i z)

theorem residualTerm_eq_incoming (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    residualTerm n i z=incoming n i z*tailMask i z := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [residualTerm,selector,incoming,Fin.cases_zero]
    ring
  · simp only [residualTerm,selector,incoming,Fin.cases_succ]
    ring

theorem value_eq_incoming_predecessor (n : ℕ) (z : Space n) :
    value n z=∑ i : Fin (n+1),(incoming n i z+predecessor n i z) := by
  rw [Fin.sum_univ_succ]
  simp only [incoming,predecessor,Fin.cases_zero,Fin.cases_succ,add_zero]
  simp only [value,edge_rewrite]

theorem carrier_exact_split (n : ℕ) (z : Space n) : carrier n z+residual n z=value n z := by
  simp [carrier]

theorem evenGate_contDiff (k : ℕ) : ContDiff ℝ k evenGate :=
  psi_contDiff.add (psi_contDiff.comp contDiff_id.neg)

theorem evenGate_hasDerivAt (t : ℝ) :
    HasDerivAt evenGate (deriv psi t-deriv psi (-t)) t := by
  have hp (s : ℝ) := ((psi_contDiff (k:=1)).differentiable (by norm_num) s).hasDerivAt
  convert (hp t).add ((hp (-t)).comp t (hasDerivAt_id t).neg) using 1
  ring

def incomingDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  Fin.cases ((-phiSlope (z 0)) • EuclideanSpace.proj (𝕜:=ℝ) 0)
    (fun j => (-(deriv psi (z j.castSucc)-deriv psi (-z j.castSucc))*phi (z j.succ)) •
      EuclideanSpace.proj (𝕜:=ℝ) j.castSucc +
      (-evenGate (z j.castSucc)*phiSlope (z j.succ)) • EuclideanSpace.proj (𝕜:=ℝ) j.succ) i

def predecessorDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  Fin.cases 0 (fun j => (-(2*phi 0)*deriv psi (-z j.castSucc)) •
    EuclideanSpace.proj (𝕜:=ℝ) j.castSucc) i

def residualDerivative (n : ℕ) (z : Space n) : Space n →L[ℝ] ℝ :=
  ∑ i : Fin (n+1),(tailMask i z • incomingDerivative n i z+incoming n i z • maskDerivative i z)

theorem incoming_contDiff (n k : ℕ) (i : Fin (n+1)) : ContDiff ℝ k (incoming n i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1))).contDiff).neg
  · exact (((evenGate_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff).neg).mul
      ((phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) j.succ).contDiff)

theorem incoming_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (incoming n i) (incomingDerivative n i z) z := by
  refine Fin.cases ?_ (fun j => ?_) i
  · convert ((phi_hasDerivAt (z 0)).hasFDerivAt.comp z
      (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1))).hasFDerivAt).neg using 1
    ext v
    simp [incomingDerivative,ContinuousLinearMap.comp_apply,mul_comm]
  · have he := (evenGate_hasDerivAt (z j.castSucc)).hasFDerivAt.comp z
      (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).hasFDerivAt
    have hp := (phi_hasDerivAt (z j.succ)).hasFDerivAt.comp z
      (EuclideanSpace.proj (𝕜:=ℝ) j.succ).hasFDerivAt
    convert he.neg.mul hp using 1
    ext v
    simp [incomingDerivative,ContinuousLinearMap.comp_apply]
    ring

theorem predecessor_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (predecessor n i) (predecessorDerivative n i z) z := by
  refine Fin.cases (hasFDerivAt_const 0 z) (fun j => ?_) i
  have hp := (((psi_contDiff (k:=1)).differentiable (by norm_num) (-z j.castSucc)).hasDerivAt.hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).hasFDerivAt.neg).const_mul (2*phi 0)
  convert hp using 1
  ext v
  simp [predecessorDerivative,ContinuousLinearMap.comp_apply]
  ring

theorem residual_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (residual n) (residualDerivative n z) z := by
  have he : residual n=fun w => ∑ i : Fin (n+1),incoming n i w*tailMask i w := by
    funext w
    simp only [residual,residualTerm_eq_incoming]
  rw [he]
  convert HasFDerivAt.sum (fun i (_ : i∈Finset.univ) =>
    (incoming_hasFDerivAt n i z).mul (tailMask_hasFDerivAt i z)) using 1
  simp only [residualDerivative,add_comm]

theorem value_hasFDerivAt_parts (n : ℕ) (z : Space n) :
    HasFDerivAt (value n) (∑ i : Fin (n+1),
      (incomingDerivative n i z+predecessorDerivative n i z)) z := by
  convert HasFDerivAt.sum (fun i (_ : i∈Finset.univ) =>
    (incoming_hasFDerivAt n i z).add (predecessor_hasFDerivAt n i z)) using 1
  exact funext (value_eq_incoming_predecessor n)

theorem carrier_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (carrier n) ((∑ i : Fin (n+1),
      (incomingDerivative n i z+predecessorDerivative n i z))-residualDerivative n z) z :=
  (value_hasFDerivAt_parts n z).sub (residual_hasFDerivAt n z)

end Bilevel.ChiBoundedChain
