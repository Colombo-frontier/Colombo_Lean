import Bilevel.ChiOuterChain

/-! Actual one-sided macro selectors. At each point their value and first
derivative either vanish together or agree with the corresponding two-sided
selector. Hence all proved square-root bounds transfer without new constants. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ZeroChainPotential

def selector (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases (tailMask 0 z) (fun j => psi (z j.castSucc)*tailMask j.succ z) i

def selectorDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  Fin.cases (maskDerivative 0 z) (fun j =>
    (deriv psi (z j.castSucc)*tailMask j.succ z) • EuclideanSpace.proj (𝕜:=ℝ) j.castSucc +
      psi (z j.castSucc) • maskDerivative j.succ z) i

theorem selector_range (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    0 ≤ selector n i z ∧ selector n i z ≤ 1 := by
  refine Fin.cases (tailMask_range 0 z) (fun j => ?_) i
  exact ⟨mul_nonneg (psi_range _).1 (tailMask_range _ _).1,
    mul_le_one₀ (psi_range _).2 (tailMask_range _ _).1 (tailMask_range _ _).2⟩

theorem selector_contDiff (n k : ℕ) (i : Fin (n+1)) : ContDiff ℝ k (selector n i) := by
  refine Fin.cases (tailMask_contDiff 0 k) (fun j => ?_) i
  exact (psi_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff).mul
    (tailMask_contDiff j.succ k)

theorem selector_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (selector n i) (selectorDerivative n i z) z := by
  refine Fin.cases (tailMask_hasFDerivAt 0 z) (fun j => ?_) i
  have hd := ((psi_contDiff (k:=1)).differentiable (by norm_num) (z j.castSucc)).hasDerivAt
  have he := hd.hasFDerivAt.comp z (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).hasFDerivAt
  convert he.mul (tailMask_hasFDerivAt j.succ z) using 1
  ext v
  simp [selectorDerivative, ContinuousLinearMap.comp_apply]
  ring

theorem selector_jet_cases (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    (selector n i z = 0 ∧ selectorDerivative n i z = 0) ∨
      (selector n i z = ChiBoundedChain.selector n i z ∧
        selectorDerivative n i z = ChiBoundedChain.selectorDerivative n i z) := by
  refine Fin.cases (Or.inr ⟨rfl,rfl⟩) (fun j => ?_) i
  by_cases ht : z j.castSucc ≤ 1/2
  · left
    simp [selector, selectorDerivative, psi_zero ht, psi_deriv_zero ht]
  · right
    have ht' : -z j.castSucc ≤ 1/2 := by linarith
    simp [selector, selectorDerivative, ChiBoundedChain.selector,
      ChiBoundedChain.selectorDerivative, evenGate, psi_zero ht', psi_deriv_zero ht']

theorem selector_unique {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hi : selector n i z ≠ 0) (hj : selector n j z ≠ 0) : i = j := by
  obtain ⟨he,_⟩ := (selector_jet_cases n i z).resolve_left (fun h => hi h.1)
  obtain ⟨hf,_⟩ := (selector_jet_cases n j z).resolve_left (fun h => hj h.1)
  apply ChiBoundedChain.selector_unique i j z
  · rwa [← he]
  · rwa [← hf]

theorem selectorDerivative_zero_of_zero {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z = 0) : selectorDerivative n i z = 0 := by
  rcases selector_jet_cases n i z with h|h
  · exact h.2
  · rw [h.2]
    exact ChiBoundedChain.selectorDerivative_zero_of_zero i z (h.1.symm.trans hi)

theorem selector_sum_le_one (n : ℕ) (z : Space n) :
    ∑ i : Fin (n+1), selector n i z ≤ 1 := by
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans (ChiBoundedChain.selector_sum_le_one n z)
  rcases selector_jet_cases n i z with h|h
  · rw [h.1]
    exact (ChiBoundedChain.selector_range n i z).1
  · exact h.1.le

theorem selector_active_tail_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hi : selector n i z ≠ 0) (j : Fin (n+1)) (hij : i ≤ j) : |z j| < 1/2 := by
  obtain ⟨he,_⟩ := (selector_jet_cases n i z).resolve_left (fun h => hi h.1)
  apply ChiBoundedChain.selector_active_tail_small i z _ j hij
  rwa [← he]

theorem selector_sqrt_bound_of_inner (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n i (z : Space n), ‖ChiBoundedChain.selectorDerivative n i z‖ ≤
      C*Real.sqrt (ChiBoundedChain.selector n i z))
    (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    ‖selectorDerivative n i z‖ ≤ C*Real.sqrt (selector n i z) := by
  rcases selector_jet_cases n i z with h|h
  · rw [h.1,h.2,norm_zero]
    positivity
  · rw [h.1,h.2]
    exact hb n i z

def residualTerm (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ := -selector n i z*phi (z i)
def residualTermDerivative (n : ℕ) (i : Fin (n+1)) (z : Space n) : Space n →L[ℝ] ℝ :=
  (-phi (z i)) • selectorDerivative n i z +
    (-selector n i z*phiSlope (z i)) • EuclideanSpace.proj (𝕜:=ℝ) i

theorem residualTerm_hasFDerivAt (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    HasFDerivAt (residualTerm n i) (residualTermDerivative n i z) z := by
  convert (selector_hasFDerivAt n i z).neg.mul
    ((phi_hasDerivAt (z i)).hasFDerivAt.comp z (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt) using 1
  ext v
  simp [residualTermDerivative, ContinuousLinearMap.comp_apply]
  ring

theorem residualTerm_nonpos (n : ℕ) (i : Fin (n+1)) (z : Space n) : residualTerm n i z ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (selector_range n i z).1) (phi_nonneg _)

theorem residualTerm_abs_bound (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    |residualTerm n i z| ≤ gaussianBound*selector n i z := by
  rw [residualTerm, abs_mul, abs_neg, abs_of_nonneg (selector_range n i z).1,
    abs_of_nonneg (phi_nonneg _)]
  simpa only [gaussianBound, mul_comm] using mul_le_mul_of_nonneg_left (phi_bounded (z i)) (selector_range n i z).1

theorem residualTerm_sqrt_bound_of_inner (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n i (z : Space n), ‖ChiBoundedChain.residualTermDerivative n i z‖ ≤
      C*Real.sqrt (ChiBoundedChain.selector n i z))
    (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    ‖residualTermDerivative n i z‖ ≤ C*Real.sqrt (selector n i z) := by
  rcases selector_jet_cases n i z with h|h
  · simp only [residualTermDerivative,h.1,h.2,smul_zero,neg_zero,zero_mul,zero_smul,add_zero,norm_zero]
    positivity
  · simpa only [residualTermDerivative,h.1,h.2,ChiBoundedChain.residualTermDerivative] using hb n i z

end Bilevel.ChiOuter
