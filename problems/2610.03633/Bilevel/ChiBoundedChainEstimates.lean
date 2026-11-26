import Bilevel.ChiBoundedChainProfileBounds
import Bilevel.ChiBoundedChainSelectors

/-! Actual global amplitude bounds for the revised bounded chain and its
nonpositive incoming-only residual. Constants do not depend on chain length. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential

def gaussianBound : ℝ := Real.sqrt (Real.exp 1)*Real.sqrt (2*Real.pi)

theorem gaussianBound_nonneg : 0≤gaussianBound := by unfold gaussianBound;positivity

theorem edge_abs_bound (a b : ℝ) : |edge a b|≤gaussianBound := by
  have hb (t : ℝ) : |phi t|≤gaussianBound := by
    rw [abs_of_nonneg (phi_nonneg t)]
    exact phi_bounded t
  calc
    |edge a b|≤|psi (-a)*phi (-b)|+|psi a*phi b| := abs_sub _ _
    _ = psi (-a)*|phi (-b)|+psi a*|phi b| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (psi_nonneg _),abs_of_nonneg (psi_nonneg _)]
    _ ≤ psi (-a)*gaussianBound+psi a*gaussianBound := add_le_add
      (mul_le_mul_of_nonneg_left (hb _) (psi_nonneg _))
      (mul_le_mul_of_nonneg_left (hb _) (psi_nonneg _))
    _ = evenGate a*gaussianBound := by unfold evenGate;ring
    _ ≤ gaussianBound := by nlinarith [(evenGate_range a).2,gaussianBound_nonneg]

theorem value_abs_bound (n : ℕ) (z : Space n) :
    |value n z|≤(n+1)*gaussianBound := by
  have hp : |phi (z 0)|≤gaussianBound := by
    rw [abs_of_nonneg (phi_nonneg _)]
    exact phi_bounded _
  calc
    |value n z|≤|-phi (z 0)|+|∑ i : Fin n,edge (z i.castSucc) (z i.succ)| := abs_add _ _
    _ ≤ gaussianBound+∑ i : Fin n,|edge (z i.castSucc) (z i.succ)| :=
      add_le_add (by simpa only [abs_neg] using hp) (Finset.abs_sum_le_sum_abs ..)
    _ ≤ gaussianBound+∑ _ : Fin n,gaussianBound := add_le_add_left
      (Finset.sum_le_sum (fun i _ => edge_abs_bound _ _)) _
    _ = (n+1)*gaussianBound := by simp;ring

theorem chain_abs_bound (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (z : Space n) :
    |chain n ℓ h z|≤(n+1)*gaussianBound*(ℓ*h^2) := by
  change |(ℓ*h^2)*value n (h⁻¹ • z)|≤_
  rw [abs_mul,abs_of_nonneg (show 0≤ℓ*h^2 by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (value_abs_bound n (h⁻¹ • z))
    (show 0≤ℓ*h^2 by positivity)]

theorem R_abs_bound (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (z : Space n) :
    |R n ℓ h z|≤gaussianBound*(ℓ*h^2) := by
  change |(ℓ*h^2)*residual n (h⁻¹ • z)|≤_
  rw [abs_mul,abs_of_nonneg (show 0≤ℓ*h^2 by positivity)]
  convert mul_le_mul_of_nonneg_left (residual_abs_bound n (h⁻¹ • z))
    (show 0≤ℓ*h^2 by positivity) using 1
  unfold gaussianBound
  ring

end Bilevel.ChiBoundedChain
