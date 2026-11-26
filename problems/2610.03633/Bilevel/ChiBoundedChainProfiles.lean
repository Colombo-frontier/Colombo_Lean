import Bilevel.ZeroChainResidualCutoffs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Concrete C-infinity bounded activation for the revised recursive chain.
It is not the earlier uncapped exponential activation. Squaring a smooth
transition makes the required square-root first-derivative estimate available.
The Gaussian primitive is exactly the already-defined manuscript primitive. -/
noncomputable section
open Set
namespace Bilevel.ChiBoundedChain
open ZeroChainPotential ZeroChainResidualCutoffs

def theta (t : ℝ) : ℝ := Real.smoothTransition (2*t-1)
def psi (t : ℝ) : ℝ := theta t ^ 2
def evenGate (t : ℝ) : ℝ := psi t+psi (-t)

theorem glue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue ((t⁻¹)^2*expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

theorem transition_deriv_nonneg (t : ℝ) : 0≤deriv Real.smoothTransition t := by
  have hd := (glue_hasDerivAt t).div
    ((glue_hasDerivAt t).add ((glue_hasDerivAt (1-t)).comp t
      ((hasDerivAt_id t).const_sub 1))) (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition _ t at hd
  rw [hd.deriv]
  simp only [Function.comp_apply]
  apply div_nonneg _ (sq_nonneg _)
  have h0 := expNegInvGlue.nonneg t
  have h1 := expNegInvGlue.nonneg (1-t)
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg t⁻¹) h0) h1,
    mul_nonneg (mul_nonneg (sq_nonneg (1-t)⁻¹) h1) h0]

theorem theta_contDiff {k : ℕ∞} : ContDiff ℝ k theta :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem psi_contDiff {k : ℕ∞} : ContDiff ℝ k psi := theta_contDiff.pow 2

theorem theta_range (t : ℝ) : 0≤theta t ∧ theta t≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem psi_range (t : ℝ) : 0≤psi t ∧ psi t≤1 := by
  have ht := theta_range t
  unfold psi
  constructor
  · positivity
  · nlinarith

theorem theta_zero {t : ℝ} (ht : t≤1/2) : theta t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem theta_one {t : ℝ} (ht : 1≤t) : theta t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem psi_zero {t : ℝ} (ht : t≤1/2) : psi t=0 := by rw [psi,theta_zero ht]; norm_num
theorem psi_one {t : ℝ} (ht : 1≤t) : psi t=1 := by rw [psi,theta_one ht]; norm_num

theorem theta_hasDerivAt (t : ℝ) :
    HasDerivAt theta (2*deriv Real.smoothTransition (2*t-1)) t := by
  have hd := ((Real.smoothTransition.contDiff (n:=1)).differentiable (by norm_num) (2*t-1)).hasDerivAt
  convert hd.comp t (((hasDerivAt_id t).const_mul 2).sub_const 1) using 1
  ring

theorem theta_deriv_nonneg (t : ℝ) : 0≤deriv theta t := by
  rw [(theta_hasDerivAt t).deriv]
  exact mul_nonneg (by norm_num) (transition_deriv_nonneg _)

theorem psi_hasDerivAt (t : ℝ) : HasDerivAt psi (2*theta t*deriv theta t) t := by
  convert ((theta_contDiff (k:=1)).differentiable (by norm_num) t).hasDerivAt.pow 2 using 1
  simp

theorem psi_deriv_nonneg (t : ℝ) : 0≤deriv psi t := by
  rw [(psi_hasDerivAt t).deriv]
  exact mul_nonneg (mul_nonneg (by norm_num) (theta_range t).1) (theta_deriv_nonneg t)

theorem psi_deriv (t : ℝ) : deriv psi t=2*theta t*deriv theta t :=
  (psi_hasDerivAt t).deriv

theorem psi_nonneg (t : ℝ) : 0≤psi t := (psi_range t).1
theorem psi_zero_of_le {t : ℝ} (ht : t≤1/2) : psi t=0 := psi_zero ht
theorem psi_ge_one {t : ℝ} (ht : 1≤t) : 1≤psi t := (psi_one ht).ge

theorem psi_monotone : Monotone psi :=
  monotone_of_deriv_nonneg (fun t => (psi_hasDerivAt t).differentiableAt) psi_deriv_nonneg

theorem psi_flat_left (k : ℕ) (hk : k≤3) (t : ℝ) (ht : t≤1/2) :
    iteratedDeriv k psi t=0 := by
  by_cases hk0 : k=0
  · subst k
    exact psi_zero ht
  · exact iteratedDeriv_zero_of_constant_on (psi_contDiff (k:=3)) (uniqueDiffOn_Iic (1/2))
      (fun _ hx => psi_zero hx) k (by omega) hk t ht

theorem psi_deriv_zero {t : ℝ} (ht : t≤1/2) : deriv psi t=0 := by
  simpa only [iteratedDeriv_one] using psi_flat_left 1 (by norm_num) t ht

theorem psi_deriv_zero_of_le {t : ℝ} (ht : t≤1/2) : deriv psi t=0 := psi_deriv_zero ht

theorem evenGate_range (t : ℝ) : 0≤evenGate t ∧ evenGate t≤1 := by
  have h0 := psi_range t
  have h1 := psi_range (-t)
  unfold evenGate
  constructor
  · linarith
  · by_cases ht : t≤1/2
    · rw [psi_zero ht,zero_add]
      exact h1.2
    · rw [psi_zero (show -t≤1/2 by linarith),add_zero]
      exact h0.2

theorem evenGate_zero {t : ℝ} (ht : |t|≤1/2) : evenGate t=0 := by
  unfold evenGate
  rw [psi_zero (abs_le.mp ht).2,psi_zero (by linarith [(abs_le.mp ht).1])]
  norm_num

theorem phiSlope_even (t : ℝ) : phiSlope (-t)=phiSlope t := by
  simp only [phiSlope,kernel,neg_sq]

/-- The exact signed-edge cancellation uses this actual Gaussian identity. -/
theorem phi_reflection (t : ℝ) : phi t+phi (-t)=2*phi 0 := by
  have hd (x : ℝ) : HasDerivAt (fun s => phi s+phi (-s)) 0 x := by
    convert (phi_hasDerivAt x).add ((phi_hasDerivAt (-x)).comp x (hasDerivAt_id x).neg) using 1
    simp only [phiSlope_even]
    ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0
  simpa only [neg_zero,two_mul] using hc

end Bilevel.ChiBoundedChain
