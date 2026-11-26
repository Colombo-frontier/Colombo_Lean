import Bilevel.ZeroChainProfiles
import Bilevel.ChiOuterPenalty

/-! Exact fixed exponential activation in the polished manuscript, with the
already proved Gaussian primitive and a valid smooth negative-side penalty.
The activation is deliberately not the capped `ChiBoundedChain.psi`. -/
noncomputable section
namespace Bilevel.PolishedLiteral

def psi : ℝ → ℝ := ZeroChainProfiles.psi

theorem psi_source_formula (t : ℝ) :
    psi t = if t ≤ 1 / 2 then 0 else Real.exp (1 - ((2*t-1)⁻¹)^2) := rfl

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := ZeroChainProfiles.psi_nonneg t

theorem psi_le_exp_one (t : ℝ) : psi t ≤ Real.exp 1 :=
  ZeroChainProfiles.psi_le_exp_one t

theorem psi_zero {t : ℝ} (ht : t ≤ 1/2) : psi t = 0 :=
  ZeroChainProfiles.psi_zero_of_le ht

theorem psi_ge_one {t : ℝ} (ht : 1 ≤ t) : 1 ≤ psi t :=
  ZeroChainProfiles.psi_ge_one ht

theorem psi_contDiff {k : ℕ} : ContDiff ℝ k psi :=
  ZeroChainProfiles.psi_contDiff

theorem psi_deriv_nonneg (t : ℝ) : 0 ≤ deriv psi t :=
  ZeroChainProfiles.psi_deriv_nonneg t

theorem psi_deriv_zero {t : ℝ} (ht : t ≤ 1/2) : deriv psi t = 0 :=
  ZeroChainProfiles.psi_deriv_zero_of_le ht

def penalty : ℝ → ℝ := ChiOuter.penalty

theorem penalty_hasDerivAt (t : ℝ) :
    HasDerivAt penalty (-ChiBoundedChain.theta (-t)) t :=
  ChiOuter.penalty_hasDerivAt t

theorem penalty_contDiff (k : ℕ) : ContDiff ℝ k penalty :=
  ChiOuter.penalty_contDiff k

theorem penalty_nonneg (t : ℝ) : 0 ≤ penalty t := ChiOuter.penalty_nonneg t

theorem penalty_zero_at_zero : penalty 0 = 0 := ChiOuter.penalty_zero_at_zero

theorem psi_flat_left (q : ℕ) (_hq : q ≤ 3) (t : ℝ) (ht : t ≤ 1/2) :
    iteratedDeriv q psi t = 0 := ZeroChainProfiles.psi_iteratedDeriv_zero_of_le q ht

theorem chain_profile_bound : ∃ K : ℝ,1≤K ∧ ∀ (j : Fin 4) (t : ℝ),
    |iteratedDeriv j.val psi t|≤K ∧ |iteratedDeriv j.val ZeroChainPotential.phi t|≤K := by
  obtain ⟨A,hA,ha⟩ := ZeroChainProfiles.psi_common_bound
  obtain ⟨B,hB,hb⟩ := ZeroChainPotential.phi_uniform_jet_bound
  refine ⟨A+B+1,by linarith,fun j t => ?_⟩
  constructor
  · exact (ha j t).trans (by linarith)
  · exact (hb j t).trans (by linarith)

end Bilevel.PolishedLiteral
