import Bilevel.ChiFineCouplingBounds

/-! Arbitrary positive extension strength and exact dual-normal trace for
the actual revised centered-frontier coupling. The chosen compact profile
is C3, which suffices for the manuscript's C2,1 primitive class. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainSchedule

namespace Parameters
variable (P : Parameters)

def coupling (n : ℕ) (lambdaExt : ℝ) (y : CompensatedMean.LowerSpace (Space n)) : ℝ :=
  lambdaExt*(P.data n).coupling y

theorem coupling_contDiff (n : ℕ) (lambdaExt : ℝ) : ContDiff ℝ 3 (P.coupling n lambdaExt) :=
  contDiff_const.mul (P.data n).coupling_contDiff

theorem coupling_zero_trace (n : ℕ) (lambdaExt : ℝ) (z : Space n) :
    P.coupling n lambdaExt (CompensatedMean.pack (Space n) z 0 0)=0 := by
  have hn (j : ℕ) : SmallGapProfiles.normal (width P.c P.β P.θ j) 0=0 := by
    have hp := width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j
    exact SmallGapProfiles.normal_core _ 0 hp (by rw [abs_zero];positivity)
  unfold coupling CompensatedMean.Data.coupling
  have hs : (∑ j ∈ Finset.range ((P.data n).J+1),
      (P.data n).couplingTerm j (CompensatedMean.pack (Space n) z 0 0))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [CompensatedMean.Data.couplingTerm,CompensatedMean.uProj_pack,
      CompensatedMean.sProj_pack]
    change P.pieces n j z*SmallGapProfiles.normal (width P.c P.β P.θ j) 0=0
    rw [hn j,mul_zero]
  rw [hs,mul_zero]

theorem coupling_normal_trace (n : ℕ) (lambdaExt : ℝ) (z : Space n) :
    HasDerivAt (fun s => P.coupling n lambdaExt (CompensatedMean.pack (Space n) z s 0))
      (lambdaExt*frontier n P.ℓ P.β z) 0 := by
  have hd (j : ℕ) : HasDerivAt (SmallGapProfiles.normal (width P.c P.β P.θ j)) 1 0 := by
    have hp := width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j
    have hh := ((SmallGapProfiles.normal_contDiff _ hp).differentiable (by norm_num) 0).hasDerivAt
    rw [SmallGapLiftSupport.normal_deriv_core _ 0 hp (by simp;positivity)] at hh
    exact hh
  have hh := (HasDerivAt.sum (u:=Finset.range (levels P.θ+1))
    (fun j _ => (hd j).const_mul (P.pieces n j z))).const_mul lambdaExt
  simp only [mul_one,P.decomposition n z] at hh
  convert hh using 1
  funext s
  simp only [coupling,CompensatedMean.Data.coupling,CompensatedMean.Data.couplingTerm,
    CompensatedMean.uProj_pack,CompensatedMean.sProj_pack]
  rfl

end Parameters

theorem arbitrary_strength_coupling_bounds : ∃ K : ℝ,1 ≤ K ∧
    ∀ (P : Parameters) (n : ℕ) (lambdaExt : ℝ),0 ≤ lambdaExt →
      ∀ y : CompensatedMean.LowerSpace (Space n),
        ‖iteratedFDeriv ℝ 2 (P.coupling n lambdaExt) y‖ ≤ K*lambdaExt*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
        ‖iteratedFDeriv ℝ 3 (P.coupling n lambdaExt) y‖ ≤ K*lambdaExt*P.ℓ*P.θ/P.c^2 := by
  obtain ⟨K,hK,hb⟩ := actual_coupling_bounds
  refine ⟨K,hK,fun P n lambdaExt hlambdaExt y => ?_⟩
  have he (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k (P.coupling n lambdaExt) y‖=lambdaExt*‖iteratedFDeriv ℝ k (P.data n).coupling y‖ := by
    change ‖iteratedFDeriv ℝ k (fun w => lambdaExt • (P.data n).coupling w) y‖=_
    rw [iteratedFDeriv_const_smul_apply' (((P.data n).coupling_contDiff).of_le
      (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)).contDiffAt,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hlambdaExt]
  rw [he 2 (by norm_num),he 3 (by norm_num)]
  exact ⟨(mul_le_mul_of_nonneg_left (hb P n y).1 hlambdaExt).trans_eq (by ring),
    (mul_le_mul_of_nonneg_left (hb P n y).2 hlambdaExt).trans_eq (by ring)⟩

end Bilevel.ChiFine
