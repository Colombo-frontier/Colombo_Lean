import Bilevel.ChiOuterReleaseJets
import Bilevel.ZeroChainFlatteningMap

/-! Literal one-sided micro residual in the earlier hierarchical mean.
The centering is one global constant, as in manuscript lines 541--545.
It is deliberately distinct from the later recursive selected centering. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
namespace Bilevel.HierarchicalMean
open ChiBoundedChain ZeroChainPotential

def normalizedResidual (n : ℕ) (z : Space n) : ℝ :=
  (∑ i : Fin (n+1), ChiOuter.residualTerm n i z)+phi 0

def residual (n : ℕ) (L β : ℝ) (z : Space n) : ℝ :=
  (L*β^2)*normalizedResidual n (β⁻¹ • z)

def flatResidual (n : ℕ) (L β δ : ℝ) (z : Space n) : ℝ :=
  residual n L β (ZeroChainFlatteningMap.flattenMap n δ z)

def approximation (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (j : ℕ) : Space n → ℝ :=
  if j<J then flatResidual n L β (δ j) else residual n L β

def piece (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) : ℕ → Space n → ℝ
  | 0 => approximation n J L β δ 0
  | j+1 => fun z => approximation n J L β δ (j+1) z-approximation n J L β δ j z

theorem normalizedResidual_contDiff (n : ℕ) : ContDiff ℝ 3 (normalizedResidual n) :=
  (ContDiff.sum (fun i _ => ChiOuter.outer_residual_contDiff n i)).add contDiff_const

theorem residual_contDiff (n : ℕ) (L β : ℝ) : ContDiff ℝ 3 (residual n L β) :=
  contDiff_const.mul ((normalizedResidual_contDiff n).comp (contDiff_id.const_smul β⁻¹))

theorem flatResidual_contDiff (n : ℕ) (L β δ : ℝ) : ContDiff ℝ 3 (flatResidual n L β δ) :=
  (residual_contDiff n L β).comp (ZeroChainFlatteningMap.flattenMap_contDiff n δ)

theorem approximation_contDiff (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (j : ℕ) :
    ContDiff ℝ 3 (approximation n J L β δ j) := by
  unfold approximation
  split_ifs
  · exact flatResidual_contDiff n L β (δ j)
  · exact residual_contDiff n L β

theorem piece_contDiff (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (j : ℕ) :
    ContDiff ℝ 3 (piece n J L β δ j) := by
  cases j with
  | zero => exact approximation_contDiff n J L β δ 0
  | succ j =>
    exact (approximation_contDiff n J L β δ (j+1)).sub (approximation_contDiff n J L β δ j)

theorem sum_piece (n J : ℕ) (L β : ℝ) (δ : ℕ → ℝ) (z : Space n) :
    (∑ j ∈ Finset.range (J+1),piece n J L β δ j z)=residual n L β z := by
  have hs (N : ℕ) : (∑ j ∈ Finset.range (N+1),piece n J L β δ j z)=
      approximation n J L β δ N z := by
    induction N with
    | zero => simp [piece]
    | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      simp only [piece]
      ring
  simpa only [approximation,if_neg (lt_irrefl J)] using hs J

theorem normalizedResidual_zero (n : ℕ) : normalizedResidual n 0=0 := by
  have hψ : psi 0=0 := psi_zero (by norm_num)
  have hm : tailMask (0:Fin (n+1)) (0:Space n)=1 :=
    tailMask_one_of_small _ _ (by intros; simp)
  simp only [normalizedResidual,ChiOuter.residualTerm,Fin.sum_univ_succ,
    ChiOuter.selector,Fin.cases_zero,Fin.cases_succ,PiLp.zero_apply,hψ,hm,
    zero_mul,neg_zero,Finset.sum_const_zero,add_zero,neg_mul,one_mul]
  ring

theorem residual_zero (n : ℕ) (L β : ℝ) : residual n L β 0=0 := by
  simp only [residual,smul_zero,normalizedResidual_zero,mul_zero]

theorem flatResidual_zero (n : ℕ) (L β δ : ℝ) : flatResidual n L β δ 0=0 := by
  rw [flatResidual,ZeroChainFlatteningMap.flattenMap_zero,residual_zero]

end Bilevel.HierarchicalMean
