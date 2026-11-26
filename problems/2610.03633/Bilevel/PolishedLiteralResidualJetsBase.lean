import Bilevel.PolishedLiteralResidual
import Bilevel.PolishedLiteralSelectorJets
import Bilevel.ChiOuterReleaseJets

/-! Mixed jets of the actual one-sided macro release correction. The
selector support removes any factor equal to the number of macro stages. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainPotential

theorem outer_residual_contDiff (n : ℕ) (i : Fin (n+1)) : ContDiff ℝ 3 (residualTerm n i) :=
  (selector_contDiff n 3 i).neg.mul ((phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

theorem outer_residual_uniform_jets : ∃ B : ℝ,1≤B ∧ ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n)
    (k : ℕ),k≤3 → ‖iteratedFDeriv ℝ k (residualTerm n i) z‖≤B := by
  obtain ⟨S,hS,hs⟩ := selector_uniform_jets
  obtain ⟨K,hK,hprof⟩ := chain_profile_bound
  have hS0 : 0≤S := by linarith
  have hK0 : 0≤K := by linarith
  refine ⟨8*S*K,by nlinarith [mul_le_mul hS hK zero_le_one hS0],fun n i z k hk => ?_⟩
  have hf : ContDiff ℝ 3 (fun y : Space n => -selector n i y) := (selector_contDiff n 3 i).neg
  have hg : ContDiff ℝ 3 (fun y : Space n => phi (y i)) := (phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff
  have hb := same_width_product_jets hf hg S K 1 hS0 hK0 (by norm_num) z k hk
    (fun q hq => by
      change ‖iteratedFDeriv ℝ q (-(selector n i)) z‖≤S/1^q
      rw [iteratedFDeriv_neg_apply,norm_neg]
      simpa only [one_pow,div_one] using hs n i z q (by omega))
    (fun q hq => by
      simpa only [one_pow,div_one] using ZeroChainResidualBounds.scalar_linear_jet_bound (phi_contDiff 3)
        (EuclideanSpace.proj (𝕜:=ℝ) i) (ZeroChainResidualBounds.projection_norm_le i) z q (by omega) K hK0
        (hprof ⟨q,by omega⟩ (z i)).2)
  simpa only [one_pow,div_one] using hb


end Bilevel.PolishedLiteral
