import Bilevel.ChiSplitChain
import Bilevel.ChiBoundedChainPayload

/-! The complete split payload has both terminal receivers at the predecessor
endpoint. Its diagonal is the original source payload exactly. -/
noncomputable section
namespace Bilevel.ChiSplitChain
open ChiBoundedChain PrimitiveGeometry

def payload (n : ℕ) (ell h A ν g hp T : ℝ) (z : Latent n) : ℝ :=
  chain n ell h z+positiveReceiver A ν g h hp (z.snd (Fin.last n))+
    negativeReceiver A g h T (z.snd (Fin.last n))

def residualTerm (n : ℕ) (ell h : ℝ) (i : Fin (n+1)) (z : Latent n) : ℝ :=
  ell*h^2*(-selector n i (h⁻¹ • z.snd)*ZeroChainPotential.phi ((h⁻¹ • z.fst) i))

theorem payload_diagonal (n : ℕ) (ell h A ν g hp T : ℝ) (z : Space n) :
    payload n ell h A ν g hp T (pack z z)=ChiBoundedChain.payload n ell h A ν g hp T z := rfl

theorem residualTerm_diagonal (n : ℕ) (ell h : ℝ) (i : Fin (n+1)) (z : Space n) :
    residualTerm n ell h i (pack z z)=Rterm n ell h i z := rfl

theorem payload_contDiff (n k : ℕ) (ell h A ν g hp T : ℝ) :
    ContDiff ℝ k (payload n ell h A ν g hp T) :=
  ((chain_contDiff n k ell h).add
    ((positiveReceiver_contDiff A ν g h hp k).comp (targetProjection (Fin.last n)).contDiff)).add
    ((negativeReceiver_contDiff A g h T k).comp (targetProjection (Fin.last n)).contDiff)

theorem residualTerm_contDiff (n k : ℕ) (ell h : ℝ) (i : Fin (n+1)) :
    ContDiff ℝ k (residualTerm n ell h i) := by
  have hs := (selector_contDiff n k i).comp
    ((PartialLegendre.jointSndLinear : Latent n →L[ℝ] Space n).contDiff.const_smul h⁻¹)
  have hp := (ZeroChainPotential.phi_contDiff k).comp ((sourceProjection i).contDiff.const_smul h⁻¹)
  exact contDiff_const.mul (hs.neg.mul hp)

end Bilevel.ChiSplitChain
