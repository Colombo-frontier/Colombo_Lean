import Bilevel.ChiSplitFineScaled
import Bilevel.ChiFineScaled

/-! Exact source-only flattening and diagonal identities. All selectors remain
functions of the predecessor endpoint, including after flattening. -/
noncomputable section
namespace Bilevel.ChiSplitFine
open ChiBoundedChain PrimitiveGeometry

theorem flattened_eq_source_composition (n : ℕ) (δ : ℝ) (z : Latent n) :
    flattened n δ z=ChiSplitChain.frontier n
      (pack (ZeroChainFlatteningMap.flattenMap n δ z.fst) z.snd) := by
  rw [frontier_eq_selected]
  unfold flattened selected
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem flattened_diagonal (n : ℕ) (δ : ℝ) (z : Space n) :
    flattened n δ (pack z z)=ChiFine.flattened n δ z := rfl

theorem frontier_diagonal (n : ℕ) (ell β : ℝ) (z : Space n) :
    frontier n ell β (pack z z)=ChiFine.frontier n ell β z := rfl

theorem flatFrontier_diagonal (n : ℕ) (ell β δ : ℝ) (z : Space n) :
    flatFrontier n ell β δ (pack z z)=ChiFine.flatFrontier n ell β δ z := rfl

end Bilevel.ChiSplitFine
