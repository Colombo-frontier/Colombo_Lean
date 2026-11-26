import Bilevel.ChiUniformActivationLengths
import Bilevel.ChiOuterSourceBarrier

/-! The activation count is exactly the product of the actual encoded
coordinate lengths. Each `Space n` has `n+1` coordinates. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiIndependentWidths
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtensionCalibration ChiOuter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def encodedCount (M : Node E) (D : Geometry F) (J : ℕ) (path : ℕ → List ℕ) : ℕ :=
  (M.n+1)*(∏ j ∈ Finset.range (J+1),((D j (path j)).n+1))

omit [CompleteSpace F] in
theorem source_encoded_count {cS cn Δ L₀ b h η T : ℝ}
    (hcn : 0≤cn) (hb : 0<b) (hh : 0<h) (hT : 1≤T) (hlen : 128≤cn/η^2)
    (hS : 1≤macroLength cS Δ L₀ b) (hn : 1≤middleLength cn b h)
    (A Kminus ζ CR Km : ℝ) (weight : ℕ → ℝ) (J : ℕ) (path : ℕ → List ℕ)
    (U : Space (macroLength cS Δ L₀ b-1) →ₗᵢ[ℝ] E)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (b/h) j)) →ₗᵢ[ℝ] F) :
    encodedCount (sourceMacroNode (macroLength cS Δ L₀ b-1) ⟨L₀,b⟩ Km U)
      (sourceGeometry ⟨L₀,b⟩ (sourceRatio T) (resolution η (b/h)) weight A Kminus ζ cn CR V) J path=
      activationCount cS cn Δ L₀ b h η T J := by
  have hs : macroLength cS Δ L₀ b-1+1=macroLength cS Δ L₀ b := by omega
  change (macroLength cS Δ L₀ b-1+1)*sourceIndexCount cn η T (b/h) J= _
  rw [hs,activationCount_source_indices hcn hb hh hT hlen hn]

end Bilevel.ChiIndependentWidths
