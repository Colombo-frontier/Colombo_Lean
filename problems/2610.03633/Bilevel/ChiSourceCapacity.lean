import Bilevel.ChiSourceReleaseCounter
import Bilevel.ChiUniformEncodedCount

/-! The success-driven compiler's stopping threshold is exactly the
manuscript's encoded activation count, not an independent asymptotic proxy. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiTreeProgress

theorem capacity_eq_product (counts : ℕ → ℕ) (d j : ℕ) :
    capacity counts d j=∏ k ∈ Finset.range (d+1),(counts (j+k)+1) := by
  induction d generalizing j with
  | zero => simp [capacity]
  | succ d ih =>
    rw [capacity,ih]
    conv_rhs => rw [Finset.prod_range_succ']
    simp only [Nat.add_zero]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    congr 2
    omega

open ChiIndependentWidths ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtensionCalibration

theorem source_capacity_encoded {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (macroN J : ℕ) (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (A Kminus ζ cn CR Km : ℝ) (U : Space macroN →ₗᵢ[ℝ] E)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] F)
    (path : ℕ → List ℕ) :
    capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0=
      encodedCount (ChiOuter.sourceMacroNode macroN initial Km U)
        (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR V) J path := by
  rw [capacity,capacity_eq_product]
  simp only [Nat.zero_add,show ∀ k : ℕ,1+k=k+1 from fun _ => Nat.add_comm _ _]
  simp only [sourceCounts,encodedCount,ChiOuter.sourceMacroNode,sourceGeometry,ChiRecursive.sourceNode]

theorem source_capacity_activation {cS cn Δ L₀ b h η T : ℝ}
    (hcn : 0≤cn) (hb : 0<b) (hh : 0<h) (hT : 1≤T) (hlen : 128≤cn/η^2)
    (hS : 1≤macroLength cS Δ L₀ b) (hn : 1≤middleLength cn b h) (J : ℕ) :
    capacity (sourceCounts (macroLength cS Δ L₀ b-1) cn (sourceRatio T) (resolution η (b/h))) (J+1) 0=
      activationCount cS cn Δ L₀ b h η T J := by
  rw [capacity,capacity_eq_product]
  simp only [Nat.zero_add,show ∀ k : ℕ,1+k=k+1 from fun _ => Nat.add_comm _ _]
  change (macroLength cS Δ L₀ b-1+1)*sourceIndexCount cn η T (b/h) J=_
  rw [show macroLength cS Δ L₀ b-1+1=macroLength cS Δ L₀ b by omega,
    ←activationCount_source_indices hcn hb hh hT hlen hn]

end Bilevel.ChiTreeProgress
