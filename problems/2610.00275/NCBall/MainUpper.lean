import NCBall.ZerothUpper
import NCBall.FreshChord

/-! # Main local two-point upper bound

The radius and iteration parameters are functions of the problem parameters,
chosen before the unknown objective or sample functions. Each iteration uses
two scalar values of one fresh sample. A positive query radius is necessary
when the local gap is zero; see `ZeroRadius`.
-/

noncomputable section
open MeasureTheory Set Metric
namespace NCBall

def zerothRadius (δ Δ L R : ℝ) : ℝ :=
  if Δ = 0 then min δ R / 2 else upperSmoothRadius δ Δ L

def zerothConfig (n : ℕ) (δ Δ L ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεL : ε ≤ L) : UpperConfig :=
  if Δ = 0 then trivialUpperConfig else positiveZerothConfig n δ Δ L ε hδ hε hεL

theorem zerothRadius_pos {δ Δ L ε R : ℝ} (hδ : 0 < δ) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hεL : ε ≤ L) (hR : 0 < R) : 0 < zerothRadius δ Δ L R := by
  unfold zerothRadius
  split_ifs with hz
  · exact div_pos (lt_min hδ hR) (by norm_num)
  · exact upperSmoothRadius_pos hδ (lt_of_le_of_ne hΔ (Ne.symm hz)) (hε.trans_le hεL)

theorem zerothConfig_scalar_bound (n : ℕ) {δ Δ L ε : ℝ}
    (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hεL : ε ≤ L) :
    let c := zerothConfig n δ Δ L ε hδ hε hεL
    (2 * (c.K * c.m) : ℕ) ≤ 5800 * (1 + (n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) := by
  by_cases hz : Δ = 0
  · subst Δ
    norm_num [zerothConfig, trivialUpperConfig]
  · simpa only [zerothConfig, if_neg hz] using
      positiveZerothConfig_scalar_bound (n := n) hδ (lt_of_le_of_ne hΔ (Ne.symm hz)) hε hεL

theorem zeroth_order_local_success {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ] {f : CoordSpace (n + 1) → ℝ}
    {F : Ξ → CoordSpace (n + 1) → ℝ} {ℓ : Ξ → ℝ} {δ Δ L ε R : ℝ}
    (hs : LipschitzSampleModel μ f F ℓ L)
    (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hεL : ε ≤ L)
    (hRpos : 0 < R) (hR : 11 * Δ / ε ≤ R) (x₀ : CoordSpace (n + 1))
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    let c := zerothConfig n δ Δ L ε hδ hε hεL
    (2 * (c.K * c.m) : ℕ) ≤ 5800 * (1 + (n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) ∧
    ZerothGuarantee μ f F x₀ δ ε R (zerothRadius δ Δ L R)
      (zerothRadius_pos hδ hΔ hε hεL hRpos) c := by
  refine ⟨zerothConfig_scalar_bound n hδ hΔ hε hεL, ?_⟩
  by_cases hz : Δ = 0
  · subst Δ
    simpa only [zerothRadius, zerothConfig, if_pos rfl] using
      zero_gap_zeroth_guarantee hs hδ hRpos hε hεL x₀ hgap
  · simpa only [zerothRadius, zerothConfig, if_neg hz] using
      positive_zeroth_guarantee hs hδ (lt_of_le_of_ne hΔ (Ne.symm hz)) hε hεL hR x₀ hgap

end NCBall
