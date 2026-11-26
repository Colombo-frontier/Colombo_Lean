import NCConcave16991.SaddleOperator
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Actual maximizing multipliers satisfy the dual variational inequality -/

namespace NCConcave16991

noncomputable section

open Set InnerProductSpace
open scoped InnerProductSpace

theorem maximizer_hasGradientAt_vi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {s : Set E} {f : E → ℝ} {g y : E}
    (hs : Convex ℝ s) (hy : y ∈ s) (hmax : IsMaxOn f s y) (hg : HasGradientAt f g y)
    (z : E) (hz : z ∈ s) : ⟪g, z - y⟫_ℝ ≤ 0 := by
  have ht : z - y ∈ posTangentConeAt s y :=
    sub_mem_posTangentConeAt_of_openSegment_subset ((openSegment_subset_segment ℝ y z).trans
      (hs.segment_subset hy hz))
  have hh := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hg.hasFDerivAt.hasFDerivWithinAt ht
  exact hh

namespace Problem

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- A genuine maximizing dual point supplies the actual dual-gradient VI,
without an interiority or value-differentiability premise. -/
theorem maximizing_dual_vi (P : Problem p dx dy K) (x : PrimalSpace dx) (y : DualSpace dy)
    (hy : y ∈ K.carrier)
    (hmax : ∀ v ∈ K.carrier,
      componentAverage P.component (jointPoint x v) ≤ componentAverage P.component (jointPoint x y))
    (v : DualSpace dy) (hv : v ∈ K.carrier) :
    ⟪(averageMap P.componentGradient (jointPoint x y)).snd, v - y⟫_ℝ ≤ 0 :=
  maximizer_hasGradientAt_vi K.convex hy hmax (P.hasGradientAt_dual_section x y hy) v hv

theorem maximizing_dual_vi_of_value_eq (P : Problem p dx dy K) (x : PrimalSpace dx) (y : DualSpace dy)
    (hy : y ∈ K.carrier)
    (hyval : componentAverage P.component (jointPoint x y) = primalObjective K P.component x)
    (v : DualSpace dy) (hv : v ∈ K.carrier) :
    ⟪(averageMap P.componentGradient (jointPoint x y)).snd, v - y⟫_ℝ ≤ 0 := by
  apply P.maximizing_dual_vi x y hy _ v hv
  intro w hw
  rw [hyval]
  exact componentAverage_le_primalObjective P x w hw

theorem maximizing_dual_zero_inner (P : Problem p dx dy K) (x : PrimalSpace dx) (y : DualSpace dy)
    (hy : y ∈ K.carrier) (hzero : (0 : DualSpace dy) ∈ K.carrier)
    (hyval : componentAverage P.component (jointPoint x y) = primalObjective K P.component x) :
    0 ≤ ⟪(averageMap P.componentGradient (jointPoint x y)).snd, y⟫_ℝ := by
  have hh := P.maximizing_dual_vi_of_value_eq x y hy hyval 0 hzero
  rw [zero_sub, inner_neg_right] at hh
  linarith

end Problem

end

end NCConcave16991
