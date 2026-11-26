import Bilevel.WrappedChainConstants
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-! Coercivity, attainment, and the actual finite initial gap of the wrapper. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem bowl_nonnegative (ν R : ℝ) (hν : 0 ≤ ν) (u : E) : 0 ≤ bowl ν R u := by
  have hs : 1 ≤ Real.sqrt (1 + ‖u‖ ^ 2 / R ^ 2) :=
    Real.one_le_sqrt.mpr (by
      have h : 0 ≤ ‖u‖ ^ 2 / R ^ 2 := by positivity
      linarith)
  exact mul_nonneg (mul_nonneg hν (sq_nonneg R)) (sub_nonneg.mpr hs)

omit [InnerProductSpace ℝ E] in
theorem bowl_linear_lower (ν R : ℝ) (hν : 0 ≤ ν) (hR : 0 < R) (u : E) :
    ν * R * ‖u‖ - ν * R ^ 2 ≤ bowl ν R u := by
  have hs := Real.sqrt_le_sqrt (show ‖u‖ ^ 2 / R ^ 2 ≤ 1 + ‖u‖ ^ 2 / R ^ 2 by linarith)
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hR.le] at hs
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hν (sq_nonneg R))
  have he : ν * R ^ 2 * (‖u‖ / R) = ν * R * ‖u‖ := by field_simp; ring
  rw [he] at hm
  dsimp [bowl]
  nlinarith

theorem wrapped_coercive [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ν R c : ℝ) (hν : 0 < ν) (hR : 0 < R) (H : Z → ℝ)
    (hH : ∀ z, c ≤ H z) (projection : E →L[ℝ] Z) :
    Tendsto (wrapped ν R H projection) (cocompact E) atTop := by
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_norm_cocompact_atTop (E := E)).eventually_ge_atTop
    ((b - c + ν * R ^ 2) / (ν * R))
  filter_upwards [hn] with u hu
  have hr := (div_le_iff₀ (mul_pos hν hR)).mp hu
  have hb := bowl_linear_lower ν R hν.le hR u
  have hc := hH (projection (compress R u))
  dsimp [wrapped]
  nlinarith

end Bilevel.RadialWrapper
namespace Bilevel.WrappedChain
open ZeroChain RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem value_zero (n : ℕ) (a β ν R : ℝ) (U : Space n →ₗᵢ[ℝ] E) :
    value n a β ν R U 0 = ScaledZeroChain.value n a β 0 := by
  simp [value, wrapped, compress, bowl]

theorem pointwise_gap (n : ℕ) (a β ν R : ℝ) (ha : 0 ≤ a) (hν : 0 ≤ ν)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    value n a β ν R U 0 - value n a β ν R U u ≤
      a * ((1 + 2 * Real.exp 1) * phiBound * (n + 1 : ℕ)) := by
  rw [value_zero]
  have hc := ScaledZeroChain.initial_gap_bound n a β ha (coordinates n R U u)
  have hb := bowl_nonnegative ν R hν u
  change ScaledZeroChain.value n a β 0 -
    (ScaledZeroChain.value n a β (coordinates n R U u) + bowl ν R u) ≤ _
  linarith

theorem coercive [FiniteDimensional ℝ E]
    (n : ℕ) (a β ν R : ℝ) (ha : 0 ≤ a) (hν : 0 < ν) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) : Tendsto (value n a β ν R U) (cocompact E) atTop := by
  apply wrapped_coercive ν R
    (ScaledZeroChain.value n a β 0 - a * ((1 + 2 * Real.exp 1) * phiBound * (n + 1 : ℕ)))
    hν hR (ScaledZeroChain.value n a β) ?_ U.toContinuousLinearMap.adjoint
  intro z
  linarith [ScaledZeroChain.initial_gap_bound n a β ha z]

theorem continuous (n : ℕ) (a β ν R : ℝ) (hR : 0 < R) (U : Space n →ₗᵢ[ℝ] E) :
    Continuous (value n a β ν R U) :=
  continuous_iff_continuousAt.mpr (fun u => (value_hasGradientAt n a β ν R hR U u).hasFDerivAt.continuousAt)

theorem minimum_attained [FiniteDimensional ℝ E]
    (n : ℕ) (a β ν R : ℝ) (ha : 0 ≤ a) (hν : 0 < ν) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) : ∃ u, ∀ v, value n a β ν R U u ≤ value n a β ν R U v :=
  (continuous n a β ν R hR U).exists_forall_le (coercive n a β ν R ha hν hR U)

theorem gap_to_infimum [FiniteDimensional ℝ E]
    (n : ℕ) (a β ν R : ℝ) (ha : 0 ≤ a) (hν : 0 < ν) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) :
    value n a β ν R U 0 - sInf (Set.range (value n a β ν R U)) ≤
      a * ((1 + 2 * Real.exp 1) * phiBound * (n + 1 : ℕ)) := by
  obtain ⟨u, hu⟩ := minimum_attained n a β ν R ha hν hR U
  have hi : sInf (Set.range (value n a β ν R U)) = value n a β ν R U u := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨value n a β ν R U u, by rintro _ ⟨v, rfl⟩; exact hu v⟩
      · exact ⟨u, rfl⟩
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨v, rfl⟩
      exact hu v
  rw [hi]
  exact pointwise_gap n a β ν R ha hν.le U u

end Bilevel.WrappedChain
