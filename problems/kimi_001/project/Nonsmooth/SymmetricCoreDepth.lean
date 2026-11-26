import Nonsmooth.HalfspaceDepthAsymmetry
import Mathlib.Analysis.LocallyConvex.Separation

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem neg_scaled_mem_of_quarter_depth {K : Set E} (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hzero : (0 : E) ∈ K) (hK0 : volume K ≠ 0)
    (hdepth : ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | 0 ≤ ℓ z}))
    {x : E} (hx : x ∈ K) : (-(1 / (4 * (Module.finrank ℝ E : ℝ)))) • x ∈ K := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℝ E)
  by_contra hout
  obtain ⟨ℓ, u, hbound, hlt⟩ := geometric_hahn_banach_closed_point hconv hcompact.isClosed hout
  have hu : 0 < u := by simpa using hbound 0 hzero
  have hℓ : ℓ ≠ 0 := by
    intro hz
    simp only [hz, ContinuousLinearMap.zero_apply] at hlt
    linarith
  have hlarge : 4 * (Module.finrank ℝ E : ℝ) * u < -ℓ x := by
    simp only [map_smul, smul_eq_mul] at hlt
    have heq : -(1 / (4 * (Module.finrank ℝ E : ℝ))) * ℓ x =
        (-ℓ x) / (4 * (Module.finrank ℝ E : ℝ)) := by ring
    rw [heq] at hlt
    have h := (lt_div_iff₀ (show 0 < 4 * (Module.finrank ℝ E : ℝ) by positivity)).mp hlt
    nlinarith
  have ha : 0 ≤ -ℓ x := by nlinarith
  have h := halfspace_depth_scalar_asymmetry hconv hcompact.measurableSet hK0
    hcompact.measure_lt_top.ne ℓ hℓ hx ha hu (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by ring : ℓ x = -(-ℓ x)) (fun z hz => (hbound z hz).le) (hdepth ℓ hℓ)
  nlinarith

/-- The symmetric part of a centered convex body. -/
def symmetricCore (K : Set E) : Set E := K ∩ {x | -x ∈ K}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem symmetricCore_neg_mem {K : Set E} {x : E} (hx : x ∈ symmetricCore K) :
    -x ∈ symmetricCore K := by
  exact ⟨hx.2, by simpa using hx.1⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem symmetricCore_convex {K : Set E} (hK : Convex ℝ K) : Convex ℝ (symmetricCore K) := by
  exact hK.inter (hK.linear_preimage (-LinearMap.id : E →ₗ[ℝ] E))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem symmetricCore_compact {K : Set E} (hK : IsCompact K) : IsCompact (symmetricCore K) := by
  exact hK.inter_right (hK.isClosed.preimage continuous_neg)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem symmetricCore_contains_ball {K : Set E} {r : ℝ}
    (hinner : Metric.closedBall (0 : E) r ⊆ K) :
    Metric.closedBall (0 : E) r ⊆ symmetricCore K := by
  intro x hx
  exact ⟨hinner hx, hinner (by simpa using hx)⟩

theorem quarter_depth_symmetric_core_sandwich {K : Set E} (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hzero : (0 : E) ∈ K) (hK0 : volume K ≠ 0)
    (hdepth : ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume K ≤ volume (K ∩ {z | 0 ≤ ℓ z})) :
    symmetricCore K ⊆ K ∧ K ⊆
      (fun z => (4 * (Module.finrank ℝ E : ℝ)) • z) '' symmetricCore K := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx
  have hd : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℝ E)
  have hdp : (0 : ℝ) < 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨(1 / (4 * (Module.finrank ℝ E : ℝ))) • x, ⟨?_, ?_⟩, ?_⟩
  · exact hconv.smul_mem_of_zero_mem hzero hx ⟨by positivity, (div_le_one hdp).mpr (by linarith)⟩
  · simpa only [mem_setOf_eq, neg_smul] using neg_scaled_mem_of_quarter_depth hconv hcompact hzero hK0 hdepth hx
  · dsimp only
    rw [smul_smul, mul_one_div_cancel hdp.ne', one_smul]

end
end Nonsmooth
