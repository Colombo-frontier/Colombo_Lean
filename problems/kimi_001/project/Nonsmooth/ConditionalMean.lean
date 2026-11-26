import Nonsmooth.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- A transcript-measurable output pairs identically with a random vector and its actual
conditional expectation. This follows from the L2 projection theorem. -/
theorem integral_inner_condExp {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {V X : Ω → E} (hV : MemLp V 2 P) (hX : MemLp X 2 P)
    (hXm : AEStronglyMeasurable[m] X P) :
    (∫ ω, ⟪V ω, X ω⟫_ℝ ∂P) = ∫ ω, ⟪(P[V | m]) ω, X ω⟫_ℝ ∂P := by
  have hX' : AEStronglyMeasurable[m] (hX.toLp X) P :=
    hXm.congr hX.coeFn_toLp.symm
  have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm (hV.toLp V) (hX.toLp X) hX'
  change (∫ ω, ⟪(condExpL2 E ℝ hm (hV.toLp V) : Ω →₂[P] E) ω, (hX.toLp X) ω⟫_ℝ ∂P) =
    ∫ ω, ⟪(hV.toLp V) ω, (hX.toLp X) ω⟫_ℝ ∂P at h
  calc
    _ = ∫ ω, ⟪(hV.toLp V) ω, (hX.toLp X) ω⟫_ℝ ∂P := by
      apply integral_congr_ae
      filter_upwards [hV.coeFn_toLp, hX.coeFn_toLp] with ω hVω hXω
      rw [hVω, hXω]
    _ = ∫ ω, ⟪(condExpL2 E ℝ hm (hV.toLp V) : Ω →₂[P] E) ω, (hX.toLp X) ω⟫_ℝ ∂P := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hV.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm, hX.coeFn_toLp]
        with ω hmω hXω
      rw [hmω, hXω]

theorem integrable_inner_of_memLp {V X : Ω → E} (hV : MemLp V 2 P)
    (hX : MemLp X 2 P) : Integrable (fun ω => ⟪V ω, X ω⟫_ℝ) P := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hV.toLp V) (hX.toLp X)).congr
  filter_upwards [hV.coeFn_toLp, hX.coeFn_toLp] with ω hVω hXω
  rw [hVω, hXω]

/-- Conditional expectations of unit-ball-valued vectors remain in the unit ball.
The proof tests the L2 projection against a measurable outward unit direction. -/
theorem condExp_norm_le_one {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {V : Ω → E} (hV : AEStronglyMeasurable[m₀] V P)
    (hVb : ∀ᵐ ω ∂P, ‖V ω‖ ≤ 1) : ∀ᵐ ω ∂P, ‖(P[V | m]) ω‖ ≤ 1 := by
  let M : Ω → E := P[V | m]
  have hM : StronglyMeasurable[m] M := stronglyMeasurable_condExp
  have hV2 : MemLp V 2 P := MemLp.of_bound hV 1 hVb
  have hM2 : MemLp M 2 P := MemLp.condExp (by norm_num) hV2
  let A : Set Ω := {ω | 1 < ‖M ω‖}
  have hA : MeasurableSet[m] A := measurableSet_lt measurable_const hM.norm.measurable
  let B : Ω → E := A.indicator (fun ω => ‖M ω‖⁻¹ • M ω)
  have hB : StronglyMeasurable[m] B :=
    (hM.norm.measurable.inv.stronglyMeasurable.smul hM).indicator hA
  have hBn (ω : Ω) : ‖B ω‖ ≤ 1 := by
    by_cases hω : ω ∈ A
    · have hpos : 0 < ‖M ω‖ := lt_trans (by norm_num) hω
      simp [B, Set.indicator_of_mem hω, norm_smul, hpos.ne']
    · simp [B, Set.indicator_of_notMem hω]
  have hB2 : MemLp B 2 P := MemLp.of_bound (hB.mono hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall hBn)
  have hmean := integral_inner_condExp hm hV2 hB2 hB.aestronglyMeasurable
  have hiV := integrable_inner_of_memLp hV2 hB2
  have hiM := integrable_inner_of_memLp hM2 hB2
  have hinner (ω : Ω) (hω : ω ∈ A) : ⟪M ω, B ω⟫_ℝ = ‖M ω‖ := by
    have hpos : 0 < ‖M ω‖ := lt_trans (by norm_num) hω
    simp only [B, Set.indicator_of_mem hω, inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
    <;> ring
  have hbound (ω : Ω) (hω : ‖V ω‖ ≤ 1) : ⟪V ω, B ω⟫_ℝ ≤ 1 := by
    have hn := real_inner_le_norm (V ω) (B ω)
    have hmul := mul_le_mul hω (hBn ω) (norm_nonneg (B ω)) (by norm_num : (0 : ℝ) ≤ 1)
    exact hn.trans (by simpa using hmul)
  have hnon : ∀ᵐ ω ∂P, 0 ≤ ⟪M ω, B ω⟫_ℝ - ⟪V ω, B ω⟫_ℝ := by
    filter_upwards [hVb] with ω hVω
    by_cases hω : ω ∈ A
    · rw [hinner ω hω]
      have hnorm : 1 < ‖M ω‖ := hω
      linarith [hbound ω hVω]
    · simp [B, Set.indicator_of_notMem hω]
  have hzero : (∫ ω, ⟪M ω, B ω⟫_ℝ - ⟪V ω, B ω⟫_ℝ ∂P) = 0 := by
    rw [integral_sub hiM hiV]
    change (∫ ω, ⟪(P[V | m]) ω, B ω⟫_ℝ ∂P) - (∫ ω, ⟪V ω, B ω⟫_ℝ ∂P) = 0
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnon (hiM.sub hiV)).mp hzero
  filter_upwards [hae, hVb] with ω hω hVω
  change ‖M ω‖ ≤ 1
  by_contra hnot
  have hmem : ω ∈ A := by change 1 < ‖M ω‖; exact lt_of_not_ge hnot
  have hnorm : 1 < ‖M ω‖ := hmem
  change ⟪M ω, B ω⟫_ℝ - ⟪V ω, B ω⟫_ℝ = 0 at hω
  rw [hinner ω hmem] at hω
  linarith [hbound ω hVω]

theorem integral_norm_sq_toLp {V : Ω → E} (hV : MemLp V 2 P) :
    (∫ ω, ‖V ω‖ ^ 2 ∂P) = ‖hV.toLp V‖ ^ 2 := by
  calc
    _ = ∫ ω, ⟪(hV.toLp V) ω, (hV.toLp V) ω⟫_ℝ ∂P := by
      apply integral_congr_ae
      filter_upwards [hV.coeFn_toLp] with ω hω
      rw [hω, real_inner_self_eq_norm_sq]
    _ = _ := (L2.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _)

theorem condExp_second_moment_le {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {V : Ω → E} (hV : MemLp V 2 P) :
    (∫ ω, ‖(P[V | m]) ω‖ ^ 2 ∂P) ≤ ∫ ω, ‖V ω‖ ^ 2 ∂P := by
  letI : MeasurableSpace Ω := m₀
  have hc := norm_condExpL2_coe_le (𝕜 := ℝ) hm (hV.toLp V)
  have heq : (∫ ω, ‖(P[V | m]) ω‖ ^ 2 ∂P) =
      ‖(condExpL2 E ℝ hm (hV.toLp V) : Ω →₂[P] E)‖ ^ 2 := by
    calc
      _ = ∫ ω, ⟪(condExpL2 E ℝ hm (hV.toLp V) : Ω →₂[P] E) ω,
          (condExpL2 E ℝ hm (hV.toLp V) : Ω →₂[P] E) ω⟫_ℝ ∂P := by
        apply integral_congr_ae
        filter_upwards [hV.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm] with ω hω
        rw [hω, real_inner_self_eq_norm_sq]
      _ = _ := (L2.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _)
  rw [heq, integral_norm_sq_toLp hV]
  exact pow_le_pow_left₀ (norm_nonneg _) hc 2

/-- Enlarging the transcript can only increase conditional-mean energy. -/
theorem condExp_second_moment_mono {m n : MeasurableSpace Ω} (hmn : m ≤ n)
    (hn : n ≤ m₀) {V : Ω → E} (hV : MemLp V 2 P) :
    (∫ ω, ‖(P[V | m]) ω‖ ^ 2 ∂P) ≤ ∫ ω, ‖(P[V | n]) ω‖ ^ 2 ∂P := by
  letI : MeasurableSpace Ω := m₀
  have h := condExp_second_moment_le (hmn.trans hn) (MemLp.condExp (m := n) (by norm_num) hV)
  have heq : (∫ ω, ‖(P[P[V | n] | m]) ω‖ ^ 2 ∂P) =
      ∫ ω, ‖(P[V | m]) ω‖ ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [condExp_condExp_of_le hmn hn (f := V) (μ := P)] with ω hω
    rw [hω]
  rwa [heq] at h

end
end Nonsmooth
