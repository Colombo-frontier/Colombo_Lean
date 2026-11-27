import Nonsmooth.SupportPosteriorKernel

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

theorem finiteSupport_dominates_sum (a : Fin k → E) (x : E) :
    ⟪∑ i, a i, x⟫_ℝ ≤ (k : ℝ) * finiteSupport a x := by
  rw [sum_inner]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => finiteSupport_ge a x i)

theorem bounded_inner_memLp {α : Type} [MeasurableSpace α] {Q : Measure α} [IsProbabilityMeasure Q]
    {V X : α → E} (hV : MemLp V 2 Q) (hX : AEStronglyMeasurable X Q)
    (hXb : ∀ a, ‖X a‖ ≤ 1) : MemLp (fun a => ⟪V a, X a⟫_ℝ) 2 Q := by
  apply MemLp.mono' hV.norm (hV.aestronglyMeasurable.inner hX) (Eventually.of_forall (fun a => ?_))
  exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (V a), hXb a])

theorem inner_square_le_norm_square {u x : E} (hx : ‖x‖ ≤ 1) : ⟪u, x⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 := by
  have h : |⟪u, x⟫_ℝ| ≤ ‖u‖ := (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg u])
  have hs := mul_self_le_mul_self (abs_nonneg ⟪u, x⟫_ℝ) h
  simpa only [← sq, sq_abs] using hs

/-- A quantitative reduction to the actual conditional-mean energy and output-direction
residual second moment. Both numerical estimates are explicit hypotheses. -/
theorem posterior_support_output_tail (hk : 0 < k) (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    {m : MeasurableSpace (Fin k → E)} (hm : m ≤ MeasurableSpace.pi)
    (X : (Fin k → E) → E) (hX : AEStronglyMeasurable[m] X Q) (hXb : ∀ a, ‖X a‖ ≤ 1)
    (hS : MemLp (fun a : Fin k → E => ∑ i, a i) 2 Q) {e v : ℝ}
    (henergy : (∫ a, ‖(Q[fun b => ∑ i, b i | m]) a‖ ^ 2 ∂Q) ≤ e)
    (hresidual : (∫ a, ⟪(∑ i, a i) - (Q[fun b => ∑ i, b i | m]) a, X a⟫_ℝ ^ 2 ∂Q) ≤ v) :
    Q.real {a | finiteSupport a (X a) < -((1 : ℝ) / (8 * Real.sqrt k))} ≤
      128 * (e + v) / k := by
  letI : MeasurableSpace (Fin k → E) := MeasurableSpace.pi
  let M := Q[fun b : Fin k → E => ∑ i, b i | m]
  have hM : MemLp M 2 Q := hS.condExp (by norm_num)
  have hSi := (bounded_inner_memLp hS (hX.mono hm) hXb).integrable_sq
  have hRi := (bounded_inner_memLp (hS.sub hM) (hX.mono hm) hXb).integrable_sq
  have hMi := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mp hM
  have hpoint (a : Fin k → E) : ⟪∑ i, a i, X a⟫_ℝ ^ 2 ≤
      2 * ‖M a‖ ^ 2 + 2 * ⟪(∑ i, a i) - M a, X a⟫_ℝ ^ 2 := by
    have hs := inner_square_le_norm_square (u := M a) (hXb a)
    have he : ⟪(∑ i, a i) - M a, X a⟫_ℝ = ⟪∑ i, a i, X a⟫_ℝ - ⟪M a, X a⟫_ℝ := inner_sub_left _ _ _
    rw [he]
    nlinarith [sq_nonneg (⟪∑ i, a i, X a⟫_ℝ - 2 * ⟪M a, X a⟫_ℝ)]
  have hRi' : Integrable (fun a : Fin k → E => ⟪(∑ i, a i) - M a, X a⟫_ℝ ^ 2) Q := hRi
  have hmoment : (∫ a, ⟪∑ i, a i, X a⟫_ℝ ^ 2 ∂Q) ≤ 2 * e + 2 * v := by
    have h := integral_mono hSi ((hMi.const_mul 2).add (hRi'.const_mul 2)) hpoint
    dsimp only [Pi.add_apply] at h
    rw [integral_add (hMi.const_mul 2) (hRi'.const_mul 2), integral_const_mul, integral_const_mul] at h
    change (∫ a, ‖M a‖ ^ 2 ∂Q) ≤ e at henergy
    change (∫ a, ⟪(∑ i, a i) - M a, X a⟫_ℝ ^ 2 ∂Q) ≤ v at hresidual
    linarith
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk'
  have hs2 : (Real.sqrt (k : ℝ)) ^ 2 = k := Real.sq_sqrt hk'.le
  have hsub : {a : Fin k → E | finiteSupport a (X a) < -((1 : ℝ) / (8 * Real.sqrt k))} ⊆
      {a | (k : ℝ) / 64 ≤ ⟪∑ i, a i, X a⟫_ℝ ^ 2} := by
    intro a ha
    have hsup := finiteSupport_dominates_sum a (X a)
    have hmul := mul_lt_mul_of_pos_left ha hk'
    have he : (k : ℝ) * -((1 : ℝ) / (8 * Real.sqrt k)) = -(Real.sqrt k / 8) := by
      field_simp
      nlinarith [hs2]
    rw [he] at hmul
    change (k : ℝ) / 64 ≤ ⟪∑ i, a i, X a⟫_ℝ ^ 2
    nlinarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := Q)
    (f := fun a : Fin k → E => ⟪∑ i, a i, X a⟫_ℝ ^ 2)
    (Eventually.of_forall (fun _ => sq_nonneg _)) hSi ((k : ℝ) / 64)
  have hprob := mul_le_mul_of_nonneg_left (measureReal_mono (μ := Q) hsub (measure_ne_top _ _))
    (by positivity : (0 : ℝ) ≤ (k : ℝ) / 64)
  apply (le_div_iff₀ hk').mpr
  nlinarith

end
end Nonsmooth
