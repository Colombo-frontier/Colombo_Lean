import Nonsmooth.ConditionalMoments

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_weighted_condExp {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f z : Ω → ℝ} (hf : MemLp f 2 P) (hz : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[m] z P) :
    (∫ ω, z ω * f ω ∂P) = ∫ ω, z ω * (P[f | m]) ω ∂P := by
  letI : MeasurableSpace Ω := m₀
  simpa only [RCLike.inner_apply, conj_trivial] using integral_inner_condExp hm hf hz hzm

theorem unit_bounded_product_integrable {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hfb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ 1) (hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ 1) :
    Integrable (fun ω => f ω * g ω) P := by
  apply (integrable_const (1 : ℝ)).mono' (hf.mul hg)
  filter_upwards [hfb, hgb] with ω hfω hgω
  change ‖f ω * g ω‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul hfω hgω (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem unit_bounded_product_norm {f g : Ω → ℝ}
    (hfb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ 1) (hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ 1) :
    ∀ᵐ ω ∂P, ‖f ω * g ω‖ ≤ 1 := by
  filter_upwards [hfb, hgb] with ω hfω hgω
  rw [norm_mul]
  exact (mul_le_mul hfω hgω (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

/-- A bounded coefficient measurable from the history can be pulled out of an actual conditional
expectation. The proof uses L2 orthogonality on every measurable history event. -/
theorem condExp_bounded_coefficient {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f z : Ω → ℝ} (hf : AEStronglyMeasurable[m₀] f P)
    (hz : AEStronglyMeasurable[m] z P)
    (hfb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ 1) (hzb : ∀ᵐ ω ∂P, ‖z ω‖ ≤ 1) :
    (fun ω => z ω * (P[f | m]) ω) =ᵐ[P] P[(fun ω => z ω * f ω) | m] := by
  letI : MeasurableSpace Ω := m₀
  have hf2 : MemLp f 2 P := MemLp.of_bound hf 1 hfb
  have hzm := hz.mono hm
  have hc : AEStronglyMeasurable[m] (P[f | m]) P := stronglyMeasurable_condExp.aestronglyMeasurable
  have hcb : ∀ᵐ ω ∂P, ‖(P[f | m]) ω‖ ≤ 1 := condExp_norm_le_one hm hf hfb
  have hzi := unit_bounded_product_integrable hzm hf hzb hfb
  have hci := unit_bounded_product_integrable hzm (hc.mono hm) hzb hcb
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hzi (fun _ _ _ => hci.integrableOn)
  · intro s hs _
    let zs : Ω → ℝ := s.indicator z
    have hzsm : AEStronglyMeasurable[m] zs P := by
      apply (hz.stronglyMeasurable_mk.indicator hs).aestronglyMeasurable.congr
      filter_upwards [hz.ae_eq_mk] with ω hω
      by_cases hmem : ω ∈ s
      · simp [zs, Set.indicator_of_mem hmem, hω]
      · simp [zs, Set.indicator_of_notMem hmem]
    have hzsb : ∀ᵐ ω ∂P, ‖zs ω‖ ≤ 1 := by
      filter_upwards [hzb] with ω hω
      by_cases hmem : ω ∈ s
      · simpa only [zs, Set.indicator_of_mem hmem] using hω
      · simp [zs, Set.indicator_of_notMem hmem]
    have hzs2 : MemLp zs 2 P := MemLp.of_bound (hzsm.mono hm) 1 hzsb
    have h := integral_weighted_condExp hm hf2 hzs2 hzsm
    have he (g : Ω → ℝ) : (fun ω => zs ω * g ω) = s.indicator (fun ω => z ω * g ω) := by
      funext ω
      by_cases hmem : ω ∈ s
      · simp [zs, Set.indicator_of_mem hmem]
      · simp [zs, Set.indicator_of_notMem hmem]
    rw [he f, he (P[f | m]), integral_indicator (hm s hs), integral_indicator (hm s hs)] at h
    exact h.symm
  · exact hz.mul hc

/-- Finite-dimensional isotropic conditional covariance remains valid for bounded coefficients
chosen from the history. This is the algebraic step needed for an adaptive test direction. -/
theorem condExp_quadratic_of_scalar_covariance {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r c : ι → Ω → ℝ) (a : Ω → ℝ)
    (hrm : ∀ i, AEStronglyMeasurable[m₀] (r i) P)
    (hcm : ∀ i, AEStronglyMeasurable[m] (c i) P)
    (hrb : ∀ i, ∀ᵐ ω ∂P, ‖r i ω‖ ≤ 1) (hcb : ∀ i, ∀ᵐ ω ∂P, ‖c i ω‖ ≤ 1)
    (hcov : ∀ i j, P[(fun ω => r i ω * r j ω) | m] =ᵐ[P] if i = j then a else 0) :
    (fun ω => a ω * ∑ i, c i ω ^ 2) =ᵐ[P]
      P[(fun ω => (∑ i, c i ω * r i ω) ^ 2) | m] := by
  letI : MeasurableSpace Ω := m₀
  let F : (ι × ι) → Ω → ℝ := fun ij ω =>
    (c ij.1 ω * c ij.2 ω) * (r ij.1 ω * r ij.2 ω)
  have hFi (ij : ι × ι) : Integrable (F ij) P :=
    unit_bounded_product_integrable (((hcm ij.1).mono hm).mul ((hcm ij.2).mono hm))
      ((hrm ij.1).mul (hrm ij.2))
      (unit_bounded_product_norm (hcb ij.1) (hcb ij.2))
      (unit_bounded_product_norm (hrb ij.1) (hrb ij.2))
  have hterm (ij : ι × ι) : P[F ij | m] =ᵐ[P]
      (fun ω => if ij.1 = ij.2 then a ω * c ij.1 ω ^ 2 else 0) := by
    have hp := condExp_bounded_coefficient hm
      (f := fun ω => r ij.1 ω * r ij.2 ω) (z := fun ω => c ij.1 ω * c ij.2 ω)
      ((hrm ij.1).mul (hrm ij.2))
      ((hcm ij.1).mul (hcm ij.2))
      (unit_bounded_product_norm (hrb ij.1) (hrb ij.2))
      (unit_bounded_product_norm (hcb ij.1) (hcb ij.2))
    filter_upwards [hp, hcov ij.1 ij.2] with ω hpω hcovω
    change P[(fun ω => (c ij.1 ω * c ij.2 ω) * (r ij.1 ω * r ij.2 ω)) | m] ω = _
    rw [← hpω, hcovω]
    by_cases hij : ij.1 = ij.2
    · simp [hij, pow_two, mul_comm, mul_left_comm, mul_assoc]
    · simp [hij]
  have hpoly : (fun ω => (∑ i, c i ω * r i ω) ^ 2) = ∑ ij : ι × ι, F ij := by
    funext ω
    simp only [Finset.sum_apply, Fintype.sum_prod_type, F]
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpoly]
  have hsum := condExp_finset_sum (s := Finset.univ) (fun ij _ => hFi ij) m
  have hall : ∀ᵐ ω ∂P, ∀ ij : ι × ι, P[F ij | m] ω =
      (if ij.1 = ij.2 then a ω * c ij.1 ω ^ 2 else 0) := ae_all_iff.mpr hterm
  filter_upwards [hsum, hall] with ω hsω hallω
  rw [hsω]
  simp only [Finset.sum_apply]
  simp [hallω, Fintype.sum_prod_type, ← Finset.mul_sum]

end
end Nonsmooth
