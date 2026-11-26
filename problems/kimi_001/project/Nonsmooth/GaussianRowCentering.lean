import Nonsmooth.GaussianRowsCharacteristic

open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def supportRowMean {k : ℕ} (b : Fin k → E) : E := (k : ℝ)⁻¹ • ∑ i, b i

def centeredSupportRows {k : ℕ} (b : Fin k → E) : Fin k → E := fun i => b i - supportRowMean b

def gaussianRowsRecombine {k : ℕ} (z : (Fin k → E) × E) : Fin k → E :=
  fun i => centeredSupportRows z.1 i + (Real.sqrt k)⁻¹ • z.2

theorem supportRowMean_continuous (k : ℕ) : Continuous (supportRowMean (E := E) (k := k)) :=
  continuous_const.smul (continuous_finsetSum _ (fun i _ => continuous_apply i))

theorem centeredSupportRows_continuous (k : ℕ) : Continuous (centeredSupportRows (E := E) (k := k)) :=
  continuous_pi (fun i => (continuous_apply i).sub (supportRowMean_continuous k))

theorem gaussianRowsRecombine_continuous (k : ℕ) : Continuous (gaussianRowsRecombine (E := E) (k := k)) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp ((centeredSupportRows_continuous k).comp continuous_fst)).add
    (continuous_const.smul continuous_snd)

theorem centeredSupportRows_sum {k : ℕ} (hk : 0 < k) (b : Fin k → E) :
    (∑ i, centeredSupportRows b i) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  simp only [centeredSupportRows, Finset.sum_sub_distrib, supportRowMean,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hk', one_smul, sub_self]

theorem centeredSupportRows_adjoint {k : ℕ} (b t : Fin k → E) :
    (∑ i, ⟪centeredSupportRows b i, t i⟫_ℝ) = ∑ i, ⟪b i, centeredSupportRows t i⟫_ℝ := by
  simp only [centeredSupportRows, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  congr 1
  rw [← inner_sum, ← sum_inner]
  simp only [supportRowMean, real_inner_smul_left, inner_smul_right]

theorem centeredSupportRows_energy {k : ℕ} (hk : 0 < k) (t : Fin k → E) :
    (∑ i, ‖centeredSupportRows t i‖ ^ 2) + ‖(Real.sqrt k)⁻¹ • ∑ i, t i‖ ^ 2 =
      ∑ i, ‖t i‖ ^ 2 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : (Real.sqrt (k : ℝ)) ^ 2 = k := Real.sq_sqrt hk'.le
  simp only [centeredSupportRows, norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← sum_inner]
  simp only [supportRowMean, norm_smul, Real.norm_eq_abs, norm_inv, abs_of_nonneg hk'.le,
    abs_of_nonneg (Real.sqrt_nonneg (k : ℝ)), mul_pow, inv_pow, hs, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem gaussianRowsRecombine_pairing {k : ℕ} (b t : Fin k → E) (z : E) :
    (∑ i, ⟪gaussianRowsRecombine (b, z) i, t i⟫_ℝ) =
      (∑ i, ⟪b i, centeredSupportRows t i⟫_ℝ) + ⟪z, (Real.sqrt k)⁻¹ • ∑ i, t i⟫_ℝ := by
  simp only [gaussianRowsRecombine, inner_add_left, Finset.sum_add_distrib, centeredSupportRows_adjoint,
    real_inner_smul_left, inner_smul_right]
  rw [← Finset.mul_sum, ← inner_sum]

theorem finiteSupport_add_common {k : ℕ} [Nonempty (Fin k)] (b : Fin k → E) (z x : E) :
    finiteSupport (fun i => b i + z) x = finiteSupport b x + ⟪z, x⟫_ℝ := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := finiteSupport_attained (fun i => b i + z) x
    rw [hi, inner_add_left]
    exact add_le_add (finiteSupport_ge b x i) le_rfl
  · obtain ⟨i, hi⟩ := finiteSupport_attained b x
    rw [hi]
    simpa only [inner_add_left] using finiteSupport_ge (fun i => b i + z) x i

theorem finiteSupport_centered_nonneg {k : ℕ} (hk : 0 < k) (b : Fin k → E) (x : E) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    0 ≤ finiteSupport (centeredSupportRows b) x := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    finiteSupport_ge (centeredSupportRows b) x i)
  rw [← sum_inner, centeredSupportRows_sum hk, inner_zero_left] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  nlinarith

variable [Nontrivial E]

/-- Adding an independent Gaussian common component to centered Gaussian rows
reconstructs the exact original independent row law. -/
theorem gaussianRows_recombine_law {k : ℕ} (hk : 0 < k) :
    Measure.map (gaussianRowsRecombine (E := E) (k := k))
      ((Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).prod (euclideanGaussianLaw E)) =
        Measure.pi (fun _ : Fin k => euclideanGaussianLaw E) := by
  apply finite_rows_measure_ext_characteristic
  intro t
  have hc : StronglyMeasurable (fun b : Fin k → E => Complex.exp (((∑ i, ⟪b i, t i⟫_ℝ : ℝ) : ℂ) * Complex.I)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  rw [integral_map_of_stronglyMeasurable (gaussianRowsRecombine_continuous k).measurable hc]
  have he (w : (Fin k → E) × E) :
      Complex.exp (((∑ i, ⟪gaussianRowsRecombine w i, t i⟫_ℝ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((∑ i, ⟪w.1 i, centeredSupportRows t i⟫_ℝ : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((⟪w.2, (Real.sqrt k)⁻¹ • ∑ i, t i⟫_ℝ : ℂ) * Complex.I) := by
    rw [show w = (w.1, w.2) from rfl, gaussianRowsRecombine_pairing]
    simp only [Complex.ofReal_add, add_mul, Complex.exp_add]
  simp_rw [he]
  rw [integral_prod_mul
    (fun b : Fin k → E => Complex.exp (((∑ i, ⟪b i, centeredSupportRows t i⟫_ℝ : ℝ) : ℂ) * Complex.I))
    (fun z : E => Complex.exp ((⟪z, (Real.sqrt k)⁻¹ • ∑ i, t i⟫_ℝ : ℂ) * Complex.I)),
    gaussianRows_characteristic, gaussianRows_characteristic]
  have hg : (∫ z : E, Complex.exp ((⟪z, (Real.sqrt k)⁻¹ • ∑ i, t i⟫_ℝ : ℂ) * Complex.I)
      ∂euclideanGaussianLaw E) = Complex.exp (-(‖(Real.sqrt k)⁻¹ • ∑ i, t i‖ : ℂ) ^ 2 / 2) :=
    euclideanGaussian_characteristic _
  rw [hg, ← Complex.exp_add]
  congr 1
  have henergy := centeredSupportRows_energy hk t
  have hcast : ((∑ i, ‖centeredSupportRows t i‖ ^ 2 : ℝ) : ℂ) +
      (‖(Real.sqrt k)⁻¹ • ∑ i, t i‖ : ℂ) ^ 2 = ((∑ i, ‖t i‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast henergy
  linear_combination (-1 / 2 : ℂ) * hcast

end
end Nonsmooth
