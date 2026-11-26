import Nonsmooth.GaussianFirstObservation
import Nonsmooth.GaussianSquareMGF
import Nonsmooth.GaussianProjectionAtoms

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem integral_le_log_exp_moment {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {Z : α → ℝ} (hZ : Integrable Z μ)
    {t B : ℝ} (ht : 0 < t) (hB : 0 < B)
    (hExp : Integrable (fun x => Real.exp (t * Z x)) μ)
    (hbound : (∫ x, Real.exp (t * Z x) ∂μ) ≤ B) :
    (∫ x, Z x ∂μ) ≤ Real.log B / t := by
  have h := (convexOn_exp : ConvexOn ℝ Set.univ Real.exp).map_integral_le
    Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall (fun _ => mem_univ _))
    (hZ.const_mul t) hExp
  rw [integral_const_mul] at h
  have hb := h.trans hbound
  rw [← Real.exp_log hB, Real.exp_le_exp] at hb
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hb)

theorem selected_square_moment_of_exponential {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {k : ℕ} [Nonempty (Fin k)]
    (X : Fin k → α → ℝ) (Z : α → ℝ) (hZ : Integrable (fun x => Z x ^ 2) μ)
    {t B : ℝ} (ht : 0 < t) (hB : 0 < B)
    (hXi : ∀ i, Integrable (fun x => Real.exp (t * X i x ^ 2)) μ)
    (hXb : ∀ i, (∫ x, Real.exp (t * X i x ^ 2) ∂μ) ≤ B)
    (hsel : ∀ x, ∃ i, Z x ^ 2 ≤ X i x ^ 2) :
    (∫ x, Z x ^ 2 ∂μ) ≤ Real.log ((k : ℝ) * B) / t := by
  have hp (x : α) : Real.exp (t * Z x ^ 2) ≤ ∑ i, Real.exp (t * X i x ^ 2) := by
    obtain ⟨i, hi⟩ := hsel x
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi ht.le)).trans
      (Finset.single_le_sum (f := fun j => Real.exp (t * X j x ^ 2))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i))
  have hsum : Integrable (fun x => ∑ i, Real.exp (t * X i x ^ 2)) μ :=
    integrable_finsetSum _ (fun i _ => hXi i)
  have hExp : Integrable (fun x => Real.exp (t * Z x ^ 2)) μ := by
    apply hsum.mono' (Real.continuous_exp.comp_aestronglyMeasurable
      (hZ.aestronglyMeasurable.const_mul t))
    exact Eventually.of_forall (fun x => by simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hp x)
  have hk : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by simpa only [Fintype.card_fin] using
      (Fintype.card_pos : 0 < Fintype.card (Fin k)))
  apply integral_le_log_exp_moment μ hZ ht (mul_pos hk hB) hExp
  calc
    _ ≤ ∫ x, ∑ i, Real.exp (t * X i x ^ 2) ∂μ := integral_mono hExp hsum hp
    _ = ∑ i, ∫ x, Real.exp (t * X i x ^ 2) ∂μ := integral_finsetSum _ (fun i _ => hXi i)
    _ ≤ ∑ _i : Fin k, B := Finset.sum_le_sum (fun i _ => hXb i)
    _ = (k : ℝ) * B := by simp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_unit_square_exponential {u : E} (hu : ‖u‖ = 1)
    {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : E => Real.exp (t * ⟪u, z⟫_ℝ ^ 2)) (euclideanGaussianLaw E) ∧
    (∫ z : E, Real.exp (t * ⟪u, z⟫_ℝ ^ 2) ∂euclideanGaussianLaw E) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hm : Measurable (fun z : E => ⟪u, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
  have hp : MeasurePreserving (fun z : E => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E)
      (gaussianReal 0 1) := ⟨hm, euclideanGaussian_unit_inner_law hu⟩
  have hf : StronglyMeasurable (fun z : ℝ => Real.exp (t * z ^ 2)) :=
    (by fun_prop : Continuous (fun z : ℝ => Real.exp (t * z ^ 2))).stronglyMeasurable
  constructor
  · apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp
    rw [hp.map_eq]
    exact standardGaussian_square_exponential_integrable ht
  · rw [← integral_map_of_stronglyMeasurable hm hf, hp.map_eq,
      standardGaussian_square_exponential_integral ht]

theorem truncatedGaussian_unit_square_exponential {u : E} (hu : ‖u‖ = 1) :
    Integrable (fun z : E => Real.exp (⟪u, z⟫_ℝ ^ 2 / 4)) (truncatedGaussianLaw E) ∧
    (∫ z : E, Real.exp (⟪u, z⟫_ℝ ^ 2 / 4) ∂truncatedGaussianLaw E) ≤ 2 := by
  have hr := euclideanGaussian_unit_square_exponential hu (t := 1 / 4) (by norm_num)
  have hi : Integrable (fun z : E => Real.exp (⟪u, z⟫_ℝ ^ 2 / 4)) (euclideanGaussianLaw E) := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hr.1
  refine ⟨integrable_under_event hi euclideanGaussianLaw_truncation_positive.ne', ?_⟩
  have he : (∫ z : E, Real.exp (⟪u, z⟫_ℝ ^ 2 / 4) ∂euclideanGaussianLaw E) =
      (Real.sqrt (1 / 2))⁻¹ := by
    convert hr.2 using 1 <;> congr 1 <;> norm_num <;> ring
  have h := integral_event_le hi (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)))
  rw [he] at h
  have hp := euclideanGaussian_truncation_probability (E := E)
  have hp0 : 0 < (euclideanGaussianLaw E).real
      (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) := by linarith
  have hpinv : ((euclideanGaussianLaw E).real
      (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))))⁻¹ ≤ 4 / 3 := by
    rw [inv_eq_one_div, div_le_iff₀ hp0]
    linarith
  have hs : 2 / 3 ≤ Real.sqrt (1 / 2) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num), Real.sqrt_nonneg (1 / 2)]
  have hs0 : 0 < Real.sqrt (1 / 2) := by linarith
  have hsinv : (Real.sqrt (1 / 2))⁻¹ ≤ 3 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]
    linarith
  exact h.trans ((mul_le_mul hpinv hsinv (by positivity) (by norm_num)).trans (by norm_num))

theorem gaussianAmbientRow_unit_square_exponential {u : E} (hu : ‖u‖ = 1) :
    Integrable (fun z : E => Real.exp ((Module.finrank ℝ E : ℝ) / 4 * ⟪u, z⟫_ℝ ^ 2))
      (gaussianAmbientRowLaw E) ∧
    (∫ z : E, Real.exp ((Module.finrank ℝ E : ℝ) / 4 * ⟪u, z⟫_ℝ ^ 2)
      ∂gaussianAmbientRowLaw E) ≤ 2 := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  have hf : StronglyMeasurable (fun z : E =>
      Real.exp ((Module.finrank ℝ E : ℝ) / 4 * ⟪u, z⟫_ℝ ^ 2)) :=
    (by fun_prop : Continuous (fun z : E =>
      Real.exp ((Module.finrank ℝ E : ℝ) / 4 * ⟪u, z⟫_ℝ ^ 2))).stronglyMeasurable
  have he (z : E) : (Module.finrank ℝ E : ℝ) / 4 *
      ⟪u, (Real.sqrt (Module.finrank ℝ E))⁻¹ • z⟫_ℝ ^ 2 = ⟪u, z⟫_ℝ ^ 2 / 4 := by
    simp only [inner_smul_right, mul_pow, inv_pow, Real.sq_sqrt hd.le]
    field_simp
    <;> ring
  rw [gaussianAmbientRowLaw, gaussianSupportRowLaw_map]
  constructor
  · apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr
    simpa only [Function.comp_def, he] using (truncatedGaussian_unit_square_exponential hu).1
  · rw [integral_map_of_stronglyMeasurable hm hf]
    simp_rw [he]
    exact (truncatedGaussian_unit_square_exponential hu).2

theorem gaussianAmbientRows_support_memLp {k : ℕ} [Nonempty (Fin k)] {u : E} (hu : ‖u‖ = 1) :
    MemLp (fun a : Fin k → E => finiteSupport a u) 2
      (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) := by
  let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
  have hrows : ∀ᵐ a ∂Q, ∀ i, ‖a i‖ ≤ 2 := by
    apply ae_all_iff.mpr
    intro i
    have h := gaussianAmbientRowLaw_norm_le_two (E := E)
    rw [← (finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq] at h
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h
  have hm : Measurable (fun a : Fin k → E => finiteSupport a u) :=
    (supportSingleObservation_measurable u).snd
  apply MemLp.of_bound hm.aestronglyMeasurable 2
  filter_upwards [hrows] with a ha
  rw [supportWinner_attained, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (by simpa only [hu, mul_one] using ha (supportWinner a u))

/-- A logarithmic second moment for the actual maximum response, with explicit constant.
This estimates the winner response; it is not a bound on the full posterior mean increment. -/
theorem gaussianAmbientRows_support_second_log {k : ℕ} [Nonempty (Fin k)]
    {u : E} (hu : ‖u‖ = 1) :
    (∫ a : Fin k → E, (finiteSupport a u) ^ 2
      ∂Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) ≤
        4 * Real.log (2 * k) / (Module.finrank ℝ E : ℝ) := by
  let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
  let t : ℝ := (Module.finrank ℝ E : ℝ) / 4
  have ht : 0 < t := div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)
  have hm : Measurable (fun z : E => Real.exp (t * ⟪u, z⟫_ℝ ^ 2)) := by fun_prop
  have hXi (i : Fin k) : Integrable (fun a : Fin k → E => Real.exp (t * ⟪u, a i⟫_ℝ ^ 2)) Q := by
    apply (integrable_map_measure hm.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mp
    rw [(finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq]
    exact (gaussianAmbientRow_unit_square_exponential hu).1
  have hXb (i : Fin k) : (∫ a : Fin k → E, Real.exp (t * ⟪u, a i⟫_ℝ ^ 2) ∂Q) ≤ 2 := by
    have hf : StronglyMeasurable (fun z : E => Real.exp (t * ⟪u, z⟫_ℝ ^ 2)) := hm.stronglyMeasurable
    have he := integral_map_of_stronglyMeasurable (μ := Q) (measurable_pi_apply i) hf
    rw [(finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq] at he
    exact he.symm.trans_le (gaussianAmbientRow_unit_square_exponential hu).2
  have h := selected_square_moment_of_exponential Q (fun i a => ⟪u, a i⟫_ℝ)
    (fun a => finiteSupport a u) (gaussianAmbientRows_support_memLp hu).integrable_sq
    ht (by norm_num : (0 : ℝ) < 2) hXi hXb (fun a =>
      ⟨supportWinner a u, by rw [supportWinner_attained, real_inner_comm u]⟩)
  convert h using 1
  dsimp only [t]
  rw [mul_comm (k : ℝ) 2]
  ring

end
end Nonsmooth
