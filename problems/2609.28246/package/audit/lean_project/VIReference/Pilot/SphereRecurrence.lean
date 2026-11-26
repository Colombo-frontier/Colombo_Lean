import VIReference.Pilot.SphereMoments
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

open MeasureTheory ProbabilityTheory Set Real Metric
open scoped RealInnerProductSpace

namespace VIReference.Pilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniformSphere_projection_moment_invariant
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (U : E ≃ₗᵢ[ℝ] E)
    (e : E) (m : ℕ) :
    (∫ ω, (inner ℝ (v ω) e) ^ m ∂μ) =
      ∫ ω, (inner ℝ (U (v ω)) e) ^ m ∂μ := by
  let f : E → ℝ := fun y => (inner ℝ y e) ^ m
  have hf : Continuous f := by fun_prop
  have hdist := hv.rotational_invariant U
  calc
    (∫ ω, (inner ℝ (v ω) e) ^ m ∂μ) = ∫ y, f y ∂Measure.map v μ :=
      (integral_map hv.measurable hf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂Measure.map (fun ω => U (v ω)) μ := by rw [hdist]
    _ = ∫ ω, (inner ℝ (U (v ω)) e) ^ m ∂μ :=
      integral_map (U.continuous.aemeasurable.comp_aemeasurable hv.measurable)
        hf.aestronglyMeasurable

theorem inner_reflection_span_pair
    (e f v : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (t : ℝ) :
    inner ℝ e (Submodule.reflection (ℝ ∙ (e + t • f)) v) =
      (((1 - t ^ 2) * inner ℝ e v + 2 * t * inner ℝ f v) / (1 + t ^ 2)) := by
  rw [Submodule.reflection_singleton_apply]
  have hfe : inner ℝ f e = 0 := by simpa [real_inner_comm] using hef
  have hnorme : ‖e‖ ^ 2 = 1 := by rw [he]; norm_num
  have hnormf : ‖f‖ ^ 2 = 1 := by rw [hf]; norm_num
  have hie : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hden : ‖e + t • f‖ ^ 2 = 1 + t ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hef, mul_zero,
      norm_smul, Real.norm_eq_abs, he, hf]
    simp only [add_zero, mul_one, one_pow]
    rw [sq_abs]
    ring
  change inner ℝ e
      (2 • (inner ℝ (e + t • f) v / (‖e + t • f‖ : ℝ) ^ 2) •
        (e + t • f) - v) = _
  rw [hden]
  have hne : 1 + t ^ 2 ≠ 0 := by positivity
  simp only [two_smul]
  simp [inner_sub_right, inner_add_right, inner_smul_right,
    inner_add_left, inner_smul_left, hie, hef, hfe]
  simp only [he, one_pow, mul_one]
  field_simp
  ring

theorem uniformSphere_reflection_pair_moment_identity
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (t : ℝ) (m : ℕ) :
    (∫ ω, (inner ℝ (v ω) e) ^ m ∂μ) =
      ∫ ω, ((((1 - t ^ 2) * inner ℝ e (v ω) +
          2 * t * inner ℝ f (v ω)) / (1 + t ^ 2)) ^ m) ∂μ := by
  let U : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ (e + t • f))
  rw [uniformSphere_projection_moment_invariant hv U e m]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [real_inner_comm]
  exact congrArg (fun z : ℝ => z ^ m)
    (inner_reflection_span_pair e f (v ω) he hf hef t)

theorem uniformSphere_projection_monomial_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (e f : E) (p q : ℕ) :
    Integrable (fun ω => (inner ℝ (v ω) e) ^ p *
      (inner ℝ (v ω) f) ^ q) μ := by
  have hemeas := uniformSphere_projection_aemeasurable hv e
  have hfmeas := uniformSphere_projection_aemeasurable hv f
  apply Integrable.of_bound ((hemeas.pow_const p).mul (hfmeas.pow_const q)).aestronglyMeasurable
    (‖e‖ ^ p * ‖f‖ ^ q)
  filter_upwards [uniformSphere_projection_bound hv e,
    uniformSphere_projection_bound hv f] with ω heω hfω
  change |(inner ℝ (v ω) e) ^ p * (inner ℝ (v ω) f) ^ q| ≤ _
  rw [abs_mul, abs_pow, abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) heω p)
    (pow_le_pow_left₀ (abs_nonneg _) hfω q) (by positivity) (by positivity)

noncomputable def reflectionMomentPolynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → E)
    (e f : E) (m : ℕ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range (m + 1),
    Polynomial.C ((m.choose r : ℝ) * 2 ^ r *
      (∫ ω, (inner ℝ (v ω) e) ^ (m - r) *
        (inner ℝ (v ω) f) ^ r ∂μ)) *
      (1 - Polynomial.X ^ 2) ^ (m - r) * Polynomial.X ^ r

noncomputable def reflectionMomentLHSPolynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → E)
    (e : E) (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (∫ ω, (inner ℝ (v ω) e) ^ m ∂μ) *
    (1 + Polynomial.X ^ 2) ^ m

theorem eval_reflectionMomentPolynomial
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (e f : E) (m : ℕ) (t : ℝ) :
    (reflectionMomentPolynomial μ v e f m).eval t =
      ∫ ω, (((1 - t ^ 2) * inner ℝ (v ω) e +
        2 * t * inner ℝ (v ω) f) ^ m) ∂μ := by
  rw [reflectionMomentPolynomial, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  calc
    _ = ∑ r ∈ Finset.range (m + 1),
        ∫ ω, (2 * t * inner ℝ (v ω) f) ^ r *
          ((1 - t ^ 2) * inner ℝ (v ω) e) ^ (m - r) * (m.choose r : ℝ) ∂μ := by
      apply Finset.sum_congr rfl
      intro r hr
      let c : ℝ := (m.choose r : ℝ) * 2 ^ r *
        (1 - t ^ 2) ^ (m - r) * t ^ r
      rw [show
        ((m.choose r : ℝ) * 2 ^ r *
            (∫ ω, (inner ℝ (v ω) e) ^ (m - r) *
              (inner ℝ (v ω) f) ^ r ∂μ)) *
              (1 - t ^ 2) ^ (m - r) * t ^ r =
          c * (∫ ω, (inner ℝ (v ω) e) ^ (m - r) *
              (inner ℝ (v ω) f) ^ r ∂μ) by simp [c]; ring]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [c, mul_pow]
      ring
    _ = ∫ ω, ∑ r ∈ Finset.range (m + 1),
        (2 * t * inner ℝ (v ω) f) ^ r *
          ((1 - t ^ 2) * inner ℝ (v ω) e) ^ (m - r) * (m.choose r : ℝ) ∂μ := by
      symm
      apply integral_finset_sum
      intro r hr
      let c : ℝ := (1 - t ^ 2) ^ (m - r) * (2 * t) ^ r * (m.choose r : ℝ)
      convert (uniformSphere_projection_monomial_integrable hv e f (m - r) r).const_mul c using 1
      funext ω
      simp [c, mul_pow]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      calc
        _ = ((2 * t * inner ℝ (v ω) f) +
              (1 - t ^ 2) * inner ℝ (v ω) e) ^ m :=
          (add_pow _ _ m).symm
        _ = _ := by rw [add_comm]

theorem reflectionMoment_polynomial_identity
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (m : ℕ) :
    reflectionMomentLHSPolynomial μ v e m =
      reflectionMomentPolynomial μ v e f m := by
  apply Polynomial.funext
  intro t
  rw [eval_reflectionMomentPolynomial hv]
  rw [reflectionMomentLHSPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  have href := uniformSphere_reflection_pair_moment_identity hv e f he hf hef t m
  rw [href]
  rw [show
    (∫ ω, (((1 - t ^ 2) * inner ℝ e (v ω) +
      2 * t * inner ℝ f (v ω)) / (1 + t ^ 2)) ^ m ∂μ) *
        (1 + t ^ 2) ^ m =
      (1 + t ^ 2) ^ m *
        (∫ ω, (((1 - t ^ 2) * inner ℝ e (v ω) +
          2 * t * inner ℝ f (v ω)) / (1 + t ^ 2)) ^ m ∂μ) by ring]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hne : 1 + t ^ 2 ≠ 0 := by positivity
  rw [real_inner_comm e (v ω), real_inner_comm f (v ω)]
  rw [div_pow]
  field_simp

theorem reflectionMoment_coeff_two_probe
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (m : ℕ) (hm : 2 ≤ m) :
    (reflectionMomentLHSPolynomial μ v e m).coeff 2 =
      (reflectionMomentPolynomial μ v e f m).coeff 2 := by
  exact congrArg (fun p : Polynomial ℝ => p.coeff 2)
    (reflectionMoment_polynomial_identity hv e f he hf hef m)

theorem coeff_two_one_add_X_sq_pow (m : ℕ) :
    ((1 + Polynomial.X ^ 2) ^ m : Polynomial ℝ).coeff 2 = (m : ℝ) := by
  induction m with
  | zero => simp [Polynomial.coeff_one]
  | succ m ih =>
      rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, ih]
      rw [Polynomial.coeff_mul_X_pow' _ 2 2]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp

theorem coeff_two_one_sub_X_sq_pow (m : ℕ) :
    ((1 - Polynomial.X ^ 2) ^ m : Polynomial ℝ).coeff 2 = -(m : ℝ) := by
  induction m with
  | zero => simp [Polynomial.coeff_one]
  | succ m ih =>
      rw [pow_succ, mul_sub, mul_one, Polynomial.coeff_sub, ih]
      rw [Polynomial.coeff_mul_X_pow' _ 2 2]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp
      ring

theorem coeff_one_one_sub_X_sq_pow (m : ℕ) :
    ((1 - Polynomial.X ^ 2) ^ m : Polynomial ℝ).coeff 1 = 0 := by
  induction m with
  | zero => simp [Polynomial.coeff_one]
  | succ m ih =>
      rw [pow_succ, mul_sub, mul_one, Polynomial.coeff_sub, ih]
      rw [Polynomial.coeff_mul_X_pow' _ 2 1]
      simp

theorem coeff_two_reflectionMomentLHS
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → E)
    (e : E) (m : ℕ) :
    (reflectionMomentLHSPolynomial μ v e m).coeff 2 =
      (m : ℝ) * (∫ ω, (inner ℝ (v ω) e) ^ m ∂μ) := by
  rw [reflectionMomentLHSPolynomial, Polynomial.coeff_C_mul,
    coeff_two_one_add_X_sq_pow]
  ring

theorem coeff_two_C_mul_one_sub_X_sq_pow (c : ℝ) (m : ℕ) :
    (Polynomial.C c * (1 - Polynomial.X ^ 2) ^ m : Polynomial ℝ).coeff 2 =
      -c * (m : ℝ) := by
  rw [Polynomial.coeff_C_mul, coeff_two_one_sub_X_sq_pow]
  ring

theorem coeff_two_C_mul_one_sub_X_sq_pow_mul_X (c : ℝ) (m : ℕ) :
    (Polynomial.C c * (1 - Polynomial.X ^ 2) ^ m * Polynomial.X :
      Polynomial ℝ).coeff 2 = 0 := by
  rw [show Polynomial.X = Polynomial.X ^ 1 by simp,
    Polynomial.coeff_mul_X_pow']
  simp [Polynomial.coeff_C_mul, coeff_one_one_sub_X_sq_pow]

theorem coeff_two_C_mul_one_sub_X_sq_pow_mul_X_sq (c : ℝ) (m : ℕ) :
    (Polynomial.C c * (1 - Polynomial.X ^ 2) ^ m * Polynomial.X ^ 2 :
      Polynomial ℝ).coeff 2 = c := by
  rw [Polynomial.coeff_mul_X_pow']
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_zero_eq_eval_zero]

theorem coeff_two_reflectionMomentPolynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → E)
    (e f : E) (q : ℕ) :
    (reflectionMomentPolynomial μ v e f (q + 2)).coeff 2 =
      -((q + 2 : ℕ) : ℝ) *
          (∫ ω, (inner ℝ (v ω) e) ^ (q + 2) ∂μ) +
        4 * (((q + 2).choose 2 : ℕ) : ℝ) *
          (∫ ω, (inner ℝ (v ω) e) ^ q *
            (inner ℝ (v ω) f) ^ 2 ∂μ) := by
  rw [reflectionMomentPolynomial]
  have hrange : q + 2 + 1 = 3 + q := by omega
  rw [hrange, Finset.sum_range_add]
  have htail :
      ((∑ x ∈ Finset.range q,
        Polynomial.C (((q + 2).choose (3 + x) : ℝ) * 2 ^ (3 + x) *
          (∫ ω, (inner ℝ (v ω) e) ^ (q + 2 - (3 + x)) *
            (inner ℝ (v ω) f) ^ (3 + x) ∂μ)) *
          (1 - Polynomial.X ^ 2) ^ (q + 2 - (3 + x)) *
            Polynomial.X ^ (3 + x)).coeff 2) = 0 := by
    change Polynomial.lcoeff ℝ 2 (∑ x ∈ Finset.range q,
        Polynomial.C (((q + 2).choose (3 + x) : ℝ) * 2 ^ (3 + x) *
          (∫ ω, (inner ℝ (v ω) e) ^ (q + 2 - (3 + x)) *
            (inner ℝ (v ω) f) ^ (3 + x) ∂μ)) *
          (1 - Polynomial.X ^ 2) ^ (q + 2 - (3 + x)) *
            Polynomial.X ^ (3 + x)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_mul_X_pow']
    split_ifs with h
    · omega
    · rfl
  rw [Polynomial.coeff_add, htail, add_zero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.sub_zero, pow_zero, pow_one, mul_one, Nat.choose_zero_right]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [coeff_two_C_mul_one_sub_X_sq_pow,
    coeff_two_C_mul_one_sub_X_sq_pow_mul_X,
    coeff_two_C_mul_one_sub_X_sq_pow_mul_X_sq]
  norm_num
  push_cast
  ring

theorem uniformSphere_orthogonal_mixed_even_moment
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (n : ℕ) :
    (∫ ω, (inner ℝ (v ω) e) ^ (2 * (n + 1)) ∂μ) =
      (2 * (n : ℝ) + 1) *
        (∫ ω, (inner ℝ (v ω) e) ^ (2 * n) *
          (inner ℝ (v ω) f) ^ 2 ∂μ) := by
  let q := 2 * n
  have hcoeff := reflectionMoment_coeff_two_probe hv e f he hf hef (q + 2) (by omega)
  rw [coeff_two_reflectionMomentLHS,
    coeff_two_reflectionMomentPolynomial] at hcoeff
  have hqpos : (0 : ℝ) < (q + 2 : ℕ) := by positivity
  have hchoose :
      (4 : ℝ) * (((q + 2).choose 2 : ℕ) : ℝ) =
        2 * ((q + 2 : ℕ) : ℝ) * ((q : ℕ) + 1 : ℕ) := by
    rw [Nat.cast_choose_two]
    push_cast
    field_simp
    ring
  rw [hchoose] at hcoeff
  push_cast at hcoeff
  have hresult : (∫ ω, (inner ℝ (v ω) e) ^ (q + 2) ∂μ) =
      ((q : ℝ) + 1) *
        (∫ ω, (inner ℝ (v ω) e) ^ q *
          (inner ℝ (v ω) f) ^ 2 ∂μ) := by
    let c : ℝ := 2 * ((q : ℝ) + 2)
    have hc : c ≠ 0 := by dsimp [c]; positivity
    have hmul : c * (∫ ω, (inner ℝ (v ω) e) ^ (q + 2) ∂μ) =
        c * (((q : ℝ) + 1) *
          (∫ ω, (inner ℝ (v ω) e) ^ q *
            (inner ℝ (v ω) f) ^ 2 ∂μ)) := by
      dsimp [c]
      linear_combination hcoeff
    exact (mul_left_cancel₀ hc hmul)
  simpa [q, Nat.mul_add] using hresult

theorem uniformSphere_basis_projection_even_moment_recurrence
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (b : OrthonormalBasis ι ℝ E) (hcard : Fintype.card ι = k)
    (i0 : ι) (n : ℕ) :
    ((k : ℝ) + 2 * (n : ℝ)) *
        (∫ ω, (inner ℝ (v ω) (b i0)) ^ (2 * (n + 1)) ∂μ) =
      (2 * (n : ℝ) + 1) *
        (∫ ω, (inner ℝ (v ω) (b i0)) ^ (2 * n) ∂μ) := by
  let J : ι → ℝ := fun i =>
    ∫ ω, (inner ℝ (v ω) (b i0)) ^ (2 * n) *
      (inner ℝ (v ω) (b i)) ^ 2 ∂μ
  let M0 : ℝ := ∫ ω, (inner ℝ (v ω) (b i0)) ^ (2 * n) ∂μ
  let M1 : ℝ := ∫ ω, (inner ℝ (v ω) (b i0)) ^ (2 * (n + 1)) ∂μ
  have hdecomp : M0 = ∑ i, J i := by
    calc
      M0 = ∫ ω, (inner ℝ (v ω) (b i0)) ^ (2 * n) * ‖v ω‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hv.unit_ae] with ω hω
        simp [M0, hω]
      _ = ∫ ω, ∑ i, (inner ℝ (v ω) (b i0)) ^ (2 * n) *
          (inner ℝ (v ω) (b i)) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← Finset.mul_sum, b.sum_sq_inner_left]
      _ = ∑ i, J i := by
        rw [integral_finset_sum]
        intro i hi
        exact uniformSphere_projection_monomial_integrable hv (b i0) (b i) (2 * n) 2
  have hJ0 : J i0 = M1 := by
    apply integral_congr_ae
    filter_upwards [] with ω
    ring
  have hmix (i : ι) (hi : i ≠ i0) :
      M1 = (2 * (n : ℝ) + 1) * J i := by
    have hnorm0 : ‖b i0‖ = 1 := b.orthonormal.1 i0
    have hnormi : ‖b i‖ = 1 := b.orthonormal.1 i
    have horth : inner ℝ (b i0) (b i) = 0 := by
      rw [orthonormal_iff_ite.mp b.orthonormal]
      simp [Ne.symm hi]
    simpa [M1, J] using
      uniformSphere_orthogonal_mixed_even_moment hv (b i0) (b i)
        hnorm0 hnormi horth n
  have hscaled : (2 * (n : ℝ) + 1) * M0 =
      ((k : ℝ) + 2 * (n : ℝ)) * M1 := by
    rw [hdecomp, Finset.mul_sum]
    rw [← Finset.add_sum_erase (Finset.univ) _ (Finset.mem_univ i0)]
    rw [hJ0]
    have hk : 1 ≤ k := by
      rw [← hcard]
      exact Fintype.card_pos_iff.mpr ⟨i0⟩
    have herase :
        (∑ i ∈ Finset.univ.erase i0, (2 * (n : ℝ) + 1) * J i) =
          ((k : ℝ) - 1) * M1 := by
      calc
        _ = ∑ _i ∈ Finset.univ.erase i0, M1 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_erase] at hi
          exact (hmix i hi.1).symm
        _ = ((Finset.univ.erase i0).card : ℝ) * M1 := by simp
        _ = ((k : ℝ) - 1) * M1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i0)]
          simp only [Finset.card_univ, hcard, Nat.cast_sub hk, Nat.cast_one]
    rw [herase]
    ring
  simpa [M0, M1] using hscaled.symm

theorem uniformSphere_even_moment_recurrence
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    {v : Ω → E} (hv : IsUniformUnitSphereLaw k v μ)
    (a : E) (n : ℕ) :
    ((k : ℝ) + 2 * (n : ℝ)) *
        (∫ ω, (inner ℝ (v ω) a) ^ (2 * (n + 1)) ∂μ) =
      (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
        (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) := by
  by_cases ha : a = 0
  · subst a
    simp
  let e : E := ‖a‖⁻¹ • a
  have hnorma : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have he : ‖e‖ = 1 := by
    simp [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hnorma]
  have ha_repr : a = ‖a‖ • e := by
    simp [e, smul_smul, hnorma]
  let i0 : Fin k := ⟨0, hk⟩
  let w : Fin k → E := fun _ => e
  let s : Set (Fin k) := {i0}
  have hw : Orthonormal ℝ (s.restrict w) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa [s, w] using he
  have hdimcard : Module.finrank ℝ E = Fintype.card (Fin k) := by
    simpa using hv.dimension
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq hdimcard
  have hb0 : b i0 = e := by
    exact hb i0 (by simp [s])
  have hbase := uniformSphere_basis_projection_even_moment_recurrence
    hv b (by simp) i0 n
  rw [hb0] at hbase
  have hscale (m : ℕ) :
      (∫ ω, (inner ℝ (v ω) a) ^ (2 * m) ∂μ) =
        ‖a‖ ^ (2 * m) *
          (∫ ω, (inner ℝ (v ω) e) ^ (2 * m) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    have hinner : inner ℝ (v ω) a = ‖a‖ * inner ℝ (v ω) e := by
      conv_lhs => rw [ha_repr]
      rw [inner_smul_right]
    rw [hinner, mul_pow]
  rw [hscale (n + 1), hscale n]
  calc
    ((k : ℝ) + 2 * (n : ℝ)) *
        (‖a‖ ^ (2 * (n + 1)) *
          (∫ ω, (inner ℝ (v ω) e) ^ (2 * (n + 1)) ∂μ)) =
      ‖a‖ ^ (2 * (n + 1)) *
        (((k : ℝ) + 2 * (n : ℝ)) *
          (∫ ω, (inner ℝ (v ω) e) ^ (2 * (n + 1)) ∂μ)) := by ring
    _ = ‖a‖ ^ (2 * (n + 1)) *
        ((2 * (n : ℝ) + 1) *
          (∫ ω, (inner ℝ (v ω) e) ^ (2 * n) ∂μ)) := by rw [hbase]
    _ = (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
        (‖a‖ ^ (2 * n) *
          (∫ ω, (inner ℝ (v ω) e) ^ (2 * n) ∂μ)) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      ring

theorem uniformSphereEvenMomentRecurrenceBridge_proof :
    UniformSphereEvenMomentRecurrenceBridge := by
  intro Ω' E' _ _ _ _ _ _ μ _ k hk v hv a n
  exact uniformSphere_even_moment_recurrence hk hv a n

/-- The geometric recurrence supplies the sharp spherical projection MGF
bound for every rotationally invariant unit-sphere law. -/
theorem uniformSphere_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    {v : Ω → E} (hv : IsUniformUnitSphereLaw k v μ) (a : E) :
    HasSubgaussianMGF (fun ω => inner ℝ (v ω) a)
      ⟨‖a‖ ^ 2 / k, div_nonneg (sq_nonneg ‖a‖) (Nat.cast_nonneg k)⟩ μ := by
  exact uniformSphere_hasSubgaussianMGF_of_evenMomentRecurrence hk hv
    (fun a n => uniformSphere_even_moment_recurrence hk hv a n) a

/-- Every uniform unit-sphere law canonically carries the MGF certificate used
by the original tail-bound layer. -/
theorem certifiedUniformUnitSphereProjectionMGF
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    {v : Ω → E} (hv : IsUniformUnitSphereLaw k v μ) :
    CertifiedUniformUnitSphereProjectionMGF k v μ where
  toIsUniformUnitSphereLaw := hv
  projection_mgf a R ha := by
    have hsharp := uniformSphere_hasSubgaussianMGF hk hv a
    refine ⟨hsharp.integrable_exp_mul, fun t => (hsharp.mgf_le t).trans ?_⟩
    apply Real.exp_le_exp.mpr
    have hR : 0 ≤ R := (norm_nonneg a).trans ha
    have hsquare : ‖a‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg a]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    have hparam : ‖a‖ ^ 2 / (k : ℝ) ≤ R ^ 2 / (k : ℝ) :=
      div_le_div_of_nonneg_right hsquare hkpos.le
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hparam (sq_nonneg t)) (by norm_num)

/-- Unconditional form of the article's spherical projection tail bound. -/
theorem spherical_tail_inequality
    {Ω : Type*} [MeasurableSpace Ω]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    {v : Ω → E} (hv : IsUniformUnitSphereLaw k v μ)
    (x : E) {R a : ℝ} (hx : ‖x‖ ≤ R) (ha : 0 < a) :
    μ.real {ω | |inner ℝ (v ω) x| > a} ≤
      2 * exp (-((k : ℝ) * a ^ 2) / (2 * R ^ 2)) := by
  exact conditional_spherical_tail_inequality hk
    (certifiedUniformUnitSphereProjectionMGF hk hv) x hx ha

/-- Proposition-valued unconditional contract for `lem:sphere`. -/
def SphericalTailClaim : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ), 1 ≤ k → ∀ (v : Ω → E),
    IsUniformUnitSphereLaw k v μ →
    ∀ (x : E) (R a : ℝ), ‖x‖ ≤ R → 0 < a →
      μ.real {ω | |inner ℝ (v ω) x| > a} ≤
        2 * exp (-((k : ℝ) * a ^ 2) / (2 * R ^ 2))

/-- Kernel-checked unconditional headline for `lem:sphere`. -/
theorem sphericalTailClaim_proof : SphericalTailClaim := by
  intro Ω' E' _ _ _ _ _ _ μ _ k hk v hv x R a hx ha
  exact spherical_tail_inequality hk hv x hx ha


end VIReference.Pilot
