import GradientHessian.SharpSphereTail
import GradientHessian.MatrixGoodUpper

/-!
# Independent spherical columns

The column law is the actual finite product of normalized Gaussian sphere laws.
A Gaussian probe converts the sharp linear MGF into a square-norm MGF, so the
operator bound does not assume the manuscript's separate singular-value lemma.
-/

namespace GradientHessian.SphereColumnNorm

open MeasureTheory ProbabilityTheory Filter Matrix
open LowRank (matrixEuclideanMap matrixEuclideanMap_apply euclidean_dot_self)
open GradientHessian.GaussianHilbert GradientHessian.SphereGaussian
open GradientHessian.SharpSphereTail GradientHessian.MatrixGoodUpper
open scoped InnerProductSpace ENNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def columnLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (n : ℕ) : Measure (Fin n → E) :=
  Measure.pi (fun _ => sphereLaw E)

instance (n : ℕ) : IsProbabilityMeasure (columnLaw E n) := by
  unfold columnLaw
  infer_instance

def columnSum {n : ℕ} (u : Fin n → ℝ) (v : Fin n → E) : E := ∑ i, u i • v i

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem columnSum_continuous {n : ℕ} (u : Fin n → ℝ) : Continuous (columnSum (E := E) u) := by
  unfold columnSum
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem columnSum_exp_inner {n : ℕ} (g : E) (u : Fin n → ℝ) (v : Fin n → E) :
    Real.exp ⟪g,columnSum u v⟫_ℝ = ∏ i, Real.exp ⟪u i • g,v i⟫_ℝ := by
  simp only [columnSum, inner_sum, inner_smul_right, real_inner_smul_left, Real.exp_sum]

theorem columnSum_exp_inner_integrable [Nontrivial E] {n : ℕ} (g : E) (u : Fin n → ℝ) :
    Integrable (fun v => Real.exp ⟪g,columnSum u v⟫_ℝ) (columnLaw E n) := by
  simp_rw [columnSum_exp_inner]
  letI : MeasureSpace E := ⟨sphereLaw E⟩
  letI : SigmaFinite (volume : Measure E) := by change SigmaFinite (sphereLaw E); infer_instance
  exact Integrable.fintype_prod fun i => sphere_exp_inner_integrable (u i • g)

theorem columnSum_exp_inner_le [Nontrivial E] {n : ℕ} (g : E) (u : Fin n → ℝ)
    (hu : ∑ i, (u i)^2 = 1) :
    (∫ v, Real.exp ⟪g,columnSum u v⟫_ℝ ∂columnLaw E n) ≤
      Real.exp (‖g‖^2/(2*(Module.finrank ℝ E : ℝ))) := by
  simp_rw [columnSum_exp_inner]
  have he : (∫ v : Fin n → E, ∏ i, Real.exp ⟪u i • g,v i⟫_ℝ ∂columnLaw E n) =
      ∏ i, ∫ x, Real.exp ⟪u i • g,x⟫_ℝ ∂sphereLaw E := by
    letI : MeasureSpace E := ⟨sphereLaw E⟩
    letI : SigmaFinite (volume : Measure E) := by change SigmaFinite (sphereLaw E); infer_instance
    exact integral_fintype_prod_eq_prod (Fin n) (fun i x => Real.exp ⟪u i • g,x⟫_ℝ)
  rw [he]
  calc
    _ ≤ ∏ i, Real.exp (‖u i • g‖^2/(2*(Module.finrank ℝ E : ℝ))) :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => (Real.exp_pos _).le)
        (fun i _ => sphere_exp_inner_le (u i • g))
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.sum_div,
        ← Finset.sum_mul, hu, one_mul]

theorem gaussian_probe_exp (a : ℝ) (v : E) :
    (∫⁻ g, ENNReal.ofReal (Real.exp ⟪a • g,v⟫_ℝ) ∂euclideanGaussianLaw E) =
      ENNReal.ofReal (Real.exp (a^2*‖v‖^2/2)) := by
  have he (g : E) : Real.exp ⟪a • g,v⟫_ℝ = Real.exp (a*⟪v,g⟫_ℝ) := by
    rw [real_inner_smul_left, real_inner_comm g v]
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (euclideanGaussian_mgf_inner_integrable E v a)
    (ae_of_all _ fun _ => (Real.exp_pos _).le), euclideanGaussian_mgf_inner]

theorem gaussian_norm_square_mgf {t : ℝ} (ht : t < 1/2) :
    (∫ g, Real.exp (t*‖g‖^2) ∂euclideanGaussianLaw E) =
      ((Real.sqrt (1-2*t))⁻¹)^(Module.finrank ℝ E) := by
  rw [euclideanGaussianLaw, integral_map_of_stronglyMeasurable
    (gaussianSynthesis_continuous E).measurable
    (show Continuous (fun g : E => Real.exp (t*‖g‖^2)) by fun_prop).stronglyMeasurable]
  simp_rw [gaussianSynthesis_norm_square]
  exact GaussianSquare.energy_exponential_integral _ ht

theorem gaussian_norm_square_exp_integrable {t : ℝ} (ht : t < 1/2) :
    Integrable (fun g : E => Real.exp (t*‖g‖^2)) (euclideanGaussianLaw E) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_norm_square_mgf ht]
  exact (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))) _).ne'

theorem columnSum_square_lintegral [Nontrivial E] {n : ℕ} (u : Fin n → ℝ)
    (hu : ∑ i, (u i)^2 = 1) :
    (∫⁻ v, ENNReal.ofReal (Real.exp ((3/8:ℝ)*(Module.finrank ℝ E : ℝ)*‖columnSum u v‖^2))
      ∂columnLaw E n) ≤ ENNReal.ofReal ((2 : ℝ)^(Module.finrank ℝ E)) := by
  let m : ℝ := Module.finrank ℝ E
  let a : ℝ := Real.sqrt (3*m/4)
  have hm : 0 < m := Nat.cast_pos.mpr Module.finrank_pos
  have ha : a^2 = 3*m/4 := Real.sq_sqrt (by positivity)
  have hp (v : Fin n → E) :
      ENNReal.ofReal (Real.exp ((3/8:ℝ)*m*‖columnSum u v‖^2)) =
        ∫⁻ g, ENNReal.ofReal (Real.exp ⟪a • g,columnSum u v⟫_ℝ) ∂euclideanGaussianLaw E := by
    rw [gaussian_probe_exp, ha]
    congr 2
    ring
  have hmeas : Measurable (fun p : (Fin n → E) × E =>
      ENNReal.ofReal (Real.exp ⟪a • p.2,columnSum u p.1⟫_ℝ)) := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    exact Real.continuous_exp.comp ((continuous_const.smul continuous_snd).inner
      ((columnSum_continuous u).comp continuous_fst))
  change (∫⁻ v, ENNReal.ofReal (Real.exp ((3/8:ℝ)*m*‖columnSum u v‖^2)) ∂columnLaw E n) ≤ _
  simp_rw [hp]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc
    _ ≤ ∫⁻ g : E, ENNReal.ofReal (Real.exp ((3/8:ℝ)*‖g‖^2)) ∂euclideanGaussianLaw E := by
      apply lintegral_mono
      intro g
      dsimp only
      rw [← ofReal_integral_eq_lintegral_ofReal (columnSum_exp_inner_integrable (a • g) u)
        (ae_of_all _ fun _ => (Real.exp_pos _).le)]
      apply ENNReal.ofReal_le_ofReal
      have h := columnSum_exp_inner_le (a • g) u hu
      convert h using 1
      congr 1
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha]
      change 3/8*‖g‖^2 = (3*m/4*‖g‖^2)/(2*m)
      field_simp [hm.ne']
      ring
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (gaussian_norm_square_exp_integrable (E := E) (by norm_num : (3/8:ℝ)<1/2))
        (ae_of_all _ fun _ => (Real.exp_pos _).le), gaussian_norm_square_mgf (by norm_num)]
      norm_num

theorem columnSum_square_exp_integrable [Nontrivial E] {n : ℕ} (u : Fin n → ℝ)
    (hu : ∑ i, (u i)^2 = 1) :
    Integrable (fun v => Real.exp ((3/8:ℝ)*(Module.finrank ℝ E : ℝ)*‖columnSum u v‖^2))
      (columnLaw E n) := by
  refine ⟨(Real.continuous_exp.comp
    (continuous_const.mul ((columnSum_continuous u).norm.pow 2))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact (columnSum_square_lintegral u hu).trans_lt ENNReal.ofReal_lt_top

theorem columnSum_square_mgf [Nontrivial E] {n : ℕ} (u : Fin n → ℝ)
    (hu : ∑ i, (u i)^2 = 1) :
    (∫ v, Real.exp ((3/8:ℝ)*(Module.finrank ℝ E : ℝ)*‖columnSum u v‖^2)
      ∂columnLaw E n) ≤ (2 : ℝ)^(Module.finrank ℝ E) := by
  have h := columnSum_square_lintegral (E := E) u hu
  rw [← ofReal_integral_eq_lintegral_ofReal (columnSum_square_exp_integrable u hu)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

theorem columnSum_norm_tail [Nontrivial E] {n : ℕ} (u : Fin n → ℝ)
    (hu : ∑ i, (u i)^2 = 1) :
    (columnLaw E n).real {v | 3 ≤ ‖columnSum u v‖} ≤
      (2*Real.exp (-(27/8:ℝ)))^(Module.finrank ℝ E) := by
  let m : ℝ := Module.finrank ℝ E
  have hm : 0 < m := Nat.cast_pos.mpr Module.finrank_pos
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := columnLaw E n) (f := fun v => Real.exp ((3/8:ℝ)*m*‖columnSum u v‖^2))
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (columnSum_square_exp_integrable u hu)
    (Real.exp ((27/8:ℝ)*m))
  have he : {v : Fin n → E | Real.exp ((27/8:ℝ)*m) ≤
      Real.exp ((3/8:ℝ)*m*‖columnSum u v‖^2)} = {v | 3 ≤ ‖columnSum u v‖} := by
    ext v
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    have hc : 0 < (3/8:ℝ)*m := by positivity
    have he' : (27/8:ℝ)*m = ((3/8:ℝ)*m)*9 := by ring
    rw [he', mul_le_mul_left hc]
    constructor <;> intro h <;> nlinarith [norm_nonneg (columnSum u v)]
  rw [he] at hmarkov
  have hbound : (columnLaw E n).real {v | 3 ≤ ‖columnSum u v‖} ≤
      (2 : ℝ)^(Module.finrank ℝ E)/Real.exp ((27/8:ℝ)*m) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hmgf := columnSum_square_mgf (E := E) u hu
    nlinarith
  calc
    _ ≤ _ := hbound
    _ = _ := by
      rw [Real.exp_neg, mul_pow, inv_pow, ← div_eq_mul_inv, ← Real.exp_nat_mul]
      congr 2
      dsimp [m]
      ring

def columnMatrix {D n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin D)) :
    Matrix (Fin D) (Fin n) ℝ := fun i j => v j i

theorem columnMatrix_apply {D n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin D))
    (u : EuclideanSpace ℝ (Fin n)) :
    matrixEuclideanMap (columnMatrix v) u = columnSum (fun i => u i) v := by
  ext i
  change (∑ j, v j i * u j) = (∑ j, u j • v j) i
  change (∑ j, v j i * u j) = (EuclideanSpace.proj i) (∑ j, u j • v j)
  simp [mul_comm]

/-- Independent sphere columns satisfy the same useful single-vector estimate
as a Gaussian matrix of coordinate variance `1/D`. -/
theorem columnMatrix_unit_tail {D n : ℕ} (hD : 0 < D)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    (columnLaw (EuclideanSpace ℝ (Fin D)) n).real
      {v | 3 ≤ ‖matrixEuclideanMap (columnMatrix v) u‖} ≤
        (2*Real.exp (-(27/8:ℝ)))^D := by
  letI : NeZero D := ⟨hD.ne'⟩
  have hu' : ∑ i, (u i)^2 = 1 := by
    have h := euclidean_dot_self u
    simpa only [dotProduct, ← pow_two, hu, one_pow] using h
  simpa only [columnMatrix_apply, finrank_euclideanSpace_fin] using
    columnSum_norm_tail (E := EuclideanSpace ℝ (Fin D)) (fun i => u i) hu'

/-- A quarter-net and the actual independent column law give an exponential
operator-norm bound, uniformly for at most `D` columns. -/
theorem columnMatrix_operator_tail {D n : ℕ} (hD : 0 < D) (hn : n ≤ D) :
    (columnLaw (EuclideanSpace ℝ (Fin D)) n).real
      {v | 4 < ‖matrixEuclideanMap (columnMatrix v)‖} ≤
        (18*Real.exp (-(27/8:ℝ)))^D := by
  classical
  obtain ⟨S,hcard,hunit,hnet⟩ := exists_quarter_sphere_net (EuclideanSpace ℝ (Fin n))
  have hcardR : (S.card : ℝ) ≤ (9 : ℝ)^D := by
    have hc : S.card ≤ 9^n := by simpa using hcard
    exact_mod_cast hc.trans (Nat.pow_le_pow_right (by norm_num : 0 < 9) hn)
  let μ := columnLaw (EuclideanSpace ℝ (Fin D)) n
  let bad := fun u : EuclideanSpace ℝ (Fin n) =>
    {v : Fin n → EuclideanSpace ℝ (Fin D) | 3 ≤ ‖matrixEuclideanMap (columnMatrix v) u‖}
  have hsub : {v : Fin n → EuclideanSpace ℝ (Fin D) | 4 < ‖matrixEuclideanMap (columnMatrix v)‖} ⊆
      ⋃ u ∈ S, bad u := by
    intro v hv
    by_contra hmem
    have hval : ∀ u ∈ S, ‖matrixEuclideanMap (columnMatrix v) u‖ ≤ 3 := by
      intro u hu
      apply le_of_not_ge
      intro hlarge
      exact hmem (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hlarge⟩⟩)
    exact (not_le_of_gt hv) (opNorm_le_four_of_quarter_net (matrixEuclideanMap (columnMatrix v)) S hnet hval)
  have ht : ∀ u ∈ S, μ.real (bad u) ≤ (2*Real.exp (-(27/8:ℝ)))^D :=
    fun u hu => columnMatrix_unit_tail hD u (hunit u hu)
  calc
    _ ≤ μ.real (⋃ u ∈ S, bad u) := measureReal_mono hsub
    _ ≤ ∑ u ∈ S, μ.real (bad u) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ S, (2*Real.exp (-(27/8:ℝ)))^D := Finset.sum_le_sum ht
    _ = (S.card : ℝ)*(2*Real.exp (-(27/8:ℝ)))^D := by simp
    _ ≤ (9 : ℝ)^D*(2*Real.exp (-(27/8:ℝ)))^D :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem columnMatrix_operator_tail_geometric {D n : ℕ} (hD : 0 < D) (hn : n ≤ D) :
    (columnLaw (EuclideanSpace ℝ (Fin D)) n).real
      {v | 4 < ‖matrixEuclideanMap (columnMatrix v)‖} ≤ (2/3:ℝ)^D := by
  apply (columnMatrix_operator_tail hD hn).trans
  have he : (27 : ℝ) ≤ Real.exp (27/8) := by
    have hp := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤27/8) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at hp
    linarith
  have hb : 18*Real.exp (-(27/8:ℝ)) ≤ 2/3 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  exact pow_le_pow_left₀ (by positivity) hb D

/-- Source `eq:column-sphere`, with explicit absolute constants
`C=1` and `c=log(3/2)>0`. -/
theorem manuscript_column_sphere_tail {m : ℕ} (hm : 0 < m) :
    (columnLaw (EuclideanSpace ℝ (Fin m)) m).real
      {v | 4 < ‖matrixEuclideanMap (columnMatrix v)‖} ≤
        Real.exp (-Real.log (3/2:ℝ)*(m:ℝ)) := by
  have h := columnMatrix_operator_tail_geometric hm (le_refl m)
  convert h using 1
  rw [mul_comm (-Real.log (3/2:ℝ)), Real.exp_nat_mul, Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ)<3/2)]
  norm_num

theorem manuscript_column_sphere_rate_pos : 0 < Real.log (3/2:ℝ) :=
  Real.log_pos (by norm_num)

end
end GradientHessian.SphereColumnNorm
