import LeanArticleAudit.Pilot.CanonicalSphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Moment consequences for a uniform spherical law

The geometric input is the single even-moment recurrence isolated in
`UniformSphereEvenMomentRecurrenceBridge`.  Everything after that recurrence
is proved here without further probabilistic assumptions.
-/

open MeasureTheory ProbabilityTheory Set Real Metric
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

/-- Product coefficient determined by the exact spherical even-moment
recurrence. -/
noncomputable def sphericalEvenMomentCoefficient (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      ((2 * (n : ℝ) + 1) / ((k : ℝ) + 2 * (n : ℝ))) *
        sphericalEvenMomentCoefficient k n

/-- Gaussian comparison coefficient, obtained by replacing every denominator
`k + 2n` in the spherical recurrence by the smaller denominator `k`. -/
noncomputable def gaussianEvenMomentCoefficient (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      ((2 * (n : ℝ) + 1) / (k : ℝ)) * gaussianEvenMomentCoefficient k n

theorem sphericalEvenMomentCoefficient_nonneg (k n : ℕ) :
    0 ≤ sphericalEvenMomentCoefficient k n := by
  induction n with
  | zero => simp [sphericalEvenMomentCoefficient]
  | succ n ih =>
      rw [sphericalEvenMomentCoefficient]
      positivity

theorem gaussianEvenMomentCoefficient_nonneg (k n : ℕ) :
    0 ≤ gaussianEvenMomentCoefficient k n := by
  induction n with
  | zero => simp [gaussianEvenMomentCoefficient]
  | succ n ih =>
      rw [gaussianEvenMomentCoefficient]
      positivity

theorem sphericalEvenMomentCoefficient_le_gaussian
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    sphericalEvenMomentCoefficient k n ≤ gaussianEvenMomentCoefficient k n := by
  induction n with
  | zero => simp [sphericalEvenMomentCoefficient, gaussianEvenMomentCoefficient]
  | succ n ih =>
      rw [sphericalEvenMomentCoefficient, gaussianEvenMomentCoefficient]
      apply mul_le_mul
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      · exact ih
      · exact sphericalEvenMomentCoefficient_nonneg k n
      · positivity

theorem gaussianEvenMomentCoefficient_div_factorial
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    gaussianEvenMomentCoefficient k n / (Nat.factorial (2 * n) : ℝ) =
      (1 / (Nat.factorial n : ℝ)) * (1 / (2 * (k : ℝ))) ^ n := by
  induction n with
  | zero => simp [gaussianEvenMomentCoefficient]
  | succ n ih =>
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hodd : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hfac : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
      calc
        gaussianEvenMomentCoefficient k (n + 1) /
            (Nat.factorial (2 * (n + 1)) : ℝ) =
          (gaussianEvenMomentCoefficient k n /
            (Nat.factorial (2 * n) : ℝ)) *
              (1 / (2 * (k : ℝ) * (n + 1))) := by
            rw [gaussianEvenMomentCoefficient]
            rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
            rw [Nat.factorial_succ, Nat.factorial_succ]
            push_cast
            field_simp [hk0, hn0, hodd, hfac]
            ring
        _ = (1 / (Nat.factorial (n + 1) : ℝ)) *
            (1 / (2 * (k : ℝ))) ^ (n + 1) := by
          rw [ih, Nat.factorial_succ, pow_succ]
          push_cast
          field_simp [hk0, hn0]

section AbstractUniformLaw

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The recurrence, once supplied, determines every even projection moment in
closed recursive-product form. -/
theorem uniformSphere_even_projection_moment_closedForm
    {k : ℕ} (hk : 1 ≤ k) (v : Ω → E) (a : E)
    (hrec : ∀ n : ℕ,
      ((k : ℝ) + 2 * (n : ℝ)) *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * (n + 1)) ∂μ) =
        (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ)) :
    ∀ n : ℕ,
      (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) =
        sphericalEvenMomentCoefficient k n * ‖a‖ ^ (2 * n) := by
  intro n
  induction n with
  | zero => simp [sphericalEvenMomentCoefficient]
  | succ n ih =>
      have hD : (k : ℝ) + 2 * (n : ℝ) ≠ 0 := by positivity
      have hr := hrec n
      rw [ih] at hr
      rw [sphericalEvenMomentCoefficient]
      have hpow : ‖a‖ ^ (2 * (n + 1)) = ‖a‖ ^ 2 * ‖a‖ ^ (2 * n) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega, pow_add]
      field_simp [hD]
      rw [hpow]
      nlinarith [hr]

/-- Gaussian upper bound for every even projection moment. -/
theorem uniformSphere_even_projection_moment_le_gaussian
    {k : ℕ} (hk : 1 ≤ k) (v : Ω → E) (a : E)
    (hrec : ∀ n : ℕ,
      ((k : ℝ) + 2 * (n : ℝ)) *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * (n + 1)) ∂μ) =
        (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ))
    (n : ℕ) :
    (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) ≤
      gaussianEvenMomentCoefficient k n * ‖a‖ ^ (2 * n) := by
  rw [uniformSphere_even_projection_moment_closedForm hk v a hrec n]
  exact mul_le_mul_of_nonneg_right
    (sphericalEvenMomentCoefficient_le_gaussian hk n) (by positivity)

theorem uniformSphere_projection_bound {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (a : E) :
    ∀ᵐ ω ∂μ, |inner ℝ (v ω) a| ≤ ‖a‖ := by
  filter_upwards [hv.unit_ae] with ω hω
  calc
    |inner ℝ (v ω) a| ≤ ‖v ω‖ * ‖a‖ := abs_real_inner_le_norm _ _
    _ = ‖a‖ := by rw [hω, one_mul]

theorem uniformSphere_projection_aemeasurable {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (a : E) :
    AEMeasurable (fun ω => inner ℝ (v ω) a) μ := by
  have hf : Continuous (fun y : E => inner ℝ y a) := by fun_prop
  exact hf.aemeasurable.comp_aemeasurable hv.measurable

theorem uniformSphere_projection_exp_integrable {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (a : E) (t : ℝ) :
    Integrable (fun ω => exp (t * inner ℝ (v ω) a)) μ := by
  apply Integrable.of_bound
    ((uniformSphere_projection_aemeasurable hv a).const_mul t).exp.aestronglyMeasurable
    (exp (|t| * ‖a‖))
  filter_upwards [uniformSphere_projection_bound hv a] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * inner ℝ (v ω) a ≤ |t * inner ℝ (v ω) a| := le_abs_self _
    _ = |t| * |inner ℝ (v ω) a| := abs_mul _ _
    _ ≤ |t| * ‖a‖ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

theorem uniformSphere_projection_exp_symm {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (a : E) (t : ℝ) :
    (∫ ω, exp (t * inner ℝ (v ω) a) ∂μ) =
      ∫ ω, exp (-t * inner ℝ (v ω) a) ∂μ := by
  let U : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  let f : E → ℝ := fun y => exp (t * inner ℝ y a)
  have hf : Continuous f := by fun_prop
  have hdist : Measure.map (fun ω => U (v ω)) μ = Measure.map v μ :=
    hv.rotational_invariant U
  calc
    (∫ ω, exp (t * inner ℝ (v ω) a) ∂μ) =
        ∫ y, f y ∂Measure.map v μ :=
      (integral_map hv.measurable hf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂Measure.map (fun ω => U (v ω)) μ := by rw [hdist]
    _ = ∫ ω, f (U (v ω)) ∂μ :=
      integral_map (U.continuous.aemeasurable.comp_aemeasurable hv.measurable)
        hf.aestronglyMeasurable
    _ = ∫ ω, exp (-t * inner ℝ (v ω) a) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [f, U]

theorem uniformSphere_mgf_eq_integral_cosh {k : ℕ} {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) (a : E) (t : ℝ) :
    mgf (fun ω => inner ℝ (v ω) a) μ t =
      ∫ ω, cosh (t * inner ℝ (v ω) a) ∂μ := by
  rw [mgf]
  have hs := uniformSphere_projection_exp_symm hv a t
  have hp := uniformSphere_projection_exp_integrable hv a t
  have hn := uniformSphere_projection_exp_integrable hv a (-t)
  calc
    (∫ ω, exp (t * inner ℝ (v ω) a) ∂μ) =
        (1 / 2 : ℝ) * ((∫ ω, exp (t * inner ℝ (v ω) a) ∂μ) +
          ∫ ω, exp (-t * inner ℝ (v ω) a) ∂μ) := by rw [hs]; ring
    _ = ∫ ω, (1 / 2 : ℝ) *
        (exp (t * inner ℝ (v ω) a) + exp (-t * inner ℝ (v ω) a)) ∂μ := by
      symm
      rw [integral_const_mul, integral_add hp hn]
    _ = ∫ ω, cosh (t * inner ℝ (v ω) a) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [cosh_eq]
      ring

theorem uniformSphere_integral_cosh_eq_tsum_moments
    {k : ℕ} {v : Ω → E} (hv : IsUniformUnitSphereLaw k v μ)
    (a : E) (t : ℝ) :
    (∫ ω, cosh (t * inner ℝ (v ω) a) ∂μ) =
      ∑' n : ℕ, t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
        (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) := by
  let X : Ω → ℝ := fun ω => inner ℝ (v ω) a
  let F : ℕ → Ω → ℝ := fun n ω =>
    (t * X ω) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)
  have hX := uniformSphere_projection_aemeasurable hv a
  have hbound := uniformSphere_projection_bound hv a
  have hF_bound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖F n ω‖ ≤ (|t| * ‖a‖) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ) := by
    filter_upwards [hbound] with ω hω
    have hmul : |t * X ω| ≤ |t| * ‖a‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg t)
    have hfact : |(Nat.factorial (2 * n) : ℝ)| =
        (Nat.factorial (2 * n) : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    dsimp [F]
    rw [abs_div, abs_pow, hfact]
    gcongr
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (((hX.const_mul t).pow_const (2 * n)).div_const
      (Nat.factorial (2 * n))).aestronglyMeasurable
  have hF_int (n : ℕ) : Integrable (F n) μ :=
    Integrable.of_bound (hF_meas n) _ (hF_bound n)
  have hF_sum : Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂μ) := by
    refine (Real.hasSum_cosh (|t| * ‖a‖)).summable.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    calc
      (∫ ω, ‖F n ω‖ ∂μ) ≤
          ∫ _, (|t| * ‖a‖) ^ (2 * n) /
            (Nat.factorial (2 * n) : ℝ) ∂μ :=
        integral_mono_ae (hF_int n).norm (integrable_const _) (hF_bound n)
      _ = (|t| * ‖a‖) ^ (2 * n) /
          (Nat.factorial (2 * n) : ℝ) := by simp
  rw [show (fun ω => cosh (t * inner ℝ (v ω) a)) =
      fun ω => ∑' n, F n ω by
        funext ω
        simp only [F, X, cosh_eq_tsum]]
  rw [← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  apply tsum_congr
  intro n
  rw [show F n = fun ω =>
      (t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) * X ω ^ (2 * n) by
    funext ω
    dsimp [F]
    rw [mul_pow]
    ring]
  rw [integral_const_mul]

/-- The exact even-moment recurrence implies the sharp spherical
sub-Gaussian MGF constant `‖a‖² / k`. -/
theorem uniformSphere_hasSubgaussianMGF_of_evenMomentRecurrence
    {k : ℕ} (hk : 1 ≤ k) {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (hrec : ∀ (a : E) (n : ℕ),
      ((k : ℝ) + 2 * (n : ℝ)) *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * (n + 1)) ∂μ) =
        (2 * (n : ℝ) + 1) * ‖a‖ ^ 2 *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ))
    (a : E) :
    HasSubgaussianMGF (fun ω => inner ℝ (v ω) a)
      ⟨‖a‖ ^ 2 / k, div_nonneg (sq_nonneg ‖a‖) (Nat.cast_nonneg k)⟩ μ := by
  refine ⟨uniformSphere_projection_exp_integrable hv a, ?_⟩
  intro t
  rw [uniformSphere_mgf_eq_integral_cosh hv a t]
  rw [uniformSphere_integral_cosh_eq_tsum_moments hv a t]
  let z : ℝ := t ^ 2 * ‖a‖ ^ 2 / (2 * (k : ℝ))
  have hterm (n : ℕ) :
      t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) ≤
        z ^ n / (Nat.factorial n : ℝ) := by
    calc
      t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
          (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) ≤
        t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
          (gaussianEvenMomentCoefficient k n * ‖a‖ ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left
          (uniformSphere_even_projection_moment_le_gaussian hk v a (hrec a) n)
          (div_nonneg ((even_two_mul n).pow_nonneg t) (Nat.cast_nonneg _))
      _ = (gaussianEvenMomentCoefficient k n /
            (Nat.factorial (2 * n) : ℝ)) *
          (t ^ (2 * n) * ‖a‖ ^ (2 * n)) := by ring
      _ = (1 / (Nat.factorial n : ℝ)) * (1 / (2 * (k : ℝ))) ^ n *
          (t ^ (2 * n) * ‖a‖ ^ (2 * n)) := by
        rw [gaussianEvenMomentCoefficient_div_factorial hk n]
      _ = z ^ n / (Nat.factorial n : ℝ) := by
        dsimp [z]
        rw [show t ^ (2 * n) = (t ^ 2) ^ n by rw [pow_mul]]
        rw [show ‖a‖ ^ (2 * n) = (‖a‖ ^ 2) ^ n by rw [pow_mul]]
        simp_rw [div_pow]
        ring
  have hright : Summable (fun n : ℕ => z ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial z
  have hleft_nonneg (n : ℕ) :
      0 ≤ t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
        (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ) := by
    apply mul_nonneg
      (div_nonneg ((even_two_mul n).pow_nonneg t) (Nat.cast_nonneg _))
    apply integral_nonneg_of_ae
    filter_upwards [] with ω
    exact (even_two_mul n).pow_nonneg _
  have hleft : Summable (fun n : ℕ =>
      t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
        (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ)) :=
    hright.of_nonneg_of_le hleft_nonneg hterm
  calc
    (∑' n : ℕ, t ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) *
        (∫ ω, (inner ℝ (v ω) a) ^ (2 * n) ∂μ)) ≤
      ∑' n : ℕ, z ^ n / (Nat.factorial n : ℝ) :=
        Summable.tsum_le_tsum hterm hleft hright
    _ = exp z := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = exp ((‖a‖ ^ 2 / (k : ℝ)) * t ^ 2 / 2) := by
      congr 1
      dsimp [z]
      field_simp

/-
/-- The single recurrence bridge supplies the exact MGF certificate used by
the conditional spherical tail theorem. -/
theorem uniformSphereProjectionMGF_of_evenMomentRecurrenceBridge
    (hbridge : UniformSphereEvenMomentRecurrenceBridge)
    {k : ℕ} (hk : 1 ≤ k) {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ)
    (a : E) (R : ℝ) (ha : ‖a‖ ≤ R) :
    HasSubgaussianMGF (fun ω => inner ℝ (v ω) a)
      ⟨R ^ 2 / k, div_nonneg (sq_nonneg R) (Nat.cast_nonneg k)⟩ μ := by
  have hsharp := uniformSphere_hasSubgaussianMGF_of_evenMomentRecurrence hk hv
    (hbridge (Ω := Ω) (E := E) μ k hk v hv) a
  refine ⟨hsharp.integrable_exp_mul, fun t => (hsharp.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have hsquare : ‖a‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg a]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hparam : ‖a‖ ^ 2 / (k : ℝ) ≤ R ^ 2 / (k : ℝ) :=
    div_le_div_of_nonneg_right hsquare hkpos.le
  exact mul_div_le_mul_div_of_nonneg_right hparam (sq_nonneg t) (by norm_num)

/-- Fully checked construction of the certificate interface from the single
even-moment recurrence bridge. -/
theorem certifiedUniformUnitSphereProjectionMGF_of_bridge
    (hbridge : UniformSphereEvenMomentRecurrenceBridge)
    {k : ℕ} (hk : 1 ≤ k) {v : Ω → E}
    (hv : IsUniformUnitSphereLaw k v μ) :
    CertifiedUniformUnitSphereProjectionMGF k v μ where
  toIsUniformUnitSphereLaw := hv
  projection_mgf a R ha :=
    uniformSphereProjectionMGF_of_evenMomentRecurrenceBridge
      hbridge hk hv a R ha
-/

end AbstractUniformLaw

end LeanArticleAudit.Pilot
