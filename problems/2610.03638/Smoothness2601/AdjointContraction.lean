import Bilevel.Clipping
import Bilevel.SpectralInverse
import Bilevel.StochasticInner
import Mathlib.Tactic

/-! Actual projected adjoint dynamics from 2601.tex, `eq:adjoint-step`.
The contraction estimate is derived from symmetric quadratic-form bounds;
the projection is the concrete radial projection onto the Euclidean ball.
-/
noncomputable section
namespace Smoothness2601.AdjointContraction
open scoped RealInnerProductSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem linear_step_contraction (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    {μ L α : ℝ} (_hμ : 0 < μ) (hμL : μ ≤ L) (hα : 0 ≤ α) (hstep : α * L ≤ 1)
    (lower : ∀ w, μ * ‖w‖ ^ 2 ≤ ⟪H w, w⟫)
    (upper : ∀ w, ⟪H w, w⟫ ≤ L * ‖w‖ ^ 2) (w : E) :
    ‖w - α • H w‖ ≤ (1 - α * μ) * ‖w‖ := by
  have hαμ : α * μ ≤ 1 := (mul_le_mul_of_nonneg_left hμL hα).trans hstep
  let T : E →ₗ[ℝ] E := LinearMap.id - α • H
  have heq : T w = w - α • H w := by simp [T]
  rw [← heq]
  apply Bilevel.SpectralInverse.coordinate_bound (hH.eigenvectorBasis rfl)
    T (fun i => 1 - α * hH.eigenvalues rfl i) _
    (sub_nonneg.mpr hαμ) _ w
  · intro v i
    dsimp [T]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change (hH.eigenvectorBasis rfl).repr v i - α * (hH.eigenvectorBasis rfl).repr (H v) i = _
    rw [hH.eigenvectorBasis_apply_self_apply rfl]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring
  · intro i
    have hi := Bilevel.SpectralInverse.eigenvalues_in_interval H hH lower upper i
    have h1 : α * hH.eigenvalues rfl i ≤ 1 :=
      (mul_le_mul_of_nonneg_left hi.2 hα).trans hstep
    rw [abs_of_nonneg (sub_nonneg.mpr h1)]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hi.1 hα) _

omit [FiniteDimensional ℝ E] in
theorem biased_drift_bound {μ α a : ℝ} (hμ : 0 < μ) (hα : 0 ≤ α)
    (ha : 0 ≤ a) (hstep : α * μ ≤ 1) (w d e : E)
    (hd : ‖d‖ ≤ (1 - α * μ) * ‖w‖) (he : ‖e‖ ≤ a) :
    ‖d - α • e‖ ^ 2 ≤ (1 - α * μ / 2) * ‖w‖ ^ 2 + 3 * α * a ^ 2 / μ := by
  have hcontract : 0 ≤ 1 - α * μ := sub_nonneg.mpr hstep
  have hn : ‖d - α • e‖ ≤ (1 - α * μ) * ‖w‖ + α * a := by
    have ht := norm_sub_le d (α • e)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα] at ht
    exact ht.trans (add_le_add hd (mul_le_mul_of_nonneg_left he hα))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ (1 - α * μ) * ‖w‖ + α * a)).mpr hn
  have hnorm : 0 ≤ ‖w‖ := norm_nonneg _
  have hcoef : (1 - α * μ) ^ 2 ≤ 1 - α * μ := by
    have hp : 0 ≤ α * μ := mul_nonneg hα hμ.le
    nlinarith
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w‖)
  have hcross : 2 * α * ‖w‖ * a ≤ α * μ / 2 * ‖w‖ ^ 2 + 2 * α * a ^ 2 / μ := by
    have hcombine : α * μ / 2 * ‖w‖ ^ 2 + 2 * α * a ^ 2 / μ =
        (α * μ ^ 2 * ‖w‖ ^ 2 / 2 + 2 * α * a ^ 2) / μ := by
      field_simp
      ring
    rw [hcombine]
    apply (le_div_iff₀ hμ).mpr
    have hh := mul_nonneg hα (sq_nonneg (μ * ‖w‖ - 2 * a))
    nlinarith
  have hα2 : α ^ 2 ≤ α / μ := (le_div_iff₀ hμ).mpr (by
    have hh := mul_le_mul_of_nonneg_left hstep hα
    nlinarith)
  have hα2' := mul_le_mul_of_nonneg_right hα2 (sq_nonneg a)
  have hsmaller : 2 * (1 - α * μ) * ‖w‖ * α * a ≤ 2 * α * ‖w‖ * a := by
    have hh := mul_nonneg (mul_nonneg (mul_nonneg hα hμ.le) hnorm)
      (mul_nonneg hα ha)
    nlinarith
  calc
    ‖d - α • e‖ ^ 2 ≤ ((1 - α * μ) * ‖w‖ + α * a) ^ 2 := hs
    _ = (1 - α * μ) ^ 2 * ‖w‖ ^ 2 +
        2 * (1 - α * μ) * ‖w‖ * α * a + α ^ 2 * a ^ 2 := by ring
    _ ≤ (1 - α * μ) * ‖w‖ ^ 2 + 2 * α * ‖w‖ * a + α / μ * a ^ 2 :=
      add_le_add (add_le_add hcoef' hsmaller) hα2'
    _ ≤ (1 - α * μ) * ‖w‖ ^ 2 +
        (α * μ / 2 * ‖w‖ ^ 2 + 2 * α * a ^ 2 / μ) + α / μ * a ^ 2 :=
      add_le_add_right (add_le_add_left hcross _) _
    _ = _ := by ring

def step (V α : ℝ) (H : E →ₗ[ℝ] E) (b v e ξ : E) : E :=
  Bilevel.Clipping.clip V (v - α • (H v - b + e + ξ))

omit [FiniteDimensional ℝ E] in
theorem solution_norm_le (H : E →ₗ[ℝ] E) {μ : ℝ} (hμ : 0 < μ)
    (lower : ∀ w, μ * ‖w‖ ^ 2 ≤ ⟪H w, w⟫)
    (b vstar : E) (hsol : H vstar = b) : ‖vstar‖ ≤ ‖b‖ / μ := by
  by_cases hz : ‖vstar‖ = 0
  · rw [hz]
    positivity
  · have hn : 0 < ‖vstar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hl := lower vstar
    rw [hsol] at hl
    have hc := hl.trans (real_inner_le_norm b vstar)
    have hmul : (μ * ‖vstar‖) * ‖vstar‖ ≤ ‖b‖ * ‖vstar‖ := by nlinarith
    have hlin := (mul_le_mul_right hn).mp hmul
    apply (le_div_iff₀ hμ).mpr
    nlinarith

omit [FiniteDimensional ℝ E] in
theorem solution_in_source_ball (H : E →ₗ[ℝ] E) {μ L₀ : ℝ} (hμ : 0 < μ)
    (lower : ∀ w, μ * ‖w‖ ^ 2 ≤ ⟪H w, w⟫)
    (b vstar : E) (hsol : H vstar = b) (hb : ‖b‖ ≤ L₀) :
    ‖vstar‖ ≤ max 1 (L₀ / μ) :=
  ((solution_norm_le H hμ lower b vstar hsol).trans
    (div_le_div_of_nonneg_right hb hμ.le)).trans (le_max_right _ _)

omit [FiniteDimensional ℝ E] in
theorem step_in_ball {V : ℝ} (hV : 0 ≤ V) (α : ℝ) (H : E →ₗ[ℝ] E)
    (b v e ξ : E) : ‖step V α H b v e ξ‖ ≤ V :=
  Bilevel.Clipping.bounded V hV _

theorem deterministic_drift (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    {μ L α a : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hα : 0 ≤ α)
    (ha : 0 ≤ a) (hstep : α * L ≤ 1)
    (lower : ∀ w, μ * ‖w‖ ^ 2 ≤ ⟪H w, w⟫)
    (upper : ∀ w, ⟪H w, w⟫ ≤ L * ‖w‖ ^ 2)
    (b v vstar e : E) (hsol : H vstar = b) (he : ‖e‖ ≤ a) :
    ‖v - α • (H v - b + e) - vstar‖ ^ 2 ≤
      (1 - α * μ / 2) * ‖v - vstar‖ ^ 2 + 3 * α * a ^ 2 / μ := by
  have hid : v - α • (H v - b + e) - vstar =
      ((v - vstar) - α • H (v - vstar)) - α • e := by
    rw [map_sub, hsol, smul_add, smul_sub]
    abel
  rw [hid]
  exact biased_drift_bound hμ hα ha
    ((mul_le_mul_of_nonneg_left hμL hα).trans hstep) _ _ _
    (linear_step_contraction H hH hμ hμL hα hstep lower upper _) he

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

omit [FiniteDimensional ℝ E] in
theorem clip_stronglyMeasurable (V : ℝ) {f : Ω → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun ω => Bilevel.Clipping.clip V (f ω)) := by
  have hcoef : StronglyMeasurable (fun ω => V / ‖f ω‖) :=
    (measurable_const.div hf.norm.measurable).stronglyMeasurable
  exact StronglyMeasurable.ite (measurableSet_le hf.norm.measurable measurable_const)
    hf (hcoef.smul hf)

/-- One update under its conditional sampling law. This holds for any
probability measure and any measurable centered noise with the stated second
moment; the drift, bias and projection are the actual update functions. -/
theorem one_step [CompleteSpace E] [IsProbabilityMeasure ν]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    {μ L α a V S : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hα : 0 ≤ α)
    (ha : 0 ≤ a) (hV : 0 ≤ V) (hstep : α * L ≤ 1)
    (lower : ∀ w, μ * ‖w‖ ^ 2 ≤ ⟪H w, w⟫)
    (upper : ∀ w, ⟪H w, w⟫ ≤ L * ‖w‖ ^ 2)
    (b v vstar e : E) (hsol : H vstar = b) (hvstar : ‖vstar‖ ≤ V) (he : ‖e‖ ≤ a)
    (noise : Ω → E) (hmeas : StronglyMeasurable noise) (hnoise : Integrable noise ν)
    (hsq : Integrable (fun ω => ‖noise ω‖ ^ 2) ν)
    (hmean : (∫ ω, noise ω ∂ν) = 0) (hvar : (∫ ω, ‖noise ω‖ ^ 2 ∂ν) ≤ S) :
    (∫ ω, ‖step V α H b v e (noise ω) - vstar‖ ^ 2 ∂ν) ≤
      (1 - α * μ / 2) * ‖v - vstar‖ ^ 2 + 3 * α * a ^ 2 / μ + α ^ 2 * S := by
  let d := v - α • (H v - b + e) - vstar
  have hid (ω : Ω) : v - α • (H v - b + e + noise ω) - vstar = d - α • noise ω := by
    dsimp [d]
    rw [smul_add]
    abel
  have hraw : Integrable (fun ω => ‖d - α • noise ω‖ ^ 2) ν := by
    have hi : Integrable (fun ω => ⟪d, noise ω⟫) ν := hnoise.const_inner d
    have hx : (fun ω => ‖d - α • noise ω‖ ^ 2) =
        fun ω => (‖d‖ ^ 2 + α ^ 2 * ‖noise ω‖ ^ 2) - 2 * α * ⟪d, noise ω⟫ := by
      funext ω
      simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [hx]
    exact ((integrable_const _).add (hsq.const_mul _)).sub (hi.const_mul _)
  have hle (ω : Ω) : ‖step V α H b v e (noise ω) - vstar‖ ^ 2 ≤
      ‖d - α • noise ω‖ ^ 2 := by
    have hp := Bilevel.Clipping.squared_error_nonincreasing V hV
      (v - α • (H v - b + e + noise ω)) vstar hvstar
    simpa only [step, hid] using hp
  have hsm : StronglyMeasurable (fun ω => step V α H b v e (noise ω)) := by
    apply clip_stronglyMeasurable
    exact stronglyMeasurable_const.sub
      ((stronglyMeasurable_const.add hmeas).const_smul α)
  have hproj : Integrable (fun ω => ‖step V α H b v e (noise ω) - vstar‖ ^ 2) ν := by
    have hms : StronglyMeasurable (fun ω => ‖step V α H b v e (noise ω) - vstar‖) :=
      (hsm.sub stronglyMeasurable_const).norm
    have hmsq : StronglyMeasurable (fun ω => ‖step V α H b v e (noise ω) - vstar‖ ^ 2) := by
      simpa only [pow_two] using hms.mul hms
    apply hraw.mono' hmsq.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_sq] using hle ω
  have hint := integral_mono_ae hproj hraw (Filter.Eventually.of_forall hle)
  rw [Bilevel.StochasticInner.fixed_step_identity d noise α hnoise hsq hmean] at hint
  have hdrift := deterministic_drift H hH hμ hμL hα ha hstep lower upper b v vstar e hsol he
  have hn := mul_le_mul_of_nonneg_left hvar (sq_nonneg α)
  change ‖d‖ ^ 2 ≤ _ at hdrift
  linarith

theorem bias_floor {α μ a : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    (3 * α * a ^ 2 / μ) / (1 - (1 - α * μ / 2)) = 6 * a ^ 2 / μ ^ 2 := by
  field_simp
  ring

theorem chosen_stepsize_range {μ L : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) :
    0 < 1 / (2 * L) ∧ (1 / (2 * L)) * L ≤ 1 ∧
      0 < 1 - (1 / (2 * L)) * μ / 2 ∧ 1 - (1 / (2 * L)) * μ / 2 < 1 := by
  have hL : 0 < L := hμ.trans_le hμL
  have hα : 0 < 1 / (2 * L) := by positivity
  have he : (1 / (2 * L)) * L = 1 / 2 := by field_simp; ring
  have hm := mul_le_mul_of_nonneg_left hμL hα.le
  rw [he] at hm
  have hp := mul_pos hα hμ
  exact ⟨hα, by rw [he]; norm_num, by linarith, by linarith⟩

end Smoothness2601.AdjointContraction
