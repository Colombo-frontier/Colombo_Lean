import Nonsmooth.GaussianZeroQuery
import Nonsmooth.SupportQueryNormalization

open MeasureTheory ProbabilityTheory Function Filter
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {Ω S : Type} [MeasurableSpace Ω] [mS : MeasurableSpace S]

theorem euclideanGaussianLaw_radial_reconstruct :
    Measure.map (fun z : ℝ × E => z.1 • z.2)
      ((Measure.map (fun z : E => ‖z‖) (euclideanGaussianLaw E)).prod (sphericalLaw E)) =
        euclideanGaussianLaw E := by
  rw [← euclideanGaussianLaw_polar, Measure.map_map (g := fun p : ℝ × E => p.1 • p.2) (measurable_fst.smul measurable_snd)
    (continuous_norm.measurable.prodMk normalizedDirection_measurable)]
  have hid : ((fun p : ℝ × E => p.1 • p.2) ∘
      (fun z : E => (‖z‖, normalizedDirection z))) = id :=
    funext normalizedDirection_reconstruct
  rw [hid]
  exact Measure.map_id

theorem linearPolicyOutput_scale (p : Policy Ω S (Feasible E 1)) (c : ℝ) (ω : Ω) (T : ℕ) (u : E) :
    linearPolicyOutput p 1 ω T (c • u) = linearPolicyOutput p c ω T u := by
  simp only [linearPolicyOutput, one_mul, real_inner_smul_left]

theorem linear_policy_output_square (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (c : ℝ) (ω : Ω) (T : ℕ) (hT : T + 1 ≤ Module.finrank ℝ E) :
    (∫ u : E, ⟪linearPolicyOutput p c ω T u, u⟫_ℝ ^ 2 ∂sphericalLaw E) ≤
      ((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  apply spherical_adaptive_output_square (policyLinearQuery p 0 (-c) ω)
    (linearPolicyOutput p c ω T) T hT
    (fun n _ => continuous_policy_query_measurable p hp ω n)
    (linearPolicyOutput_known p hp c ω T)
  exact Eventually.of_forall (fun u => (p.result (fun x => c * ⟪u, x.val⟫_ℝ) ω T).property)

theorem gaussian_linear_policy_square_integrable (p : Policy Ω S (Feasible E 1))
    (hp : p.IsMeasurable) (ω : Ω) (T : ℕ) :
    Integrable (fun z : E => ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ ^ 2) (euclideanGaussianLaw E) := by
  have hW : Measurable (linearPolicyOutput p 1 ω T) :=
    (linearPolicyOutput_joint_measurable p hp ω T).comp (measurable_const.prodMk measurable_id)
  have hV : MemLp (fun z : E => z) 2 (euclideanGaussianLaw E) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
      euclideanGaussian_norm_square_integrable
  apply (MemLp.mono' hV.norm ((continuous_fst.inner continuous_snd).measurable.comp
    (hW.prodMk measurable_id)).aestronglyMeasurable _).integrable_sq
  apply Eventually.of_forall
  intro z
  change ‖⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ‖ ≤ ‖z‖
  have hw : ‖linearPolicyOutput p 1 ω T z‖ ≤ 1 := (p.result _ ω T).property
  exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg z])

theorem gaussian_linear_policy_output_square (p : Policy Ω S (Feasible E 1))
    (hp : p.IsMeasurable) (ω : Ω) (T : ℕ) (hT : T + 1 ≤ Module.finrank ℝ E) :
    (∫ z : E, ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) ≤ (T : ℝ) + 1 := by
  let R := Measure.map (fun z : E => ‖z‖) (euclideanGaussianLaw E)
  let F : E → ℝ := fun z => ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ ^ 2
  have hW : Measurable (linearPolicyOutput p 1 ω T) :=
    (linearPolicyOutput_joint_measurable p hp ω T).comp (measurable_const.prodMk measurable_id)
  have hF : StronglyMeasurable F :=
    (((continuous_fst.inner continuous_snd).measurable.comp (hW.prodMk measurable_id)).pow_const 2).stronglyMeasurable
  have hpmap : MeasurePreserving (fun z : ℝ × E => z.1 • z.2) (R.prod (sphericalLaw E)) (euclideanGaussianLaw E) :=
    ⟨measurable_fst.smul measurable_snd, euclideanGaussianLaw_radial_reconstruct⟩
  have hprod : Integrable (fun z : ℝ × E => F (z.1 • z.2)) (R.prod (sphericalLaw E)) :=
    (hpmap.integrable_comp hF.aestronglyMeasurable).mpr (gaussian_linear_policy_square_integrable p hp ω T)
  have hiR : Integrable (fun r : ℝ => r ^ 2) R :=
    ((show MeasurePreserving (fun z : E => ‖z‖) (euclideanGaussianLaw E) R from
      ⟨continuous_norm.measurable, rfl⟩).integrable_comp (continuous_id.pow 2).measurable.aestronglyMeasurable).mp
      euclideanGaussian_norm_square_integrable
  have hR : (∫ r : ℝ, r ^ 2 ∂R) = (Module.finrank ℝ E : ℝ) := by
    dsimp only [R]
    have hc : StronglyMeasurable (fun r : ℝ => r ^ 2) := (continuous_id.pow 2).stronglyMeasurable
    exact (integral_map_of_stronglyMeasurable continuous_norm.measurable hc).trans
      euclideanGaussian_norm_second_moment
  have hpoint (r : ℝ) : (∫ u : E, F (r • u) ∂sphericalLaw E) ≤
      r ^ 2 * (((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ)) := by
    have he (u : E) : F (r • u) = r ^ 2 * ⟪linearPolicyOutput p r ω T u, u⟫_ℝ ^ 2 := by
      dsimp only [F]
      rw [linearPolicyOutput_scale, inner_smul_right, mul_pow]
    simp_rw [he]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (linear_policy_output_square p hp r ω T hT) (sq_nonneg r)
  calc
    _ = ∫ z : ℝ × E, F (z.1 • z.2) ∂R.prod (sphericalLaw E) := by
      have hm := integral_map_of_stronglyMeasurable (μ := R.prod (sphericalLaw E)) hpmap.measurable hF
      rw [hpmap.map_eq] at hm
      exact hm
    _ = ∫ r : ℝ, ∫ u : E, F (r • u) ∂sphericalLaw E ∂R := integral_prod _ hprod
    _ ≤ ∫ r : ℝ, r ^ 2 * (((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ)) ∂R :=
      integral_mono hprod.integral_prod_left (hiR.mul_const _) hpoint
    _ = (T : ℝ) + 1 := by
      rw [integral_mul_const, hR]
      have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := (Nat.cast_pos.mpr Module.finrank_pos).ne'
      field_simp

theorem gaussian_linear_policy_output_tail (p : Policy Ω S (Feasible E 1))
    (hp : p.IsMeasurable) (ω : Ω) (T : ℕ) (hT : T + 1 ≤ Module.finrank ℝ E)
    {r : ℝ} (hr : 0 < r) :
    (euclideanGaussianLaw E).real {z : E | ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ < -r} ≤
      ((T : ℝ) + 1) / r ^ 2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := euclideanGaussianLaw E)
    (f := fun z : E => ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ ^ 2)
    (Eventually.of_forall (fun _ => sq_nonneg _)) (gaussian_linear_policy_square_integrable p hp ω T) (r ^ 2)
  have hsub : {z : E | ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ < -r} ⊆
      {z : E | r ^ 2 ≤ ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ ^ 2} := by
    intro z hz
    change r ^ 2 ≤ ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ ^ 2
    have hz' : ⟪linearPolicyOutput p 1 ω T z, z⟫_ℝ < -r := hz
    nlinarith
  have hprob := mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := euclideanGaussianLaw E) hsub (measure_ne_top _ _)) (sq_nonneg r)
  have he := gaussian_linear_policy_output_square p hp ω T hT
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

def knownOffsetPolicy (p : Policy Ω S (Feasible E 1)) (H : Feasible E 1 → ℝ) (c : ℝ) :
    Policy Ω S (Feasible E 1) := p.simulate id (fun x y => H x + c * y)

theorem knownOffsetPolicy_measurable (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    {H : Feasible E 1 → ℝ} (hH : Measurable H) (c : ℝ) : (knownOffsetPolicy p H c).IsMeasurable :=
  simulation_measurable hp measurable_id ((hH.comp measurable_fst).add (measurable_const.mul measurable_snd))

theorem knownOffsetPolicy_output (p : Policy Ω S (Feasible E 1)) (H : Feasible E 1 → ℝ)
    (c : ℝ) (ω : Ω) (T : ℕ) (z : E) :
    linearPolicyOutput (knownOffsetPolicy p H c) 1 ω T z =
      (p.result (fun x => H x + c * ⟪z, x.val⟫_ℝ) ω T).val := by
  have he := simulation_output_exact p id (fun x y => H x + c * y)
    (fun x : Feasible E 1 => ⟪z, x.val⟫_ℝ) (fun x => H x + c * ⟪z, x.val⟫_ℝ) (fun _ => rfl) ω T
  simpa only [linearPolicyOutput, one_mul, knownOffsetPolicy, id_eq] using congrArg Subtype.val he

theorem gaussian_known_offset_output_tail (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    {H : Feasible E 1 → ℝ} (hH : Measurable H) (c : ℝ) (ω : Ω) (T : ℕ)
    (hd : 2048 ≤ Module.finrank ℝ E) (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2048) :
    (euclideanGaussianLaw E).real {z : E |
      ⟪(p.result (fun x => H x + c * ⟪z, x.val⟫_ℝ) ω T).val, z⟫_ℝ <
        -(Real.sqrt (Module.finrank ℝ E) / 8)} ≤ 1 / 16 := by
  have hd' : (2048 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hT' : T + 1 ≤ Module.finrank ℝ E := by
    have h : (T : ℝ) + 1 ≤ Module.finrank ℝ E := by linarith
    exact_mod_cast h
  have hdpos : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hr : 0 < Real.sqrt (Module.finrank ℝ E) / 8 := by positivity
  have h := gaussian_linear_policy_output_tail (knownOffsetPolicy p H c)
    (knownOffsetPolicy_measurable p hp hH c) ω T hT' hr
  simp_rw [knownOffsetPolicy_output] at h
  apply h.trans
  rw [div_pow, Real.sq_sqrt hdpos.le]
  apply (div_le_iff₀ (by positivity : 0 < (Module.finrank ℝ E : ℝ) / 8 ^ 2)).mpr
  norm_num
  linarith

end
end Nonsmooth
