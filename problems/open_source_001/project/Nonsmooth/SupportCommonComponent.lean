import Nonsmooth.GaussianRowCentering
import Nonsmooth.GaussianAdaptiveSquare

open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem gaussianScaleRows_continuous (k : ℕ) : Continuous (gaussianScaleRows E k) :=
  continuous_pi (fun i => continuous_const.smul (continuous_apply i))

theorem finiteSupport_smul_rows {k : ℕ} [Nonempty (Fin k)] (b : Fin k → E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    finiteSupport (fun i => c • b i) x = c * finiteSupport b x := by
  calc
    _ = finiteSupport b (c • x) := by simp only [finiteSupport, real_inner_smul_left, inner_smul_right]
    _ = _ := finiteSupport_homogeneous b hc x

theorem gaussianScaleRows_centered_nonneg {k : ℕ} (hk : 0 < k) (b : Fin k → E) (x : E) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    0 ≤ finiteSupport (gaussianScaleRows E k (centeredSupportRows b)) x := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  change 0 ≤ finiteSupport (fun i => (Real.sqrt (Module.finrank ℝ E))⁻¹ • centeredSupportRows b i) x
  rw [finiteSupport_smul_rows _ (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (finiteSupport_centered_nonneg hk b x)

theorem gaussianScaleRows_recombine_support {k : ℕ} [Nonempty (Fin k)] (b : Fin k → E) (z x : E) :
    finiteSupport (gaussianScaleRows E k (gaussianRowsRecombine (b, z))) x =
      finiteSupport (gaussianScaleRows E k (centeredSupportRows b)) x +
        ((Real.sqrt (Module.finrank ℝ E))⁻¹ * (Real.sqrt k)⁻¹) * ⟪z, x⟫_ℝ := by
  have he : gaussianScaleRows E k (gaussianRowsRecombine (b, z)) =
      fun i => gaussianScaleRows E k (centeredSupportRows b) i +
        ((Real.sqrt (Module.finrank ℝ E))⁻¹ * (Real.sqrt k)⁻¹) • z := by
    funext i
    simp only [gaussianScaleRows, gaussianRowsRecombine, smul_add, smul_smul]
  rw [he, finiteSupport_add_common, real_inner_smul_left]

def supportPolicyOutput {k : ℕ} [Nonempty (Fin k)] (p : Policy Ω S (Feasible E 1))
    (ω : Ω) (T : ℕ) (a : Fin k → E) : E :=
  (p.result (fun x => finiteSupport a x.val) ω T).val

theorem supportPolicyOutput_measurable {k : ℕ} [Nonempty (Fin k)]
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ) :
    Measurable (supportPolicyOutput (k := k) p ω T) := by
  have hF : Measurable (Function.uncurry (fun (a : Fin k → E) (x : Feasible E 1) => finiteSupport a x.val)) :=
    finiteSupport_joint_continuous.measurable.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  exact measurable_subtype_coe.comp ((family_policy_output_measurable hp _ hF T).comp
    (measurable_id.prodMk measurable_const))

theorem supportPolicyValue_measurable {k : ℕ} [Nonempty (Fin k)]
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ) :
    Measurable (fun a : Fin k → E => finiteSupport a (supportPolicyOutput p ω T a)) :=
  finiteSupport_joint_continuous.measurable.comp
    (measurable_id.prodMk (supportPolicyOutput_measurable p hp ω T))

theorem supportPolicyOutput_recombine {k : ℕ} [Nonempty (Fin k)]
    (p : Policy Ω S (Feasible E 1)) (ω : Ω) (T : ℕ) (b : Fin k → E) (z : E) :
    supportPolicyOutput p ω T (gaussianScaleRows E k (gaussianRowsRecombine (b, z))) =
      (p.result (fun x => finiteSupport (gaussianScaleRows E k (centeredSupportRows b)) x.val +
        ((Real.sqrt (Module.finrank ℝ E))⁻¹ * (Real.sqrt k)⁻¹) * ⟪z, x.val⟫_ℝ) ω T).val := by
  have he : (fun x : Feasible E 1 => finiteSupport (gaussianScaleRows E k (gaussianRowsRecombine (b, z))) x.val) =
      fun x => finiteSupport (gaussianScaleRows E k (centeredSupportRows b)) x.val +
        ((Real.sqrt (Module.finrank ℝ E))⁻¹ * (Real.sqrt k)⁻¹) * ⟪z, x.val⟫_ℝ :=
    funext (fun x => gaussianScaleRows_recombine_support b z x.val)
  simp only [supportPolicyOutput, he]

theorem gaussian_recombined_output_bad {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 2048 ≤ Module.finrank ℝ E) (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2048)
    (b : Fin k → E) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    (euclideanGaussianLaw E).real {z : E |
      finiteSupport (gaussianScaleRows E k (gaussianRowsRecombine (b, z)))
        (supportPolicyOutput p ω T (gaussianScaleRows E k (gaussianRowsRecombine (b, z)))) <
          -((1 : ℝ) / (8 * Real.sqrt k))} ≤ 1 / 16 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let H : Feasible E 1 → ℝ := fun x => finiteSupport (gaussianScaleRows E k (centeredSupportRows b)) x.val
  let c : ℝ := (Real.sqrt (Module.finrank ℝ E))⁻¹ * (Real.sqrt k)⁻¹
  have hH : Measurable H := finiteSupport_joint_continuous.measurable.comp
    (measurable_const.prodMk measurable_subtype_coe)
  apply le_trans (measureReal_mono (μ := euclideanGaussianLaw E) _ (measure_ne_top _ _))
    (gaussian_known_offset_output_tail p hp hH c ω T hd hT)
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  rw [gaussianScaleRows_recombine_support (E := E) b z,
    supportPolicyOutput_recombine p ω T b z] at hz
  let W : Feasible E 1 := p.result (fun x => H x + c * ⟪z, x.val⟫_ℝ) ω T
  change H W + c * ⟪z, W.val⟫_ℝ < -((1 : ℝ) / (8 * Real.sqrt k)) at hz
  change ⟪W.val, z⟫_ℝ < -(Real.sqrt (Module.finrank ℝ E) / 8)
  have hnonneg : 0 ≤ H W := gaussianScaleRows_centered_nonneg hk b W.val
  have hdk : 0 < Real.sqrt (Module.finrank ℝ E) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  have hkk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hc : 0 < c := mul_pos (inv_pos.mpr hdk) (inv_pos.mpr hkk)
  have he : -((1 : ℝ) / (8 * Real.sqrt k)) = c * (-(Real.sqrt (Module.finrank ℝ E) / 8)) := by
    dsimp only [c]
    field_simp
  have hi : c * ⟪z, W.val⟫_ℝ < c * (-(Real.sqrt (Module.finrank ℝ E) / 8)) := by rw [← he]; linarith
  rw [real_inner_comm]
  exact (mul_lt_mul_iff_of_pos_left hc).mp hi

end
end Nonsmooth
