import Nonsmooth.GaussianPosteriorEnergy
import Nonsmooth.PosteriorSupportTail
import Nonsmooth.GaussianAdaptiveRows

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

def supportAmbientPolicy (p : Policy Ω S (Feasible E 1)) : Policy Ω S E :=
  p.simulate Subtype.val (fun _ y => y)

theorem supportAmbientPolicy_measurable (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) :
    (supportAmbientPolicy p).IsMeasurable :=
  simulation_measurable hp measurable_subtype_coe measurable_snd

theorem supportAmbientPolicy_result (p : Policy Ω S (Feasible E 1)) (f : E → ℝ) (ω : Ω) (T : ℕ) :
    (supportAmbientPolicy p).result f ω T = (p.result (fun x => f x.val) ω T).val :=
  simulation_output_exact p Subtype.val (fun _ y => y) f (fun x => f x.val) (fun _ => rfl) ω T

theorem gaussianSupportPrior_gap_of_ambient_bad {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 256 ≤ Module.finrank ℝ E) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)).real {a : Fin k → E |
      finiteSupport a (supportPolicyOutput p ω T a) < -((1 : ℝ) / (8 * Real.sqrt k))} ≤ 1 / 8 →
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val -
          minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro hbad
  let Q := gaussianSupportPrior E k
  let A : Set (BoundedSupportRows E (Fin k)) := {a |
    (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a)}
  let B : Set (Fin k → E) := {a |
    -((1 : ℝ) / (8 * Real.sqrt k)) ≤ finiteSupport a (supportPolicyOutput p ω T a)}
  let rows : BoundedSupportRows E (Fin k) → (Fin k → E) := fun a i => (a i).val
  have hmrows : Measurable rows :=
    measurable_pi_lambda _ (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
  have hB : MeasurableSet B := measurableSet_le measurable_const (supportPolicyValue_measurable p hp ω T)
  have hBraw : 7 / 8 ≤ (Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)).real B := by
    have hsum := measureReal_add_measureReal_compl
      (μ := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)) hB
    have he : Bᶜ = {a : Fin k → E |
      finiteSupport a (supportPolicyOutput p ω T a) < -((1 : ℝ) / (8 * Real.sqrt k))} := by
      ext a
      simp only [B, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [he, measureReal_univ_eq_one] at hsum
    linarith
  have hBprob : 7 / 8 ≤ Q.real (rows ⁻¹' B) := by
    have he := congrArg (fun μ : Measure (Fin k → E) => μ.real B) (gaussianSupportPrior_ambient_map (E := E) k)
    try dsimp only at he
    rw [map_measureReal_apply hmrows hB] at he
    exact hBraw.trans_eq he.symm
  have hA : 7 / 8 ≤ Q.real A := gaussianSupportPrior_negative_event hd hk hkd
  have hinter : 3 / 4 ≤ Q.real (A ∩ rows ⁻¹' B) := by
    have h := measureReal_union_add_inter (μ := Q) (s := A) (hmrows hB)
    have hu : Q.real (A ∪ rows ⁻¹' B) ≤ 1 := by
      simpa only [measureReal_univ_eq_one] using
        measureReal_mono (μ := Q) (Set.subset_univ (A ∪ rows ⁻¹' B)) (measure_ne_top _ _)
    linarith
  apply hinter.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro a ⟨ha, hb⟩
  change (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a) at ha
  change -((1 : ℝ) / (8 * Real.sqrt k)) ≤
    boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val at hb
  change 7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
    boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val -
      minimumValue 1 (boundedFiniteSupport a)
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hmargin : 7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
      (1 / 4 : ℝ) / Real.sqrt k - 1 / (8 * Real.sqrt k) := by
    convert! mul_lt_mul_of_pos_right (by norm_num : (7 / 64 : ℝ) < 1 / 8) (inv_pos.mpr hs) using 1 <;> first | rfl | ring
  linarith

theorem gaussianSupportPrior_gap_of_posterior_moments {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 256 ≤ Module.finrank ℝ E) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    let M := gaussianSupportMean (supportAmbientPolicy p) ω T
    (∫ a, ‖M a‖ ^ 2 ∂Q) ≤ (k : ℝ) / 4096 →
    (∫ a, ⟪(∑ i, a i) - M a, supportPolicyOutput p ω T a⟫_ℝ ^ 2 ∂Q) ≤ (k : ℝ) / 4096 →
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val -
          minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  dsimp only
  let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
  intro henergy hresidual
  have hq := supportAmbientPolicy_measurable p hp
  have hX : @Measurable (Fin k → E) E
      (supportTranscriptInformation (supportAmbientPolicy p) ω T) inferInstance (supportPolicyOutput p ω T) := by
    have h := support_output_transcript_measurable (k := k) (supportAmbientPolicy p) hq ω T
    convert! h using 1
    funext a
    simp only [supportAmbientPolicy_result, supportPolicyOutput]
  have hXb (a : Fin k → E) : ‖supportPolicyOutput p ω T a‖ ≤ 1 := (p.result _ ω T).property
  have h := posterior_support_output_tail hk Q
    (supportTranscriptInformation_le (supportAmbientPolicy p) hq ω T)
    (supportPolicyOutput p ω T) hX.aestronglyMeasurable hXb
    gaussianAmbientRows_aggregate_memLp henergy hresidual
  apply gaussianSupportPrior_gap_of_ambient_bad hk p hp ω T hd hkd
  apply h.trans
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (div_le_iff₀ hk').mpr
  nlinarith

end
end Nonsmooth
