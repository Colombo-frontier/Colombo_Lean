import Nonsmooth.SupportCommonComponent

open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem gaussian_raw_support_output_bad {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 2048 ≤ Module.finrank ℝ E) (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2048) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real {b : Fin k → E |
      finiteSupport (gaussianScaleRows E k b) (supportPolicyOutput p ω T (gaussianScaleRows E k b)) <
        -((1 : ℝ) / (8 * Real.sqrt k))} ≤ 1 / 16 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let bad : Set (Fin k → E) := {b |
    finiteSupport (gaussianScaleRows E k b) (supportPolicyOutput p ω T (gaussianScaleRows E k b)) <
      -((1 : ℝ) / (8 * Real.sqrt k))}
  have hbad : MeasurableSet bad := measurableSet_lt
    ((supportPolicyValue_measurable p hp ω T).comp (gaussianScaleRows_measurable k)) measurable_const
  have hprob : ((Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).prod (euclideanGaussianLaw E)).real
      ((gaussianRowsRecombine (E := E) (k := k)) ⁻¹' bad) ≤ 1 / 16 := by
    apply product_probability_of_slice_bound _ _ _
      ((gaussianRowsRecombine_continuous k).measurable hbad) (by norm_num)
    intro b
    exact gaussian_recombined_output_bad hk p hp ω T hd hT b
  have hm := congrArg (fun μ : Measure (Fin k → E) => μ.real bad) (gaussianRows_recombine_law (E := E) hk)
  try dsimp only at hm
  rw [map_measureReal_apply (gaussianRowsRecombine_continuous k).measurable hbad] at hm
  exact hm.symm.trans_le hprob

theorem gaussianSupportPrior_event_of_raw_probability {k : ℕ}
    (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 16)
    (s : Set (Fin k → E)) (hs : MeasurableSet s)
    (hraw : 15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      ((gaussianScaleRows E k) ⁻¹' s)) :
    7 / 8 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) | (fun i => (a i).val) ∈ s} := by
  have ht := gaussian_truncated_product_event hkd _ ((gaussianScaleRows_measurable k) hs) hraw
  have hm : Measurable (fun a : BoundedSupportRows E (Fin k) => fun i => (a i).val) :=
    measurable_pi_lambda _ (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
  have he : Measure.map (fun a : BoundedSupportRows E (Fin k) => fun i => (a i).val) (gaussianSupportPrior E k) =
      Measure.map (gaussianScaleRows E k) (Measure.pi (fun _ : Fin k => truncatedGaussianLaw E)) :=
    (gaussianSupportPrior_ambient_map k).trans (gaussianScaledProduct_map k).symm
  have hprob := congrArg (fun μ : Measure (Fin k → E) => μ.real s) he
  try dsimp only at hprob
  rw [map_measureReal_apply hm hs, map_measureReal_apply (gaussianScaleRows_measurable k) hs] at hprob
  exact ht.trans_eq hprob.symm

theorem gaussianSupportPrior_adaptive_output_value {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 2048 ≤ Module.finrank ℝ E) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512)
    (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2048) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    7 / 8 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      -((1 : ℝ) / (8 * Real.sqrt k)) ≤
        boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let s : Set (Fin k → E) := {a | -((1 : ℝ) / (8 * Real.sqrt k)) ≤
    finiteSupport a (supportPolicyOutput p ω T a)}
  have hs : MeasurableSet s := measurableSet_le measurable_const (supportPolicyValue_measurable p hp ω T)
  have hraw : 15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      ((gaussianScaleRows E k) ⁻¹' s) := by
    have hbad := gaussian_raw_support_output_bad hk p hp ω T hd hT
    have hsum := measureReal_add_measureReal_compl
      (μ := Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)) ((gaussianScaleRows_measurable k) hs)
    have he : ((gaussianScaleRows E k) ⁻¹' s)ᶜ = {b : Fin k → E |
        finiteSupport (gaussianScaleRows E k b) (supportPolicyOutput p ω T (gaussianScaleRows E k b)) <
          -((1 : ℝ) / (8 * Real.sqrt k))} := by
      ext b
      simp only [s, Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, not_le]
    rw [he, measureReal_univ_eq_one] at hsum
    linarith
  have hkd' : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 16 := by
    have hd0 : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    linarith
  exact gaussianSupportPrior_event_of_raw_probability hkd' s hs hraw

/-- Positive-budget adaptive hardness for every admissible k, on the manuscript's
actual fixed prior. The proved budget is T<=d/2048, without the extra k/log(e*k)
factor required by the full external support theorem. -/
theorem gaussianSupportPrior_adaptive_gap_linear_budget {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 2048 ≤ Module.finrank ℝ E) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512)
    (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2048) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val -
          minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let Q := gaussianSupportPrior E k
  let A : Set (BoundedSupportRows E (Fin k)) := {a |
    (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a)}
  let B : Set (BoundedSupportRows E (Fin k)) := {a |
    -((1 : ℝ) / (8 * Real.sqrt k)) ≤
      boundedFiniteSupport a (p.result (fun x => boundedFiniteSupport a x.val) ω T).val}
  have hA : 7 / 8 ≤ Q.real A := gaussianSupportPrior_negative_event (by omega) hk hkd
  have hBprob : 7 / 8 ≤ Q.real B := gaussianSupportPrior_adaptive_output_value hk p hp ω T hd hkd hT
  have hrows : Measurable (fun a : BoundedSupportRows E (Fin k) => fun i => (a i).val) :=
    measurable_pi_lambda _ (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
  have hB : MeasurableSet B := measurableSet_le measurable_const
    ((supportPolicyValue_measurable p hp ω T).comp hrows)
  have hinter : 3 / 4 ≤ Q.real (A ∩ B) := by
    have h := measureReal_union_add_inter (μ := Q) (s := A) hB
    have hu : Q.real (A ∪ B) ≤ 1 := by
      simpa only [measureReal_univ_eq_one] using
        measureReal_mono (μ := Q) (Set.subset_univ (A ∪ B)) (measure_ne_top _ _)
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

theorem gaussianSupportPrior_adaptive_gap_linear_budget_unbounded {k : ℕ} (hk : 0 < k)
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (T : ℕ)
    (hd : 2048 ≤ Module.finrank ℝ E) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512)
    (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2048) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    (∀ a : BoundedSupportRows E (Fin k), ‖p.result (boundedFiniteSupport a) ω T‖ ≤ 1) →
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (boundedFiniteSupport a) ω T) - minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro hout
  have h := gaussianSupportPrior_adaptive_gap_linear_budget hk (supportUnitPolicy p)
    (supportUnitPolicy_measurable hp) ω T hd hkd hT
  have he : {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a ((supportUnitPolicy p).result (fun x => boundedFiniteSupport a x.val) ω T).val -
          minimumValue 1 (boundedFiniteSupport a)} =
      {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (boundedFiniteSupport a) ω T) - minimumValue 1 (boundedFiniteSupport a)} := by
    ext a
    simp only [Set.mem_setOf_eq, supportUnitPolicy_result_of_feasible p (boundedFiniteSupport_model a) ω T (hout a)]
  rwa [he] at h

end
end Nonsmooth
