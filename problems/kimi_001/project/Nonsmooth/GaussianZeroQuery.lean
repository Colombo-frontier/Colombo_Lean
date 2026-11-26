import Nonsmooth.GaussianLinearTail

open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSupportPrior_fixed_output_gap (hd : 256 ≤ Module.finrank ℝ E)
    {k : ℕ} (hk : 0 < k) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512)
    (W : Feasible E 1) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a W.val - minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let i : Fin k := ⟨0, hk⟩
  let Q := gaussianSupportPrior E k
  let A : Set (BoundedSupportRows E (Fin k)) :=
    {a | (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a)}
  let B : Set (BoundedSupportRows E (Fin k)) :=
    {a | -((1 : ℝ) / (8 * Real.sqrt k)) ≤ ⟪W.val, (a i).val⟫_ℝ}
  have hB : MeasurableSet B := measurableSet_le measurable_const
    (continuous_const.inner (continuous_subtype_val.comp (continuous_apply i))).measurable
  have hbad : Q.real Bᶜ ≤ 1 / 8 := by
    have hs : MeasurableSet {a : Feasible E 2 | ⟪W.val, a.val⟫_ℝ < -((1 : ℝ) / (8 * Real.sqrt k))} :=
      measurableSet_lt (continuous_const.inner continuous_subtype_val).measurable measurable_const
    have hm := map_measureReal_apply (μ := Q) (gaussianSupportPrior_coordinate (E := E) i).measurable hs
    rw [(gaussianSupportPrior_coordinate (E := E) i).map_eq] at hm
    have he : Bᶜ = (fun a : BoundedSupportRows E (Fin k) => a i) ⁻¹'
        {a : Feasible E 2 | ⟪W.val, a.val⟫_ℝ < -((1 : ℝ) / (8 * Real.sqrt k))} := by
      ext a
      simp only [B, Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, not_le]
    rw [he, ← hm]
    exact gaussianSupportRowLaw_fixed_direction_tail hk hkd W.property
  have hBprob : 7 / 8 ≤ Q.real B := by
    have hsum := measureReal_add_measureReal_compl (μ := Q) hB
    rw [measureReal_univ_eq_one] at hsum
    linarith
  have hA : 7 / 8 ≤ Q.real A := gaussianSupportPrior_negative_event hd hk hkd
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
  change -((1 : ℝ) / (8 * Real.sqrt k)) ≤ ⟪W.val, (a i).val⟫_ℝ at hb
  change 7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
    boundedFiniteSupport a W.val - minimumValue 1 (boundedFiniteSupport a)
  have hge : ⟪W.val, (a i).val⟫_ℝ ≤ boundedFiniteSupport a W.val := by
    rw [real_inner_comm]
    exact finiteSupport_ge (fun i => (a i).val) W.val i
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hmargin : 7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
      (1 / 4 : ℝ) / Real.sqrt k - 1 / (8 * Real.sqrt k) := by
    convert! mul_lt_mul_of_pos_right (by norm_num : (7 / 64 : ℝ) < 1 / 8) (inv_pos.mpr hs) using 1 <;> first | rfl | ring
  linarith

theorem gaussianSupportPrior_zero_query_gap (hd : 256 ≤ Module.finrank ℝ E)
    {k : ℕ} (hk : 0 < k) (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512)
    {Ω S : Type} (q : Policy Ω S (Feasible E 1)) (ω : Ω) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (q.result (fun x => boundedFiniteSupport a x.val) ω 0).val -
          minimumValue 1 (boundedFiniteSupport a)} :=
  gaussianSupportPrior_fixed_output_gap hd hk hkd (q.output ω (q.initial ω))

end
end Nonsmooth
