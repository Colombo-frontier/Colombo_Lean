import Nonsmooth.GaussianHardnessReduction
import Nonsmooth.ProjectedPolicy

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem support_normalized_response {h : E → ℝ} (hh : SupportModel h) (x : E) :
    max 1 ‖x‖ * h (projectPoint 1 (by norm_num) x).val = h x := by
  change max 1 ‖x‖ * h (ballProject 1 x) = h x
  by_cases hx : ‖x‖ ≤ 1
  · rw [max_eq_left hx, ballProject_fixed hx, one_mul]
  · have hn : 0 < ‖x‖ := by linarith
    rw [max_eq_right (le_of_not_ge hx), ballProject, if_neg hx,
      hh.homogeneous _ (div_nonneg (by norm_num) hn.le)]
    field_simp

/-- One bounded query reconstructs one arbitrary-size exact support-function
query. The same states, seed and response count are preserved. -/
def supportUnitPolicy {Ω S : Type} (p : Policy Ω S E) : Policy Ω S (Feasible E 1) :=
  p.simulate (projectPoint 1 (by norm_num)) (fun x y => max 1 ‖x‖ * y)

theorem supportUnitPolicy_measurable {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    {p : Policy Ω S E} (hp : p.IsMeasurable) : (supportUnitPolicy p).IsMeasurable := by
  apply simulation_measurable hp (projectPoint_measurable (by norm_num))
  exact ((continuous_const.max continuous_fst.norm).mul continuous_snd).measurable

theorem supportUnitPolicy_run {Ω S : Type} (p : Policy Ω S E) {h : E → ℝ}
    (hh : SupportModel h) (ω : Ω) (T : ℕ) :
    (supportUnitPolicy p).run (fun x => h x.val) ω T = p.run h ω T :=
  simulation_run_exact p (projectPoint 1 (by norm_num)) (fun x y => max 1 ‖x‖ * y)
    (fun x : Feasible E 1 => h x.val) h (support_normalized_response hh) ω T

theorem supportUnitPolicy_result {Ω S : Type} (p : Policy Ω S E) {h : E → ℝ}
    (hh : SupportModel h) (ω : Ω) (T : ℕ) :
    ((supportUnitPolicy p).result (fun x => h x.val) ω T).val = ballProject 1 (p.result h ω T) := by
  have hres := simulation_output_exact p (projectPoint 1 (by norm_num))
    (fun x y => max 1 ‖x‖ * y) (fun x : Feasible E 1 => h x.val) h
    (support_normalized_response hh) ω T
  exact congrArg Subtype.val hres

theorem supportUnitPolicy_result_of_feasible {Ω S : Type} (p : Policy Ω S E) {h : E → ℝ}
    (hh : SupportModel h) (ω : Ω) (T : ℕ) (hout : ‖p.result h ω T‖ ≤ 1) :
    ((supportUnitPolicy p).result (fun x => h x.val) ω T).val = p.result h ω T := by
  rw [supportUnitPolicy_result p hh, ballProject_fixed hout]

theorem gaussianSupportPrior_single_unbounded_gap {S : Type} [MeasurableSpace S]
    (p : Policy Unit S E) (hp : p.IsMeasurable) (T : ℕ)
    (hd : 86 ≤ Module.finrank ℝ E) (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 128)
    (hout : ∀ a : BoundedSupportRows E (Fin 1), ‖p.result (boundedFiniteSupport a) () T‖ ≤ 1) :
    3 / 4 ≤ (gaussianSupportPrior E 1).real {a : BoundedSupportRows E (Fin 1) |
      7 * ((1 / 2 : ℝ) / Real.sqrt 1) / 16 <
        boundedFiniteSupport a (p.result (boundedFiniteSupport a) () T) - minimumValue 1 (boundedFiniteSupport a)} := by
  have h := gaussianSupportPrior_single_output_gap (supportUnitPolicy p) (supportUnitPolicy_measurable hp) T hd hT
  have he : {a : BoundedSupportRows E (Fin 1) |
      7 * ((1 / 2 : ℝ) / Real.sqrt 1) / 16 <
        boundedFiniteSupport a ((supportUnitPolicy p).result (fun x => boundedFiniteSupport a x.val) () T).val -
          minimumValue 1 (boundedFiniteSupport a)} =
      {a : BoundedSupportRows E (Fin 1) |
      7 * ((1 / 2 : ℝ) / Real.sqrt 1) / 16 <
        boundedFiniteSupport a (p.result (boundedFiniteSupport a) () T) - minimumValue 1 (boundedFiniteSupport a)} := by
    ext a
    simp only [Set.mem_setOf_eq, supportUnitPolicy_result_of_feasible p (boundedFiniteSupport_model a) () T (hout a)]
  rwa [he] at h

theorem gaussianSupportPrior_unbounded_gap_of_adaptive {cprob : ℝ}
    (hadapt : GaussianAdaptiveHardnessInput E cprob)
    (hd : 256 ≤ Module.finrank ℝ E) {k : ℕ} (hk : 0 < k)
    (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512) (T : ℕ)
    (hT : (T : ℝ) ≤ cprob * Module.finrank ℝ E * k / Real.log (Real.exp 1 * k))
    {S : Type} [mS : MeasurableSpace S] (p : Policy Unit S E) (hp : p.IsMeasurable) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    (∀ a : BoundedSupportRows E (Fin k), ‖p.result (boundedFiniteSupport a) () T‖ ≤ 1) →
    3 / 4 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (boundedFiniteSupport a) () T) - minimumValue 1 (boundedFiniteSupport a)} := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro hout
  have h := hadapt k hk hd hkd T hT S mS (supportUnitPolicy p) (supportUnitPolicy_measurable hp)
  have he : {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a ((supportUnitPolicy p).result (fun x => boundedFiniteSupport a x.val) () T).val -
          minimumValue 1 (boundedFiniteSupport a)} =
      {a : BoundedSupportRows E (Fin k) |
      7 * ((1 / 4 : ℝ) / Real.sqrt k) / 16 <
        boundedFiniteSupport a (p.result (boundedFiniteSupport a) () T) - minimumValue 1 (boundedFiniteSupport a)} := by
    ext a
    simp only [Set.mem_setOf_eq, supportUnitPolicy_result_of_feasible p (boundedFiniteSupport_model a) () T (hout a)]
  rwa [he] at h

end
end Nonsmooth
