import Nonsmooth.DiscreteConeReadout
import Nonsmooth.AspectConeParameters
import Nonsmooth.ConeCapGeometry

open MeasureTheory Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- For any specified aspect ratio, an actual value-query policy certifies a near-central halfspace cut. -/
theorem actual_aspect_body_cut_policy_discrete_readout (r : ℝ) (hr : 0 < r) (A : ℕ) (hA : 0 < A) (G : Set E)
    (hinner : Metric.closedBall (0 : E) r ⊆ G)
    (houter : G ⊆ Metric.closedBall (0 : E) ((A : ℝ) * r))
    (hd : 2 ≤ Module.finrank ℝ E) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E r),
      ∃ out : CircularHistory → Feasible E r, ∃ axis : CircularHistory → E,
      p.IsMeasurable ∧ (∀ st, p.output () st = out st.1) ∧ Measurable out ∧ Measurable axis ∧
      (T : ℝ) ≤ 62 * (Module.finrank ℝ E : ℝ) * (2 * Real.log ((Module.finrank ℝ E : ℝ) + 1) + Real.log ((A : ℝ) + 1)) ∧
      ∀ f : E → ℝ, ConvexOn ℝ G f → ∃ e : E,
        e = axis (p.run (fun z => f z.val) () T).1 ∧ ‖e‖ = 1 ∧
        let x := (p.result (fun z => f z.val) () T).val
        ‖x‖ ≤ r / (8 * (Module.finrank ℝ E : ℝ)) ∧ f 0 ≤ f x ∧
          ∀ z : E, z ∈ G → r / (4 * (Module.finrank ℝ E : ℝ)) ≤ ⟪z, e⟫_ℝ → f x ≤ f z := by
  let d := Module.finrank ℝ E
  let ρ := r / (4 * (d : ℝ))
  let P := 4 * d * A
  have hdp : 0 < d := by dsimp [d]; omega
  obtain ⟨hρ, hρr⟩ := normalized_cone_query_radius hr d hdp
  have hball : Metric.closedBall (0 : E) ρ ⊆ G := by
    intro z hz
    apply hinner
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    simpa using hz'.trans hρr
  obtain ⟨T, p, out, axis, hp, hout, houtm, haxis, hcount, hcert⟩ :=
    actual_adjustable_cone_policy_discrete_readout ρ hρ G hball hd P (aspect_cone_precision_scale d A hA)
  let inclusion : Feasible E ρ → Feasible E r := fun x => ⟨x.val, x.property.trans hρr⟩
  have hi : Measurable inclusion := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe
  let p' := p.simulate inclusion (fun _ y => y)
  have hcount' : (T : ℝ) ≤ 62 * (d : ℝ) * (2 * Real.log ((d : ℝ) + 1) + Real.log ((A : ℝ) + 1)) := by
    have hl := mul_le_mul_of_nonneg_left (aspect_cone_precision_log_bound d A hdp)
      (show (0 : ℝ) ≤ 62 * (d : ℝ) by positivity)
    change (T : ℝ) ≤ 62 * (d : ℝ) * Real.log ((P : ℝ) + 1) at hcount
    change 62 * (d : ℝ) * Real.log ((P : ℝ) + 1) ≤ _ at hl
    nlinarith only [hcount, hl]
  refine ⟨T, p', (fun h => inclusion (out h)), axis,
    simulation_measurable hp hi measurable_snd,
    (fun st => congrArg inclusion (hout st)), hi.comp houtm, haxis, hcount', ?_⟩
  intro f hf
  obtain ⟨e, hcomputed, he, hxnorm, hzero, hcone⟩ := hcert f hf
  have hres : (p'.result (fun z => f z.val) () T).val = (p.result (fun z => f z.val) () T).val := by
    have h := simulation_output_exact p inclusion (fun _ y => y) (fun z : Feasible E r => f z.val)
      (fun z : Feasible E ρ => f z.val) (fun _ => rfl) () T
    exact congrArg Subtype.val h
  have hxnorm' : ‖(p.result (fun z => f z.val) () T).val‖ ≤ r / (8 * (d : ℝ)) := by
    have heq : ρ / 2 = r / (8 * (d : ℝ)) := by dsimp [ρ]; ring
    simpa only [heq] using hxnorm
  have hrun : p'.run (fun z => f z.val) () T = p.run (fun z => f z.val) () T :=
    simulation_run_exact p inclusion (fun _ y => y) (fun z : Feasible E r => f z.val)
      (fun z : Feasible E ρ => f z.val) (fun _ => rfl) () T
  refine ⟨e, by rw [hrun]; exact hcomputed, he, ?_⟩
  dsimp only
  rw [hres]
  refine ⟨hxnorm', hzero, ?_⟩
  intro z hz hcap
  apply hcone z hz
  have hzNorm : ‖z‖ ≤ (A : ℝ) * r := by simpa only [Metric.mem_closedBall, dist_zero_right] using houter hz
  have hPpos : (0 : ℝ) < P := by dsimp [P]; positivity
  apply wide_cone_contains_cap he (by positivity : (0 : ℝ) ≤ 1 / (4 * (P : ℝ))) hxnorm' hzNorm
  have hcoeff : (1 / (4 * (P : ℝ)) : ℝ) = 1 / (16 * (d : ℝ) * (A : ℝ)) := by dsimp [P]; push_cast; ring
  rw [hcoeff]
  exact (aspect_cone_cap_threshold hr.le d A hdp hA).trans hcap

end
end Nonsmooth
