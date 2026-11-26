import Nonsmooth.ActualFullDimensionalConePolicy
import Nonsmooth.NormalizedConeParameters
import Nonsmooth.ConeCapGeometry

open MeasureTheory Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- For a normalized body, an actual value-query policy certifies a near-central halfspace cut. -/
theorem actual_normalized_body_cut_policy_with_direction (r : ℝ) (hr : 0 < r) (G : Set E)
    (hinner : Metric.closedBall (0 : E) r ⊆ G)
    (houter : G ⊆ Metric.closedBall (0 : E) ((Module.finrank ℝ E : ℝ) * r))
    (hd : 2 ≤ Module.finrank ℝ E) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E r),
      ∃ axis : CircularHistory × CyclicPeakState → E,
      p.IsMeasurable ∧ Measurable axis ∧
      (T : ℝ) ≤ 248 * (Module.finrank ℝ E : ℝ) * Real.log ((Module.finrank ℝ E : ℝ) + 1) ∧
      ∀ f : E → ℝ, ConvexOn ℝ G f → ∃ e : E,
        e = axis (p.run (fun z => f z.val) () T) ∧ ‖e‖ = 1 ∧
        let x := (p.result (fun z => f z.val) () T).val
        ‖x‖ ≤ r / (8 * (Module.finrank ℝ E : ℝ)) ∧ f 0 ≤ f x ∧
          ∀ z : E, z ∈ G → r / (4 * (Module.finrank ℝ E : ℝ)) ≤ ⟪z, e⟫_ℝ → f x ≤ f z := by
  let d := Module.finrank ℝ E
  let ρ := r / (4 * (d : ℝ))
  let P := 4 * d ^ 2
  have hdp : 0 < d := by dsimp [d]; omega
  obtain ⟨hρ, hρr⟩ := normalized_cone_query_radius hr d hdp
  have hball : Metric.closedBall (0 : E) ρ ⊆ G := by
    intro z hz
    apply hinner
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    simpa using hz'.trans hρr
  obtain ⟨T, p, axis, hp, haxis, hcount, hcert⟩ :=
    actual_adjustable_cone_policy_with_direction ρ hρ G hball hd P (normalized_cone_precision_scale d)
  let inclusion : Feasible E ρ → Feasible E r := fun x => ⟨x.val, x.property.trans hρr⟩
  have hi : Measurable inclusion := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe
  let p' := p.simulate inclusion (fun _ y => y)
  have hcount' : (T : ℝ) ≤ 248 * (d : ℝ) * Real.log ((d : ℝ) + 1) := by
    have hl := mul_le_mul_of_nonneg_left (normalized_cone_precision_log_bound d)
      (show (0 : ℝ) ≤ 62 * (d : ℝ) by positivity)
    change (T : ℝ) ≤ 62 * (d : ℝ) * Real.log ((P : ℝ) + 1) at hcount
    change 62 * (d : ℝ) * Real.log ((P : ℝ) + 1) ≤ _ at hl
    nlinarith only [hcount, hl]
  refine ⟨T, p', axis, simulation_measurable hp hi measurable_snd, haxis, hcount', ?_⟩
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
  have hzNorm : ‖z‖ ≤ (d : ℝ) * r := by simpa only [Metric.mem_closedBall, dist_zero_right] using houter hz
  have hPpos : (0 : ℝ) < P := by dsimp [P]; positivity
  apply wide_cone_contains_cap he (by positivity : (0 : ℝ) ≤ 1 / (4 * (P : ℝ))) hxnorm' hzNorm
  have hcoeff : (1 / (4 * (P : ℝ)) : ℝ) = 1 / (16 * (d : ℝ) ^ 2) := by dsimp [P]; push_cast; ring
  rw [hcoeff]
  exact (normalized_cone_cap_threshold hr.le d hdp).trans hcap

theorem actual_normalized_body_cut_policy (r : ℝ) (hr : 0 < r) (G : Set E)
    (hinner : Metric.closedBall (0 : E) r ⊆ G)
    (houter : G ⊆ Metric.closedBall (0 : E) ((Module.finrank ℝ E : ℝ) * r))
    (hd : 2 ≤ Module.finrank ℝ E) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E r),
      p.IsMeasurable ∧ (T : ℝ) ≤ 248 * (Module.finrank ℝ E : ℝ) * Real.log ((Module.finrank ℝ E : ℝ) + 1) ∧
      ∀ f : E → ℝ, ConvexOn ℝ G f → ∃ e : E, ‖e‖ = 1 ∧
        let x := (p.result (fun z => f z.val) () T).val
        ‖x‖ ≤ r / (8 * (Module.finrank ℝ E : ℝ)) ∧ f 0 ≤ f x ∧
          ∀ z : E, z ∈ G → r / (4 * (Module.finrank ℝ E : ℝ)) ≤ ⟪z, e⟫_ℝ → f x ≤ f z := by
  obtain ⟨T, p, axis, hp, _, hT, hcert⟩ := actual_normalized_body_cut_policy_with_direction r hr G hinner houter hd
  refine ⟨T, p, hp, hT, ?_⟩
  intro f hf
  obtain ⟨e, _, he, hrest⟩ := hcert f hf
  exact ⟨e, he, hrest⟩

end
end Nonsmooth
