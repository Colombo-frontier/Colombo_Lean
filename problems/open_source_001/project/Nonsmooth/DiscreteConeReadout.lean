import Nonsmooth.ActualFullDimensionalConePolicy

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A fixed Borel policy certifies a full-dimensional cone with a freely chosen precision scale. -/
theorem actual_adjustable_cone_policy_discrete_readout (R : ℝ) (hR : 0 < R) (G : Set E)
    (hballG : Metric.closedBall (0 : E) R ⊆ G)
    (hd : 2 ≤ Module.finrank ℝ E) (P : ℕ) (hP : Module.finrank ℝ E ≤ P) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E R),
      ∃ out : CircularHistory → Feasible E R, ∃ axis : CircularHistory → E,
      p.IsMeasurable ∧ (∀ st, p.output () st = out st.1) ∧ Measurable out ∧ Measurable axis ∧
      (T : ℝ) ≤ 62 * (Module.finrank ℝ E : ℝ) * Real.log ((P : ℝ) + 1) ∧
      ∀ f : E → ℝ, ConvexOn ℝ G f → ∃ e : E,
        e = axis (p.run (fun z => f z.val) () T).1 ∧ ‖e‖ = 1 ∧
        let x := (p.result (fun z => f z.val) () T).val
        ‖x‖ ≤ R / 2 ∧ f 0 ≤ f x ∧
          ∀ z : E, z ∈ G →
            (1 / (4 * (P : ℝ))) * ‖z - x‖ ≤ ⟪z - x, e⟫_ℝ → f x ≤ f z := by
  let d := Module.finrank ℝ E
  let ε : ℝ := 1 / (8 * (P : ℝ) ^ 2)
  let N := dimensionCircularPrecision P
  let D := d - 1
  have hdp : 0 < d := by dsimp [d]; omega
  have hPpos : 0 < P := lt_of_lt_of_le hdp hP
  obtain ⟨hε, hε1⟩ := dimension_cone_tolerance_bounds P hPpos
  have hD : 0 < D := by dsimp [D, d]; omega
  let p := nestedCircularPolicy (E := E) R ε N hR.le hε hε1
  let T := D * (3 * N + 4)
  have hT : (T : ℝ) ≤ 62 * (d : ℝ) * Real.log ((P : ℝ) + 1) := by
    have hs := dimensionCircularPrecision_query_bound P hPpos
    have hDd : (D : ℝ) ≤ d := by exact_mod_cast (show D ≤ d by dsimp [D]; omega)
    have h1 := mul_le_mul_of_nonneg_right hDd
      (show (0 : ℝ) ≤ (3 * N + 4 : ℕ) from Nat.cast_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ d from Nat.cast_nonneg d)
    change ((D * (3 * N + 4) : ℕ) : ℝ) ≤ _
    change (d : ℝ) * (3 * N + 4 : ℕ) ≤ (d : ℝ) * (62 * Real.log ((P : ℝ) + 1)) at h2
    push_cast at h1 h2 ⊢
    nlinarith only [h1, h2]
  refine ⟨T, p, nestedCircularOutput R ε N hR.le hε hε1,
    (fun h => circularGeometryDirection R ε N h.entries),
    nestedCircularPolicy_measurable R ε N hR.le hε hε1,
    (fun _ => rfl), measurable_of_countable _, measurable_of_countable _, hT, ?_⟩
  intro f hf
  let x := nestedCircularApex R ε N hR.le hε hε1 f D
  let e := nestedCircularRadial R ε N hR.le hε hε1 f (D - 1)
  have he : ‖e‖ = 1 := nestedCircularRadial_unit R ε N hR.le hε hε1 f (D - 1) (by dsimp [D, d] at *; omega)
  have hx : (p.result (fun z => f z.val) () T).val = x := by
    change ((nestedCircularPolicy R ε N hR.le hε hε1).result (fun z => f z.val) () (D * (3 * N + 4))).val = x
    rw [nestedCircularPolicy_result_exact]
    rfl
  have hline : Module.finrank ℝ (nestedCircularSpace R ε N hR.le hε hε1 f D) = 1 := by
    rw [nestedCircularSpace_dimension]
    dsimp [D, d]
    omega
  have hcone := nestedCircular_full_cone_certificate R ε N hR.le hε hε1 f hR G hballG hf D hD
    (show D ≤ Module.finrank ℝ E - 1 from le_rfl) hline (dimensionCircularPrecision_slope P hPpos)
  have hwide : comparisonConeExcluded G f ⊤ x e (1 / (4 * (P : ℝ))) (f x) :=
    comparisonConeExcluded_dimension_scale P hPpos D (by dsimp [D, d]; omega) hcone
  have haxis : e = nestedCircularDirection R ε N (p.run (fun z => f z.val) () T) :=
    (nestedCircularDirection_run_exact R ε N hR.le hε hε1 f D hD).symm
  refine ⟨e, haxis, he, ?_⟩
  dsimp only
  rw [hx]
  have hnorm : ‖x‖ ≤ R / 2 := by
    have h := nestedCircularPolicy_norm_le_half R ε N hR.le hε hε1 f D
    change ‖(p.result (fun z => f z.val) () T).val‖ ≤ R / 2 at h
    simpa only [hx] using h
  have hzero : f 0 ≤ f x := by
    have h := nestedCircularApex_value_monotone R ε N hR.le hε hε1 f (Nat.zero_le D)
    simpa only [(nestedCircular_initial_geometry R ε N hR.le hε hε1 f).1] using h
  refine ⟨hnorm, hzero, ?_⟩
  intro z hz hslope
  have hz' : x + (z - x) = z := by abel
  have hfz := hwide (z - x) (Submodule.mem_top) (by simpa only [hz'] using hz) hslope
  simpa only [hz'] using hfz

end
end Nonsmooth
