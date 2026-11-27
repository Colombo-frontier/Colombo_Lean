import UpperGhostProgram

/-! Feasibility of both finite coupled projected processes and their averaged
outputs. No clipping, acceptance or sample tail hypothesis is needed here. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set
namespace Task006.Full

def upperGhostFeasible {d : ℕ} (P : UpperProgramParameters) (n : ℕ)
    (j : GhostState (UpperGhostState d)) : Prop :=
  ‖j.1.1.1‖ ≤ P.R - (P.ρ + P.δ) ∧ ‖j.1.2.1‖ ≤ P.R - (P.ρ + P.δ) ∧
    ‖j.1.1.2‖ ≤ n * (P.R - (P.ρ + P.δ)) ∧ ‖j.1.2.2‖ ≤ n * (P.R - (P.ρ + P.δ))

theorem upperGhostFeasible_measurable {d : ℕ} (P : UpperProgramParameters) (n : ℕ) :
    MeasurableSet {j : GhostState (UpperGhostState d) | upperGhostFeasible P n j} := by
  have h1 : MeasurableSet {j : GhostState (UpperGhostState d) | ‖j.1.1.1‖ ≤ P.R - (P.ρ + P.δ)} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {j : GhostState (UpperGhostState d) | ‖j.1.2.1‖ ≤ P.R - (P.ρ + P.δ)} :=
    measurableSet_le (by fun_prop) measurable_const
  have h3 : MeasurableSet {j : GhostState (UpperGhostState d) | ‖j.1.1.2‖ ≤ n * (P.R - (P.ρ + P.δ))} :=
    measurableSet_le (by fun_prop) measurable_const
  have h4 : MeasurableSet {j : GhostState (UpperGhostState d) | ‖j.1.2.2‖ ≤ n * (P.R - (P.ρ + P.δ))} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter (h2.inter (h3.inter h4))

theorem upperGhostUpdate_feasible {d : ℕ} {Ω : Type*} (P : UpperProgramParameters)
    (F : Space d → Ω → ℝ) (G : UpperGhostState d → Set (UpperSampleBlock d Ω))
    (n : ℕ) (j : GhostState (UpperGhostState d)) (p : UpperSampleBlock d Ω × UpperSampleBlock d Ω)
    (hj : upperGhostFeasible P n j) :
    upperGhostFeasible P (n + 1) (ghostUpdate G (upperGhostStep P F) (j, p)) := by
  have hp (u : Space d) : ‖ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg u‖ ≤ P.R - (P.ρ + P.δ) := by
    simpa only [mem_closedBall, dist_zero_right] using ballProj_mem _ P.inner_nonneg u
  refine ⟨hp _, hp _, ?_, ?_⟩
  · change ‖j.1.1.2 + j.1.1.1‖ ≤ (n + 1 : ℕ) * (P.R - (P.ρ + P.δ))
    have hh := norm_add_le j.1.1.2 j.1.1.1
    push_cast
    nlinarith [hj.1, hj.2.2.1]
  · change ‖j.1.2.2 + j.1.2.1‖ ≤ (n + 1 : ℕ) * (P.R - (P.ρ + P.δ))
    have hh := norm_add_le j.1.2.2 j.1.2.1
    push_cast
    nlinarith [hj.2.1, hj.2.2.2]

theorem ghostProcess_upperStep_feasible {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : UpperProgramParameters) (F : Space d → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (ν : Measure (UpperSampleBlock d Ω)) [IsProbabilityMeasure ν]
    (G : UpperGhostState d → Set (UpperSampleBlock d Ω))
    (hG : MeasurableSet {p : UpperGhostState d × UpperSampleBlock d Ω | p.2 ∈ G p.1})
    (hpos : ∀ x, ν (G x) ≠ 0) (n : ℕ) :
    ∀ᵐ j ∂ghostProcessLaw ν G hG hpos (upperGhostStep P F) (upperGhostStep_measurable P hF) (0, 0) n,
      upperGhostFeasible P n j := by
  induction n with
  | zero =>
    rw [ghostProcessLaw]
    apply (ae_dirac_iff (upperGhostFeasible_measurable P 0)).mpr
    simp only [upperGhostFeasible, norm_zero, Nat.cast_zero, zero_mul]
    exact ⟨P.inner_nonneg, P.inner_nonneg, le_rfl, le_rfl⟩
  | succ n ih =>
    rw [ghostProcessLaw]
    apply Measure.ae_comp_of_ae_ae (upperGhostFeasible_measurable P (n + 1))
    filter_upwards [ih] with j hj
    rw [ghostTransition_apply]
    have hm : Measurable (fun p : UpperSampleBlock d Ω × UpperSampleBlock d Ω =>
        ghostUpdate G (upperGhostStep P F) (j, p)) :=
      (ghostUpdate_measurable G hG _ (upperGhostStep_measurable P hF)).comp measurable_prodMk_left
    exact (ae_map_iff hm.aemeasurable (upperGhostFeasible_measurable P (n + 1))).mpr
      (ae_of_all _ (fun p => upperGhostUpdate_feasible P F G n j p hj))

theorem upperGhost_average_norm_le {d : ℕ} (P : UpperProgramParameters) {n : ℕ} (hn : 0 < n)
    {sum : Space d} (hsum : ‖sum‖ ≤ n * (P.R - (P.ρ + P.δ))) :
    ‖(n : ℝ)⁻¹ • sum‖ ≤ P.R - (P.ρ + P.δ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnR)]
  calc
    (n : ℝ)⁻¹ * ‖sum‖ ≤ (n : ℝ)⁻¹ * (n * (P.R - (P.ρ + P.δ))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp [hnR.ne']

#print axioms ghostProcess_upperStep_feasible
end Task006.Full
