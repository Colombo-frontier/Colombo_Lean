import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-! Genuine finite comparator nets and their deterministic regret cost. -/

noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace

namespace HeavyTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finite_ball_comparator_net [FiniteDimensional ℝ E] (c : E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ Z : Set E, Z.Finite ∧ c ∈ Z ∧ Z ⊆ closedBall c R ∧
      ∀ u ∈ closedBall c R, ∃ z ∈ Z, ‖u - z‖ < ε := by
  obtain ⟨Z, hZsub, hZfin, hcover⟩ :=
    (isCompact_closedBall c R).totallyBounded.exists_subset (Metric.dist_mem_uniformity hε)
  refine ⟨insert c Z, hZfin.insert c, mem_insert c Z, ?_, ?_⟩
  · intro z hz
    rcases hz with rfl | hz
    · exact mem_closedBall_self hR
    · exact hZsub hz
  · intro u hu
    rcases mem_iUnion.mp (hcover hu) with ⟨z, hz⟩
    rcases mem_iUnion.mp hz with ⟨hzZ, huz⟩
    refine ⟨z, mem_insert_of_mem c hzZ, ?_⟩
    simpa only [mem_setOf_eq, dist_eq_norm] using huz

theorem finite_net_regret_comparison {b x : ℕ → E} {u ustar : E} {M ε : ℝ}
    (hM : 0 ≤ M) (_hε : 0 ≤ ε) (hnet : ‖ustar - u‖ ≤ ε)
    (n : ℕ) (hb : ∀ t ∈ Finset.range n, ‖b t‖ ≤ M) :
    (∑ t ∈ Finset.range n, ⟪b t, x t - u⟫_ℝ) ≤
      (∑ t ∈ Finset.range n, ⟪b t, x t - ustar⟫_ℝ) + (n : ℝ) * M * ε := by
  have hstep : ∀ t ∈ Finset.range n, ⟪b t, x t - u⟫_ℝ ≤
      ⟪b t, x t - ustar⟫_ℝ + M * ε := by
    intro t ht
    have hcs := (real_inner_le_norm (b t) (ustar - u)).trans
      (mul_le_mul (hb t ht) hnet (norm_nonneg _) hM)
    simp only [inner_sub_right] at hcs ⊢
    linarith
  have h := Finset.sum_le_sum hstep
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_assoc] using h

theorem finite_net_average_regret_comparison {b x : ℕ → E} {u ustar : E} {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hnet : ‖ustar - u‖ ≤ ε)
    {n : ℕ} (hn : 0 < n) (hb : ∀ t ∈ Finset.range n, ‖b t‖ ≤ M) :
    (∑ t ∈ Finset.range n, ⟪b t, x t - u⟫_ℝ) / n ≤
      (∑ t ∈ Finset.range n, ⟪b t, x t - ustar⟫_ℝ) / n + M * ε := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right
    (finite_net_regret_comparison (x := x) hM hε hnet n hb) hnreal.le
  have hid : (n : ℝ) * M * ε / n = M * ε := by field_simp; ring
  simpa only [add_div, hid] using h

end HeavyTail
