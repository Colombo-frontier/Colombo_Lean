import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped Classical

namespace SecondOrder
noncomputable section

theorem strict_majorities_intersect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hA : Fintype.card ι < 2*A.card) (hB : Fintype.card ι < 2*B.card) :
    (A ∩ B).Nonempty := by
  have hu := Finset.card_le_card (Finset.subset_univ (A ∪ B))
  have hc := Finset.card_inter_add_card_union A B
  simp only [Finset.card_univ] at hu
  apply Finset.card_pos.mp
  omega

def goodObservations {E : Type*} [PseudoMetricSpace E] {R : ℕ}
    (z : Fin R → E) (μ : E) (r : ℝ) : Finset (Fin R) :=
  Finset.univ.filter (fun i => dist (z i) μ ≤ r)

def centerCandidates {E : Type*} [PseudoMetricSpace E] {R : ℕ}
    (z : Fin R → E) (r : ℝ) : Finset (Fin R) :=
  Finset.univ.filter (fun i => R < 2*(goodObservations z (z i) (2*r)).card)

def robustCenter {E : Type*} [PseudoMetricSpace E] {R : ℕ} (hR : 0 < R)
    (z : Fin R → E) (r : ℝ) : E :=
  if h : (centerCandidates z r).Nonempty then z ((centerCandidates z r).min' h) else z ⟨0,hR⟩

theorem good_is_candidate {E : Type*} [PseudoMetricSpace E] {R : ℕ}
    (z : Fin R → E) (μ : E) (r : ℝ)
    (hmajor : R < 2*(goodObservations z μ r).card) {i : Fin R}
    (hi : i ∈ goodObservations z μ r) : i ∈ centerCandidates z r := by
  have hsub : goodObservations z μ r ⊆ goodObservations z (z i) (2*r) := by
    intro j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have ht := dist_triangle (z j) μ (z i)
    rw [dist_comm μ (z i)] at ht
    linarith
  have hc := Finset.card_le_card hsub
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  omega

theorem candidate_is_close {E : Type*} [PseudoMetricSpace E] {R : ℕ}
    (z : Fin R → E) (μ : E) (r : ℝ)
    (hmajor : R < 2*(goodObservations z μ r).card) {i : Fin R}
    (hi : i ∈ centerCandidates z r) : dist (z i) μ ≤ 3*r := by
  have hi' := (Finset.mem_filter.mp hi).2
  obtain ⟨j,hj⟩ := strict_majorities_intersect (goodObservations z μ r)
    (goodObservations z (z i) (2*r)) (by simpa using hmajor) (by simpa using hi')
  have hg := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2
  have hc := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
  have ht := dist_triangle (z i) (z j) μ
  rw [dist_comm (z i) (z j)] at ht
  linarith

/-- Deterministic robust-center guarantee; concentration and measurability are
separate from this geometric assertion. -/
theorem robustCenter_close {E : Type*} [PseudoMetricSpace E] {R : ℕ} (hR : 0 < R)
    (z : Fin R → E) (μ : E) (r : ℝ)
    (hmajor : R < 2*(goodObservations z μ r).card) : dist (robustCenter hR z r) μ ≤ 3*r := by
  have hgood : (goodObservations z μ r).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi⟩ := hgood
  have hcan : (centerCandidates z r).Nonempty := ⟨i,good_is_candidate z μ r hmajor hi⟩
  rw [robustCenter, dif_pos hcan]
  exact candidate_is_close z μ r hmajor (Finset.min'_mem _ _)

end
end SecondOrder
