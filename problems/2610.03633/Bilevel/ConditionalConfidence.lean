import Mathlib.Data.Finset.Max
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
# Finite median-distance selection

This file formalizes the deterministic selector used in
`cache:lem:confidence` of the chi-refinement manuscript. For each candidate
it computes the least radius containing `ceil(q/2)` candidates, and chooses
the least index attaining the least such radius. The majority guarantee and
the resulting event inclusion are proved for this actual selector.

The exponential estimate from conditional second moments is proved in
`ConditionalConfidenceTail`; its finite-run form is in
`ConditionalConfidenceFinite`. It is not assumed in the selector theorem.
-/

noncomputable section
open Finset
namespace Bilevel.ConditionalConfidence

variable {E : Type*} [PseudoMetricSpace E] {q : ℕ} [NeZero q]

/-- The ceiling of half the number of candidates. -/
def half (q : ℕ) : ℕ := (q + 1) / 2

theorem half_pos : 0 < half q := by
  have := NeZero.ne q
  unfold half
  omega

omit [NeZero q] in
theorem half_le : half q ≤ q := by
  unfold half
  omega

/-- Candidate indices in a closed distance ball, retaining duplicates. -/
def ball (z : Fin q → E) (i : Fin q) (r : ℝ) : Finset (Fin q) :=
  Finset.univ.filter fun j => dist (z i) (z j) ≤ r

omit [NeZero q] in
@[simp] theorem mem_ball {z : Fin q → E} {i j : Fin q} {r : ℝ} :
    j ∈ ball z i r ↔ dist (z i) (z j) ≤ r := by
  classical
  simp [ball]

/-- Radii need only be tested at one of the finitely many distances. -/
def radii (z : Fin q → E) (i : Fin q) : Finset ℝ :=
  ((Finset.univ : Finset (Fin q)).filter fun j =>
    half q ≤ (ball z i (dist (z i) (z j))).card).image fun j => dist (z i) (z j)

theorem radii_nonempty (z : Fin q → E) (i : Fin q) : (radii z i).Nonempty := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin q))
    (fun j => dist (z i) (z j)) Finset.univ_nonempty
  have hb : ball z i (dist (z i) (z j)) = Finset.univ := by
    ext k
    simp only [mem_ball, mem_univ, iff_true]
    exact hj k (Finset.mem_univ _)
  refine ⟨dist (z i) (z j), Finset.mem_image.mpr ⟨j, ?_, rfl⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb, Finset.card_univ,
    Fintype.card_fin]
  exact half_le

/-- The actual smallest half-containing radius about candidate `i`. -/
def radius (z : Fin q → E) (i : Fin q) : ℝ :=
  (radii z i).min' (radii_nonempty z i)

theorem radius_capacity (z : Fin q → E) (i : Fin q) :
    half q ≤ (ball z i (radius z i)).card := by
  classical
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp
    (Finset.min'_mem (radii z i) (radii_nonempty z i))
  rw [radius, ← he]
  exact (Finset.mem_filter.mp hj).2

theorem radius_nonneg (z : Fin q → E) (i : Fin q) : 0 ≤ radius z i := by
  classical
  obtain ⟨j, _, he⟩ := Finset.mem_image.mp
    (Finset.min'_mem (radii z i) (radii_nonempty z i))
  rw [radius, ← he]
  exact dist_nonneg

theorem radius_le_of_capacity (z : Fin q → E) (i : Fin q) {r : ℝ}
    (hr : half q ≤ (ball z i r).card) : radius z i ≤ r := by
  classical
  have hne : (ball z i r).Nonempty := Finset.card_pos.mp (half_pos.trans_le hr)
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (ball z i r)
    (fun j => dist (z i) (z j)) hne
  have hsub : ball z i r ⊆ ball z i (dist (z i) (z j)) := by
    intro k hk
    exact mem_ball.mpr (hmax k hk)
  have hcap := hr.trans (Finset.card_le_card hsub)
  have hjr : dist (z i) (z j) ∈ radii z i := by
    refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcap
  exact ((radii z i).min'_le _ hjr).trans (mem_ball.mp hj)

def optimalIndices (z : Fin q → E) : Finset (Fin q) :=
  Finset.univ.filter fun i => ∀ j, radius z i ≤ radius z j

theorem optimalIndices_nonempty (z : Fin q → E) : (optimalIndices z).Nonempty := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin q))
    (radius z) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  simp only [optimalIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun j => hi j (Finset.mem_univ _)

/-- Ties in radius are resolved by the least original index. -/
def selectedIndex (z : Fin q → E) : Fin q :=
  (optimalIndices z).min' (optimalIndices_nonempty z)

def select (z : Fin q → E) : E := z (selectedIndex z)

theorem selected_radius_le (z : Fin q → E) (j : Fin q) :
    radius z (selectedIndex z) ≤ radius z j := by
  classical
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (optimalIndices z) (optimalIndices_nonempty z))).2 j

theorem selectedIndex_le_of_optimal (z : Fin q → E) (i : Fin q)
    (hi : ∀ j, radius z i ≤ radius z j) : selectedIndex z ≤ i := by
  classical
  apply Finset.min'_le
  simp [optimalIndices, hi]

def bad (z : Fin q → E) (target : E) (r : ℝ) : Finset (Fin q) :=
  Finset.univ.filter fun i => r < dist (z i) target

omit [NeZero q] in
@[simp] theorem mem_bad {z : Fin q → E} {target : E} {r : ℝ} {i : Fin q} :
    i ∈ bad z target r ↔ r < dist (z i) target := by
  classical
  simp [bad]

/-- The exact median-distance selector is within three times the good-point
radius whenever fewer than half (rounded up) of the candidates are bad. -/
theorem select_distance_le_of_majority (z : Fin q → E) (target : E) (r : ℝ)
    (hbad : (bad z target r).card < half q) : dist (select z) target ≤ 3 * r := by
  classical
  let good := (Finset.univ : Finset (Fin q)).filter fun i => dist (z i) target ≤ r
  have hpartition : good.card + (bad z target r).card = q := by
    simpa only [good, bad, not_le, Finset.card_univ, Fintype.card_fin] using
      Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
        (fun i : Fin q => dist (z i) target ≤ r)
  have hgood : half q ≤ good.card := by
    unfold half at *
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (half_pos.trans_le hgood)
  have hi' : dist (z i) target ≤ r := (Finset.mem_filter.mp hi).2
  have hsub : good ⊆ ball z i (2 * r) := by
    intro j hj
    have hj' : dist (z j) target ≤ r := (Finset.mem_filter.mp hj).2
    apply mem_ball.mpr
    calc
      dist (z i) (z j) ≤ dist (z i) target + dist target (z j) := dist_triangle _ _ _
      _ ≤ 2 * r := by rw [dist_comm target]; linarith
  have hri : radius z i ≤ 2 * r :=
    radius_le_of_capacity z i (hgood.trans (Finset.card_le_card hsub))
  have hselected : radius z (selectedIndex z) ≤ 2 * r :=
    (selected_radius_le z i).trans hri
  have hcard : (bad z target r).card <
      (ball z (selectedIndex z) (radius z (selectedIndex z))).card :=
    hbad.trans_le (radius_capacity z (selectedIndex z))
  obtain ⟨j, hj, hjgood⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  have hjtarget : dist (z j) target ≤ r := le_of_not_gt (fun h => hjgood (mem_bad.mpr h))
  have hjdist := (mem_ball.mp hj).trans hselected
  unfold select
  calc
    dist (z (selectedIndex z)) target ≤
        dist (z (selectedIndex z)) (z j) + dist (z j) target := dist_triangle _ _ _
    _ ≤ 3 * r := by linarith

/-- The deterministic conclusion, with precisely the manuscript's quarter
bad-count hypothesis and target accuracy. -/
theorem select_distance_le (z : Fin q → E) (target : E) (a : ℝ)
    (hbad : 4 * (bad z target (a / 3)).card < q) : dist (select z) target ≤ a := by
  have hb : (bad z target (a / 3)).card < half q := by unfold half; omega
  simpa only [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)] using
    select_distance_le_of_majority z target (a / 3) hb

/-- Pathwise failure containment, with no independence assumption. -/
theorem failure_subset_bad_count {Ω : Type*} (Z : Ω → Fin q → E)
    (target : E) (a : ℝ) :
    {ω | a < dist (select (Z ω)) target} ⊆
      {ω | q ≤ 4 * (bad (Z ω) target (a / 3)).card} := by
  intro ω hω
  by_contra h
  exact (not_lt_of_ge (select_distance_le (Z ω) target a (lt_of_not_ge h))) hω

/-- The actual selected-point failure probability reduces to the bad-count
tail. The measure may already encode conditioning on a starting history. -/
theorem failure_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (Z : Ω → Fin q → E) (target : E) (a : ℝ) :
    μ {ω | a < dist (select (Z ω)) target} ≤
      μ {ω | q ≤ 4 * (bad (Z ω) target (a / 3)).card} :=
  MeasureTheory.measure_mono (failure_subset_bad_count Z target a)

end Bilevel.ConditionalConfidence
