import Nonsmooth.SphericalLaw
import Mathlib.Data.Nat.Lattice

open MeasureTheory Metric Function Set
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem volume_ball_real_scale (x : E) {r : ℝ} (hr : 0 < r) :
    (volume : Measure E).real (ball x r) = r ^ Module.finrank ℝ E * (volume : Measure E).real (ball 0 1) := by
  simp only [measureReal_def, (volume : Measure E).addHaar_ball_of_pos x hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

theorem unit_ball_packing_card (s : Finset E) (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 / 16 : ℝ) ≤ ‖x - y‖) :
    s.card ≤ 33 ^ Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  let U : Set E := ⋃ x ∈ s, ball x (1 / 32)
  have hdis : PairwiseDisjoint (s : Set E) (fun x => ball x (1 / 32)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have h := hsep x hx y hy hxy
    linarith
  have hsub : U ⊆ ball (0 : E) (33 / 32) := by
    apply iUnion₂_subset
    intro x hx
    apply ball_subset_ball'
    rw [dist_zero_right]
    have h := hs x hx
    linarith
  have hv : 0 < (volume : Measure E).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1)).ne'
      measure_ball_lt_top.ne
  have hmeasure := measureReal_mono (μ := volume) hsub measure_ball_lt_top.ne
  change (volume : Measure E).real (⋃ x ∈ s, ball x (1 / 32)) ≤ _ at hmeasure
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_ball)
    (fun _ _ => measure_ball_lt_top.ne)] at hmeasure
  simp only [volume_ball_real_scale _ (by norm_num : (0 : ℝ) < 1 / 32),
    volume_ball_real_scale _ (by norm_num : (0 : ℝ) < 33 / 32), Finset.sum_const,
    nsmul_eq_mul] at hmeasure
  have h : (s.card : ℝ) * (1 / 32 : ℝ) ^ d ≤ (33 / 32 : ℝ) ^ d := by
    apply (mul_le_mul_iff_of_pos_right hv).mp
    simpa only [mul_assoc] using hmeasure
  have he : (33 / 32 : ℝ) ^ d = (33 : ℝ) ^ d * (1 / 32 : ℝ) ^ d := by
    rw [div_pow, div_pow, one_pow]
    ring
  rw [he] at h
  have hc := (mul_le_mul_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 1 / 32) d)).mp h
  exact_mod_cast hc

theorem unit_sphere_finite_net : ∃ s : Finset E,
    (∀ x ∈ s, ‖x‖ = 1) ∧ s.card ≤ 33 ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ ≤ 1 / 16 := by
  classical
  let P : Finset E → Prop := fun s =>
    (∀ x ∈ s, ‖x‖ = 1) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 / 16 : ℝ) ≤ ‖x - y‖
  let A : Set ℕ := {n | ∃ s : Finset E, s.card = n ∧ P s}
  have hne : A.Nonempty := ⟨0, ∅, rfl, by simp [P]⟩
  have hbd : BddAbove A := by
    refine ⟨33 ^ Module.finrank ℝ E, ?_⟩
    rintro n ⟨s, rfl, hs, hsep⟩
    exact unit_ball_packing_card s (fun x hx => (hs x hx).le) hsep
  obtain ⟨s, hcard, hs, hsep⟩ := Nat.sSup_mem hne hbd
  refine ⟨s, hs, unit_ball_packing_card s (fun x hx => (hs x hx).le) hsep, ?_⟩
  intro x hx
  by_contra hnot
  push_neg at hnot
  have hxs : x ∉ s := by
    intro hmem
    have h := hnot x hmem
    norm_num at h
  have hinsert : P (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs y hy
    · intro y hy z hz hyz
      by_cases hyx : y = x
      · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (fun hzx => hyz (hyx.trans hzx.symm))
        rw [hyx]
        exact (hnot z hzs).le
      · have hys : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyx
        by_cases hzx : z = x
        · rw [hzx, norm_sub_rev]
          exact (hnot y hys).le
        · exact hsep y hys z ((Finset.mem_insert.mp hz).resolve_left hzx) hyz
  have hmax := le_csSup hbd (show (insert x s).card ∈ A from ⟨insert x s, rfl, hinsert⟩)
  rw [Finset.card_insert_of_notMem hxs, hcard] at hmax
  omega

end
end Nonsmooth
