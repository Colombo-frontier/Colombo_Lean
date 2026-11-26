import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Data.Nat.Lattice

open MeasureTheory Metric Set Module Function
open scoped ENNReal
set_option autoImplicit false
namespace MatchingBounds1005.GaussianNets
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A volume packing estimate at the resolution used for the Gaussian design. -/
theorem spectral_packing_card (s : Finset E) (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 8 ≤ ‖x - y‖) :
    s.card ≤ 17 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1 / 16
  let ρ : ℝ := 17 / 16
  have hδ : 0 < δ := by norm_num [δ]
  have hρ : 0 < ρ := by norm_num [ρ]
  let A := ⋃ x ∈ s, ball (x : E) δ
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun x => ball (x : E) δ) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep x hx y hy hxy using 1
    norm_num [δ]
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    have := hs x hx
    dsimp [δ, ρ]
    linarith
  have hb : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ x ∈ s, ball (x : E) δ from rfl,
          measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hj : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_right (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).mp hb
  have hk := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] at hk
  have he : ρ = 17 * δ := by norm_num [ρ, δ]
  rw [he, mul_pow] at hk
  have hn : (s.card : ℝ) ≤ (17 : ℝ) ^ finrank ℝ E :=
    (mul_le_mul_right (pow_pos hδ _)).mp hk
  exact_mod_cast hn

/-- A finite unit-sphere net, including the empty sphere in dimension zero. -/
theorem spectral_sphere_net : ∃ s : Finset E,
    s.card ≤ 17 ^ finrank ℝ E ∧ (∀ x ∈ s, ‖x‖ = 1) ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 8 := by
  classical
  let good (s : Finset E) : Prop := (∀ x ∈ s, ‖x‖ = 1) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 8 ≤ ‖x - y‖
  let sizes : Set ℕ := {n | ∃ s : Finset E, s.card = n ∧ good s}
  have hne : sizes.Nonempty := ⟨0, ∅, by simp, by simp [good]⟩
  have hb : BddAbove sizes := by
    refine ⟨17 ^ finrank ℝ E, ?_⟩
    rintro n ⟨s, rfl, hs⟩
    exact spectral_packing_card s (fun x hx => (hs.1 x hx).le) hs.2
  obtain ⟨s, hcard, hs⟩ := Nat.sSup_mem hne hb
  refine ⟨s, spectral_packing_card s (fun x hx => (hs.1 x hx).le) hs.2, hs.1, ?_⟩
  intro x hx
  by_contra hnone
  have hfar : ∀ y ∈ s, (1 : ℝ) / 8 ≤ ‖x - y‖ := by
    intro y hy
    exact le_of_not_gt (fun h => hnone ⟨y, hy, h⟩)
  have hxs : x ∉ s := by
    intro h
    have := hfar x h
    simp only [sub_self, norm_zero] at this
    norm_num at this
  have hg : good (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | has
      · subst a
        rcases Finset.mem_insert.mp hb with hbx | hbs
        · exact False.elim (hab hbx.symm)
        · exact hfar b hbs
      · rcases Finset.mem_insert.mp hb with hbx | hbs
        · subst b
          rw [norm_sub_rev]
          exact hfar a has
        · exact hs.2 a has b hbs hab
  have hm : (insert x s).card ∈ sizes := ⟨insert x s, rfl, hg⟩
  have hh := le_csSup hb hm
  rw [Finset.card_insert_of_not_mem hxs, hcard] at hh
  omega

end
end MatchingBounds1005.GaussianNets

namespace MatchingBounds1005.GaussianNets
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite net converts the chi-square good event into genuine lower and
upper singular-value bounds. No spectral conclusion is assumed. -/
theorem operator_bounds_of_net (T : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 8)
    (hb : ∀ y ∈ s, (1 : ℝ) / 2 ≤ ‖T y‖ ^ 2 ∧ ‖T y‖ ^ 2 ≤ (3 : ℝ) / 2) :
    ‖T‖ ≤ 10 / 7 ∧ ∀ v : E, ‖v‖ / 2 ≤ ‖T v‖ := by
  have hupper (y : E) (hy : y ∈ s) : ‖T y‖ ≤ (5 : ℝ) / 4 := by
    nlinarith [hb y hy, norm_nonneg (T y)]
  have hlower (y : E) (hy : y ∈ s) : (7 : ℝ) / 10 ≤ ‖T y‖ := by
    nlinarith [hb y hy, norm_nonneg (T y)]
  have hop' : ‖T‖ ≤ 5 / 4 + ‖T‖ / 8 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖T x‖ = ‖T y + T (x - y)‖ := by rw [← map_add, add_sub_cancel]
      _ ≤ ‖T y‖ + ‖T (x - y)‖ := norm_add_le _ _
      _ ≤ 5 / 4 + ‖T‖ * ‖x - y‖ := add_le_add (hupper y hy) (T.le_opNorm _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hxy.le (norm_nonneg T)]
  have hop : ‖T‖ ≤ 10 / 7 := by linarith
  refine ⟨hop, ?_⟩
  have hunit (x : E) (hx : ‖x‖ = 1) : (1 : ℝ) / 2 ≤ ‖T x‖ := by
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have hd : ‖T (y - x)‖ ≤ 5 / 28 := by
      calc
        _ ≤ ‖T‖ * ‖y - x‖ := T.le_opNorm _
        _ ≤ (10 / 7 : ℝ) * (1 / 8) :=
          mul_le_mul hop (by simpa only [norm_sub_rev] using hxy.le)
            (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have htri : ‖T y‖ ≤ ‖T x‖ + ‖T (y - x)‖ := by
      calc
        _ = ‖T x + T (y - x)‖ := by rw [← map_add, ← add_sub_assoc, add_sub_cancel_left]
        _ ≤ _ := norm_add_le _ _
    linarith [hlower y hy]
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnv : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hu := hunit (‖v‖⁻¹ • v) hnv
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] at hu
  have hm := mul_le_mul_of_nonneg_left hu hn.le
  rwa [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_one_div] at hm

end
end MatchingBounds1005.GaussianNets

