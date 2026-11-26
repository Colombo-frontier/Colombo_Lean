import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Deterministic geometry of the ball--simplex reduction

These results formalize the positive-margin witness and the analytic recovery
step in `lem:l21-witness` and `lem:l21-small-gap` of `source/matvec/matvec.tex`.
The strategy constraint is written as `‖z‖² + s² ≤ 1`, the exact Euclidean
ball constraint on the homogeneous coordinate pair. The final `fullGap_residual`
result derives the margin from the explicit signed-row payoff and a full
saddle-gap bound in universal pairwise form. Earlier lemmas expose individual
analytic steps. Existence of a source solution of norm at most one is explicit;
`source_solution_of_surjective_lower_bound` derives it from linear-map
assumptions. No randomized query lower bound is asserted here.
-/

set_option autoImplicit false

namespace Matvec
namespace BallReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Feasible (z : E) (s : ℝ) : Prop := ‖z‖ ^ 2 + s ^ 2 ≤ 1

noncomputable def witnessScale (z : E) : ℝ := (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹

omit [NormedSpace ℝ E] in
theorem witnessScale_pos (z : E) : 0 < witnessScale z := by
  unfold witnessScale
  positivity

theorem witness_on_sphere (z : E) :
    ‖witnessScale z • z‖ ^ 2 + witnessScale z ^ 2 = 1 := by
  have hp : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := by positivity
  have hs : Real.sqrt (1 + ‖z‖ ^ 2) ^ 2 = 1 + ‖z‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (witnessScale_pos z)]
  unfold witnessScale
  field_simp
  nlinarith

theorem witness_feasible (z : E) : Feasible (witnessScale z • z) (witnessScale z) := by
  exact le_of_eq (witness_on_sphere z)

omit [NormedSpace ℝ E] in
theorem witnessScale_lower {z : E} (hz : ‖z‖ ≤ 1) :
    1 / Real.sqrt 2 ≤ witnessScale z := by
  have hsq : 1 + ‖z‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg z]
  have hroot : Real.sqrt (1 + ‖z‖ ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hsq
  simpa [witnessScale, one_div] using
    one_div_le_one_div_of_le (show 0 < Real.sqrt (1 + ‖z‖ ^ 2) by positivity) hroot

theorem witness_residual_zero (H : E →ₗ[ℝ] E) {b z : E} (hz : H z = b) :
    H (witnessScale z • z) - witnessScale z • b = 0 := by
  simp [hz]

theorem positive_margin_witness (H : E →ₗ[ℝ] E) {b z : E} {α : ℝ}
    (hz : H z = b) (hn : ‖z‖ ≤ 1) (hα : 0 ≤ α) :
    ∃ (z' : E) (s : ℝ), Feasible z' s ∧ H z' - s • b = 0 ∧
      α / Real.sqrt 2 ≤ α * s := by
  refine ⟨witnessScale z • z, witnessScale z, witness_feasible z,
    witness_residual_zero H hz, ?_⟩
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (witnessScale_lower hn) hα

omit [NormedSpace ℝ E] in
theorem feasible_scalar_le_one {z : E} {s : ℝ} (h : Feasible z s) : s ≤ 1 := by
  unfold Feasible at h
  nlinarith [sq_nonneg ‖z‖]

theorem margin_threshold_pos : 0 < 1 / Real.sqrt 2 - 1 / 16 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have ht : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hhalf : (1 / 2 : ℝ) < 1 / Real.sqrt 2 := by
    exact (lt_div_iff₀ hs).2 (by nlinarith)
  linarith

/-- Scalar recovery estimates, with the infinity residual represented by `ρ`.
The hypothesis `hmargin` is the consequence of the full-gap bound and witness.
-/
theorem margin_recovery {α β s ρ D : ℝ}
    (hβ : 0 < β) (hD : 0 < D) (hα : α = β / (8 * D))
    (hρ : 0 ≤ ρ) (hs : s ≤ 1)
    (hmargin : α / Real.sqrt 2 - α / 16 ≤ α * s - β * ρ) :
    1 / Real.sqrt 2 - 1 / 16 ≤ s ∧ 0 < s ∧ D * ρ < s / 2 := by
  have hαpos : 0 < α := by rw [hα]; positivity
  have hβρ : 0 ≤ β * ρ := mul_nonneg hβ.le hρ
  have hscale : α * (8 * D) = β := by rw [hα]; field_simp
  have hs0 : 1 / Real.sqrt 2 - 1 / 16 ≤ s := by
    apply (mul_le_mul_left hαpos).mp
    calc
      α * (1 / Real.sqrt 2 - 1 / 16) = α / Real.sqrt 2 - α / 16 := by ring
      _ ≤ α * s := by linarith
  have hspos : 0 < s := lt_of_lt_of_le margin_threshold_pos hs0
  have hrootpos : 0 < Real.sqrt 2 := by positivity
  have hroot : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hinv : (2 / 3 : ℝ) < 1 / Real.sqrt 2 := by
    apply (lt_div_iff₀ hrootpos).2
    nlinarith
  have hαbound : α * ((2 / 3 : ℝ) - 1 / 16) < α / Real.sqrt 2 - α / 16 := by
    have := mul_lt_mul_of_pos_left hinv hαpos
    convert sub_lt_sub_right this (α / 16) using 1 <;> ring
  have hres : β * ρ < α * (1 - ((2 / 3 : ℝ) - 1 / 16)) := by
    have := mul_le_mul_of_nonneg_left hs hαpos.le
    nlinarith
  have hbound : D * ρ < (1 - ((2 / 3 : ℝ) - 1 / 16)) / 8 := by
    apply (mul_lt_mul_left hαpos).mp
    nlinarith [hscale]
  refine ⟨hs0, hspos, ?_⟩
  linarith

theorem unscale_residual (H : E →ₗ[ℝ] E) (z b : E) {s : ℝ} (hs : s ≠ 0) :
    H (s⁻¹ • z) - b = s⁻¹ • (H z - s • b) := by
  simp [smul_sub, smul_smul, hs]

/-- Actual normed-space residual recovery. The scalar `D` is `√d` in the
manuscript, and `ρ` is `‖Hz - sb‖∞`.
-/
theorem small_gap_residual (H : E →ₗ[ℝ] E) (z b : E) {α β s ρ D : ℝ}
    (hβ : 0 < β) (hD : 0 < D) (hα : α = β / (8 * D))
    (hfeasible : Feasible z s) (hρ : 0 ≤ ρ)
    (hcompare : ‖H z - s • b‖ ≤ D * ρ)
    (hmargin : α / Real.sqrt 2 - α / 16 ≤ α * s - β * ρ) :
    1 / Real.sqrt 2 - 1 / 16 ≤ s ∧ 0 < s ∧ ‖H (s⁻¹ • z) - b‖ < 1 / 2 := by
  obtain ⟨hs0, hs, hres⟩ :=
    margin_recovery hβ hD hα hρ (feasible_scalar_le_one hfeasible) hmargin
  refine ⟨hs0, hs, ?_⟩
  rw [unscale_residual H z b hs.ne', norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs)]
  have hn : ‖H z - s • b‖ < s / 2 := lt_of_le_of_lt hcompare hres
  have := mul_lt_mul_of_pos_left hn (inv_pos.mpr hs)
  have heq : s⁻¹ * (s / 2) = 1 / 2 := by field_simp
  rwa [heq] at this

theorem euclidean_norm_le_sqrt_mul {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hv : ∀ i, ‖v i‖ ≤ ρ) :
    ‖v‖ ≤ Real.sqrt n * ρ := by
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt (∑ _ : Fin n, ρ ^ 2) := by
      gcongr with i
      exact hv i
    _ = Real.sqrt n * ρ := by
      simp [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hρ]

/-- Recovery specialized to actual finite-dimensional Euclidean coordinates.
Only the full-gap-to-margin implication remains an external hypothesis here.
-/
theorem euclidean_small_gap_residual {n : ℕ} (hn : 0 < n)
    (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (z b : EuclideanSpace ℝ (Fin n)) {α β s ρ : ℝ}
    (hβ : 0 < β) (hα : α = β / (8 * Real.sqrt n))
    (hfeasible : Feasible z s) (hρ : 0 ≤ ρ)
    (hcoords : ∀ i, ‖(H z - s • b) i‖ ≤ ρ)
    (hmargin : α / Real.sqrt 2 - α / 16 ≤ α * s - β * ρ) :
    1 / Real.sqrt 2 - 1 / 16 ≤ s ∧ 0 < s ∧ ‖H (s⁻¹ • z) - b‖ < 1 / 2 := by
  apply small_gap_residual H z b hβ (by positivity) hα hfeasible hρ
    (euclidean_norm_le_sqrt_mul _ hρ hcoords) hmargin

section ActualGame

variable {n : ℕ}

/-- The simplex for the `2n` signed rows. -/
def RowSimplex (y : Fin n × Bool → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1

/-- A row of `A = -C`; the Boolean sign reverses the paper's sign index.
This harmless reindexing exchanges the two copies of each row. -/
noncomputable def rowPayoff (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) (j : Fin n × Bool) : ℝ :=
  -α * s + β * (if j.2 then 1 else -1) * (H z - s • b) j.1

noncomputable def payoff (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (z : EuclideanSpace ℝ (Fin n)) (s : ℝ)
    (y : Fin n × Bool → ℝ) : ℝ := ∑ j, y j * rowPayoff H b α β z s j

/-- Full saddle-gap bound in its universal pairwise form: every feasible
deviation pair has payoff difference at most `ε`. This formulation requires
no choice of maximizers and is equivalent to the max-minus-min bound whenever
the extrema exist. -/
def FullGapLE (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) (y : Fin n × Bool → ℝ) (ε : ℝ) : Prop :=
  ∀ (z' : EuclideanSpace ℝ (Fin n)) (s' : ℝ), Feasible z' s' →
    ∀ y', RowSimplex y' → payoff H b α β z s y' - payoff H b α β z' s' y ≤ ε

/-- Exact connection between the universal deviation formulation and the
paper's maximum-minus-minimum definition, whenever the extrema are attained. -/
theorem fullGapLE_iff_of_extrema
    (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b z : EuclideanSpace ℝ (Fin n)) (α β s : ℝ) (y : Fin n × Bool → ℝ)
    (P D ε : ℝ)
    (hP : ∀ y', RowSimplex y' → payoff H b α β z s y' ≤ P)
    (hPatt : ∃ y', RowSimplex y' ∧ payoff H b α β z s y' = P)
    (hD : ∀ z' s', Feasible z' s' → D ≤ payoff H b α β z' s' y)
    (hDatt : ∃ z' s', Feasible z' s' ∧ payoff H b α β z' s' y = D) :
    FullGapLE H b α β z s y ε ↔ P - D ≤ ε := by
  constructor
  · intro hg
    obtain ⟨yp, hyp, hep⟩ := hPatt
    obtain ⟨zd, sd, hd, hed⟩ := hDatt
    have := hg zd sd hd yp hyp
    rwa [hep, hed] at this
  · intro hg z' s' hz' y' hy'
    have hp := hP y' hy'
    have hd := hD z' s' hz'
    linarith

noncomputable def pureStrategy (j : Fin n × Bool) : Fin n × Bool → ℝ :=
  fun k => if k = j then 1 else 0

theorem pureStrategy_simplex (j : Fin n × Bool) : RowSimplex (pureStrategy j) := by
  classical
  constructor
  · intro k
    simp only [pureStrategy]
    split_ifs <;> norm_num
  · simp [pureStrategy]

theorem payoff_pure (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (z : EuclideanSpace ℝ (Fin n))
    (s : ℝ) (j : Fin n × Bool) :
    payoff H b α β z s (pureStrategy j) = rowPayoff H b α β z s j := by
  classical
  simp [payoff, pureStrategy]

theorem payoff_of_zero_residual
    (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (z : EuclideanSpace ℝ (Fin n))
    (s : ℝ) (y : Fin n × Bool → ℝ) (hy : RowSimplex y) (hz : H z - s • b = 0) :
    payoff H b α β z s y = -α * s := by
  unfold payoff
  simp only [rowPayoff, hz, PiLp.zero_apply, mul_zero, add_zero]
  rw [← Finset.sum_mul, hy.2, one_mul]

/-- Derives the margin inequality from the actual game gap, rather than
postulating it as a residual estimate. -/
theorem fullGap_margin (hn : 0 < n)
    (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b z : EuclideanSpace ℝ (Fin n)) (α β s : ℝ) (y : Fin n × Bool → ℝ)
    (hα : 0 ≤ α) (hβ : 0 < β) (hy : RowSimplex y)
    (hsource : ∃ zstar, H zstar = b ∧ ‖zstar‖ ≤ 1)
    (hgap : FullGapLE H b α β z s y (α / 16)) :
    α / Real.sqrt 2 - α / 16 ≤
      α * s - β * ‖fun i : Fin n => (H z - s • b) i‖ := by
  obtain ⟨zstar, hzstar, hnorm⟩ := hsource
  obtain ⟨zw, sw, hw, hzero, hmargin⟩ := positive_margin_witness H hzstar hnorm hα
  have hwpay := payoff_of_zero_residual H b α β zw sw y hy hzero
  have hrow (j : Fin n × Bool) : rowPayoff H b α β z s j + α * sw ≤ α / 16 := by
    have hg := hgap zw sw hw (pureStrategy j) (pureStrategy_simplex j)
    rw [payoff_pure, hwpay] at hg
    linarith
  let c := α * s - α / Real.sqrt 2 + α / 16
  have hplus (i : Fin n) : β * (H z - s • b) i ≤ c := by
    have hh := hrow (i, true)
    simp only [rowPayoff, if_true, mul_one] at hh
    change β * (H z - s • b) i ≤ α * s - α / Real.sqrt 2 + α / 16
    linarith
  have hminus (i : Fin n) : -(β * (H z - s • b) i) ≤ c := by
    have hh := hrow (i, false)
    simp only [rowPayoff, Bool.false_eq_true, if_false, mul_neg_one] at hh
    change -(β * (H z - s • b) i) ≤ α * s - α / Real.sqrt 2 + α / 16
    nlinarith
  have hc : 0 ≤ c := by
    have hp := hplus ⟨0, hn⟩
    have hm := hminus ⟨0, hn⟩
    linarith
  have hcoord (i : Fin n) : ‖(H z - s • b) i‖ ≤ c / β := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · rw [← neg_div]
      apply (div_le_iff₀ hβ).2
      nlinarith [hminus i]
    · apply (le_div_iff₀ hβ).2
      nlinarith [hplus i]
  have hsup : ‖fun i : Fin n => (H z - s • b) i‖ ≤ c / β :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hc hβ.le)).2 hcoord
  have hmul := (le_div_iff₀ hβ).mp hsup
  change ‖fun i : Fin n => (H z - s • b) i‖ * β ≤
    α * s - α / Real.sqrt 2 + α / 16 at hmul
  nlinarith

/-- The full ball--simplex residual recovery statement for the explicit
signed-row payoff. The source-solution assumption is precisely the consequence
of invertibility, `σ_min(H) ≥ 1`, and `‖b‖ = 1` used by the paper. -/
theorem fullGap_residual (hn : 0 < n)
    (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (b z : EuclideanSpace ℝ (Fin n)) {α β s : ℝ} (y : Fin n × Bool → ℝ)
    (hβ : 0 < β) (hα : α = β / (8 * Real.sqrt n))
    (hz : Feasible z s) (hy : RowSimplex y)
    (hsource : ∃ zstar, H zstar = b ∧ ‖zstar‖ ≤ 1)
    (hgap : FullGapLE H b α β z s y (α / 16)) :
    1 / Real.sqrt 2 - 1 / 16 ≤ s ∧ 0 < s ∧ ‖H (s⁻¹ • z) - b‖ < 1 / 2 := by
  have hαpos : 0 < α := by rw [hα]; positivity
  exact euclidean_small_gap_residual hn H z b hβ hα hz (norm_nonneg _)
    (fun i => norm_le_pi_norm (fun i : Fin n => (H z - s • b) i) i)
    (fullGap_margin hn H b z α β s y hαpos.le hβ hy hsource hgap)

end ActualGame

theorem source_solution_of_surjective_lower_bound (H : E →ₗ[ℝ] E)
    (honto : Function.Surjective H) (hlower : ∀ z, ‖z‖ ≤ ‖H z‖)
    {b : E} (hb : ‖b‖ ≤ 1) : ∃ zstar, H zstar = b ∧ ‖zstar‖ ≤ 1 := by
  obtain ⟨zstar, hz⟩ := honto b
  refine ⟨zstar, hz, (hlower zstar).trans ?_⟩
  simpa [hz] using hb

end BallReduction
end Matvec
