import Bilevel.BatchMean
import Mathlib.Algebra.Order.Floor.Ring

/-! Independent-node allocation arithmetic and the corresponding genuine L2
error estimate. Centered adapted node errors are explicit hypotheses here;
constructing these errors from the article algorithm remains a separate step. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace Smoothness2601.WeightedBatches

def weightNorm (s : Finset ℕ) (d : ℕ → ℝ) : ℝ := ∑ j ∈ s, |d j|
def nodeCount (s : Finset ℕ) (d : ℕ → ℝ) (B : ℝ) (j : ℕ) : ℕ :=
  ⌈B * |d j| / weightNorm s d⌉₊

theorem weightNorm_pos {s : Finset ℕ} {d : ℕ → ℝ}
    (h : ∃ j ∈ s, d j ≠ 0) : 0 < weightNorm s d := by
  obtain ⟨j,hj,hd⟩ := h
  exact Finset.sum_pos' (fun i _ => abs_nonneg (d i)) ⟨j,hj,abs_pos.mpr hd⟩

theorem nodeCount_pos {s : Finset ℕ} {d : ℕ → ℝ} {B : ℝ} {j : ℕ}
    (hB : 0 < B) (hW : 0 < weightNorm s d) (hd : d j ≠ 0) :
    0 < nodeCount s d B j := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos hB (abs_pos.mpr hd)) hW

theorem allocation_lower {s : Finset ℕ} {d : ℕ → ℝ} {B : ℝ} (j : ℕ) :
    B * |d j| / weightNorm s d ≤ (nodeCount s d B j : ℝ) := Nat.le_ceil _

theorem node_cost {s : Finset ℕ} {d : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hW : 0 < weightNorm s d) :
    (∑ j ∈ s, (nodeCount s d B j : ℝ)) ≤ B + s.card := by
  have hc (j : ℕ) : (nodeCount s d B j : ℝ) ≤
      B * |d j| / weightNorm s d + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hB (abs_nonneg _)) hW.le)).le
  calc
    _ ≤ ∑ j ∈ s, (B * |d j| / weightNorm s d + 1) :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = B + s.card := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      change B * weightNorm s d / weightNorm s d + (s.card : ℝ) = _
      rw [mul_div_cancel_right₀ _ hW.ne']

theorem node_variance_term {s : Finset ℕ} {d : ℕ → ℝ} {B : ℝ} (j : ℕ)
    (hB : 0 < B) (hW : 0 < weightNorm s d) :
    d j ^ 2 / (nodeCount s d B j : ℝ) ≤ weightNorm s d * |d j| / B := by
  by_cases hd : d j = 0
  · simp [hd]
  have hb : 0 < (nodeCount s d B j : ℝ) := by
    exact_mod_cast nodeCount_pos hB hW hd
  have ha := allocation_lower (s := s) (d := d) (B := B) j
  have ha' := (div_le_iff₀ hW).mp ha
  apply (div_le_iff₀ hb).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hB).mpr
  have hm := mul_le_mul_of_nonneg_right ha' (abs_nonneg (d j))
  nlinarith [sq_abs (d j)]

theorem variance_allocation {s : Finset ℕ} {d : ℕ → ℝ} {B : ℝ}
    (hB : 0 < B) (hW : 0 < weightNorm s d) :
    (∑ j ∈ s, d j ^ 2 / (nodeCount s d B j : ℝ)) ≤ weightNorm s d ^ 2 / B := by
  calc
    _ ≤ ∑ j ∈ s, weightNorm s d * |d j| / B :=
      Finset.sum_le_sum (fun j _ => node_variance_term j hB hW)
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; simp only [weightNorm, pow_two]

variable {Ω E : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The weighted actual L2 random variable; node errors can be dependent as
long as they are centered conditionally on all preceding nodes. -/
def weightedError (s : Finset ℕ) (d : ℕ → ℝ) (ξ : ℕ → Lp E 2 ν) : Lp E 2 ν :=
  ∑ j ∈ s, d j • ξ j

theorem weighted_variance
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ ‹MeasurableSpace Ω›)
    (ξ : ℕ → Lp E 2 ν)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) ν)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 ν) = 0)
    (s : Finset ℕ) (d : ℕ → ℝ) :
    (∫ ω, ‖weightedError s d ξ ω‖^2 ∂ν) =
      ∑ j ∈ s, d j ^ 2 * (∫ ω, ‖ξ j ω‖^2 ∂ν) := by
  change Bilevel.StochasticInner.risk _ = ∑ j ∈ s, d j ^ 2 * Bilevel.StochasticInner.risk _
  simp only [Bilevel.StochasticInner.risk_eq_norm_sq, weightedError]
  rw [Bilevel.InexactHorner.orthogonal_sum_sq s (fun j => d j • ξ j) (by
    intro i _ j _ hij
    rw [real_inner_smul_left, real_inner_smul_right,
      Bilevel.BatchMean.errors_orthogonal past hle ξ adapted centered hij, mul_zero, mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Equations `Zvariance` and `Zcost` once the actual node means have their
conditional centering and `σ²/b_j` moment bound. -/
theorem weighted_error_and_cost
    (past : ℕ → MeasurableSpace Ω) (hle : ∀ j, past j ≤ ‹MeasurableSpace Ω›)
    (ξ : ℕ → Lp E 2 ν)
    (adapted : ∀ i j, i < j → AEStronglyMeasurable[past j] (ξ i) ν)
    (centered : ∀ j, (condExpL2 E ℝ (hle j) (ξ j) : Lp E 2 ν) = 0)
    (s : Finset ℕ) (d : ℕ → ℝ) {B σ : ℝ}
    (hB : 0 < B) (hW : 0 < weightNorm s d)
    (variance : ∀ j ∈ s, (∫ ω, ‖ξ j ω‖^2 ∂ν) ≤ σ^2 / (nodeCount s d B j : ℝ)) :
    (∫ ω, ‖weightedError s d ξ ω‖^2 ∂ν) ≤ σ^2 * weightNorm s d ^ 2 / B ∧
    (∑ j ∈ s, (nodeCount s d B j : ℝ)) ≤ B + s.card := by
  refine ⟨?_, node_cost hB.le hW⟩
  rw [weighted_variance past hle ξ adapted centered]
  calc
    _ ≤ ∑ j ∈ s, d j ^ 2 * (σ^2 / (nodeCount s d B j : ℝ)) :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (variance j hj) (sq_nonneg _))
    _ = σ^2 * (∑ j ∈ s, d j ^ 2 / (nodeCount s d B j : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ σ^2 * (weightNorm s d ^ 2 / B) :=
      mul_le_mul_of_nonneg_left (variance_allocation hB hW) (sq_nonneg _)
    _ = _ := by ring

end Smoothness2601.WeightedBatches
