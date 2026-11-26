import FreshGradientMinimax.LabelInteraction
import FreshGradientMinimax.FiniteBadEvents

/-! An unconditional bound on all discrepancies of the real auxiliary run.
Only the auxiliary process is used to form the bad projections; it is never
stopped or conditioned on survival. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def boundedRead {I : Type*} {D : ℕ} (q : I → Euclid D) (B : ℝ) (z : I) : Euclid D :=
  if ‖q z‖ ≤ B then q z else 0

theorem boundedRead_norm {I : Type*} {D : ℕ} (q : I → Euclid D) {B : ℝ} (hB : 0 ≤ B) (z : I) :
    ‖boundedRead q B z‖ ≤ B := by
  unfold boundedRead
  split_ifs with h
  · exact h
  · simpa only [norm_zero] using hB

theorem boundedRead_projection {I : Type*} {D : ℕ} (q : I → Euclid D) (B : ℝ)
    {a : ℝ} (ha : 0 < a) (z : I) (j : Fin D) :
    truthValue (‖q z‖ ≤ B ∧ a < |q z j|) = truthValue (a < |boundedRead q B z j|) := by
  classical
  unfold boundedRead
  by_cases h : ‖q z‖ ≤ B
  · simp only [h, if_true, true_and]
  · simp [h, truthValue, not_lt.mpr ha.le]

theorem expect_bounded_hidden_projection {m D : ℕ} [NeZero D]
    (q : (Fin m → Fin D) → Euclid D) (i : Fin m)
    (hind : ∀ z j, q (Function.update z i j) = q z)
    {B a : ℝ} (hB : 0 ≤ B) (ha : 0 < a) :
    (𝔼 z, truthValue (‖q z‖ ≤ B ∧ a < |q z (z i)|)) ≤ B ^ 2 / ((D : ℝ) * a ^ 2) := by
  simp_rw [boundedRead_projection q B ha]
  apply expect_hidden_projection _ i _ ha (boundedRead_norm q hB)
  intro z j
  simp only [boundedRead, hind]

namespace Algorithm
variable {D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm 1 D Seed)

def labelBadProjection (p : Parameters) (N : ℕ) (seed : Seed)
    (z : Fin (4 * N + 4) → Fin D) (t : Fin N) (i : Fin (4 * N + 4)) : Prop :=
  i ∉ pathVisible (4 * N + 4) (t.val + 1) ∧
    ‖(A.labelQuery p N z t.val seed).2‖ ≤ 2 * pathHardRadius p.L p.μ p.ε (4 * N + 3) ∧
      pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2 < |(A.labelQuery p N z t.val seed).2 (z i)|

theorem labelBad_witness (p : Parameters) (N : ℕ) (seed : Seed) (z : Fin (4 * N + 4) → Fin D)
    (h : ¬ A.LabelGood p N z seed) :
    ¬ Function.Injective z ∨ ∃ t : Fin N, ∃ i, A.labelBadProjection p N seed z t i := by
  classical
  by_cases hz : Function.Injective z
  · right
    have hq : ¬ (∀ t < N,
        ‖(A.labelQuery p N z t seed).2‖ ≤ 2 * pathHardRadius p.L p.μ p.ε (4 * N + 3) →
          ∀ i ∉ pathVisible (4 * N + 4) (t + 1),
            |(A.labelQuery p N z t seed).2 (z i)| ≤ pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) :=
      fun hq => h ⟨hz, hq⟩
    push_neg at hq
    obtain ⟨t, ht, hn, i, hi, hp⟩ := hq
    exact ⟨⟨t, ht⟩, i, hi, hn, hp⟩
  · exact Or.inl hz

theorem labelBad_indicator_le (p : Parameters) (N : ℕ) (seed : Seed) (z : Fin (4 * N + 4) → Fin D) :
    truthValue (¬ A.LabelGood p N z seed) ≤ truthValue (¬ Function.Injective z) +
      ∑ t : Fin N, ∑ i, truthValue (A.labelBadProjection p N seed z t i) := by
  have he := (truthValue_exists_le (fun t : Fin N => ∃ i, A.labelBadProjection p N seed z t i)).trans
    (Finset.sum_le_sum (fun t _ => truthValue_exists_le _))
  exact (truthValue_mono (A.labelBad_witness p N seed z)).trans
    ((truthValue_or_le _ _).trans (add_le_add_left he _))

theorem expect_labelBadProjection_le [NeZero D] (p : Parameters) (N : ℕ) (seed : Seed)
    (t : Fin N) (i : Fin (4 * N + 4)) :
    (𝔼 z, truthValue (A.labelBadProjection p N seed z t i)) ≤
      (2 * pathHardRadius p.L p.μ p.ε (4 * N + 3)) ^ 2 /
        ((D : ℝ) * (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) ^ 2) := by
  have hL : 0 < p.L := lt_of_lt_of_le p.μ_pos p.μ_le_L
  have hR := pathHardRadius_pos hL p.μ_pos p.ε_pos (4 * N + 3)
  have hδ := pathHardFlatWidth_pos hL p.μ_pos p.ε_pos (4 * N + 3)
  by_cases hi : i ∈ pathVisible (4 * N + 4) (t.val + 1)
  · simp only [labelBadProjection, hi, not_true_eq_false, false_and, truthValue, if_false,
      Finset.expect_const_zero]
    positivity
  · simp only [labelBadProjection, hi, not_false_eq_true, true_and]
    apply expect_bounded_hidden_projection _ i _ (by positivity) (by positivity)
    intro z j
    rw [A.labelQuery_update_hidden p N seed t.val z i hi j]

theorem expect_labelBad_le [NeZero D] (p : Parameters) (N : ℕ) (seed : Seed) :
    (𝔼 z : Fin (4 * N + 4) → Fin D, truthValue (¬ A.LabelGood p N z seed)) ≤
      ((4 * N + 4 : ℕ) : ℝ) ^ 2 / D + (N : ℝ) * (4 * N + 4 : ℕ) *
        ((2 * pathHardRadius p.L p.μ p.ε (4 * N + 3)) ^ 2 /
          ((D : ℝ) * (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) ^ 2)) := by
  calc
    _ ≤ 𝔼 z : Fin (4 * N + 4) → Fin D, (truthValue (¬ Function.Injective z) +
        ∑ t : Fin N, ∑ i, truthValue (A.labelBadProjection p N seed z t i)) :=
      Finset.expect_le_expect (fun z _ => A.labelBad_indicator_le p N seed z)
    _ = (𝔼 z : Fin (4 * N + 4) → Fin D, truthValue (¬ Function.Injective z)) +
        ∑ t : Fin N, ∑ i, 𝔼 z, truthValue (A.labelBadProjection p N seed z t i) := by
      simp only [Finset.expect_add_distrib, Finset.expect_sum_comm]
    _ ≤ ((4 * N + 4 : ℕ) : ℝ) ^ 2 / D + ∑ _ : Fin N, ∑ _ : Fin (4 * N + 4),
        ((2 * pathHardRadius p.L p.μ p.ε (4 * N + 3)) ^ 2 /
          ((D : ℝ) * (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3) / 2) ^ 2)) :=
      add_le_add expect_collision_le (Finset.sum_le_sum (fun t _ =>
        Finset.sum_le_sum (fun i _ => A.expect_labelBadProjection_le p N seed t i)))
    _ = _ := by simp; ring

end Algorithm
end FreshGradientMinimax
