import FreshGradientMinimax.PrimalLabelCoupling
import FreshGradientMinimax.LabelBadProbability

/-! Unconditional finite-label bounds for the actual unstopped auxiliary
queries and the compressed terminal output. The coin word is held fixed. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators
namespace Algorithm
variable {n D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

def primalBadX (L ε μ σ : ℝ) (c : ℕ → Bool) (seed : Seed)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (t : ℕ) (i : Fin ((n + 1) + (n + n))) : Prop :=
  coinPrefixCount c t < primalLabelStage n i ∧ primalLengthScale L ε / 4 <
    |radialCompression (primalCompressionRadius n L ε) (A.primalLabelQuery z L ε μ σ c t seed).1 (z i)|

def primalBadY (L ε μ σ : ℝ) (c : ℕ → Bool) (seed : Seed)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (t : ℕ) (i : Fin ((n + 1) + (n + n))) : Prop :=
  coinPrefixCount c t < primalLabelStage n i ∧
    ‖(A.primalLabelQuery z L ε μ σ c t seed).2‖ ≤ paperDualProtectionRadius n μ (primalValueScale L ε) ∧
    primalLengthScale L ε < |(A.primalLabelQuery z L ε μ σ c t seed).2 (z i)|

def primalBadOutput (L ε μ σ : ℝ) (c : ℕ → Bool) (N : ℕ) (seed : Seed)
    (z : Fin ((n + 1) + (n + n)) → Fin D) (i : Fin ((n + 1) + (n + n))) : Prop :=
  coinPrefixCount c N < primalLabelStage n i ∧ primalLengthScale L ε / 4 <
    |radialCompression (primalCompressionRadius n L ε) (A.primalLabelOutput z L ε μ σ c N seed) (z i)|

def PrimalLabelBad (L ε μ σ : ℝ) (c : ℕ → Bool) (N : ℕ) (seed : Seed)
    (z : Fin ((n + 1) + (n + n)) → Fin D) : Prop :=
  ¬ Function.Injective z ∨ (∃ t : Fin N, ∃ i, A.primalBadX L ε μ σ c seed z t.val i) ∨
    (∃ t : Fin N, ∃ i, A.primalBadY L ε μ σ c seed z t.val i) ∨
      ∃ i, A.primalBadOutput L ε μ σ c N seed z i

theorem expect_primalBadX_le [NeZero D] {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (seed : Seed) (t : ℕ) (i : Fin ((n + 1) + (n + n))) :
    (𝔼 z, truthValue (A.primalBadX L ε μ σ c seed z t i)) ≤
      primalCompressionRadius n L ε ^ 2 / ((D : ℝ) * (primalLengthScale L ε / 4) ^ 2) := by
  by_cases hi : coinPrefixCount c t < primalLabelStage n i
  · simp only [primalBadX, hi, true_and]
    apply expect_hidden_projection _ i _ (div_pos (primalLengthScale_pos hL hε) (by norm_num))
      (fun z => radialCompression_norm_bound (primalCompressionRadius_pos n hL hε).le _)
    intro z j
    rw [A.primalLabelQuery_update_hidden hL hε μ σ c seed t z i hi j]
  · simp only [primalBadX, hi, false_and, truthValue, if_false, Finset.expect_const_zero]
    positivity

theorem expect_primalBadY_le [NeZero D] {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (seed : Seed) (t : ℕ) (i : Fin ((n + 1) + (n + n))) :
    (𝔼 z, truthValue (A.primalBadY L ε μ σ c seed z t i)) ≤
      paperDualProtectionRadius n μ (primalValueScale L ε) ^ 2 / ((D : ℝ) * primalLengthScale L ε ^ 2) := by
  by_cases hi : coinPrefixCount c t < primalLabelStage n i
  · simp only [primalBadY, hi, true_and]
    apply expect_bounded_hidden_projection _ i _ (by unfold paperDualProtectionRadius; positivity)
      (primalLengthScale_pos hL hε)
    intro z j
    rw [A.primalLabelQuery_update_hidden hL hε μ σ c seed t z i hi j]
  · simp only [primalBadY, hi, false_and, truthValue, if_false, Finset.expect_const_zero]
    positivity

theorem expect_primalBadOutput_le [NeZero D] {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (N : ℕ) (seed : Seed) (i : Fin ((n + 1) + (n + n))) :
    (𝔼 z, truthValue (A.primalBadOutput L ε μ σ c N seed z i)) ≤
      primalCompressionRadius n L ε ^ 2 / ((D : ℝ) * (primalLengthScale L ε / 4) ^ 2) := by
  by_cases hi : coinPrefixCount c N < primalLabelStage n i
  · simp only [primalBadOutput, hi, true_and]
    apply expect_hidden_projection _ i _ (div_pos (primalLengthScale_pos hL hε) (by norm_num))
      (fun z => radialCompression_norm_bound (primalCompressionRadius_pos n hL hε).le _)
    intro z j
    rw [A.primalLabelOutput_update_hidden hL hε μ σ c seed N z i hi j]
  · simp only [primalBadOutput, hi, false_and, truthValue, if_false, Finset.expect_const_zero]
    positivity

theorem primalLabelBad_indicator_le (L ε μ σ : ℝ) (c : ℕ → Bool) (N : ℕ) (seed : Seed)
    (z : Fin ((n + 1) + (n + n)) → Fin D) :
    truthValue (A.PrimalLabelBad L ε μ σ c N seed z) ≤ truthValue (¬ Function.Injective z) +
      ((∑ t : Fin N, ∑ i, truthValue (A.primalBadX L ε μ σ c seed z t.val i)) +
        ((∑ t : Fin N, ∑ i, truthValue (A.primalBadY L ε μ σ c seed z t.val i)) +
          ∑ i, truthValue (A.primalBadOutput L ε μ σ c N seed z i))) := by
  have hx := (truthValue_exists_le (fun t : Fin N => ∃ i, A.primalBadX L ε μ σ c seed z t.val i)).trans
    (Finset.sum_le_sum (fun t _ => truthValue_exists_le _))
  have hy := (truthValue_exists_le (fun t : Fin N => ∃ i, A.primalBadY L ε μ σ c seed z t.val i)).trans
    (Finset.sum_le_sum (fun t _ => truthValue_exists_le _))
  exact (truthValue_or_le _ _).trans (add_le_add_left
    ((truthValue_or_le _ _).trans (add_le_add hx
      ((truthValue_or_le _ _).trans (add_le_add hy (truthValue_exists_le _))))) _)

theorem expect_primalLabelBad_le [NeZero D] {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (μ σ : ℝ)
    (c : ℕ → Bool) (N : ℕ) (seed : Seed) :
    (𝔼 z : Fin ((n + 1) + (n + n)) → Fin D, truthValue (A.PrimalLabelBad L ε μ σ c N seed z)) ≤
      (((n + 1) + (n + n) : ℕ) : ℝ) ^ 2 / D +
        (N + 1 : ℝ) * ((n + 1) + (n + n) : ℕ) *
          (primalCompressionRadius n L ε ^ 2 / ((D : ℝ) * (primalLengthScale L ε / 4) ^ 2)) +
        (N : ℝ) * ((n + 1) + (n + n) : ℕ) *
          (paperDualProtectionRadius n μ (primalValueScale L ε) ^ 2 / ((D : ℝ) * primalLengthScale L ε ^ 2)) := by
  have h0 := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ : Finset (Fin ((n + 1) + (n + n)) → Fin D))) =>
    A.primalLabelBad_indicator_le L ε μ σ c N seed z)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm] at h0
  apply h0.trans
  calc
    _ ≤ (((n + 1) + (n + n) : ℕ) : ℝ) ^ 2 / D +
        ((∑ _t : Fin N, ∑ _i : Fin ((n + 1) + (n + n)),
          primalCompressionRadius n L ε ^ 2 / ((D : ℝ) * (primalLengthScale L ε / 4) ^ 2)) +
          ((∑ _t : Fin N, ∑ _i : Fin ((n + 1) + (n + n)),
            paperDualProtectionRadius n μ (primalValueScale L ε) ^ 2 / ((D : ℝ) * primalLengthScale L ε ^ 2)) +
            ∑ _i : Fin ((n + 1) + (n + n)),
              primalCompressionRadius n L ε ^ 2 / ((D : ℝ) * (primalLengthScale L ε / 4) ^ 2))) :=
      add_le_add expect_collision_le
        (add_le_add (Finset.sum_le_sum (fun t _ =>
          Finset.sum_le_sum (fun i _ => A.expect_primalBadX_le hL hε μ σ c seed t.val i)))
          (add_le_add (Finset.sum_le_sum (fun t _ =>
            Finset.sum_le_sum (fun i _ => A.expect_primalBadY_le hL hε μ σ c seed t.val i)))
            (Finset.sum_le_sum (fun i _ => A.expect_primalBadOutput_le hL hε μ σ c N seed i))))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Algorithm
end FreshGradientMinimax
