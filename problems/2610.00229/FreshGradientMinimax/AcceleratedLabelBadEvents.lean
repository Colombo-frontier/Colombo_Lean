import FreshGradientMinimax.AcceleratedLabelInteraction
import FreshGradientMinimax.AcceleratedHidingThreshold
import FreshGradientMinimax.LabelBadProbability

/-! Unconditional projection bounds along the unstopped auxiliary run.
The final arbitrary output is included as one extra compressed query. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators
namespace Algorithm
variable {n k D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

def acceleratedBadX (L ε : ℝ) (seed : Seed)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (t : ℕ) (i : Fin ((k * 2 + 1) + k * (n + 2))) : Prop :=
  t < acceleratedLabelStage n k i ∧ acceleratedHidingThreshold n k <
    |radialCompression (acceleratedPrimalRadius k)
      ((acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).1) (z i)|

def acceleratedBadY (L ε : ℝ) (seed : Seed)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (t : ℕ) (i : Fin ((k * 2 + 1) + k * (n + 2))) : Prop :=
  t < acceleratedLabelStage n k i ∧
    ‖(acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).2‖ ≤ 2 * acceleratedDualRadius n k ∧
      acceleratedHidingThreshold n k <
        |((acceleratedLengthScale L ε)⁻¹ • (A.acceleratedLabelQuery z L ε t seed).2) (z i)|

def acceleratedBadOutput (L ε : ℝ) (H : ℕ) (seed : Seed)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (i : Fin ((k * 2 + 1) + k * (n + 2))) : Prop :=
  H < acceleratedLabelStage n k i ∧ acceleratedHidingThreshold n k <
    |radialCompression (acceleratedPrimalRadius k)
      ((acceleratedLengthScale L ε)⁻¹ • A.acceleratedLabelOutput z L ε H seed) (z i)|

def AcceleratedLabelBad (L ε : ℝ) (H : ℕ) (seed : Seed)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) : Prop :=
  ¬ Function.Injective z ∨ (∃ t : Fin H, ∃ i, A.acceleratedBadX L ε seed z t.val i) ∨
    (∃ t : Fin H, ∃ i, A.acceleratedBadY L ε seed z t.val i) ∨
      ∃ i, A.acceleratedBadOutput L ε H seed z i

theorem expect_acceleratedBadX_le [NeZero D] (hk : 0 < k) (L ε : ℝ)
    (seed : Seed) (t : ℕ) (i : Fin ((k * 2 + 1) + k * (n + 2))) :
    (𝔼 z, truthValue (A.acceleratedBadX L ε seed z t i)) ≤
      acceleratedPrimalRadius k ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2) := by
  by_cases hi : t < acceleratedLabelStage n k i
  · simp only [acceleratedBadX, hi, true_and]
    apply expect_hidden_projection _ i _ (acceleratedHidingThreshold_pos n hk)
      (fun z => radialCompression_norm_bound (acceleratedPrimalRadius_pos k).le _)
    intro z j
    rw [A.acceleratedLabelQuery_update_hidden L ε seed t z i hi j]
  · simp only [acceleratedBadX, hi, false_and, truthValue, if_false, Finset.expect_const_zero]
    positivity

theorem expect_acceleratedBadY_le [NeZero D] (hk : 0 < k) (L ε : ℝ)
    (seed : Seed) (t : ℕ) (i : Fin ((k * 2 + 1) + k * (n + 2))) :
    (𝔼 z, truthValue (A.acceleratedBadY L ε seed z t i)) ≤
      (2 * acceleratedDualRadius n k) ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2) := by
  by_cases hi : t < acceleratedLabelStage n k i
  · simp only [acceleratedBadY, hi, true_and]
    apply expect_bounded_hidden_projection _ i _ (by have := acceleratedDualRadius_pos n k; positivity)
      (acceleratedHidingThreshold_pos n hk)
    intro z j
    rw [A.acceleratedLabelQuery_update_hidden L ε seed t z i hi j]
  · simp only [acceleratedBadY, hi, false_and, truthValue, if_false, Finset.expect_const_zero]
    positivity

theorem expect_acceleratedBadOutput_le [NeZero D] (hk : 0 < k) (L ε : ℝ)
    (H : ℕ) (seed : Seed) (i : Fin ((k * 2 + 1) + k * (n + 2))) :
    (𝔼 z, truthValue (A.acceleratedBadOutput L ε H seed z i)) ≤
      acceleratedPrimalRadius k ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2) := by
  by_cases hi : H < acceleratedLabelStage n k i
  · simp only [acceleratedBadOutput, hi, true_and]
    apply expect_hidden_projection _ i _ (acceleratedHidingThreshold_pos n hk)
      (fun z => radialCompression_norm_bound (acceleratedPrimalRadius_pos k).le _)
    intro z j
    rw [A.acceleratedLabelOutput_update_hidden L ε seed H z i hi j]
  · simp only [acceleratedBadOutput, hi, false_and, truthValue, if_false, Finset.expect_const_zero]
    positivity

theorem acceleratedLabelBad_indicator_le (L ε : ℝ) (H : ℕ) (seed : Seed)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) :
    truthValue (A.AcceleratedLabelBad L ε H seed z) ≤ truthValue (¬ Function.Injective z) +
      ((∑ t : Fin H, ∑ i, truthValue (A.acceleratedBadX L ε seed z t.val i)) +
        ((∑ t : Fin H, ∑ i, truthValue (A.acceleratedBadY L ε seed z t.val i)) +
          ∑ i, truthValue (A.acceleratedBadOutput L ε H seed z i))) := by
  have hx := (truthValue_exists_le (fun t : Fin H => ∃ i, A.acceleratedBadX L ε seed z t.val i)).trans
    (Finset.sum_le_sum (fun t _ => truthValue_exists_le _))
  have hy := (truthValue_exists_le (fun t : Fin H => ∃ i, A.acceleratedBadY L ε seed z t.val i)).trans
    (Finset.sum_le_sum (fun t _ => truthValue_exists_le _))
  exact (truthValue_or_le _ _).trans (add_le_add_left
    ((truthValue_or_le _ _).trans (add_le_add hx
      ((truthValue_or_le _ _).trans (add_le_add hy (truthValue_exists_le _))))) _)

theorem expect_acceleratedLabelBad_le [NeZero D] (hk : 0 < k) (L ε : ℝ) (H : ℕ) (seed : Seed) :
    (𝔼 z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D, truthValue (A.AcceleratedLabelBad L ε H seed z)) ≤
      (((k * 2 + 1) + k * (n + 2) : ℕ) : ℝ) ^ 2 / D +
        (H + 1 : ℝ) * ((k * 2 + 1) + k * (n + 2) : ℕ) *
          (acceleratedPrimalRadius k ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2)) +
        (H : ℝ) * ((k * 2 + 1) + k * (n + 2) : ℕ) *
          ((2 * acceleratedDualRadius n k) ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2)) := by
  have h0 := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ :
      Finset (Fin ((k * 2 + 1) + k * (n + 2)) → Fin D))) => A.acceleratedLabelBad_indicator_le L ε H seed z)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm] at h0
  apply h0.trans
  calc
    _ ≤ (((k * 2 + 1) + k * (n + 2) : ℕ) : ℝ) ^ 2 / D +
        ((∑ _t : Fin H, ∑ _i : Fin ((k * 2 + 1) + k * (n + 2)),
          acceleratedPrimalRadius k ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2)) +
          ((∑ _t : Fin H, ∑ _i : Fin ((k * 2 + 1) + k * (n + 2)),
            (2 * acceleratedDualRadius n k) ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2)) +
            ∑ _i : Fin ((k * 2 + 1) + k * (n + 2)),
              acceleratedPrimalRadius k ^ 2 / ((D : ℝ) * acceleratedHidingThreshold n k ^ 2))) :=
      add_le_add expect_collision_le
        (add_le_add (Finset.sum_le_sum (fun t _ =>
          Finset.sum_le_sum (fun i _ => A.expect_acceleratedBadX_le hk L ε seed t.val i)))
          (add_le_add (Finset.sum_le_sum (fun t _ =>
            Finset.sum_le_sum (fun i _ => A.expect_acceleratedBadY_le hk L ε seed t.val i)))
            (Finset.sum_le_sum (fun i _ => A.expect_acceleratedBadOutput_le hk L ε H seed i))))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Algorithm
end FreshGradientMinimax
