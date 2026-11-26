import FreshGradientMinimax.AcceleratedLabelBadEvents

/-! The ambient dimension is fixed before the algorithm. It bounds all
bad events, including label collisions and the final output. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

def acceleratedLabelHidingMass (n k H : ℕ) : ℝ :=
  (((k * 2 + 1) + k * (n + 2) : ℕ) : ℝ) ^ 2 +
    (H + 1 : ℝ) * ((k * 2 + 1) + k * (n + 2) : ℕ) *
      (acceleratedPrimalRadius k ^ 2 / acceleratedHidingThreshold n k ^ 2) +
    (H : ℝ) * ((k * 2 + 1) + k * (n + 2) : ℕ) *
      ((2 * acceleratedDualRadius n k) ^ 2 / acceleratedHidingThreshold n k ^ 2)

def acceleratedLabelDimension (n k H : ℕ) : ℕ :=
  (k * 2 + 1) + k * (n + 2) + 1 + ⌈12 * acceleratedLabelHidingMass n k H⌉₊

theorem acceleratedLabelDimension_size (n k H : ℕ) :
    (k * 2 + 1) + k * (n + 2) ≤ acceleratedLabelDimension n k H := by
  unfold acceleratedLabelDimension
  omega

theorem acceleratedLabelDimension_pos (n k H : ℕ) : 0 < acceleratedLabelDimension n k H := by
  have h := acceleratedLabelDimension_size n k H
  omega

instance acceleratedLabelDimension_neZero (n k H : ℕ) : NeZero (acceleratedLabelDimension n k H) :=
  ⟨ne_of_gt (acceleratedLabelDimension_pos n k H)⟩

theorem acceleratedLabelDimension_mass (n k H : ℕ) :
    12 * acceleratedLabelHidingMass n k H ≤ (acceleratedLabelDimension n k H : ℝ) := by
  apply (Nat.le_ceil (12 * acceleratedLabelHidingMass n k H)).trans
  exact_mod_cast (show ⌈12 * acceleratedLabelHidingMass n k H⌉₊ ≤ acceleratedLabelDimension n k H by
    unfold acceleratedLabelDimension; omega)

theorem acceleratedLabelDimension_ratio (n k H : ℕ) :
    acceleratedLabelHidingMass n k H / acceleratedLabelDimension n k H ≤ (1 / 12 : ℝ) := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (acceleratedLabelDimension_pos n k H) :
    (0 : ℝ) < acceleratedLabelDimension n k H)).mpr
  linarith only [acceleratedLabelDimension_mass n k H]

theorem Algorithm.acceleratedLabelBad_one_twelfth (n k H : ℕ) (hk : 0 < k) (L ε : ℝ)
    {Seed : Type*} [MeasurableSpace Seed]
    (A : Algorithm (acceleratedLabelDimension n k H) (acceleratedLabelDimension n k H) Seed) (seed : Seed) :
    (𝔼 z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin (acceleratedLabelDimension n k H),
      truthValue (A.AcceleratedLabelBad L ε H seed z)) ≤ (1 / 12 : ℝ) := by
  have h := A.expect_acceleratedLabelBad_le hk L ε H seed (n := n)
  have he : (((k * 2 + 1) + k * (n + 2) : ℕ) : ℝ) ^ 2 / acceleratedLabelDimension n k H +
        (H + 1 : ℝ) * ((k * 2 + 1) + k * (n + 2) : ℕ) *
          (acceleratedPrimalRadius k ^ 2 / ((acceleratedLabelDimension n k H : ℝ) * acceleratedHidingThreshold n k ^ 2)) +
        (H : ℝ) * ((k * 2 + 1) + k * (n + 2) : ℕ) *
          ((2 * acceleratedDualRadius n k) ^ 2 / ((acceleratedLabelDimension n k H : ℝ) * acceleratedHidingThreshold n k ^ 2)) =
      acceleratedLabelHidingMass n k H / acceleratedLabelDimension n k H := by
    unfold acceleratedLabelHidingMass
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact (h.trans_eq he).trans (acceleratedLabelDimension_ratio n k H)

end FreshGradientMinimax
