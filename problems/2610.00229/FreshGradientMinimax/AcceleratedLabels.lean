import FreshGradientMinimax.AcceleratedRawModel
import FreshGradientMinimax.CoordinateFrame

/-! Independent finite labels for both accelerated frame blocks. Actual
instances use legal fallback frames; auxiliary replies use raw readings. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedLabelStage (n k : ℕ) : Fin ((k * 2 + 1) + k * (n + 2)) → ℕ :=
  Fin.addCases (acceleratedPrimalStage n) (acceleratedDualStage n)

def acceleratedPrimalLabels {n k D : ℕ} (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) :
    Fin (k * 2 + 1) → Fin D := fun i => z (i.castAdd (k * (n + 2)))

def acceleratedDualLabels {n k D : ℕ} (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) :
    Fin (k * (n + 2)) → Fin D := fun i => z (i.natAdd (k * 2 + 1))

theorem acceleratedPrimalLabels_injective {n k D : ℕ}
    {z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D} (hz : Function.Injective z) :
    Function.Injective (acceleratedPrimalLabels z) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun a : Fin ((k * 2 + 1) + k * (n + 2)) => a.val) (hz h)

theorem acceleratedDualLabels_injective {n k D : ℕ}
    {z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D} (hz : Function.Injective z) :
    Function.Injective (acceleratedDualLabels z) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val (hz h)
  change k * 2 + 1 + i.val = k * 2 + 1 + j.val at he
  omega

def acceleratedPrimalLabelFrame {n k D : ℕ} (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid D :=
  labelFrame (by omega) (acceleratedPrimalLabels z)

def acceleratedDualLabelFrame {n k D : ℕ} (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid D :=
  labelFrame (by omega) (acceleratedDualLabels z)

theorem acceleratedPrimalLabelFrame_coordinates {n k D : ℕ} (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (hz : Function.Injective z) :
    frameCoordinates (acceleratedPrimalLabelFrame hD z) = coordinateRead (acceleratedPrimalLabels z) := by
  rw [acceleratedPrimalLabelFrame, labelFrame_of_injective _ _ (acceleratedPrimalLabels_injective hz),
    coordinateFrame_coordinates]

theorem acceleratedDualLabelFrame_coordinates {n k D : ℕ} (hD : (k * 2 + 1) + k * (n + 2) ≤ D)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (hz : Function.Injective z) :
    frameCoordinates (acceleratedDualLabelFrame hD z) = coordinateRead (acceleratedDualLabels z) := by
  rw [acceleratedDualLabelFrame, labelFrame_of_injective _ _ (acceleratedDualLabels_injective hz),
    coordinateFrame_coordinates]

def acceleratedLabelReply {n k D : ℕ} (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (L ε : ℝ) (t : ℕ) : Joint D D → Joint D D :=
  acceleratedPrefixReply (coordinateRead (acceleratedPrimalLabels z))
    (coordinateRead (acceleratedDualLabels z)) L ε (t + 1)

theorem acceleratedLabelReply_measurable {n k D : ℕ}
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D) (hk : 0 < k) (L ε : ℝ) (t : ℕ) :
    Measurable (acceleratedLabelReply z L ε t) := acceleratedPrefixReply_measurable _ _ hk L ε _

theorem acceleratedLabelReply_congr {n k D t : ℕ}
    {z z' : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D} (L ε : ℝ)
    (h : ∀ i, acceleratedLabelStage n k i ≤ t + 1 → z i = z' i) :
    acceleratedLabelReply z L ε t = acceleratedLabelReply z' L ε t := by
  apply acceleratedPrefixReply_congr
  · intro j hj x
    change x (z (j.castAdd (k * (n + 2)))) = x (z' (j.castAdd (k * (n + 2))))
    rw [h _ (by simpa only [acceleratedLabelStage, Fin.addCases_left] using hj)]
  · intro j hj y
    change y (z (j.natAdd (k * 2 + 1))) = y (z' (j.natAdd (k * 2 + 1)))
    rw [h _ (by simpa only [acceleratedLabelStage, Fin.addCases_right] using hj)]

end FreshGradientMinimax
