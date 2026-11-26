import FullJet.AdaptiveBatch
import Mathlib.Analysis.InnerProductSpace.Dual

namespace FullJet

section Riesz
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real Riesz representation, exposed as a linear map for finite means. -/
noncomputable def dualVectorLinear : (E →L[ℝ] ℝ) →ₗ[ℝ] E where
  toFun := (InnerProductSpace.toDual ℝ E).symm
  map_add' := map_add _
  map_smul' := by
    intro c x
    simpa using (InnerProductSpace.toDual ℝ E).symm.map_smulₛₗ c x

@[simp] theorem norm_dualVectorLinear (x : E →L[ℝ] ℝ) : ‖dualVectorLinear x‖ = ‖x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map x

theorem dualVectorLinear_injective : Function.Injective (dualVectorLinear (E := E)) :=
  (InnerProductSpace.toDual ℝ E).symm.injective

theorem uniformMean_dualVector {α : Type*} [Fintype α] [Nonempty α] (X : α → E →L[ℝ] ℝ) :
    uniformMean (fun a => dualVectorLinear (X a)) = dualVectorLinear (uniformMean X) :=
  pmfMean_linearMap _ _ _

theorem batchMean_dualVector {α : Type*} (X : α → E →L[ℝ] ℝ) {B : ℕ} (samples : Fin B → α) :
    batchMean (fun a => dualVectorLinear (X a)) samples = dualVectorLinear (batchMean X samples) :=
  batchMean_linearMap _ _ _

theorem finiteMartingale_dualVector {α : Type*}
    (step : (t : ℕ) → (Fin t → α) → α → E →L[ℝ] ℝ) (t : ℕ) (samples : Fin t → α) :
    finiteMartingale (fun t past a => dualVectorLinear (step t past a)) t samples =
      dualVectorLinear (finiteMartingale step t samples) := by
  induction t with
  | zero => simp [finiteMartingale]
  | succ t ih => simp only [finiteMartingale, ih, map_add]

theorem adaptiveBatchError_dualVector {α : Type*} [Fintype α] [Nonempty α] {B : ℕ}
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E →L[ℝ] ℝ)
    (t : ℕ) (samples : Fin t → Fin B → α) :
    adaptiveBatchError (fun t past a => dualVectorLinear (X t past a)) t samples =
      dualVectorLinear (adaptiveBatchError X t samples) := by
  unfold adaptiveBatchError
  have h : centeredBatchIncrement (fun t past a => dualVectorLinear (X t past a)) =
      fun t past samples => dualVectorLinear (centeredBatchIncrement X t past samples) := by
    funext t past samples
    simp only [centeredBatchIncrement, batchMean_dualVector, uniformMean_dualVector, map_sub]
  rw [h, finiteMartingale_dualVector]

theorem dual_adaptiveBatchError_mean_zero {α : Type*} [Fintype α] [Nonempty α] {B : ℕ}
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E →L[ℝ] ℝ) (hB : 0 < B) (t : ℕ) :
    uniformMean (adaptiveBatchError X t) = 0 := by
  apply dualVectorLinear_injective
  rw [← uniformMean_dualVector, map_zero]
  have h := adaptiveBatchError_mean_zero (fun t past a => dualVectorLinear (X t past a)) hB t
  change uniformMean (fun samples =>
    adaptiveBatchError (fun t past a => dualVectorLinear (X t past a)) t samples) = 0 at h
  simpa only [adaptiveBatchError_dualVector] using h

theorem dual_adaptiveBatchError_second_moment_upto {α : Type*} [Fintype α] [Nonempty α] {B : ℕ}
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E →L[ℝ] ℝ) (hB : 0 < B)
    (K : ℝ) (T : ℕ) (hK : ∀ t < T, ∀ past a, ‖X t past a‖ ≤ K) :
    uniformMean (fun samples => ‖adaptiveBatchError X T samples‖ ^ 2) ≤ (T : ℝ) * K ^ 2 / B := by
  have h := adaptiveBatchError_bounded_second_moment_upto
    (fun t past a => dualVectorLinear (X t past a)) hB K T
    (fun t ht past a => by simpa only [norm_dualVectorLinear] using hK t ht past a)
  simpa only [adaptiveBatchError_dualVector, norm_dualVectorLinear] using h

theorem dual_adaptiveBatchError_mean_norm_upto {α : Type*} [Fintype α] [Nonempty α] {B : ℕ}
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E →L[ℝ] ℝ) (hB : 0 < B)
    (K : ℝ) (hK : 0 ≤ K) (T : ℕ) (hbound : ∀ t < T, ∀ past a, ‖X t past a‖ ≤ K) :
    uniformMean (fun samples => ‖adaptiveBatchError X T samples‖) ≤
      Real.sqrt T * K / Real.sqrt B := by
  have hs := dual_adaptiveBatchError_second_moment_upto X hB K T hbound
  have hj := pmfMean_norm_le_sqrt (PMF.uniformOfFintype (Fin T → Fin B → α))
    (fun samples => dualVectorLinear (adaptiveBatchError X T samples))
  simp only [norm_dualVectorLinear] at hj
  calc
    _ ≤ Real.sqrt (uniformMean (fun samples => ‖adaptiveBatchError X T samples‖ ^ 2)) := hj
    _ ≤ Real.sqrt ((T : ℝ) * K ^ 2 / B) := Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)),
        Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hK]

/-- Transfer the adaptive Hilbert-space calculation to the actual operator norm
used for gradients by the oracle model. -/
theorem dual_adaptiveBatchError_second_moment {α : Type*} [Fintype α] [Nonempty α] {B : ℕ}
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E →L[ℝ] ℝ) (hB : 0 < B)
    (K : ℝ) (hK : ∀ t past a, ‖X t past a‖ ≤ K) (t : ℕ) :
    uniformMean (fun samples => ‖adaptiveBatchError X t samples‖ ^ 2) ≤ (t : ℝ) * K ^ 2 / B := by
  have h := adaptiveBatchError_bounded_second_moment
    (fun t past a => dualVectorLinear (X t past a)) hB K
    (fun t past a => by simpa only [norm_dualVectorLinear] using hK t past a) t
  simpa only [adaptiveBatchError_dualVector, norm_dualVectorLinear] using h

theorem dual_adaptiveBatchError_mean_norm {α : Type*} [Fintype α] [Nonempty α] {B : ℕ}
    (X : (t : ℕ) → (Fin t → Fin B → α) → α → E →L[ℝ] ℝ) (hB : 0 < B)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ t past a, ‖X t past a‖ ≤ K) (t : ℕ) :
    uniformMean (fun samples => ‖adaptiveBatchError X t samples‖) ≤
      Real.sqrt t * K / Real.sqrt B := by
  have h := adaptiveBatchError_mean_norm (fun t past a => dualVectorLinear (X t past a)) hB K hK
    (fun t past a => by simpa only [norm_dualVectorLinear] using hbound t past a) t
  simpa only [adaptiveBatchError_dualVector, norm_dualVectorLinear] using h

end Riesz

end FullJet
