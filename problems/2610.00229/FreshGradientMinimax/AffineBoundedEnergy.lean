import FreshGradientMinimax.BoundedEnergy
import FreshGradientMinimax.ConvexGradient

/-! Affine edge maps, with their exact gradient, convexity, uniform gradient
bound and the accumulated threshold perturbation. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct
variable {n m : ℕ}

def affineBoundedEnergy (A : Euclid n →L[ℝ] Euclid m) (z : Euclid m) (δ b : ℝ) (x : Euclid n) : ℝ :=
  boundedEnergy δ b (A x + z)

def affineBoundedGradient (A : Euclid n →L[ℝ] Euclid m) (z : Euclid m) (δ b : ℝ) (x : Euclid n) : Euclid n :=
  (A†) (boundedSlope δ b (A x + z))

theorem affineBoundedEnergy_hasFDerivAt (A : Euclid n →L[ℝ] Euclid m) (z : Euclid m)
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    HasFDerivAt (affineBoundedEnergy A z δ b) (innerSL ℝ (affineBoundedGradient A z δ b x)) x := by
  have hd := (boundedEnergy_hasFDerivAt hδ hb (A x + z)).comp x (A.hasFDerivAt.add_const z)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [affineBoundedGradient, innerSL_apply, ContinuousLinearMap.adjoint_inner_left]

theorem affineBoundedEnergy_convex (A : Euclid n →L[ℝ] Euclid m) (z : Euclid m)
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) : ConvexOn ℝ Set.univ (affineBoundedEnergy A z δ b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have h := (boundedEnergy_convex hδ hb).2 (Set.mem_univ (A x + z)) (Set.mem_univ (A y + z)) hs ht hst
  have he : A (s • x + t • y) + z = s • (A x + z) + t • (A y + z) := by
    have ht' : t = 1 - s := by linarith
    rw [ht', map_add, map_smul, map_smul]
    module
  simpa only [affineBoundedEnergy, he, smul_eq_mul] using h

theorem affineBoundedGradient_norm (A : Euclid n →L[ℝ] Euclid m) (z : Euclid m)
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    ‖affineBoundedGradient A z δ b x‖ ≤ ‖A‖ * b * Real.sqrt m := by
  have h := (A†).le_opNorm (boundedSlope δ b (A x + z))
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (boundedSlope_norm hδ hb (A x + z)) (norm_nonneg A))

theorem affineBoundedGradient_perturbation (A : Euclid n →L[ℝ] Euclid m) (z : Euclid m)
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    ‖affineBoundedGradient A z δ b x - affineBoundedGradient A z 0 b x‖ ≤
      ‖A‖ * δ * Real.sqrt m := by
  unfold affineBoundedGradient
  rw [← map_sub]
  have h := (A†).le_opNorm (boundedSlope δ b (A x + z) - boundedSlope 0 b (A x + z))
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (boundedSlope_perturbation hδ hb (A x + z)) (norm_nonneg A))

end FreshGradientMinimax
