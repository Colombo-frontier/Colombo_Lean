import FreshGradientMinimax.SignedPath
import FreshGradientMinimax.FramedPath

/-! Literal correspondence with the endpoint-plus-adjacent-edges formula in
Appendix B. Reversed edge orientation and the endpoint row sign leave the
actual flat energy unchanged; this is proved, not taken as a convention. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators

theorem real_unit_sign_cases {s : ℝ} (hs : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h : (s - 1) * (s + 1) = 0 := by nlinarith only [hs]
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

theorem flatEdge_unit_mul {δ s : ℝ} (hδ : 0 ≤ δ) (hs : s ^ 2 = 1) (t : ℝ) :
    flatEdge δ (s * t) = flatEdge δ t := by
  rcases real_unit_sign_cases hs with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul, flatEdge_even hδ]

theorem flatEdge_signed_swap {δ s : ℝ} (hδ : 0 ≤ δ) (hs : s ^ 2 = 1) (a b : ℝ) :
    flatEdge δ (b - s * a) = flatEdge δ (a - s * b) := by
  rcases real_unit_sign_cases hs with rfl | rfl
  · rw [one_mul, one_mul, show b - a = -(a - b) by ring, flatEdge_even hδ]
  · congr 1; ring

theorem flatPathEnergy_formula {n : ℕ} {e : Fin (n + 2) → ℝ} (he : ∀ i, e i ^ 2 = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid (n + 1)) :
    flatEnergy δ (pathIncidence e x) = flatEdge δ (x 0) +
      (∑ i : Fin n, flatEdge δ (x i.castSucc - e i.castSucc.succ * x i.succ)) + flatEdge δ (x (Fin.last n)) := by
  have hzero : pathIncidence e x 0 = x 0 := by
    rw [pathIncidence_apply, Fin.cons_zero, mul_zero, sub_zero]
    change Fin.snoc (α := fun _ => ℝ) (fun j => x j) 0 (0 : Fin (n + 1)).castSucc = x 0
    rw [Fin.snoc_castSucc]
  have hlast : pathIncidence e x (Fin.last (n + 1)) = -e (Fin.last (n + 1)) * x (Fin.last n) := by
    rw [pathIncidence_apply, Fin.snoc_last]
    rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl, Fin.cons_succ]
    ring
  have hi (i : Fin n) : pathIncidence e x i.castSucc.succ = x i.succ - e i.castSucc.succ * x i.castSucc := by
    rw [pathIncidence_apply, Fin.cons_succ, Fin.succ_castSucc, Fin.snoc_castSucc]
  have hf (i : Fin n) : flatEdge δ (pathIncidence e x i.castSucc.succ) =
      flatEdge δ (x i.castSucc - e i.castSucc.succ * x i.succ) := by
    rw [hi]
    exact flatEdge_signed_swap hδ (he _) _ _
  rw [flatEnergy, Fin.sum_univ_succ, Fin.sum_univ_castSucc, hzero]
  simp_rw [hf]
  rw [Fin.succ_last, hlast, flatEdge_unit_mul hδ (by simpa using he (Fin.last (n + 1)))]
  ring

theorem tailPath_internal_sign {n : ℕ} (k : ℕ) {s : ℝ} (hs : s ^ 2 = 1) (i : Fin n) :
    pathSignsFromVertices (tailVertexSigns (n := n + 1) k s) i.castSucc.succ =
      if i.val + 1 = k then s else 1 := by
  unfold pathSignsFromVertices
  rw [Fin.cons_succ, Fin.succ_castSucc, Fin.snoc_castSucc]
  simp only [tailVertexSigns, Fin.val_succ, Fin.coe_castSucc]
  by_cases hi : i.val < k
  · by_cases hj : i.val + 1 < k
    · have he : i.val + 1 ≠ k := by omega
      simp [hi, hj, he]
    · have he : i.val + 1 = k := by omega
      simp [hi, hj, he]
  · have hj : ¬ i.val + 1 < k := by omega
    have he : i.val + 1 ≠ k := by omega
    simp only [hi, hj, he, if_false]
    nlinarith only [hs]

theorem framedPathEnergy_original_formula {n dy : ℕ} (V : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dy)
    (k : ℕ) {s δ : ℝ} (hs : s ^ 2 = 1) (hδ : 0 ≤ δ) (β : ℝ) (y : Euclid dy) :
    framedPathEnergy V (pathSignsFromVertices (tailVertexSigns k s)) β δ y =
      β * (flatEdge δ (frameCoordinates V y 0) +
        (∑ i : Fin n, flatEdge δ (frameCoordinates V y i.castSucc -
          (if i.val + 1 = k then s else 1) * frameCoordinates V y i.succ)) +
        flatEdge δ (frameCoordinates V y (Fin.last n))) := by
  unfold framedPathEnergy linearFlatEnergy framedPathOperator
  rw [ContinuousLinearMap.comp_apply, flatPathEnergy_formula
    (pathSignsFromVertices_sq (tailVertexSigns_sq k hs)) hδ]
  simp_rw [tailPath_internal_sign k hs]

end FreshGradientMinimax
