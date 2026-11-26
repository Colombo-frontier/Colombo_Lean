import FreshGradientMinimax.PathGauge
import FreshGradientMinimax.PathGreen

/-! The central sign flip and its exact action on the true inverse entries.
The diagonal entry is sign independent; the end-to-end entry changes sign. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def tailVertexSigns {n : ℕ} (k : ℕ) (s : ℝ) (i : Fin n) : ℝ := if i.val < k then 1 else s

theorem tailVertexSigns_sq {n : ℕ} (k : ℕ) {s : ℝ} (hs : s ^ 2 = 1) (i : Fin n) :
    tailVertexSigns k s i ^ 2 = 1 := by
  unfold tailVertexSigns
  split_ifs
  · norm_num
  · exact hs

theorem tailVertexSigns_first {n : ℕ} {k : ℕ} (hk : 0 < k) (s : ℝ) :
    tailVertexSigns (n := n + 1) k s 0 = 1 := by simp [tailVertexSigns, hk]

theorem tailVertexSigns_last {n k : ℕ} (hk : k ≤ n) (s : ℝ) :
    tailVertexSigns k s (Fin.last n) = s := by simp [tailVertexSigns, not_lt.mpr hk]

theorem normalPath_inverse_entry {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1)
    {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (i j : Fin n) :
    normalInverse (pathIncidence (pathSignsFromVertices d)) μ β hμ hβ
      (EuclideanSpace.single j 1) i = d i * d j *
        normalInverse (pathIncidence (fun _ => 1)) μ β hμ hβ (EuclideanSpace.single j 1) i := by
  rw [normalPath_inverse_gauge hd hμ hβ, coordinateMultiplier_single, map_smul]
  simp only [coordinateMultiplier_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem normalPath_inverse_diagonal {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1)
    {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (i : Fin n) :
    normalInverse (pathIncidence (pathSignsFromVertices d)) μ β hμ hβ
      (EuclideanSpace.single i 1) i =
        normalInverse (pathIncidence (fun _ => 1)) μ β hμ hβ (EuclideanSpace.single i 1) i := by
  rw [normalPath_inverse_entry hd hμ hβ, ← pow_two, hd, one_mul]

theorem normalPath_diagonal_nonneg {n : ℕ} (s : Fin (n + 1) → ℝ)
    {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (i : Fin n) :
    0 ≤ normalInverse (pathIncidence s) μ β hμ hβ (EuclideanSpace.single i 1) i := by
  simpa [EuclideanSpace.inner_single_left] using
    normalInverse_positive (pathIncidence s) hμ hβ (EuclideanSpace.single i 1)

theorem signedPath_endpoint {n k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n)
    {s μ β : ℝ} (hs : s ^ 2 = 1) (hμ : 0 < μ) (hβ : 0 < β) :
    normalInverse (pathIncidence (pathSignsFromVertices (tailVertexSigns (n := n + 1) k s)))
      μ β hμ hβ.le (EuclideanSpace.single (Fin.last n) 1) 0 =
        s * (Real.sinh (pathTheta μ β) / (β * Real.sinh (((n : ℝ) + 2) * pathTheta μ β))) := by
  rw [normalPath_inverse_entry (tailVertexSigns_sq k hs) hμ hβ.le,
    tailVertexSigns_first hk0, tailVertexSigns_last hkn, one_mul, positivePath_endpoint_entry hμ hβ]

end FreshGradientMinimax
