import Bilevel.EndpointTransportSpectral

/-! Exact minimization of the endpoint-coupled quadratic, prior to orthogonal
block transport. All assertions use the actual certified finite matrix. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportMatrix

theorem quadratic_cross_symm (n : ℕ) (x y : Index n → ℝ) :
    dotProduct x ((matrix n).mulVec y) = dotProduct y ((matrix n).mulVec x) := by
  rw [Matrix.dotProduct_mulVec]
  have hs : Matrix.vecMul x (matrix n) = (matrix n).mulVec x := by
    have ht := Matrix.vecMul_transpose (matrix n) x
    rw [matrix_symmetric n] at ht
    exact ht
  rw [hs, dotProduct_comm]

theorem quadratic_sub (n : ℕ) (x y : Index n → ℝ) :
    quadratic n (matrix n) (x-y) = quadratic n (matrix n) x +
      quadratic n (matrix n) y - 2*dotProduct x ((matrix n).mulVec y) := by
  unfold quadratic
  change dotProduct (x-y) ((matrix n).mulVec (x-y)) = _
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    quadratic_cross_symm n y x]
  change dotProduct x ((matrix n).mulVec x) - dotProduct x ((matrix n).mulVec y) -
    (dotProduct x ((matrix n).mulVec y) - dotProduct y ((matrix n).mulVec y)) = _
  unfold dotProduct
  ring

def scalarResponse (n : ℕ) (δ c v : ℝ) : Index n → ℝ :=
  (c / δ * v) • endpointColumn n

def scalarLower (n : ℕ) (δ c v : ℝ) (y : Index n → ℝ) : ℝ :=
  δ/2 * quadratic n (matrix n) y - c*v*y (Fin.last (n+1))

theorem scalarResponse_equation (n : ℕ) (δ c v : ℝ) :
    (matrix n).mulVec (scalarResponse n δ c v) = (c/δ*v) • lastUnit n := by
  rw [scalarResponse, Matrix.mulVec_smul, matrix_endpointColumn]

theorem scalarResponse_cross (n : ℕ) (δ c v : ℝ) (y : Index n → ℝ) :
    dotProduct y ((matrix n).mulVec (scalarResponse n δ c v)) =
      (c/δ*v) * y (Fin.last (n+1)) := by
  rw [scalarResponse_equation, dotProduct_smul, lastUnit_eq_single]
  simp

/-- Exact square completion around the actual response. -/
theorem scalarLower_difference (n : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (c v : ℝ)
    (y : Index n → ℝ) :
    scalarLower n δ c v y - scalarLower n δ c v (scalarResponse n δ c v) =
      δ/2 * quadratic n (matrix n) (y - scalarResponse n δ c v) := by
  rw [quadratic_sub, scalarResponse_cross]
  have hq : quadratic n (matrix n) (scalarResponse n δ c v) =
      (c/δ*v) * (scalarResponse n δ c v) (Fin.last (n+1)) :=
    scalarResponse_cross n δ c v (scalarResponse n δ c v)
  unfold scalarLower
  rw [hq]
  field_simp
  ring

theorem scalarLower_growth (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (c v : ℝ)
    (y : Index n → ℝ) :
    δ/(4*(n+1:ℝ)^2) * (∑ i : Index n, (y i - scalarResponse n δ c v i)^2) ≤
      scalarLower n δ c v y - scalarLower n δ c v (scalarResponse n δ c v) := by
  rw [scalarLower_difference n hδ.ne']
  have h := mul_le_mul_of_nonneg_left
    (quadratic_spectral_sandwich n (y-scalarResponse n δ c v)).1
    (div_nonneg hδ.le (by norm_num : (0:ℝ) ≤ 2))
  have he : δ/(4*(n+1:ℝ)^2) = δ/2 * (1/(2*(n+1:ℝ)^2)) := by
    rw [mul_one_div, div_div]
    congr 1
    ring
  rw [he, mul_assoc]
  exact h

theorem scalarLower_minimum (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (c v : ℝ)
    (y : Index n → ℝ) :
    scalarLower n δ c v (scalarResponse n δ c v) ≤ scalarLower n δ c v y := by
  have h := scalarLower_growth n hδ c v y
  have hp : 0 ≤ δ/(4*(n+1:ℝ)^2) *
      (∑ i : Index n, (y i - scalarResponse n δ c v i)^2) := by positivity
  linarith

/-- Equality with the minimum holds at exactly the displayed response. -/
theorem scalarLower_eq_min_iff (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (c v : ℝ)
    (y : Index n → ℝ) :
    scalarLower n δ c v y = scalarLower n δ c v (scalarResponse n δ c v) ↔
      y = scalarResponse n δ c v := by
  constructor
  · intro he
    have h := scalarLower_growth n hδ c v y
    rw [he, sub_self] at h
    have hc : 0 < δ/(4*(n+1:ℝ)^2) := by positivity
    have hsum : (∑ i : Index n, (y i - scalarResponse n δ c v i)^2) = 0 := by
      have hn : 0 ≤ ∑ i : Index n, (y i - scalarResponse n δ c v i)^2 := by positivity
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Index n))) => sq_nonneg
        (y i-scalarResponse n δ c v i))).mp hsum
    funext i
    have hi := hz i (Finset.mem_univ i)
    nlinarith [sq_nonneg (y i-scalarResponse n δ c v i)]
  · intro he
    rw [he]

end Bilevel.EndpointTransportMatrix
