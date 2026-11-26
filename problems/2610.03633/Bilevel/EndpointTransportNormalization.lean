import Bilevel.EndpointTransportSpectral
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Explicit endpoint-transport normalization

For the source's layer count `floor(sqrt(kappa/128))`, the concrete threshold
3200 suffices for at least five layers and all normalization estimates in
`tr:eq:K-uniform` which involve only this count. Extra middle-chain floor
thresholds elsewhere in the construction are not asserted here.

The matrix library counts interior coordinates, hence its parameter is
`interiors = layers - 2`, and its `n+1` equals the source `m = layers-1`.
-/
noncomputable section
namespace Bilevel.EndpointTransportNormalization
open EndpointTransportMatrix

def layers (κ : ℝ) : ℕ := ⌊Real.sqrt (κ / 128)⌋₊
def middle (κ : ℝ) : ℕ := layers κ - 1
def interiors (κ : ℝ) : ℕ := layers κ - 2
def alpha (κ : ℝ) : ℝ := 2 * (middle κ : ℝ) ^ 2 / 3
def gain (κ : ℝ) : ℝ := 4 * alpha κ
def coupling (L κ : ℝ) : ℝ := (3 * (L / κ) / 2) * gain κ

theorem sqrt_scale_ge_five {κ : ℝ} (hκ : 3200 ≤ κ) : 5 ≤ Real.sqrt (κ / 128) := by
  apply Real.le_sqrt_of_sq_le
  linarith

theorem layers_ge_five {κ : ℝ} (hκ : 3200 ≤ κ) : 5 ≤ layers κ := by
  unfold layers
  exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by exact_mod_cast sqrt_scale_ge_five hκ)

theorem interiors_add_two {κ : ℝ} (hκ : 3200 ≤ κ) : interiors κ + 2 = layers κ := by
  have := layers_ge_five hκ
  unfold interiors
  omega

theorem interiors_add_one {κ : ℝ} (hκ : 3200 ≤ κ) : interiors κ + 1 = middle κ := by
  have := layers_ge_five hκ
  unfold interiors middle
  omega

theorem middle_ge_four {κ : ℝ} (hκ : 3200 ≤ κ) : 4 ≤ middle κ := by
  have := layers_ge_five hκ
  unfold middle
  omega

theorem middle_cast {κ : ℝ} (hκ : 3200 ≤ κ) : (middle κ : ℝ) = (layers κ : ℝ) - 1 := by
  unfold middle
  rw [Nat.cast_sub (by have := layers_ge_five hκ; omega), Nat.cast_one]

theorem interior_middle_cast {κ : ℝ} (hκ : 3200 ≤ κ) :
    (interiors κ : ℝ) + 1 = (middle κ : ℝ) := by
  exact_mod_cast interiors_add_one hκ

theorem middle_sqrt_bounds {κ : ℝ} (hκ : 3200 ≤ κ) :
    Real.sqrt (κ / 128) / 2 ≤ (middle κ : ℝ) ∧
      (middle κ : ℝ) ≤ Real.sqrt (κ / 128) := by
  have hfloor : (layers κ : ℝ) ≤ Real.sqrt (κ / 128) := Nat.floor_le (Real.sqrt_nonneg _)
  have hnext : Real.sqrt (κ / 128) < (layers κ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlarge := sqrt_scale_ge_five hκ
  rw [middle_cast hκ]
  constructor <;> linarith

theorem middle_square_bounds {κ : ℝ} (hκ : 3200 ≤ κ) :
    κ / 512 ≤ (middle κ : ℝ) ^ 2 ∧ (middle κ : ℝ) ^ 2 ≤ κ / 128 := by
  have hs := Real.sq_sqrt (show 0 ≤ κ / 128 by linarith)
  have hb := middle_sqrt_bounds hκ
  have hs0 := Real.sqrt_nonneg (κ / 128)
  have hm0 : 0 ≤ (middle κ : ℝ) := Nat.cast_nonneg _
  constructor <;> nlinarith

/-- Explicit two-sided comparison with kappa; c_K can be 1/192. -/
theorem gain_bounds {κ : ℝ} (hκ : 3200 ≤ κ) : κ / 192 ≤ gain κ ∧ gain κ ≤ κ / 48 := by
  have hb := middle_square_bounds hκ
  unfold gain alpha
  constructor <;> nlinarith

theorem gain_pos {κ : ℝ} (hκ : 3200 ≤ κ) : 0 < gain κ := by
  have := (gain_bounds hκ).1
  linarith

/-- Quantitative layer-count comparison, expressed in the source's scaled
square root (equivalently constants times sqrt(kappa)). -/
theorem layers_sqrt_bounds {κ : ℝ} (hκ : 3200 ≤ κ) :
    Real.sqrt (κ / 128) / 2 ≤ (layers κ : ℝ) ∧
      (layers κ : ℝ) ≤ Real.sqrt (κ / 128) := by
  have hb := (middle_sqrt_bounds hκ).1
  rw [middle_cast hκ] at hb
  exact ⟨by linarith, Nat.floor_le (Real.sqrt_nonneg _)⟩

theorem layers_sqrt_kappa_bounds {κ : ℝ} (hκ : 3200 ≤ κ) :
    Real.sqrt κ / (2 * Real.sqrt 128) ≤ (layers κ : ℝ) ∧
      (layers κ : ℝ) ≤ Real.sqrt κ / Real.sqrt 128 := by
  have hb := layers_sqrt_bounds hκ
  rw [Real.sqrt_div (by linarith : 0 ≤ κ)] at hb
  convert hb using 1
  ring

theorem coupling_le {L κ : ℝ} (hL : 0 ≤ L) (hκ : 3200 ≤ κ) : coupling L κ ≤ L / 32 := by
  have hk : 0 < κ := by linarith
  have hb := mul_le_mul_of_nonneg_left (gain_bounds hκ).2
    (show 0 ≤ 3 * (L / κ) / 2 by positivity)
  unfold coupling
  apply hb.trans_eq
  field_simp
  ring

theorem coupling_nonneg {L κ : ℝ} (hL : 0 ≤ L) (hκ : 3200 ≤ κ) : 0 ≤ coupling L κ := by
  have hk : 0 < κ := by linarith
  have hg := (gain_pos hκ).le
  unfold coupling
  positivity

/-- This is the actual inverse entry, with the floor-calibrated index. -/
theorem alpha_eq_inverse_entry {κ : ℝ} (hκ : 3200 ≤ κ) :
    alpha κ = (matrix (interiors κ))⁻¹
      (Fin.last (interiors κ + 1)) (Fin.last (interiors κ + 1)) := by
  rw [inverse_last_last, interior_middle_cast hκ]
  rfl

theorem gain_eq_endpoint_ratio {L κ : ℝ} (hL : 0 < L) (hκ : 3200 ≤ κ) :
    gain κ = ((L / 4) / (L / 16)) *
      (matrix (interiors κ))⁻¹ (Fin.last (interiors κ + 1)) (Fin.last (interiors κ + 1)) := by
  rw [← alpha_eq_inverse_entry hκ]
  unfold gain
  field_simp
  ring

/-- The source's lower Hessian slack coefficient, with mu = L/kappa. -/
theorem lower_coefficient_slack {L κ : ℝ} (hL : 0 ≤ L) (hκ : 3200 ≤ κ) :
    4 * (L / κ) ≤ (L / 16) * (1 / (2 * (middle κ : ℝ) ^ 2)) := by
  have hk : 0 < κ := by linarith
  have hm : 0 < (middle κ : ℝ) := by exact_mod_cast (show 0 < middle κ by have := middle_ge_four hκ; omega)
  have hdenom : 32 * (middle κ : ℝ) ^ 2 ≤ κ / 4 := by
    have := (middle_square_bounds hκ).2
    linarith
  have hb := div_le_div_of_nonneg_left hL (show 0 < 32 * (middle κ : ℝ) ^ 2 by positivity) hdenom
  calc
    4 * (L / κ) = L / (κ / 4) := by field_simp; ring
    _ ≤ L / (32 * (middle κ : ℝ) ^ 2) := hb
    _ = (L / 16) * (1 / (2 * (middle κ : ℝ) ^ 2)) := by ring

def normalizedMatrix (L κ : ℝ) : Matrix (Index (interiors κ)) (Index (interiors κ)) ℝ :=
  (L / 16) • matrix (interiors κ)

theorem normalized_quadratic (L κ : ℝ) (x : Index (interiors κ) → ℝ) :
    quadratic (interiors κ) (normalizedMatrix L κ) x =
      (L / 16) * quadratic (interiors κ) (matrix (interiors κ)) x := by
  unfold quadratic normalizedMatrix
  simp only [Matrix.smul_mulVec_assoc, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Actual scalar transport Hessian sandwich, after the manuscript's
floor-based normalization, not merely an abstract coefficient implication. -/
theorem normalized_quadratic_bounds {L κ : ℝ} (hL : 0 ≤ L) (hκ : 3200 ≤ κ)
    (x : Index (interiors κ) → ℝ) :
    4 * (L / κ) * (∑ i, x i ^ 2) ≤ quadratic (interiors κ) (normalizedMatrix L κ) x ∧
      quadratic (interiors κ) (normalizedMatrix L κ) x ≤ (L / 4) * ∑ i, x i ^ 2 := by
  have hb := quadratic_spectral_sandwich (interiors κ) x
  have hlo := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ L / 16 by positivity)
  have hhi := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ L / 16 by positivity)
  rw [interior_middle_cast hκ] at hlo
  have hcoef := mul_le_mul_of_nonneg_right (lower_coefficient_slack hL hκ)
    (show 0 ≤ ∑ i, x i ^ 2 by positivity)
  rw [normalized_quadratic]
  constructor <;> nlinarith

/-- The same normalized bounds in genuine Loewner/PSD form, including
Hermitian symmetry of the actual scaled matrix. -/
theorem normalized_spectral_sandwich {L κ : ℝ} (hL : 0 ≤ L) (hκ : 3200 ≤ κ) :
    (normalizedMatrix L κ - (4 * (L / κ)) •
      (1 : Matrix (Index (interiors κ)) (Index (interiors κ)) ℝ)).PosSemidef ∧
    ((L / 4) • (1 : Matrix (Index (interiors κ)) (Index (interiors κ)) ℝ) -
      normalizedMatrix L κ).PosSemidef := by
  have ha : (matrix (interiors κ)).conjTranspose = matrix (interiors κ) := by
    ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using
      congrArg (fun A : Matrix (Index (interiors κ)) (Index (interiors κ)) ℝ => A i j)
        (matrix_symmetric (interiors κ))
  have hH : (normalizedMatrix L κ).conjTranspose = normalizedMatrix L κ := by
    simp only [normalizedMatrix, Matrix.conjTranspose_smul, ha, star_trivial]
  constructor
  · constructor
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH,
        Matrix.conjTranspose_one, star_trivial]
    · intro x
      have h := sub_nonneg.mpr (normalized_quadratic_bounds hL hκ x).1
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_trivial]
      simpa [quadratic, dotProduct, pow_two] using h
  · constructor
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH,
        Matrix.conjTranspose_one, star_trivial]
    · intro x
      have h := sub_nonneg.mpr (normalized_quadratic_bounds hL hκ x).2
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, star_trivial]
      simpa [quadratic, dotProduct, pow_two] using h

end Bilevel.EndpointTransportNormalization
