import MatchingBounds1005.ChainSpectral

/-! An actual finite number of inactive copies with the requested Gaussian
angle confidence; the copy count has an explicit upper bound. -/
noncomputable section
open MeasureTheory
open MatchingBounds1005.GaussianMatrix MatchingBounds1005.GaussianBlockGeometry

namespace MatchingBounds1005.MultiplicityCalibration

def copies (k : ℕ) (η s : ℝ) : ℕ := Nat.ceil ((96 * ((k : ℝ) + 1) + 32 * s) / η ^ 2)

theorem copies_sufficient (k : ℕ) {η s : ℝ} (hη : 0 < η) :
    96 * ((k : ℝ) + 1) + 32 * s ≤ ((copies k η s + 1 : ℕ) : ℝ) * η ^ 2 := by
  have hceil := Nat.le_ceil ((96 * ((k : ℝ) + 1) + 32 * s) / η ^ 2)
  have hm := (div_le_iff₀ (sq_pos_of_pos hη)).mp hceil
  change _ ≤ (copies k η s : ℝ) * η ^ 2 at hm
  push_cast
  nlinarith only [hm, sq_nonneg η]

theorem copies_upper (k : ℕ) {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    ((copies k η s + 1 : ℕ) : ℝ) ≤
      (96 * ((k : ℝ) + 1) + 32 * s) / η ^ 2 + 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ (96 * ((k : ℝ) + 1) + 32 * s) / η ^ 2 by positivity)
  change (copies k η s : ℝ) < _ at h
  push_cast
  linarith

def confidence (D : ℕ) (ζ : ℝ) : ℝ := Real.log (4 * (D : ℝ) / ζ)

theorem confidence_nonneg {D : ℕ} (hD : 0 < D) {ζ : ℝ} (hζ : 0 < ζ) (hζone : ζ ≤ 1) :
    0 ≤ confidence D ζ := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  apply Real.log_nonneg
  apply (le_div_iff₀ hζ).mpr
  linarith

theorem confidence_exact {D : ℕ} (hD : 0 < D) {ζ : ℝ} (hζ : 0 < ζ) :
    4 * (D : ℝ) * Real.exp (-confidence D ζ) = ζ := by
  unfold confidence
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 4 * (D : ℝ) / ζ)]
  field_simp

end MatchingBounds1005.MultiplicityCalibration

namespace MatchingBounds1005.BlockGeometry
open MultiplicityCalibration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

theorem chain_copy_confidence (n k : ℕ) (hD : 0 < baseDimension (E := E) n)
    {η ζ : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) (hζ : 0 < ζ) (hζone : ζ ≤ 1) :
    let K := copies k η (confidence (baseDimension (E := E) n) ζ)
    (gaussianMatrixLaw (copyDimension (E := E) n K) k).real
      {g | ¬ CyclicAngleGood (copyAmbientActiveSpace n K) (G.copyAmbientOperator n K) g η} ≤ ζ := by
  dsimp only
  have h := G.chain_copy_high_multiplicity n _ k hη.le hηhalf
    (confidence_nonneg hD hζ hζone) (copies_sufficient k hη)
  rwa [confidence_exact hD hζ] at h

end MatchingBounds1005.BlockGeometry
