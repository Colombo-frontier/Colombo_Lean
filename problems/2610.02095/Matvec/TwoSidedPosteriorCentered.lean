import Matvec.TwoSidedAmbientPosterior

/-! The constructed fresh residual is the actual hidden block `Uᵀ G V`, not
an unrelated coupled Gaussian: the visible affine term has zero residual block. -/

namespace Matvec
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def TwoSidedState.Centered {m n r s : ℕ} (st : TwoSidedState m n r s) : Prop :=
  st.2.1ᵀ * st.1 * st.2.2 = 0

theorem representedTwoSided_coordinates {m n r s : ℕ} (st : TwoSidedState m n r s)
    (horth : st.Orthogonal) (D : Matrix (Fin r) (Fin s) ℝ) :
    st.2.1ᵀ * representedTwoSided st D * st.2.2 = st.2.1ᵀ * st.1 * st.2.2 + D := by
  unfold representedTwoSided
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc st.2.1ᵀ st.2.1, horth.1, Matrix.one_mul,
    horth.2, Matrix.mul_one]

theorem representedTwoSided_hidden_block {m n r s : ℕ} (st : TwoSidedState m n r s)
    (horth : st.Orthogonal) (hcenter : st.Centered) (D : Matrix (Fin r) (Fin s) ℝ) :
    st.2.1ᵀ * representedTwoSided st D * st.2.2 = D := by
  rw [representedTwoSided_coordinates st horth, hcenter, zero_add]

theorem tail_bilinear_block {m n r s : ℕ}
    (U : Matrix (Fin m) (Fin (r + 1)) ℝ) (V : Matrix (Fin n) (Fin (s + 1)) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) :
    (U.submatrix id Fin.succ)ᵀ * B * (V.submatrix id Fin.succ) =
      (Uᵀ * B * V).submatrix Fin.succ Fin.succ := by
  ext i j
  rfl

theorem updateTwoSidedState_centered {m n r s : ℕ}
    (st : TwoSidedState m n (r + 1) (s + 1)) (horth : st.Orthogonal) (hcenter : st.Centered)
    (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : L * Lᵀ = 1) (hR : R * Rᵀ = 1)
    (e : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) :
    (updateTwoSidedState st L R e).Centered := by
  let rot : TwoSidedState m n (r + 1) (s + 1) := (st.1, (st.2.1 * Lᵀ, st.2.2 * Rᵀ))
  have hrot : rot.Orthogonal := by
    constructor
    · change (st.2.1 * Lᵀ)ᵀ * (st.2.1 * Lᵀ) = 1
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc st.2.1ᵀ st.2.1, horth.1, Matrix.one_mul, hL]
    · change (st.2.2 * Rᵀ)ᵀ * (st.2.2 * Rᵀ) = 1
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc st.2.2ᵀ st.2.2, horth.2, Matrix.one_mul, hR]
  have hcrot : rot.Centered := by
    change (st.2.1 * Lᵀ)ᵀ * st.1 * (st.2.2 * Rᵀ) = 0
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc st.2.1ᵀ st.1,
      ← Matrix.mul_assoc (st.2.1ᵀ * st.1) st.2.2, hcenter, Matrix.zero_mul, Matrix.mul_zero]
  change (rot.2.1.submatrix id Fin.succ)ᵀ *
    representedTwoSided rot (exposedTwoSidedMatrix e) * (rot.2.2.submatrix id Fin.succ) = 0
  rw [tail_bilinear_block, representedTwoSided_hidden_block rot hrot hcrot]
  ext i j
  simp [exposedTwoSidedMatrix]

theorem initialTwoSidedState_centered (m n : ℕ) : (initialTwoSidedState m n).Centered := by
  simp [TwoSidedState.Centered, initialTwoSidedState]

theorem readTwoSidedState_centered (m n r s t : ℕ) {S T : Type u}
    [MeasurableSpace S] [MeasurableSpace T] (policy : TwoSidedOraclePolicy m n t T)
    (st : OracleMap S (TwoSidedState m n (r + t) (s + t))) (mem : OracleMap S T)
    (horth : ∀ z, (st.1 z).Orthogonal) (hcenter : ∀ z, (st.1 z).Centered) :
    ∀ h, (readTwoSidedState m n r s t policy st mem h).Centered := by
  induction t generalizing S T with
  | zero => exact hcenter
  | succ t ih =>
    apply ih policy.2
    · intro p
      exact updateTwoSidedState_orthogonal (st.1 p.1) (horth p.1) _ _
        (queryGauge_orthogonal _ _) (queryGauge_orthogonal _ _) p.2
    · intro p
      exact updateTwoSidedState_centered (st.1 p.1) (horth p.1) (hcenter p.1) _ _
        (queryGauge_orthogonal _ _) (queryGauge_orthogonal _ _) p.2

theorem ambientTwoSided_factors_centered (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    (ambientTwoSidedFactors r s t policy p).Centered :=
  readTwoSidedState_centered (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)
    (fun _ => initialTwoSidedState_orthogonal _ _) (fun _ => initialTwoSidedState_centered _ _) _

/-- The actual hidden block of the original matrix is exactly the fresh iid
residual produced by the proved adaptive process. -/
theorem ambientTwoSided_actual_hidden_block (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    (ambientTwoSidedFactors r s t policy p).2.1ᵀ * p.2 *
      (ambientTwoSidedFactors r s t policy p).2.2 = ambientTwoSidedResidual r s t policy p := by
  have h := representedTwoSided_hidden_block (ambientTwoSidedFactors r s t policy p)
    (ambientTwoSided_factors_orthogonal r s t policy p)
    (ambientTwoSided_factors_centered r s t policy p) (ambientTwoSidedResidual r s t policy p)
  rwa [ambientTwoSided_factorization] at h

end
end Matvec
