import Matvec.TwoSidedGaussianQueries

/-! Pointwise affine factorization for direct two-sided adaptive revelation.
The visible state stores `B, U, V`; the actual ambient matrix is `B + U D Vᵀ`.
A step exposes one residual row and column and updates all three visible
matrices, including the cumulative residual frames. -/

namespace Matvec
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

abbrev TwoSidedState (m n r s : ℕ) := Matrix (Fin m) (Fin n) ℝ ×
  (Matrix (Fin m) (Fin r) ℝ × Matrix (Fin n) (Fin s) ℝ)

def representedTwoSided {m n r s : ℕ} (st : TwoSidedState m n r s)
    (D : Matrix (Fin r) (Fin s) ℝ) := st.1 + st.2.1 * D * st.2.2ᵀ

def exposedTwoSidedMatrix {r s : ℕ}
    (e : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ :=
  Fin.cons e.1 (fun i => Fin.cons (e.2 i) 0)

def padTwoSidedMatrix {r s : ℕ} (D : Matrix (Fin r) (Fin s) ℝ) :
    Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ := Fin.cons 0 (fun i => Fin.cons 0 (D i))

theorem splitTwoSided_reconstruct {r s : ℕ}
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    exposedTwoSidedMatrix (splitTwoSided X).1 + padTwoSidedMatrix (splitTwoSided X).2 = X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [exposedTwoSidedMatrix, padTwoSidedMatrix, splitTwoSided]
  · refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [exposedTwoSidedMatrix, padTwoSidedMatrix, splitTwoSided]

theorem padded_tail_product {m n r s : ℕ}
    (U : Matrix (Fin m) (Fin (r + 1)) ℝ) (V : Matrix (Fin n) (Fin (s + 1)) ℝ)
    (D : Matrix (Fin r) (Fin s) ℝ) :
    U * padTwoSidedMatrix D * Vᵀ =
      U.submatrix id Fin.succ * D * (V.submatrix id Fin.succ)ᵀ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, padTwoSidedMatrix, Fin.sum_univ_succ]

def updateTwoSidedState {m n r s : ℕ} (st : TwoSidedState m n (r + 1) (s + 1))
    (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (e : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : TwoSidedState m n r s :=
  let U := st.2.1 * Lᵀ
  let V := st.2.2 * Rᵀ
  (st.1 + U * exposedTwoSidedMatrix e * Vᵀ,
    (U.submatrix id Fin.succ, V.submatrix id Fin.succ))

theorem updateTwoSidedState_represents {m n r s : ℕ}
    (st : TwoSidedState m n (r + 1) (s + 1))
    (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : Lᵀ * L = 1) (hR : Rᵀ * R = 1)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    representedTwoSided (updateTwoSidedState st L R (splitTwoSided (twoSidedRotate L R D)).1)
      (splitTwoSided (twoSidedRotate L R D)).2 = representedTwoSided st D := by
  let Z := twoSidedRotate L R D
  have hz := splitTwoSided_reconstruct Z
  change st.1 + (st.2.1 * Lᵀ) * exposedTwoSidedMatrix (splitTwoSided Z).1 *
    (st.2.2 * Rᵀ)ᵀ +
    (st.2.1 * Lᵀ).submatrix id Fin.succ * (splitTwoSided Z).2 *
    ((st.2.2 * Rᵀ).submatrix id Fin.succ)ᵀ = _
  rw [← padded_tail_product]
  rw [add_assoc, ← Matrix.add_mul, ← Matrix.mul_add, hz]
  simp only [Z, twoSidedRotate, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Lᵀ L, hL, Matrix.one_mul,
    ← Matrix.mul_assoc Rᵀ R, hR, Matrix.one_mul]
  simp only [representedTwoSided, Matrix.mul_assoc]

def TwoSidedState.Orthogonal {m n r s : ℕ} (st : TwoSidedState m n r s) : Prop :=
  st.2.1ᵀ * st.2.1 = 1 ∧ st.2.2ᵀ * st.2.2 = 1

theorem tail_frame_orthogonal {m r : ℕ} (U : Matrix (Fin m) (Fin (r + 1)) ℝ)
    (hU : Uᵀ * U = 1) :
    (U.submatrix id Fin.succ)ᵀ * U.submatrix id Fin.succ = 1 := by
  ext i j
  have h := congrFun (congrFun hU i.succ) j.succ
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    id_eq, Matrix.one_apply, Fin.succ_inj] using h

theorem updateTwoSidedState_orthogonal {m n r s : ℕ}
    (st : TwoSidedState m n (r + 1) (s + 1)) (hst : st.Orthogonal)
    (L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (R : Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ)
    (hL : L * Lᵀ = 1) (hR : R * Rᵀ = 1)
    (e : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) :
    (updateTwoSidedState st L R e).Orthogonal := by
  constructor
  · apply tail_frame_orthogonal
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc st.2.1ᵀ st.2.1, hst.1, Matrix.one_mul, hL]
  · apply tail_frame_orthogonal
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc st.2.2ᵀ st.2.2, hst.2, Matrix.one_mul, hR]

theorem measurable_updateTwoSidedState {m n r s : ℕ} :
    Measurable (fun p : TwoSidedState m n (r + 1) (s + 1) ×
      ((Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ × Matrix (Fin (s + 1)) (Fin (s + 1)) ℝ) ×
      ((Fin (s + 1) → ℝ) × (Fin r → ℝ))) =>
      updateTwoSidedState p.1 p.2.1.1 p.2.1.2 p.2.2) := by
  have he : Measurable (exposedTwoSidedMatrix (r := r) (s := s)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (measurable_pi_apply j).comp measurable_fst
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact (measurable_pi_apply i).comp measurable_snd
      · exact measurable_const
  unfold updateTwoSidedState
  apply Measurable.prodMk
  · apply measurable_pi_lambda; intro i
    apply measurable_pi_lambda; intro j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  · apply Measurable.prodMk <;>
      apply measurable_pi_lambda <;> intro i <;>
      apply measurable_pi_lambda <;> intro j <;>
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply] <;> fun_prop

def initialTwoSidedState (m n : ℕ) : TwoSidedState m n m n := (0, (1, 1))

theorem initialTwoSidedState_represents {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) :
    representedTwoSided (initialTwoSidedState m n) D = D := by
  simp [representedTwoSided, initialTwoSidedState]

theorem initialTwoSidedState_orthogonal (m n : ℕ) : (initialTwoSidedState m n).Orthogonal := by
  simp [TwoSidedState.Orthogonal, initialTwoSidedState]

/-- Replay the ambient answer from visible data and newly exposed coordinates. -/
def ambientTwoSidedReply {m n r s : ℕ}
    (st : TwoSidedState m n (r + 1) (s + 1)) (u : Fin m → ℝ) (w : Fin n → ℝ)
    (e : (Fin (s + 1) → ℝ) × (Fin r → ℝ)) : (Fin m → ℝ) × (Fin n → ℝ) :=
  let reply := scaledExposedTwoSidedReply
    (EuclideanSpace.basisFun (Fin (r + 1)) ℝ) (EuclideanSpace.basisFun (Fin (s + 1)) ℝ)
    (st.2.1ᵀ *ᵥ u) (st.2.2ᵀ *ᵥ w) e
  (st.1 *ᵥ w + st.2.1 *ᵥ reply.1, st.1ᵀ *ᵥ u + st.2.2 *ᵥ reply.2)

theorem ambientTwoSidedReply_eq_oracle {m n r s : ℕ}
    (st : TwoSidedState m n (r + 1) (s + 1)) (u : Fin m → ℝ) (w : Fin n → ℝ)
    (D : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ) :
    let b := EuclideanSpace.basisFun (Fin (r + 1)) ℝ
    let c := EuclideanSpace.basisFun (Fin (s + 1)) ℝ
    let L := queryGauge b (st.2.1ᵀ *ᵥ u)
    let R := queryGauge c (st.2.2ᵀ *ᵥ w)
    ambientTwoSidedReply st u w (splitTwoSided (twoSidedRotate L R D)).1 =
      (representedTwoSided st D *ᵥ w, (representedTwoSided st D)ᵀ *ᵥ u) := by
  dsimp only
  unfold ambientTwoSidedReply
  rw [scaledExposedTwoSidedReply_eq_oracle]
  simp only [representedTwoSided, Matrix.add_mulVec, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem measurable_ambientTwoSidedReply {m n r s : ℕ} :
    Measurable (fun p : (TwoSidedState m n (r + 1) (s + 1) ×
      ((Fin m → ℝ) × (Fin n → ℝ))) × ((Fin (s + 1) → ℝ) × (Fin r → ℝ)) =>
      ambientTwoSidedReply p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let u := fun p : TwoSidedState m n (r + 1) (s + 1) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
    p.1.2.1ᵀ *ᵥ p.2.1
  let w := fun p : TwoSidedState m n (r + 1) (s + 1) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
    p.1.2.2ᵀ *ᵥ p.2.2
  have hu : Measurable u := by
    apply measurable_pi_lambda; intro i
    simp only [u, Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    fun_prop
  have hw : Measurable w := by
    apply measurable_pi_lambda; intro i
    simp only [w, Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    fun_prop
  have hr := measurable_scaledExposedTwoSidedReply
    (EuclideanSpace.basisFun (Fin (r + 1)) ℝ)
    (EuclideanSpace.basisFun (Fin (s + 1)) ℝ) u w hu hw
  unfold ambientTwoSidedReply
  apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro i <;>
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply] <;> fun_prop

end
end Matvec
