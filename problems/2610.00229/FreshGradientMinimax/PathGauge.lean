import FreshGradientMinimax.PathCoordinates

/-! Vertex signs induce the actual signed path. Their diagonal gauge is an
involution, and conjugates the positive-path normal operator and its inverse. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem coordinateMultiplier_adjoint {n : ℕ} (d : Fin n → ℝ) :
    (coordinateMultiplier d)† = coordinateMultiplier d := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  have h := (coordinateMultiplier d).adjoint_inner_left (EuclideanSpace.single i 1) x
  simpa [coordinateMultiplier_single, EuclideanSpace.inner_single_right,
    real_inner_smul_right] using h

theorem coordinateMultiplier_involution {n : ℕ} {d : Fin n → ℝ}
    (hd : ∀ i, d i ^ 2 = 1) (x : Euclid n) : coordinateMultiplier d (coordinateMultiplier d x) = x := by
  ext i
  change d i * (d i * x i) = x i
  rw [← mul_assoc, ← pow_two, hd, one_mul]

theorem coordinateMultiplier_inner {n : ℕ} {d : Fin n → ℝ}
    (hd : ∀ i, d i ^ 2 = 1) (x y : Euclid n) :
    ⟪coordinateMultiplier d x, coordinateMultiplier d y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, coordinateMultiplier_adjoint,
    coordinateMultiplier_involution hd]

def pathSignsFromVertices {n : ℕ} (d : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  Fin.snoc (α := fun _ => ℝ) d 1 i * Fin.cons (α := fun _ => ℝ) 1 d i

theorem signPadLeft_sq {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1) (i : Fin (n + 1)) :
    (Fin.snoc (α := fun _ => ℝ) d 1 i) ^ 2 = 1 := by
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [hd]

theorem signPadRight_sq {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1) (i : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ℝ) 1 d i) ^ 2 = 1 := by
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [hd]

theorem pathSignsFromVertices_sq {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1) (i : Fin (n + 1)) :
    pathSignsFromVertices d i ^ 2 = 1 := by
  simp only [pathSignsFromVertices, mul_pow, signPadLeft_sq hd, signPadRight_sq hd, one_mul]

theorem pathSignsFromVertices_abs {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1) (i : Fin (n + 1)) :
    |pathSignsFromVertices d i| ≤ 1 := by
  have h := pathSignsFromVertices_sq hd i
  nlinarith [sq_abs (pathSignsFromVertices d i), abs_nonneg (pathSignsFromVertices d i)]

theorem pathPadLeft_diagonal {n : ℕ} (d : Fin n → ℝ) (x : Euclid n) :
    pathPadLeft n (coordinateMultiplier d x) =
      coordinateMultiplier (Fin.snoc (α := fun _ => ℝ) d 1) (pathPadLeft n x) := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp

theorem pathPadRight_diagonal {n : ℕ} (d : Fin n → ℝ) (x : Euclid n) :
    pathPadRight n (coordinateMultiplier d x) =
      coordinateMultiplier (Fin.cons (α := fun _ => ℝ) 1 d) (pathPadRight n x) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;> simp

theorem pathIncidence_gauge {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1) (x : Euclid n) :
    pathIncidence (pathSignsFromVertices d) (coordinateMultiplier d x) =
      coordinateMultiplier (Fin.snoc (α := fun _ => ℝ) d 1) (pathIncidence (fun _ => 1) x) := by
  change pathPadLeft n (coordinateMultiplier d x) -
    coordinateMultiplier (pathSignsFromVertices d) (pathPadRight n (coordinateMultiplier d x)) = _
  rw [pathPadLeft_diagonal, pathPadRight_diagonal]
  ext i
  simp only [PiLp.sub_apply, coordinateMultiplier_apply, pathIncidence_apply, pathSignsFromVertices]
  have h := congrArg (fun t : ℝ => Fin.snoc (α := fun _ => ℝ) d 1 i * t *
    Fin.cons (α := fun _ => ℝ) 0 (fun j => x j) i) (signPadRight_sq hd i)
  dsimp only at h
  simp only [pathPadLeft_apply, pathPadRight_apply]
  nlinarith only [h]

theorem pathIncidence_gauge_clm {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1) :
    pathIncidence (pathSignsFromVertices d) =
      (coordinateMultiplier (Fin.snoc (α := fun _ => ℝ) d 1)).comp
        ((pathIncidence (fun _ => 1)).comp (coordinateMultiplier d)) := by
  apply ContinuousLinearMap.ext
  intro x
  simpa only [coordinateMultiplier_involution hd, ContinuousLinearMap.comp_apply] using
    pathIncidence_gauge hd (coordinateMultiplier d x)

theorem normalPath_gauge {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1)
    (μ β : ℝ) (x : Euclid n) :
    normalOperator (pathIncidence (pathSignsFromVertices d)) μ β (coordinateMultiplier d x) =
      coordinateMultiplier d (normalOperator (pathIncidence (fun _ => 1)) μ β x) := by
  rw [normalOperator_apply, pathIncidence_gauge hd, pathIncidence_gauge_clm hd]
  simp only [ContinuousLinearMap.adjoint_comp, coordinateMultiplier_adjoint,
    ContinuousLinearMap.comp_apply, coordinateMultiplier_involution (signPadLeft_sq hd),
    normalOperator_apply, map_add, map_smul]

theorem normalPath_inverse_gauge {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, d i ^ 2 = 1)
    {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) (b : Euclid n) :
    normalInverse (pathIncidence (pathSignsFromVertices d)) μ β hμ hβ b =
      coordinateMultiplier d (normalInverse (pathIncidence (fun _ => 1)) μ β hμ hβ
        (coordinateMultiplier d b)) := by
  apply normalInverse_eq_of_root
  rw [normalPath_gauge hd, normalInverse_right, coordinateMultiplier_involution hd]

end FreshGradientMinimax
