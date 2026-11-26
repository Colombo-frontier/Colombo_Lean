import FreshGradientMinimax.NormalInverse

/-! Exact coordinate formulas for the finite incidence operator and its
adjoint. The endpoint rows are part of the operator, including at dimension 1. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem pathPadLeft_single {n : ℕ} (i : Fin n) (t : ℝ) :
    pathPadLeft n (EuclideanSpace.single i t) = EuclideanSpace.single i.castSucc t := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [EuclideanSpace.single_apply, ne_of_gt (Fin.castSucc_lt_last i)]
  · simp [EuclideanSpace.single_apply]

theorem pathPadRight_single {n : ℕ} (i : Fin n) (t : ℝ) :
    pathPadRight n (EuclideanSpace.single i t) = EuclideanSpace.single i.succ t := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [EuclideanSpace.single_apply, (Fin.succ_ne_zero i).symm]
  · simp [EuclideanSpace.single_apply]

theorem coordinateMultiplier_single {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    coordinateMultiplier s (EuclideanSpace.single i t) = s i • EuclideanSpace.single i t := by
  ext j
  by_cases hij : i = j
  · subst j; simp
  · simp [EuclideanSpace.single_apply, hij, Ne.symm hij]

theorem pathIncidence_single {n : ℕ} (s : Fin (n + 1) → ℝ) (i : Fin n) (t : ℝ) :
    pathIncidence s (EuclideanSpace.single i t) =
      EuclideanSpace.single i.castSucc t - s i.succ • EuclideanSpace.single i.succ t := by
  change pathPadLeft n (EuclideanSpace.single i t) -
    coordinateMultiplier s (pathPadRight n (EuclideanSpace.single i t)) = _
  rw [pathPadLeft_single, pathPadRight_single, coordinateMultiplier_single]

theorem pathIncidence_adjoint_apply {n : ℕ} (s : Fin (n + 1) → ℝ) (w : Euclid (n + 1)) (i : Fin n) :
    ((pathIncidence s)†) w i = w i.castSucc - s i.succ * w i.succ := by
  have h := (pathIncidence s).adjoint_inner_left (EuclideanSpace.single i 1) w
  simpa [pathIncidence_single, EuclideanSpace.inner_single_right,
    inner_sub_right, real_inner_smul_right] using h

theorem normalPath_apply {n : ℕ} (s : Fin (n + 1) → ℝ) (μ β : ℝ) (x : Euclid n) (i : Fin n) :
    normalOperator (pathIncidence s) μ β x i = μ * x i + β *
      (pathIncidence s x i.castSucc - s i.succ * pathIncidence s x i.succ) := by
  simp only [normalOperator_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    pathIncidence_adjoint_apply]

theorem normalPath_coordinate {n : ℕ} (s : Fin (n + 1) → ℝ) (μ β : ℝ) (x : Euclid n) (i : Fin n) :
    normalOperator (pathIncidence s) μ β x i =
      (μ + β * (1 + s i.succ ^ 2)) * x i -
        β * s i.castSucc * Fin.cons (α := fun _ => ℝ) 0 (fun j => x j) i.castSucc -
        β * s i.succ * Fin.snoc (α := fun _ => ℝ) (fun j => x j) 0 i.succ := by
  rw [normalPath_apply]
  simp only [pathIncidence_apply, Fin.snoc_castSucc, Fin.cons_succ]
  ring

end FreshGradientMinimax
