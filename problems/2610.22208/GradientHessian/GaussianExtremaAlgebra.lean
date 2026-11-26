import GradientHessian.GaussianFiniteMinMax

/-! Exact finite-extremum algebra for cancelling the independent scalar
and separating the two Gaussian vector terms in the matrix comparison. -/

noncomputable section
namespace GradientHessian.GaussianConcentration

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

theorem finiteMaximum_add_const (x : I → ℝ) (c : ℝ) :
    finiteMaximum (fun i => x i + c) = finiteMaximum x + c := by
  apply le_antisymm
  · exact finiteMaximum_le (fun i => add_le_add_right (le_finiteMaximum x i) c)
  · obtain ⟨i,hi⟩ := finiteMaximum_attained x
    rw [hi]
    exact le_finiteMaximum (fun j => x j + c) i

theorem finiteMinimum_add_const (x : I → ℝ) (c : ℝ) :
    finiteMinimum (fun i => x i + c) = finiteMinimum x + c := by
  apply le_antisymm
  · obtain ⟨i,hi⟩ := finiteMinimum_attained x
    rw [hi]
    exact finiteMinimum_le _ i
  · exact le_finiteMinimum (fun i => add_le_add_right (finiteMinimum_le x i) c)

theorem finiteMaximum_pair_add (x : I → ℝ) (y : J → ℝ) :
    finiteMaximum (fun p : I × J => x p.1 + y p.2) = finiteMaximum x + finiteMaximum y := by
  apply le_antisymm
  · exact finiteMaximum_le (fun p => add_le_add (le_finiteMaximum x p.1) (le_finiteMaximum y p.2))
  · obtain ⟨i,hi⟩ := finiteMaximum_attained x
    obtain ⟨j,hj⟩ := finiteMaximum_attained y
    rw [hi,hj]
    exact le_finiteMaximum (fun p : I × J => x p.1 + y p.2) (i,j)

theorem finiteMinMax_pair_add (x : I → ℝ) (y : J → ℝ) :
    finiteMinMax (fun p : I × J => x p.1 + y p.2) = finiteMinimum x + finiteMaximum y := by
  have he (i : I) : finiteRows (fun p : I × J => x p.1 + y p.2) i = x i + finiteMaximum y := by
    change finiteMaximum (fun j : J => x i + y j) = x i + finiteMaximum y
    simp only [add_comm (x i),finiteMaximum_add_const]
  unfold finiteMinMax
  simp_rw [funext he]
  exact finiteMinimum_add_const x _

theorem finiteMinMax_add_const (x : I × J → ℝ) (c : ℝ) :
    finiteMinMax (fun p => x p + c) = finiteMinMax x + c := by
  have he : finiteRows (fun p => x p + c) = fun i => finiteRows x i + c := by
    funext i
    exact finiteMaximum_add_const (fun j => x (i,j)) c
  unfold finiteMinMax
  rw [he,finiteMinimum_add_const]

end GradientHessian.GaussianConcentration
