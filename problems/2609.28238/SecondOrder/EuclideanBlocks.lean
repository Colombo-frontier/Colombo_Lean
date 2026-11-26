import SecondOrder.CurvatureProgress

namespace SecondOrder
noncomputable section

def blockCoordinateEquiv (n d : ℕ) : (Σ _ : Fin n, Fin d) ≃ Fin (n*d) :=
  (Equiv.sigmaEquivProd (Fin n) (Fin d)).trans finProdFinEquiv

/-- The actual block norm is isometric to the ordinary Euclidean norm in the
total dimension. This includes empty blocks and zero total dimension. -/
def euclideanBlockEquiv (n d : ℕ) : Point (n*d) ≃ₗᵢ[ℝ] HomogeneousBlocks (Fin n) (Point d) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockCoordinateEquiv n d).symm).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun _ : Fin n => fun _ : Fin d => ℝ))

@[simp] theorem euclideanBlockEquiv_apply (n d : ℕ) (x : Point (n*d)) (i : Fin n) (j : Fin d) :
    euclideanBlockEquiv n d x i j = x (blockCoordinateEquiv n d ⟨i,j⟩) := rfl

abbrev CurvatureDimension (m T : ℕ) := (T+1)*(2*m)

def curvatureCoordinates (m T : ℕ) : Point (CurvatureDimension m T) ≃ₗᵢ[ℝ] CurvatureSpace m T :=
  euclideanBlockEquiv (T+1) (2*m)

theorem curvatureCoordinates_norm (m T : ℕ) (x : Point (CurvatureDimension m T)) :
    ‖curvatureCoordinates m T x‖=‖x‖ := (curvatureCoordinates m T).norm_map x

theorem curvatureCoordinates_contDiff (m T : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (curvatureCoordinates m T) := (curvatureCoordinates m T).toContinuousLinearEquiv.contDiff

theorem curvatureCoordinates_measurable (m T : ℕ) : Measurable (curvatureCoordinates m T) :=
  (curvatureCoordinates m T).continuous.measurable

end
end SecondOrder
