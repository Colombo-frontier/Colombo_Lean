import FreshGradientMinimax.FramedPath

/-! Finite coordinate labels give an actual orthonormal frame whenever distinct.
A deterministic fallback makes every label list an admissible hard instance;
the auxiliary interaction will use the raw labels, never this global test. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def coordinateRead {m D : ℕ} (z : Fin m → Fin D) : Euclid D →L[ℝ] Euclid m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => (WithLp.equiv 2 _).symm (fun i => y (z i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp]
theorem coordinateRead_apply {m D : ℕ} (z : Fin m → Fin D) (y : Euclid D) (i : Fin m) :
    coordinateRead z y i = y (z i) := rfl

theorem coordinateRead_adjoint {m D : ℕ} (z : Fin m → Fin D) (x : Euclid m) :
    ((coordinateRead z)†) x = ∑ i, x i • EuclideanSpace.single (z i) 1 := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner]
  simp only [real_inner_smul_left, EuclideanSpace.inner_single_left, one_mul]
  simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial, coordinateRead_apply, one_mul]

theorem coordinateRead_adjoint_inverse {m D : ℕ} (z : Fin m → Fin D)
    (hz : Function.Injective z) (x : Euclid m) :
    coordinateRead z (((coordinateRead z)†) x) = x := by
  ext j
  rw [coordinateRead_apply, coordinateRead_adjoint]
  change (EuclideanSpace.proj (𝕜 := ℝ) (z j)) (∑ i, x i • EuclideanSpace.single (z i) 1) = x j
  rw [map_sum]
  simp [EuclideanSpace.proj, EuclideanSpace.single_apply, hz.eq_iff]

theorem coordinateRead_adjoint_norm {m D : ℕ} (z : Fin m → Fin D)
    (hz : Function.Injective z) (x : Euclid m) : ‖((coordinateRead z)†) x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left,
    coordinateRead_adjoint_inverse z hz, real_inner_self_eq_norm_sq]

def coordinateFrame {m D : ℕ} (z : Fin m → Fin D) (hz : Function.Injective z) :
    Euclid m →ₗᵢ[ℝ] Euclid D where
  toLinearMap := ((coordinateRead z)†).toLinearMap
  norm_map' := coordinateRead_adjoint_norm z hz

theorem coordinateFrame_single {m D : ℕ} (z : Fin m → Fin D) (hz : Function.Injective z)
    (i : Fin m) : coordinateFrame z hz (EuclideanSpace.single i 1) = EuclideanSpace.single (z i) 1 := by
  change ((coordinateRead z)†) (EuclideanSpace.single i 1) = _
  rw [coordinateRead_adjoint]
  simp [EuclideanSpace.single_apply]

theorem coordinateFrame_coordinates {m D : ℕ} (z : Fin m → Fin D) (hz : Function.Injective z) :
    frameCoordinates (coordinateFrame z hz) = coordinateRead z := by
  change ((coordinateRead z)†)† = coordinateRead z
  exact ContinuousLinearMap.adjoint_adjoint _

def standardCoordinateLabels {m D : ℕ} (h : m ≤ D) (i : Fin m) : Fin D :=
  ⟨i.val, lt_of_lt_of_le i.isLt h⟩

theorem standardCoordinateLabels_injective {m D : ℕ} (h : m ≤ D) :
    Function.Injective (standardCoordinateLabels h) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun j : Fin D => j.val) he

def labelFrame {m D : ℕ} (h : m ≤ D) (z : Fin m → Fin D) : Euclid m →ₗᵢ[ℝ] Euclid D :=
  if hz : Function.Injective z then coordinateFrame z hz
  else coordinateFrame (standardCoordinateLabels h) (standardCoordinateLabels_injective h)

theorem labelFrame_of_injective {m D : ℕ} (h : m ≤ D) (z : Fin m → Fin D)
    (hz : Function.Injective z) : labelFrame h z = coordinateFrame z hz := by
  simp only [labelFrame, dif_pos hz]

end FreshGradientMinimax
