import Bilevel.EndpointTransportBlockSpectral
import Bilevel.ChiQuadraticSpectral
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual transported block Hessian as a continuous linear operator.
Its symmetry and dimension-free norm follow from the concrete matrix. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix

def hessianLinear {n D : ℕ} (δ : ℝ) (Q : Rotations n D) : Physical n D →ₗ[ℝ] Physical n D where
  toFun Y := physical (hessianAction δ Q Y)
  map_add' Y Z := by
    ext i d
    simp [physical,hessianAction,map_add,smul_add,Finset.sum_add_distrib]
    ring
  map_smul' c Y := by
    ext i d
    simp [physical,hessianAction,map_smul,smul_smul,mul_comm]
    simp only [mul_smul,← Finset.smul_sum,PiLp.smul_apply,smul_eq_mul]
    ring

def physicalHessian {n D : ℕ} (δ : ℝ) (Q : Rotations n D) : Physical n D →L[ℝ] Physical n D :=
  LinearMap.toContinuousLinearMap (hessianLinear δ Q)

theorem physicalHessian_apply {n D : ℕ} (δ : ℝ) (Q : Rotations n D) (Y : Physical n D) :
    physicalHessian δ Q Y=physical (hessianAction δ Q Y) := rfl

theorem inner_hessian_coordinates {n D : ℕ} (δ : ℝ) (Q : Rotations n D)
    (Y Z : Physical n D) :
    ⟪Y,physicalHessian δ Q Z⟫=
      δ*∑ d : Fin D,dotProduct (coordinates Q Y d) ((matrix n).mulVec (coordinates Q Z d)) := by
  rw [PiLp.inner_apply]
  have hi (i : Index n) : ⟪Y i,hessianAction δ Q Z i⟫=
      ∑ d : Fin D,δ*(coordinates Q Y d i*(matrix n).mulVec (coordinates Q Z d) i) := by
    rw [← (Q i).symm.inner_map_map,PiLp.inner_apply]
    simp only [RCLike.inner_apply',conj_trivial]
    apply Finset.sum_congr rfl
    intro d _
    change coordinates Q Y d i*coordinates Q (hessianAction δ Q Z) d i= _
    rw [hessianAction_coordinates]
    ring
  change (∑ i : Index n,⟪Y i,hessianAction δ Q Z i⟫)= _
  simp_rw [hi]
  rw [Finset.sum_comm]
  simp only [dotProduct,Finset.mul_sum]

theorem physicalHessian_symmetric {n D : ℕ} (δ : ℝ) (Q : Rotations n D)
    (Y Z : Physical n D) : ⟪physicalHessian δ Q Y,Z⟫=⟪Y,physicalHessian δ Q Z⟫ := by
  rw [real_inner_comm,inner_hessian_coordinates,inner_hessian_coordinates]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  exact quadratic_cross_symm n _ _

theorem physicalHessian_quadratic {n D : ℕ} (δ : ℝ) (Q : Rotations n D) (Y : Physical n D) :
    ⟪Y,physicalHessian δ Q Y⟫=blockQuadratic δ Q Y := by
  rw [inner_hessian_coordinates,blockQuadratic_coordinates]
  rfl

theorem physicalHessian_spectral {n D : ℕ} {δ : ℝ} (hδ : 0≤δ)
    (Q : Rotations n D) (Y : Physical n D) :
    δ*(1/(2*(n+1:ℝ)^2))*‖Y‖^2≤⟪Y,physicalHessian δ Q Y⟫ ∧
      ⟪Y,physicalHessian δ Q Y⟫≤(4*δ)*‖Y‖^2 := by
  rw [physicalHessian_quadratic]
  exact block_spectral_sandwich hδ Q Y

theorem physicalHessian_norm {n D : ℕ} {δ : ℝ} (hδ : 0≤δ) (Q : Rotations n D) :
    ‖physicalHessian δ Q‖≤4*δ := by
  apply ChiQuadratic.symmetric_operator_norm _ (physicalHessian_symmetric δ Q) (by positivity)
  intro Y
  have hb := physicalHessian_spectral hδ Q Y
  have hn : 0≤⟪Y,physicalHessian δ Q Y⟫ := le_trans (by positivity) hb.1
  rw [abs_of_nonneg hn]
  exact hb.2

theorem normalized_physicalHessian {D : ℕ} {L κ : ℝ} (hL : 0≤L) (hκ : 3200≤κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D) :
    ‖physicalHessian (L/16) Q‖≤L/4 ∧
      ∀ Y,4*(L/κ)*‖Y‖^2≤⟪Y,physicalHessian (L/16) Q Y⟫ := by
  constructor
  · convert physicalHessian_norm (show 0≤L/16 by positivity) Q using 1
    ring
  · intro Y
    rw [physicalHessian_quadratic]
    exact (normalized_block_bounds hL hκ Q Y).1

end Bilevel.EndpointTransportResponse
