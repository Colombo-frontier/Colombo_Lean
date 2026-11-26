import Bilevel.EndpointTransportResponse
import Bilevel.EndpointTransportNormalization

/-! The quadratic-form bounds for the actual orthogonally transported block
operator, with the manuscript's floor normalization. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse

open EndpointTransportMatrix

def physical {n D : ℕ} (Y : Configuration n D) : Physical n D :=
  (WithLp.equiv 2 _).symm Y

def blockQuadratic {n D : ℕ} (δ : ℝ) (Q : Rotations n D)
    (Y : Configuration n D) : ℝ :=
  ∑ i : Index n, ⟪Y i, hessianAction δ Q Y i⟫

theorem blockQuadratic_coordinates {n D : ℕ} (δ : ℝ) (Q : Rotations n D)
    (Y : Configuration n D) :
    blockQuadratic δ Q Y =
      δ * ∑ d : Fin D, quadratic n (matrix n) (coordinates Q Y d) := by
  have hi (i : Index n) : ⟪Y i, hessianAction δ Q Y i⟫ =
      ∑ d : Fin D, δ * (coordinates Q Y d i *
        (matrix n).mulVec (coordinates Q Y d) i) := by
    rw [← (Q i).symm.inner_map_map, PiLp.inner_apply]
    simp only [RCLike.inner_apply', conj_trivial]
    apply Finset.sum_congr rfl
    intro d _
    change coordinates Q Y d i * coordinates Q (hessianAction δ Q Y) d i = _
    rw [hessianAction_coordinates]
    ring
  unfold blockQuadratic
  simp_rw [hi]
  rw [Finset.sum_comm]
  simp only [quadratic, Finset.mul_sum]

theorem coordinates_norm_sq {n D : ℕ} (Q : Rotations n D) (Y : Configuration n D) :
    (∑ d : Fin D, ∑ i : Index n, coordinates Q Y d i ^ 2) = ‖physical Y‖^2 := by
  rw [Finset.sum_comm, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ d : Fin D, ((Q i).symm (Y i)) d ^ 2) = ‖Y i‖^2
  rw [← (Q i).symm.norm_map (Y i), PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Genuine Rayleigh bounds for the transported block matrix. -/
theorem block_spectral_sandwich {n D : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (Q : Rotations n D) (Y : Configuration n D) :
    δ * (1/(2*(n+1:ℝ)^2)) * ‖physical Y‖^2 ≤ blockQuadratic δ Q Y ∧
      blockQuadratic δ Q Y ≤ (4*δ) * ‖physical Y‖^2 := by
  have hl := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin D)))
    (fun d _ => (quadratic_spectral_sandwich n (coordinates Q Y d)).1)
  have hu := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin D)))
    (fun d _ => (quadratic_spectral_sandwich n (coordinates Q Y d)).2)
  rw [← Finset.mul_sum, coordinates_norm_sq] at hl hu
  rw [blockQuadratic_coordinates]
  constructor
  · convert mul_le_mul_of_nonneg_left hl hδ using 1
    ring
  · convert mul_le_mul_of_nonneg_left hu hδ using 1
    ring

/-- The coordinate definition of the lower objective equals the usual physical
quadratic `1/2 <Y,HY> - c <Q_last v,Y_last>`. -/
theorem lower_block_formula {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (v : Block D) (Y : Configuration n D) :
    lower δ c Q v Y = blockQuadratic δ Q Y / 2 -
      c * ⟪Q (Fin.last (n+1)) v, Y (Fin.last (n+1))⟫ := by
  rw [lower_physical_formula, blockQuadratic_coordinates]
  ring

/-- The manuscript's `4 μ` and `L/4` Rayleigh bounds on every physical block
vector, for the actual floor-selected transport length. -/
theorem normalized_block_bounds {D : ℕ} {L κ : ℝ} (hL : 0 ≤ L) (hκ : 3200 ≤ κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (Y : Configuration (EndpointTransportNormalization.interiors κ) D) :
    4 * (L/κ) * ‖physical Y‖^2 ≤ blockQuadratic (L/16) Q Y ∧
      blockQuadratic (L/16) Q Y ≤ (L/4) * ‖physical Y‖^2 := by
  have hb := block_spectral_sandwich (show 0 ≤ L/16 by positivity) Q Y
  rw [EndpointTransportNormalization.interior_middle_cast hκ] at hb
  have hc := mul_le_mul_of_nonneg_right
    (EndpointTransportNormalization.lower_coefficient_slack hL hκ)
    (sq_nonneg ‖physical Y‖)
  constructor
  · exact hc.trans hb.1
  · convert hb.2 using 1
    ring

end Bilevel.EndpointTransportResponse
