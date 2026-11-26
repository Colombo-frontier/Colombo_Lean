import Bilevel.ChiCarrierProjectionBlind
import Bilevel.ChiSourceActivation

/-! Arbitrary returned points need only their terminal inner-product
observation. Radial compression turns the relative inner bound into an
absolute hidden-coordinate bound, without requiring a prior query there. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportHierarchy
open ChiRecursive ChiBoundedChain ChiHierarchyIndex ChiTreeProgress RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem terminal_coordinate_bound (M : Node E) (hR : 0<M.radius) (x : E) (k : Fin (M.n+1))
    (cap : ℝ) (hi : |⟪M.frame (basis k),x⟫|≤Real.sqrt cap*‖x‖) :
    |M.coordinates x k|≤M.radius*Real.sqrt cap := by
  rw [M.coordinate_eq_inner,compress,real_inner_smul_right,abs_mul,abs_of_pos (scale_pos M.radius x)]
  have hn : scale M.radius x*‖x‖≤M.radius := by
    have hh := compress_norm_le_radius M.radius hR x
    simpa only [compress,norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos M.radius x)] using hh
  calc
    _≤scale M.radius x*(Real.sqrt cap*‖x‖) := mul_le_mul_of_nonneg_left hi (scale_pos M.radius x).le
    _=Real.sqrt cap*(scale M.radius x*‖x‖) := by ring
    _≤Real.sqrt cap*M.radius := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg cap)
    _=M.radius*Real.sqrt cap := mul_comm _ _

theorem macro_incomplete_before_transport_capacity (counts : ℕ → ℕ) (J length N : ℕ)
    (hL : 0<length) (hN : N<length*capacity counts (J+1) 0) :
    counter counts (J+1) (N/length) 0 []≤counts 0 := by
  have hq : N/length<capacity counts (J+1) 0 :=
    (Nat.div_lt_iff_lt_mul hL).mpr (by simpa only [Nat.mul_comm] using hN)
  exact ChiHierarchyHaar.macro_incomplete_of_successes_lt counts J (N/length) hq

end Bilevel.TransportHierarchy
