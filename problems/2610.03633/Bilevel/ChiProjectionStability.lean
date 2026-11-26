import Bilevel.ChiCarrierProjectionBlind
import Bilevel.WrappedRegularity

/-! Point-independent old-space projection budgets survive a small change
of the restricted inverse. Bounds are on the actual radially compressed
frame coordinates, simultaneously for every node and column. -/
noncomputable section
namespace Bilevel.ChiRecursive.Node
open ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinate_difference_bound (D : Node E) (hR : 0<D.radius) (u v : E) (k : Fin (D.n+1)) :
    |D.coordinates u k-D.coordinates v k|≤‖u-v‖ := by
  have hh := PiLp.norm_apply_le (D.coordinates u-D.coordinates v) k
  simp only [PiLp.sub_apply,Real.norm_eq_abs] at hh
  exact hh.trans (WrappedChain.coordinates_lipschitz D.n D.radius hR D.frame u v)

theorem coordinate_near_old_space (D : Node E) (hR : 0<D.radius)
    (W : Submodule ℝ E) [CompleteSpace W] (u : E) (v : W) (k : Fin (D.n+1))
    (ε η : ℝ) (hproj : D.radius*‖W.orthogonalProjection (D.frame (basis k))‖≤ε)
    (hdist : ‖u-(v:E)‖≤η) : |D.coordinates u k|≤ε+η := by
  have hd := (D.coordinate_difference_bound hR u (v:E) k).trans hdist
  have hp := (D.coordinate_projection_bound hR W v k).trans hproj
  have ha := abs_add_le (D.coordinates u k-D.coordinates (v:E) k) (D.coordinates (v:E) k)
  rw [sub_add_cancel] at ha
  linarith

end Bilevel.ChiRecursive.Node

namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive PrimitiveGeometry ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem lower_block_difference_bound {m s : ℕ} (z w : Full (Blocks m E) s) (i : Fin m) :
    ‖z.fst i-w.fst i‖≤‖z-w‖ := by
  have hp := PiLp.norm_apply_le (z-w).fst i
  exact hp.trans (WithLp.norm_fst_le (Blocks m E) (z-w))

theorem coordinate_near_normalKnown {m s : ℕ} (W : Fin m → Submodule ℝ E)
    [∀ i,CompleteSpace (W i)] (z : Full (Blocks m E) s) (w : normalKnown W s)
    (i : Fin m) (D : Node E) (hR : 0<D.radius) (k : Fin (D.n+1))
    (ε η : ℝ) (hproj : D.radius*‖(W i).orthogonalProjection (D.frame (basis k))‖≤ε)
    (hdist : ‖z-(w:Full (Blocks m E) s)‖≤η) : |D.coordinates (z.fst i) k|≤ε+η := by
  exact D.coordinate_near_old_space hR (W i) (z.fst i) ⟨(w:Full (Blocks m E) s).fst i,w.property i⟩
    k ε η hproj ((lower_block_difference_bound z (w:Full (Blocks m E) s) i).trans hdist)

end Bilevel.ChiCarrier
