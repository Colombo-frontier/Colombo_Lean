import Bilevel.ChiProjectionStability
import Bilevel.ChiHierarchyHomotopyCompare

/-! Simultaneous actual tree-coordinate confinement from old-space
projection margins and an inverse perturbation of at most 6 W_last/11. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive PrimitiveGeometry ChiExtension
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem treeBlind_of_near_old {m s : ℕ} (D : Geometry F) (J : ℕ) (hm : J<m)
    (W V : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)] (hWV : ∀ i,W i≤V i)
    (r : ℕ → List ℕ → ℕ) (htree : TreeProjection D 0 J (by simpa using hm) W r)
    (Wlast : ℝ) (z : normalKnown V s) (z0 : normalKnown W s)
    (hdist : ‖(z:Full (Blocks m F) s)-(z0:Full (Blocks m F) s)‖≤6*Wlast/11)
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (hwidth : ∀ j P,j≤J → Wlast≤(D j P).width/128) :
    TreeBlind D 0 J (by simpa using hm) V (z:Full (Blocks m F) s).fst r := by
  intro j P hj hjJ
  have hb := htree j P hj hjJ
  refine ⟨hb.width_pos,hb.radius_pos,z.property _,fun k hk => hWV _ (hb.columns_mem k hk),?_⟩
  intro k hk
  have hp := coordinate_near_normalKnown W (z:Full (Blocks m F) s) z0 ⟨j,by omega⟩ (D j P) hb.radius_pos
    k ((D j P).width/8) (6*Wlast/11) (hmargin j P (by omega) k hk) hdist
  have hw := hwidth j P (by omega)
  have hh := hb.width_pos
  linarith

end Bilevel.ChiCarrier
