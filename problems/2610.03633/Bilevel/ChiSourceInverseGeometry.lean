import Bilevel.ChiSourceGermWidths
import Bilevel.ChiExtensionSourceRadial
import Bilevel.ChiCarrierProjectionBlind

/-! The concrete source supplies all point-independent node geometry used
by the inverse/evaluation equality. Only actual column membership and
projection bounds remain for the finite-frame observer. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem source_inverse_geometry
    (initial : Scale) (r η weight : ℕ → ℝ) (A Kminus ζ cn CR Km : ℝ) (n : ℕ)
    (U : Space n →ₗᵢ[ℝ] E)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤r j) (hη : ∀ j,0<η j) (hη1 : ∀ j,η j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km) :
    let M := sourceMacroNode n initial Km U
    let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
    0<M.width ∧ 0<M.radius ∧
    (∀ j P,0<(D j P).width ∧ 0<(D j P).radius ∧ 0<(D j P).ell ∧
      0<(D j P).parentWidth ∧ (D j P).width≤(D j P).parentWidth) ∧
    (∀ j P,(D j P).width=(D j []).width) := by
  dsimp only
  have hp := parentScale_positive initial r η hl hw hr hη
  refine ⟨hw,?_,?_,fun _ _ => rfl⟩
  · change 0<Km*initial.width*Real.sqrt ((n:ℝ)+1)
    positivity
  · intro j P
    have hrj : 0<r j := (by norm_num : (0:ℝ)<1).trans_le (hr j)
    refine ⟨(hp (j+1)).2,?_,(hp (j+1)).1,(hp j).2,?_⟩
    · exact source_radial_radius_pos hCR (hp j).1 (hp j).2 hrj (hweight j) hζ
    · change η j*(parentScale initial r η j).width/r j≤(parentScale initial r η j).width
      apply (div_le_iff₀ hrj).mpr
      nlinarith only [mul_le_mul_of_nonneg_right ((hη1 j).trans (hr j)) (hp j).2.le]

omit [CompleteSpace F] in
theorem treeProjection_of_half_margin {m : ℕ} (D : Geometry F) (J : ℕ) (hm : J<m)
    (W : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)] (r : ℕ → List ℕ → ℕ)
    (hw : ∀ j P,j≤J → 0<(D j P).width) (hR : ∀ j P,j≤J → 0<(D j P).radius)
    (hcols : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),k.val<r j P →
      (D j P).frame (basis k)∈W ⟨j,by omega⟩)
    (hproj : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8) :
    TreeProjection D 0 J (by omega) W r := by
  intro j P _ hj
  have hjJ : j≤J := by omega
  refine ⟨hw j P hjJ,hR j P hjJ,hcols j P hjJ,?_⟩
  intro k hk
  exact (hproj j P hjJ k hk).trans (by have hh := hw j P hjJ;linarith)

end Bilevel.ChiExtensionCalibration
