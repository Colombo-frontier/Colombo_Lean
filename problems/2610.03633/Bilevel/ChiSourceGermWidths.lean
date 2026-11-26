import Bilevel.ChiSourceBlindOrdering
import Bilevel.ChiOuterSourceBarrier

/-! A positive common open-neighborhood radius for all actual source nodes.
The source's finest width is dominated by the macro and every inner width;
this uses only the already calibrated monotone source resolutions. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ZeroChainSchedule
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem source_finest_uniform_widths
    (initial : Scale) (r η weight : ℕ → ℝ) (A Kminus ζ cn CR Km : ℝ) (n : ℕ)
    (U : Space n →ₗᵢ[ℝ] E)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤r j) (hη : ∀ j,0<η j) (hη1 : ∀ j,η j≤1)
    (J : ℕ) (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v) :
    let M := sourceMacroNode n initial Km U
    let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
    let W := width c (D J []).width v (levels v)
    0<W ∧ W≤M.width/128 ∧ ∀ j P,j≤J → W≤(D j P).width/128 := by
  dsimp only
  let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
  have hp := parentScale_positive initial r η hl hw hr hη
  have hβ : 0<(D J []).width := (hp (J+1)).2
  have hell : 0≤(D J []).ell := (hp (J+1)).1.le
  let P : ChiFine.Parameters := ⟨(D J []).ell,(D J []).width,v,c,hell,hβ,hv,hc,hcs⟩
  have hsmall := P.normal_width_small (levels v)
  have hmono : (D J []).width≤ initial.width :=
    parentScale_width_antitone initial r η hl hw hr hη hη1 (Nat.zero_le (J+1))
  refine ⟨width_pos c (D J []).width v hc hβ hv (levels v),?_,?_⟩
  · exact hsmall.trans (div_le_div_of_nonneg_right hmono (by norm_num))
  · intro j I hj
    exact source_finest_le_node_width initial r η weight A Kminus ζ cn CR V hl hw hr hη hη1 J j hj c v hc hcs hv

theorem source_uniform_germ_radius
    (initial : Scale) (r η weight : ℕ → ℝ) (A Kminus ζ cn CR Km : ℝ) (n : ℕ)
    (U : Space n →ₗᵢ[ℝ] E)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F)
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤r j) (hη : ∀ j,0<η j) (hη1 : ∀ j,η j≤1)
    (J : ℕ) (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hv : 1≤v) :
    let M := sourceMacroNode n initial Km U
    let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
    let δ := width c (D J []).width v (levels v)/16
    0<δ ∧ δ≤M.width/16 ∧ ∀ j P,j≤J → δ≤(D j P).width/16 := by
  dsimp only
  have h := source_finest_uniform_widths initial r η weight A Kminus ζ cn CR Km n U V hl hw hr hη hη1 J c v hc hcs hv
  dsimp only at h
  refine ⟨div_pos h.1 (by norm_num),?_,?_⟩
  · have hm := h.2.1
    change _≤ initial.width/16
    change _≤ initial.width/128 at hm
    linarith
  · intro j P hj
    have hd := h.2.2 j P hj
    have hh : 0<(sourceGeometry initial r η weight A Kminus ζ cn CR V j P).width :=
      (parentScale_positive initial r η hl hw hr hη (j+1)).2
    linarith

end Bilevel.ChiExtensionCalibration
