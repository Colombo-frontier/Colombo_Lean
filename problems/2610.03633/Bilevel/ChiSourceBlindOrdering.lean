import Bilevel.ChiCarrierSourceWidths
import Bilevel.ChiSourceCoarseExtension
import Bilevel.ChiFineCouplingCore

/-! The actual finest normal width is smaller than every ancestor
physical width and every coarse normal width. One hidden-force bound
therefore controls all the source blind thresholds. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ZeroChainSchedule

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem source_finest_le_node_width
    (initial : Scale) (r η weight : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F)
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1 ≤ r j) (hη : ∀ j,0 < η j) (hη1 : ∀ j,η j ≤ 1)
    (J j : ℕ) (hj : j ≤ J) (c v : ℝ) (hc : 0 < c) (hcs : c ≤ 1/128) (hv : 1 ≤ v) :
    let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
    width c (D J []).width v (levels v) ≤ (D j []).width/128 := by
  dsimp only
  let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
  have hp := parentScale_positive initial r η hl hw hr hη
  have hβ : 0 < (D J []).width := (hp (J+1)).2
  have hell : 0 ≤ (D J []).ell := (hp (J+1)).1.le
  let P : ChiFine.Parameters := ⟨(D J []).ell,(D J []).width,v,c,hell,hβ,hv,hc,hcs⟩
  have hsmall := P.normal_width_small (levels v)
  have hmono : (D J []).width ≤ (D j []).width :=
    parentScale_width_antitone initial r η hl hw hr hη hη1 (by omega : j+1 ≤ J+1)
  exact hsmall.trans (div_le_div_of_nonneg_right hmono (by norm_num))

theorem source_finest_le_coarse_width
    (initial : Scale) (r η weight : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
    (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F)
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1 ≤ r j) (hη : ∀ j,0 < η j) (hη1 : ∀ j,η j ≤ 1)
    (J : ℕ) (i : Fin J) (c v : ℝ) (hc : 0 < c) (hcs : c ≤ 1/128) (hv : 1 ≤ v) :
    let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
    width c (D J []).width v (levels v) ≤ coarseWidths D J i/128 := by
  dsimp only
  let D := sourceGeometry initial r η weight A Kminus ζ cn CR V
  have hsmall := source_finest_le_node_width initial r η weight A Kminus ζ cn CR V hl hw hr hη hη1
    J (i.val+1) (by omega) c v hc hcs hv
  have hn : 1 ≤ ((D (i.val+1) []).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (D (i.val+1) []).n; linarith
  have hrpow := (ChiCoarse.cube_width_properties hn).1
  have hβ : 0 ≤ (D (i.val+1) []).width :=
    (parentScale_positive initial r η hl hw hr hη (i.val+2)).2.le
  have hwidth : (D (i.val+1) []).width ≤ coarseWidths D J i := le_mul_of_one_le_right hβ hrpow
  exact hsmall.trans (div_le_div_of_nonneg_right hwidth (by norm_num))

end Bilevel.ChiExtensionCalibration
