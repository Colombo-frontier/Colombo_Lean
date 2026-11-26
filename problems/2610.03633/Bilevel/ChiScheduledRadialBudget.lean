import Bilevel.ChiExtensionSourceRadial
import Bilevel.ChiSourcePhysicalScales

/-! Global second and third derivative budgets of the actual finite public
radial extension with the nonuniform source curvature schedule. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtension PrimitiveGeometry

theorem scheduled_radial_jets
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {J m : ℕ} (hJ : 1 ≤ J) (index : Fin J → Fin m) (proj : Fin J → E →L[ℝ] F)
    (hproj : ∀ j,‖proj j‖ ≤ 1)
    (L η₀ b η K κ T ζ CR : ℝ) (weight : Fin J → ℝ)
    (hL : 0 < L) (hη₀ : 0 < η₀) (hb : 0 < b) (hη : 0 < η) (hη1 : η ≤ 1)
    (hκ : 1 ≤ κ) (hK : K = κ/6) (hT : 1 ≤ T) (hTκ : T ≤ κ)
    (hζ : 0 < ζ) (hCR : 0 < CR) (hw : ∀ j,0 < weight j) (hw1 : ∀ j,weight j ≤ 1)
    (z : Full E m) :
    let initial : Scale := ⟨η₀*L,b⟩
    let s := fun j : Fin J => parentScale initial (sourceRatio T) (resolution η K) (j.val+1)
    let ν := fun j => weight j*(ζ*(s j).curvature)
    let R := fun j => sourceLocalRadius CR (s j).curvature (s j).width (sourceRatio T (j.val+1)) (weight j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index proj hproj ν R (normalCoefficient L J)) z‖ ≤
      144*CR*η₀*b*((J:ℝ)+1)^2 ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index proj hproj ν R (normalCoefficient L J)) z‖ ≤
      72*ζ*η₀*((J:ℝ)+1)^2*T := by
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let s := fun j : Fin J => parentScale initial (sourceRatio T) (resolution η K) (j.val+1)
  have hκp : 0 < κ := by linarith
  have hKp : 0 < K := by rw [hK]; positivity
  have hTp : 0 < T := by linarith
  have hp := parentScale_positive initial (sourceRatio T) (resolution η K)
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one hT) (base_resolution_positive hη hKp)
  have hcurv (j : Fin J) : (s j).curvature ≤ initial.curvature*T := by
    rw [source_parent_curvature initial hTp]
    exact mul_le_mul_of_nonneg_left (curvature_bounds hT j.val).2 (mul_nonneg hη₀.le hL.le)
  have hforce (j : Fin J) : (s j).curvature*(s j).width*
      Real.sqrt (sourceRatio T (j.val+1)) ≤ 6*initial.force :=
    parent_force_ratio_bound initial hT hTκ hκ hη.le hη1 (mul_nonneg hη₀.le hL.le) hb.le hK j.val
  have hj := source_radialSum_uniform_budgets index proj hproj
    (fun j => (s j).curvature) (fun j => (s j).width)
    (fun j => sourceRatio T (j.val+1)) weight CR ζ (normalCoefficient L J)
    (6*initial.force) (initial.curvature*T)
    (fun j => (hp (j.val+1)).1) (fun j => (hp (j.val+1)).2)
    (fun j => lt_of_lt_of_le zero_lt_one (sourceRatio_ge_one hT _)) hw hw1 hCR hζ
    (normalCoefficient_pos hL hJ) hforce hcurv z
  have hs := sqrt_two_depth_le J
  have hJ0 : (0:ℝ) ≤ J := Nat.cast_nonneg _
  constructor
  · apply hj.1.trans
    have he : (J:ℝ)*(3*CR*(6*initial.force)/normalCoefficient L J) =
        72*CR*η₀*b*(J:ℝ)*Real.sqrt (2*(J:ℝ)) := by
      dsimp only [initial,Scale.force,normalCoefficient]
      field_simp
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 72*CR*η₀*b*(J:ℝ) by positivity)
    have hp' : (J:ℝ)*((J:ℝ)+1) ≤ ((J:ℝ)+1)^2 := by nlinarith
    have hm' := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 144*CR*η₀*b by positivity)
    nlinarith only [hm,hm']
  · apply hj.2.trans
    have he : (J:ℝ)*(9*ζ*(initial.curvature*T)/normalCoefficient L J) =
        36*ζ*η₀*T*(J:ℝ)*Real.sqrt (2*(J:ℝ)) := by
      dsimp only [initial,normalCoefficient]
      field_simp
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 36*ζ*η₀*T*(J:ℝ) by positivity)
    have hp' : (J:ℝ)*((J:ℝ)+1) ≤ ((J:ℝ)+1)^2 := by nlinarith
    have hm' := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 72*ζ*η₀*T by positivity)
    nlinarith only [hm,hm']

end Bilevel.ChiExtensionCalibration
