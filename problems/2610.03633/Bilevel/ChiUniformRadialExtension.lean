import Bilevel.ChiExtensionSourceRadial
import Bilevel.ChiSourcePhysicalScales
import Bilevel.ChiUniformCurvatureSums

/-! Actual public radial jets at independent base width. Lower selector
weights cancel from the Hessian, including very small active weights. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtension PrimitiveGeometry

theorem independent_parent_force_bound (initial : Scale) {T η Kg : ℝ}
    (hT : 1≤T) (hη : 0≤η) (hη1 : η≤1) (hK : 0<Kg)
    (hl : 0≤ initial.curvature) (hb : 0≤ initial.width) (j : ℕ) :
    (parentScale initial (sourceRatio T) (resolution η Kg) (j+1)).force*
      Real.sqrt (sourceRatio T (j+1))≤ initial.force/Kg*T^(3/8:ℝ) := by
  have hg : 0≤ initial.force := mul_nonneg hl hb
  rw [source_force_formula initial (sourceRatio T) (sourceRatio_ge_one hT)]
  have hh := mul_le_mul (pow_le_one₀ hη hη1 (n:=j)) (ratio_sqrt_le hT j)
    (Real.sqrt_nonneg _) zero_le_one
  have hm := mul_le_mul_of_nonneg_left hh (div_nonneg hg hK.le)
  change η^j*(initial.force/Kg)*Real.sqrt (curvature T (j+1)/curvature T j)≤_
  nlinarith only [hm]

theorem independent_radial_jets
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {J m : ℕ} (index : Fin J → Fin m) (proj : Fin J → E →L[ℝ] F)
    (hproj : ∀ j,‖proj j‖≤1)
    (initial : Scale) (η Kg T ζ CR d : ℝ) (weight : Fin J → ℝ)
    (hl : 0 < initial.curvature) (hb : 0 < initial.width) (hη : 0<η) (hη1 : η≤1)
    (hK : 0<Kg) (hT : 1≤T) (hζ : 0<ζ) (hCR : 0<CR) (hd : 0<d)
    (hw : ∀ j,0<weight j) (hw1 : ∀ j,weight j≤1) (z : Full E m) :
    let s := fun j : Fin J => parentScale initial (sourceRatio T) (resolution η Kg) (j.val+1)
    let ν := fun j => weight j*(ζ*(s j).curvature)
    let R := fun j => sourceLocalRadius CR (s j).curvature (s j).width
      (sourceRatio T (j.val+1)) (weight j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index proj hproj ν R d) z‖≤
      3*CR*(initial.force/(Kg*d))*(J:ℝ)*T^(3/8:ℝ) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index proj hproj ν R d) z‖≤
      9*ζ*(initial.curvature/d)*(J:ℝ)*T := by
  dsimp only
  let s := fun j : Fin J => parentScale initial (sourceRatio T) (resolution η Kg) (j.val+1)
  have hTp : 0<T := by linarith
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg)
    hl hb (sourceRatio_ge_one hT) (base_resolution_positive hη hK)
  have hcurv (j : Fin J) : (s j).curvature≤ initial.curvature*T := by
    rw [source_parent_curvature initial hTp]
    exact mul_le_mul_of_nonneg_left (curvature_bounds hT j.val).2 hl.le
  have hforce (j : Fin J) : (s j).curvature*(s j).width*
      Real.sqrt (sourceRatio T (j.val+1))≤ initial.force/Kg*T^(3/8:ℝ) :=
    independent_parent_force_bound initial hT hη.le hη1 hK hl.le hb.le j.val
  have hj := source_radialSum_uniform_budgets index proj hproj
    (fun j => (s j).curvature) (fun j => (s j).width)
    (fun j => sourceRatio T (j.val+1)) weight CR ζ d
    (initial.force/Kg*T^(3/8:ℝ)) (initial.curvature*T)
    (fun j => (hp (j.val+1)).1) (fun j => (hp (j.val+1)).2)
    (fun j => lt_of_lt_of_le zero_lt_one (sourceRatio_ge_one hT _)) hw hw1 hCR hζ hd hforce hcurv z
  constructor
  · convert hj.1 using 1
    ring
  · convert hj.2 using 1
    ring

end Bilevel.ChiExtensionCalibration

