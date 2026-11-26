import HardIntegrability254
import SurrogateCurvature254

noncomputable section
open Set
namespace Paper254

def squareExponential (y x : ℝ) : ℝ := Real.exp (-(2/9 : ℝ)*(x-y)^2)
def squareExponentialDeriv (y x : ℝ) : ℝ := -(4/9 : ℝ)*(x-y)*squareExponential y x
def squareExponentialSecond (y x : ℝ) : ℝ := ((16/81 : ℝ)*(x-y)^2-4/9)*squareExponential y x

theorem squareExponential_derivative (y x : ℝ) :
    HasDerivAt (squareExponential y) (squareExponentialDeriv y x) x := by
  convert ((((hasDerivAt_id x).sub_const y).pow 2).const_mul (-(2/9 : ℝ))).exp using 1
  dsimp [squareExponentialDeriv,squareExponential]
  ring

theorem squareExponential_second (y x : ℝ) :
    HasDerivAt (squareExponentialDeriv y) (squareExponentialSecond y x) x := by
  convert (((hasDerivAt_id x).sub_const y).const_mul (-(4/9 : ℝ))).mul
    (squareExponential_derivative y x) using 1
  dsimp [squareExponentialDeriv,squareExponentialSecond]
  ring

theorem squareExponential_concave (y : ℝ) (hy : |y| ≤ 1) :
    ConcaveOn ℝ (Icc (-(1/2 : ℝ)) (1/2)) (squareExponential y) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun x _ => (squareExponential_derivative y x).continuousAt.continuousWithinAt)
    (fun x _ => (squareExponential_derivative y x).hasDerivWithinAt)
    (fun x _ => (squareExponential_second y x).hasDerivWithinAt)
  intro x hx
  have hb : x ∈ Icc (-(1/2 : ℝ)) (1/2) := interior_subset hx
  have hy' := abs_le.mp hy
  have hsq : (x-y)^2 ≤ 9/4 := by
    have hh := mul_nonneg (show 0 ≤ 3/2-(x-y) by linarith [hb.1,hb.2,hy'.1,hy'.2])
      (show 0 ≤ 3/2+(x-y) by linarith [hb.1,hb.2,hy'.1,hy'.2])
    nlinarith only [hh]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

theorem coordinateSquare_expConcave {d : ℕ} (j : Fin d) (y : Bool) :
    ExpConcaveOn (4/9) (ballDomain d).carrier (coordinateSquare j y) := by
  let z : ℝ := if y then 1 else -1
  have hz : |z| ≤ 1 := by cases y <;> norm_num [z]
  have hmem : ∀ w ∈ (ballDomain d).carrier, w j ∈ Icc (-(1/2 : ℝ)) (1/2) := by
    intro w hw
    exact abs_le.mp (ball_coordinate_bound ⟨w,hw⟩ j)
  have he : ∀ w : Space d, Real.exp (-(4/9 : ℝ)*coordinateSquare j y w) = squareExponential z (w j) := by
    intro w
    unfold coordinateSquare squareExponential
    congr 1
    dsimp [z]
    ring
  refine ⟨(ballDomain d).convex,?_⟩
  intro v hv w hw a b ha hb hab
  simp_rw [he]
  have hh := (squareExponential_concave z hz).2 (hmem v hv) (hmem w hw) ha hb hab
  exact hh

theorem coordinate_projection_norm {d : ℕ} (j : Fin d) :
    ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  simpa only [one_mul] using PiLp.norm_apply_le w j

theorem coordinateSquare_gradient {d : ℕ} (j : Fin d) (y : Bool)
    (w : (ballDomain d).carrier) :
    ∃ g : Space d, HasGradientWithinAt (coordinateSquare j y) g (ballDomain d).carrier w.val ∧ ‖g‖ ≤ 3/2 := by
  let z : ℝ := if y then 1 else -1
  let L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j
  have hcoord : HasFDerivAt (fun v : Space d => v j) L w.val := L.hasFDerivAt
  have hf : HasFDerivAt (coordinateSquare j y) ((w.val j-z) • L) w.val := by
    convert ((hcoord.sub_const z).pow 2).const_mul (1/2 : ℝ) using 1
    · funext v
      dsimp [coordinateSquare,z]
      ring
    · ext v
      simp [ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring
  refine ⟨_,hf.hasFDerivWithinAt.hasGradientWithinAt,?_⟩
  rw [(InnerProductSpace.toDual ℝ (Space d)).symm.norm_map, norm_smul,Real.norm_eq_abs]
  have hc : |w.val j-z| ≤ 3/2 := by
    have hw := abs_le.mp (ball_coordinate_bound w j)
    cases y <;> apply abs_le.mpr <;> dsimp [z] <;> constructor <;> linarith
  have hL : ‖L‖ ≤ 1 := coordinate_projection_norm j
  have hh := mul_le_mul hc hL (norm_nonneg L) (by norm_num : (0 : ℝ) ≤ 3/2)
  simpa only [mul_one] using hh

theorem hard_loss_admissible {d : ℕ} (j : Fin d) (y : Bool) :
    AdmissibleLoss (ballDomain d) (3/2) (4/9) (coordinateSquare j y) := by
  refine ⟨coordinateSquare_expConcave j y,?_⟩
  intro w hw
  exact coordinateSquare_gradient j y ⟨w,hw⟩

end Paper254
#print axioms Paper254.hard_loss_admissible
