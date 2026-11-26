import Bilevel.FrozenTilt
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Joint vector derivatives from Lipschitz partial Fréchet derivatives. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Bilevel.JointVectorDerivative
variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem joint_remainder (f : X → Y → Z)
    (A : X → Y → X →L[ℝ] Z) (B : X → Y → Y →L[ℝ] Z)
    {L : ℝ} (hL : 0 ≤ L)
    (hx : ∀ x y, HasFDerivAt (fun z => f z y) (A x y) x)
    (hy : ∀ x y, HasFDerivAt (f x) (B x y) y)
    (hxx : ∀ x z y, ‖A x y - A z y‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x y z, ‖A x y - A x z‖ ≤ L * ‖y - z‖)
    (hyy : ∀ x y z, ‖B x y - B x z‖ ≤ L * ‖y - z‖)
    (x : X) (y : Y) (dx : X) (dy : Y) :
    ‖f (x + dx) (y + dy) - f x y - (A x y dx + B x y dy)‖ ≤
      2 * L * ‖(dx, dy)‖ ^ 2 := by
  let ex := f (x + dx) (y + dy) - f x (y + dy) - A x (y + dy) dx
  let ey := f x (y + dy) - f x y - B x y dy
  let ec := (A x (y + dy) - A x y) dx
  have hex : ‖ex‖ ≤ L / 2 * ‖dx‖ ^ 2 :=
    FrozenTilt.taylor_remainder_bound (fun z => f z (y + dy))
      (fun z => A z (y + dy)) x dx L
      (fun z => hx z (y + dy)) (fun z w => hxx z w (y + dy))
  have hey : ‖ey‖ ≤ L / 2 * ‖dy‖ ^ 2 :=
    FrozenTilt.taylor_remainder_bound (f x) (B x) y dy L (hy x) (hyy x)
  have hec : ‖ec‖ ≤ L * ‖dy‖ * ‖dx‖ := by
    calc
      ‖ec‖ ≤ ‖A x (y + dy) - A x y‖ * ‖dx‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖dy‖ * ‖dx‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg dx)
        simpa only [add_sub_cancel_left] using hxy x (y + dy) y
  have heq : f (x + dx) (y + dy) - f x y - (A x y dx + B x y dy) =
      (ex + ey) + ec := by
    dsimp [ex, ey, ec]
    abel
  rw [heq]
  calc
    ‖ex + ey + ec‖ ≤ ‖ex‖ + ‖ey‖ + ‖ec‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ L / 2 * ‖dx‖ ^ 2 + L / 2 * ‖dy‖ ^ 2 + L * ‖dy‖ * ‖dx‖ := by gcongr
    _ ≤ 2 * L * ‖(dx, dy)‖ ^ 2 := by
      have hdx : ‖dx‖ ≤ ‖(dx, dy)‖ := le_max_left _ _
      have hdy : ‖dy‖ ≤ ‖(dx, dy)‖ := le_max_right _ _
      have hx2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdx) (show 0 ≤ L / 2 by positivity)
      have hy2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdy) (show 0 ≤ L / 2 by positivity)
      have hc := mul_le_mul_of_nonneg_left
        (mul_le_mul hdy hdx (norm_nonneg _) (norm_nonneg _)) hL
      nlinarith

theorem hasFDerivAt_joint (f : X → Y → Z)
    (A : X → Y → X →L[ℝ] Z) (B : X → Y → Y →L[ℝ] Z)
    {L : ℝ} (hL : 0 ≤ L)
    (hx : ∀ x y, HasFDerivAt (fun z => f z y) (A x y) x)
    (hy : ∀ x y, HasFDerivAt (f x) (B x y) y)
    (hxx : ∀ x z y, ‖A x y - A z y‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x y z, ‖A x y - A x z‖ ≤ L * ‖y - z‖)
    (hyy : ∀ x y z, ‖B x y - B x z‖ ≤ L * ‖y - z‖)
    (x : X) (y : Y) :
    HasFDerivAt (fun p : X × Y => f p.1 p.2)
      ((A x y).comp (ContinuousLinearMap.fst ℝ X Y) +
        (B x y).comp (ContinuousLinearMap.snd ℝ X Y)) (x, y) := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply IsBigO.trans_isLittleO _ (isLittleO_norm_pow_id (E' := X × Y) one_lt_two)
  apply IsBigO.of_bound (2 * L)
  apply Filter.Eventually.of_forall
  intro d
  change ‖f (x + d.1) (y + d.2) - f x y - (A x y d.1 + B x y d.2)‖ ≤
    2 * L * ‖‖d‖ ^ 2‖
  rw [Real.norm_of_nonneg (sq_nonneg ‖d‖)]
  exact joint_remainder f A B hL hx hy hxx hxy hyy x y d.1 d.2

end Bilevel.JointVectorDerivative
