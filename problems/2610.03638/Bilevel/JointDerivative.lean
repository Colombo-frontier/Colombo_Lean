import Bilevel.ModelBridge
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Joint derivatives from the article's partial-gradient certificates

Coordinate-path Taylor estimates turn Lipschitz partial gradients into an
actual joint Fréchet derivative. This module does not postulate joint
differentiability of the upper objective.
-/

noncomputable section
open scoped RealInnerProductSpace Topology
open Filter Asymptotics

namespace Bilevel.JointDerivative

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Taylor remainder from a Lipschitz gradient, without a Hessian assumption. -/
theorem gradient_taylor (f : X → ℝ) (g : X → X) (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖) (x d : X) :
    ‖f (x + d) - f x - ⟪g x, d⟫‖ ≤ L / 2 * ‖d‖ ^ 2 := by
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f (x + t • d)) ⟪g (x + s • d), d⟫ s := by
    intro s _
    have hline : HasDerivAt (fun t : ℝ => x + t • d) d s := by
      simpa using ((hasDerivAt_id s).smul_const d).const_add x
    simpa only [InnerProductSpace.toDual_apply] using (hf _).hasFDerivAt.comp_hasDerivAt s hline
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖⟪g (x + s • d), d⟫ - ⟪g (x + (0 : ℝ) • d), d⟫‖ ≤ (L * ‖d‖ ^ 2) * s := by
    intro s hs
    simp only [zero_smul, add_zero, ← inner_sub_left]
    calc
      ‖⟪g (x + s • d) - g x, d⟫‖ ≤ ‖g (x + s • d) - g x‖ * ‖d‖ :=
        norm_inner_le_norm _ _
      _ ≤ (L * ‖x + s • d - x‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hg _ _) (norm_nonneg d)
      _ = (L * ‖d‖ ^ 2) * s := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        ring
  have h := FrozenTilt.path_remainder_bound _ _ (L * ‖d‖ ^ 2) hd hv
  simpa [mul_div_assoc, div_mul_eq_mul_div] using h

omit [InnerProductSpace ℝ X] [CompleteSpace X] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
/-- A reusable extraction of a component Lipschitz bound from joint squared norms. -/
theorem component_bound {u : X} {v : Y} {L D : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (h : ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ L ^ 2 * D ^ 2) : ‖u‖ ≤ L * D := by
  have hs : ‖u‖ ^ 2 ≤ (L * D) ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL hD)).mp hs

/-- Joint derivative with a quantitative quadratic remainder. -/
theorem joint_remainder (f : X → Y → ℝ) (gx : X → Y → X) (gy : X → Y → Y)
    {L : ℝ} (hL : 0 ≤ L)
    (hx : ∀ x y, HasGradientAt (fun z => f z y) (gx x y) x)
    (hy : ∀ x y, HasGradientAt (f x) (gy x y) y)
    (hxx : ∀ x z y, ‖gx x y - gx z y‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x y z, ‖gx x y - gx x z‖ ≤ L * ‖y - z‖)
    (hyy : ∀ x y z, ‖gy x y - gy x z‖ ≤ L * ‖y - z‖)
    (x : X) (y : Y) (dx : X) (dy : Y) :
    ‖f (x + dx) (y + dy) - f x y - (⟪gx x y, dx⟫ + ⟪gy x y, dy⟫)‖ ≤
      2 * L * ‖(dx, dy)‖ ^ 2 := by
  let ex := f (x + dx) (y + dy) - f x (y + dy) - ⟪gx x (y + dy), dx⟫
  let ey := f x (y + dy) - f x y - ⟪gy x y, dy⟫
  let ec := ⟪gx x (y + dy) - gx x y, dx⟫
  have hex : ‖ex‖ ≤ L / 2 * ‖dx‖ ^ 2 :=
    gradient_taylor (fun z => f z (y + dy)) (fun z => gx z (y + dy)) L
      (fun z => hx z (y + dy)) (fun z w => hxx z w (y + dy)) x dx
  have hey : ‖ey‖ ≤ L / 2 * ‖dy‖ ^ 2 :=
    gradient_taylor (f x) (gy x) L (hy x) (hyy x) y dy
  have hec : ‖ec‖ ≤ L * ‖dy‖ * ‖dx‖ := by
    calc
      ‖ec‖ ≤ ‖gx x (y + dy) - gx x y‖ * ‖dx‖ := norm_inner_le_norm _ _
      _ ≤ L * ‖dy‖ * ‖dx‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg dx)
        simpa only [add_sub_cancel_left] using hxy x (y + dy) y
  have heq : f (x + dx) (y + dy) - f x y - (⟪gx x y, dx⟫ + ⟪gy x y, dy⟫) =
      (ex + ey) + ec := by dsimp [ex, ey, ec]; rw [inner_sub_left]; ring
  rw [heq]
  calc
    ‖ex + ey + ec‖ ≤ ‖ex‖ + ‖ey‖ + ‖ec‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
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

theorem hasFDerivAt_joint (f : X → Y → ℝ) (gx : X → Y → X) (gy : X → Y → Y)
    {L : ℝ} (hL : 0 ≤ L)
    (hx : ∀ x y, HasGradientAt (fun z => f z y) (gx x y) x)
    (hy : ∀ x y, HasGradientAt (f x) (gy x y) y)
    (hxx : ∀ x z y, ‖gx x y - gx z y‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x y z, ‖gx x y - gx x z‖ ≤ L * ‖y - z‖)
    (hyy : ∀ x y z, ‖gy x y - gy x z‖ ≤ L * ‖y - z‖)
    (x : X) (y : Y) :
    HasFDerivAt (fun p : X × Y => f p.1 p.2)
      ((InnerProductSpace.toDual ℝ X (gx x y)).comp (ContinuousLinearMap.fst ℝ X Y) +
        (InnerProductSpace.toDual ℝ Y (gy x y)).comp (ContinuousLinearMap.snd ℝ X Y)) (x, y) := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply IsBigO.trans_isLittleO _ (isLittleO_norm_pow_id (E' := X × Y) one_lt_two)
  apply IsBigO.of_bound (2 * L)
  apply Filter.Eventually.of_forall
  intro d
  change ‖f (x + d.1) (y + d.2) - f x y -
    (⟪gx x y, d.1⟫ + ⟪gy x y, d.2⟫)‖ ≤ 2 * L * ‖‖d‖ ^ 2‖
  rw [Real.norm_of_nonneg (sq_nonneg ‖d‖)]
  exact joint_remainder f gx gy hL hx hy hxx hxy hyy x y d.1 d.2

/-- Joint-gradient smoothness in sum-of-squares form supplies the three
coordinate bounds used in `hasFDerivAt_joint`. -/
theorem hasFDerivAt_joint_of_smooth
    (f : X → Y → ℝ) (gx : X → Y → X) (gy : X → Y → Y)
    {L : ℝ} (hL : 0 ≤ L)
    (hx : ∀ x y, HasGradientAt (fun z => f z y) (gx x y) x)
    (hy : ∀ x y, HasGradientAt (f x) (gy x y) y)
    (hsmooth : ∀ x z y w,
      ‖gx x y - gx z w‖ ^ 2 + ‖gy x y - gy z w‖ ^ 2 ≤
        L ^ 2 * (‖x - z‖ ^ 2 + ‖y - w‖ ^ 2))
    (x : X) (y : Y) :
    HasFDerivAt (fun p : X × Y => f p.1 p.2)
      ((InnerProductSpace.toDual ℝ X (gx x y)).comp (ContinuousLinearMap.fst ℝ X Y) +
        (InnerProductSpace.toDual ℝ Y (gy x y)).comp (ContinuousLinearMap.snd ℝ X Y)) (x, y) := by
  apply hasFDerivAt_joint f gx gy hL hx hy
  · intro z w v
    apply component_bound hL (norm_nonneg (z - w)) (v := gy z v - gy w v)
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      using hsmooth z w v v
  · intro z v w
    apply component_bound hL (norm_nonneg (v - w)) (v := gy z v - gy z w)
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
      using hsmooth z z v w
  · intro z v w
    apply component_bound hL (norm_nonneg (v - w)) (v := gx z v - gx z w)
    have h := hsmooth z z v w
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
    linarith

end Bilevel.JointDerivative

namespace Bilevel.Model.Primitive

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

/-- The actual joint upper derivative follows from the primitive assumptions. -/
theorem has_joint_f (x : X) (y : Y) :
    HasFDerivAt (fun p : X × Y => P.f p.1 p.2)
      ((InnerProductSpace.toDual ℝ X (P.fx x y)).comp (ContinuousLinearMap.fst ℝ X Y) +
        (InnerProductSpace.toDual ℝ Y (P.fy x y)).comp (ContinuousLinearMap.snd ℝ X Y)) (x, y) :=
  JointDerivative.hasFDerivAt_joint_of_smooth P.f P.fx P.fy P.Lf_nonneg
    P.has_fx P.has_fy P.smooth_f x y

/-- The same argument also establishes the actual joint lower derivative. -/
theorem has_joint_g (x : X) (y : Y) :
    HasFDerivAt (fun p : X × Y => P.g p.1 p.2)
      ((InnerProductSpace.toDual ℝ X (P.gx x y)).comp (ContinuousLinearMap.fst ℝ X Y) +
        (InnerProductSpace.toDual ℝ Y (P.gy x y)).comp (ContinuousLinearMap.snd ℝ X Y)) (x, y) :=
  JointDerivative.hasFDerivAt_joint_of_smooth P.g P.gx P.gy P.Lg_nonneg
    P.has_gx P.has_gy P.smooth_g x y

end Bilevel.Model.Primitive
