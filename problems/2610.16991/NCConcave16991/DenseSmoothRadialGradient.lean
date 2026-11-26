/- Adapted from the proved radial-calculus fragments in ../0105_formalization/Manuscript0105/RadialGradient.lean. No assumed lower bounds are imported. -/
import NCConcave16991.DenseSmoothRadialBasics
import NCConcave16991.DenseSmoothRadialConstants

/-!
# Algebra behind the radial-gradient comparison

This file records the exact `q`--`ζ` identities used in Lemma `lem:radial-gradient` and the
monotonicity of the squared distance when the radial gradient is multiplied by a coefficient
`c ≥ 1`.
-/

open scoped InnerProductSpace Real

namespace NCConcave16991.DenseSmooth

section Identities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The reciprocal radial scale `ζ=(1+‖x‖²)⁻¹`. -/
noncomputable def radialZeta (x : E) : ℝ := (1 + ‖x‖ ^ 2)⁻¹

/-- A denominator form of the radial gradient, convenient for exact algebra. -/
noncomputable def radialGradient (u x : E) : E :=
  (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ • u -
    (⟪u, x⟫_ℝ * (1 + ‖x‖ ^ 2)⁻¹ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) • x

theorem radialGradient_eq (u x : E) :
    radialGradient u x = radialCoordinateGradient u x := by
  have hs : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
  have hspos : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hs0 : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  dsimp [radialGradient, radialCoordinateGradient]
  rw [show (1 + ‖x‖ ^ 2) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hs]
    ]
  congr 1
  rw [show (1 + ‖x‖ ^ 2) ^ (-(3 / 2 : ℝ)) =
      (1 + ‖x‖ ^ 2)⁻¹ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hs]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hspos]
    rw [Real.rpow_one]
    field_simp]
  simp only [mul_assoc]

theorem radialCoordinate_eq_inner_mul_sqrt_inv (u x : E) :
    radialCoordinate u x =
      ⟪u, x⟫_ℝ * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ := by
  simp [radialCoordinate, div_eq_mul_inv]

theorem radialZeta_pos (x : E) : 0 < radialZeta x := by
  dsimp [radialZeta]
  positivity

theorem radialZeta_le_one (x : E) : radialZeta x ≤ 1 := by
  dsimp [radialZeta]
  exact (inv_le_one₀ (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2)).2
    (by nlinarith [sq_nonneg ‖x‖])

/-- First identity in `(radial-identities)`. -/
theorem inner_radialGradient (u x : E) :
    ⟪x, radialGradient u x⟫_ℝ =
      radialCoordinate u x * radialZeta x := by
  let s : ℝ := 1 + ‖x‖ ^ 2
  let d : ℝ := Real.sqrt s
  have hs : 0 < s := by dsimp [s]; positivity
  have hd : 0 < d := by exact Real.sqrt_pos.2 hs
  have hd2 : d ^ 2 = s := by simpa [d] using Real.sq_sqrt hs.le
  rw [radialGradient, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [radialCoordinate_eq_inner_mul_sqrt_inv]
  dsimp [radialZeta]
  change d⁻¹ * ⟪x, u⟫_ℝ -
      (⟪u, x⟫_ℝ * s⁻¹ * d⁻¹) * ‖x‖ ^ 2 =
    (⟪u, x⟫_ℝ * d⁻¹) * s⁻¹
  rw [real_inner_comm x u]
  have hsx : ‖x‖ ^ 2 = s - 1 := by dsimp [s]; ring
  rw [hsx]
  field_simp
  ring

/-- The exact squared-norm identity in `(radial-identities)`. -/
theorem norm_radialGradient_sq {u : E} (hu : ‖u‖ = 1) (x : E) :
    ‖radialGradient u x‖ ^ 2 =
      radialZeta x *
        (1 - (radialCoordinate u x) ^ 2 -
          (radialCoordinate u x) ^ 2 * radialZeta x) := by
  let s : ℝ := 1 + ‖x‖ ^ 2
  let d : ℝ := Real.sqrt s
  have hs : 0 < s := by dsimp [s]; positivity
  have hd : 0 < d := by exact Real.sqrt_pos.2 hs
  have hd2 : d ^ 2 = s := by simpa [d] using Real.sq_sqrt hs.le
  rw [radialGradient, norm_sub_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, hu, mul_one,
    real_inner_smul_left, real_inner_smul_right]
  rw [radialCoordinate_eq_inner_mul_sqrt_inv]
  dsimp [radialZeta]
  change |d⁻¹| ^ 2 -
      2 * (d⁻¹ * (⟪u, x⟫_ℝ * s⁻¹ * d⁻¹ * ⟪u, x⟫_ℝ)) +
      (|⟪u, x⟫_ℝ * s⁻¹ * d⁻¹| * ‖x‖) ^ 2 =
    s⁻¹ * (1 - (⟪u, x⟫_ℝ * d⁻¹) ^ 2 -
      (⟪u, x⟫_ℝ * d⁻¹) ^ 2 * s⁻¹)
  rw [abs_of_pos (inv_pos.2 hd)]
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hs), abs_of_pos (inv_pos.2 hd)]
  have hsx : ‖x‖ ^ 2 = s - 1 := by dsimp [s]; ring
  field_simp
  nlinarith [hd2, hsx, sq_abs ⟪u, x⟫_ℝ]

/-- The feasible upper bound `ζ ≤ 1-q²`. -/
theorem radialZeta_le_one_sub_sq {u : E} (hu : ‖u‖ = 1) (x : E) :
    radialZeta x ≤ 1 - (radialCoordinate u x) ^ 2 := by
  let s : ℝ := 1 + ‖x‖ ^ 2
  let d : ℝ := Real.sqrt s
  have hs : 0 < s := by dsimp [s]; positivity
  have hd : 0 < d := Real.sqrt_pos.2 hs
  have hd2 : d ^ 2 = s := by simpa [d] using Real.sq_sqrt hs.le
  have hinner : ⟪u, x⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h := abs_real_inner_le_norm u x
    rw [hu, one_mul] at h
    calc
      ⟪u, x⟫_ℝ ^ 2 = |⟪u, x⟫_ℝ| ^ 2 := (sq_abs _).symm
      _ ≤ ‖x‖ ^ 2 := by nlinarith [abs_nonneg ⟪u, x⟫_ℝ, norm_nonneg x]
  rw [radialCoordinate_eq_inner_mul_sqrt_inv]
  dsimp [radialZeta]
  change s⁻¹ ≤ 1 - (⟪u, x⟫_ℝ * d⁻¹) ^ 2
  have hsx : ‖x‖ ^ 2 = s - 1 := by dsimp [s]; ring
  rw [hsx] at hinner
  field_simp
  nlinarith

theorem radialZeta_mul_norm_sq (x : E) :
    radialZeta x * ‖x‖ ^ 2 = 1 - radialZeta x := by
  dsimp [radialZeta]
  have hs : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Identities

section BarrierProfile

/-- The scalar profile obtained by minimizing the positive-alignment radial square in `ζ`. -/
noncomputable def radialBarrierProfile (q : ℝ) : ℝ :=
  ((1 - q ^ 2) ^ 2 - (33 / 16 : ℝ) * q) / Real.sqrt (1 - q ^ 2)

theorem radialBarrierProfile_at_threshold :
    radialBarrierProfile (9 / 32) = radialBarrierConstant := by
  rfl

theorem radialBarrierProfile_sq {q : ℝ} (hq : 0 < 1 - q ^ 2) :
    radialBarrierProfile q ^ 2 =
      ((1 - q ^ 2) ^ 2 - (33 / 16 : ℝ) * q) ^ 2 / (1 - q ^ 2) := by
  have hsqrt : Real.sqrt (1 - q ^ 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  dsimp [radialBarrierProfile]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hq.le]
  ring

theorem hasDerivAt_radialBarrierProfile {q : ℝ} (hq : 0 < 1 - q ^ 2) :
    HasDerivAt radialBarrierProfile
      ((-3 * q * (1 - q ^ 2) ^ 2 - (33 / 16 : ℝ)) /
        ((1 - q ^ 2) * Real.sqrt (1 - q ^ 2))) q := by
  have hA : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2) (-2 * q) q := by
    convert (hasDerivAt_const q 1).sub ((hasDerivAt_id q).pow 2) using 1
    · funext t
      simp
    · simp
  have hH : HasDerivAt
      (fun t : ℝ ↦ (1 - t ^ 2) ^ 2 - (33 / 16 : ℝ) * t)
      (2 * (1 - q ^ 2) * (-2 * q) - (33 / 16 : ℝ)) q := by
    convert (hA.pow 2).sub ((hasDerivAt_id q).const_mul (33 / 16 : ℝ)) using 1
    · funext t
      simp
    · simp
  have hS : HasDerivAt (fun t : ℝ ↦ Real.sqrt (1 - t ^ 2))
      ((-2 * q) / (2 * Real.sqrt (1 - q ^ 2))) q := by
    simpa [div_eq_mul_inv] using hA.sqrt hq.ne'
  have hsqrt : Real.sqrt (1 - q ^ 2) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  convert hH.div hS hsqrt using 1
  · funext t
    rfl
  · have hsqrtSq : (Real.sqrt (1 - q ^ 2)) ^ 2 = 1 - q ^ 2 :=
      Real.sq_sqrt hq.le
    field_simp [hsqrt]
    rw [hsqrtSq]
    ring

theorem radialBarrierProfile_strictAntiOn :
    StrictAntiOn radialBarrierProfile (Set.Icc (0 : ℝ) (9 / 32)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) (9 / 32))
  · intro q hq
    have hA : 0 < 1 - q ^ 2 := by
      have hq0 : 0 ≤ q := hq.1
      have hq1 : q ≤ 9 / 32 := hq.2
      nlinarith [mul_self_le_mul_self hq0 hq1]
    exact (hasDerivAt_radialBarrierProfile hA).continuousAt.continuousWithinAt
  · intro q hq
    have hqIoo : q ∈ Set.Ioo (0 : ℝ) (9 / 32) := by
      simpa [interior_Icc] using hq
    have hA : 0 < 1 - q ^ 2 := by
      nlinarith [mul_self_le_mul_self hqIoo.1.le hqIoo.2.le]
    rw [(hasDerivAt_radialBarrierProfile hA).deriv]
    have hden : 0 < (1 - q ^ 2) * Real.sqrt (1 - q ^ 2) :=
      mul_pos hA (Real.sqrt_pos.2 hA)
    have hnum : -3 * q * (1 - q ^ 2) ^ 2 - (33 / 16 : ℝ) < 0 := by
      have hnonneg : 0 ≤ 3 * q * (1 - q ^ 2) ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hqIoo.1.le) (sq_nonneg _)
      nlinarith
    exact div_neg_of_neg_of_pos hnum hden

theorem radialBarrierProfile_ge_constant {q : ℝ}
    (hq0 : 0 ≤ q) (hqb : q ≤ 9 / 32) :
    radialBarrierConstant ≤ radialBarrierProfile q := by
  rw [← radialBarrierProfile_at_threshold]
  by_cases h : q = 9 / 32
  · rw [h]
  · exact (radialBarrierProfile_strictAntiOn
      ⟨hq0, hqb⟩ ⟨by norm_num, le_rfl⟩ (lt_of_le_of_ne hqb h)).le

theorem radialBarrierConstant_lt_one : radialBarrierConstant < 1 := by
  have hanti := radialBarrierProfile_strictAntiOn
    (show (0 : ℝ) ∈ Set.Icc 0 (9 / 32) by norm_num)
    (show (9 / 32 : ℝ) ∈ Set.Icc 0 (9 / 32) by norm_num)
    (by norm_num : (0 : ℝ) < 9 / 32)
  rw [radialBarrierProfile_at_threshold] at hanti
  simpa [radialBarrierProfile] using hanti

end BarrierProfile

section CoefficientComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_smul_sub_smul_sq_sub
    (lam c : ℝ) (x g : E) :
    ‖lam • x - c • g‖ ^ 2 - ‖lam • x - g‖ ^ 2 =
      (c - 1) * ((c + 1) * ‖g‖ ^ 2 - 2 * lam * ⟪x, g⟫_ℝ) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left]
  nlinarith [sq_abs lam, sq_abs c]

/-- Multiplying the radial gradient by any `c ≥ 1` can only increase its distance from
`(33/16)x`, as long as the radial coordinate is at most the gate threshold `9/32`. -/
theorem radialGradient_coefficient_monotone
    {u : E} (hu : ‖u‖ = 1) (x : E) {c : ℝ} (hc : 1 ≤ c)
    (hq : radialCoordinate u x ≤ 9 / 32) :
    ‖(33 / 16 : ℝ) • x - radialGradient u x‖ ≤
      ‖(33 / 16 : ℝ) • x - c • radialGradient u x‖ := by
  let q : ℝ := radialCoordinate u x
  let z : ℝ := radialZeta x
  let g : E := radialGradient u x
  have hz : 0 < z := radialZeta_pos x
  have hzupper : z ≤ 1 - q ^ 2 := radialZeta_le_one_sub_sq hu x
  have hinner : ⟪x, g⟫_ℝ = q * z := inner_radialGradient u x
  have hg : ‖g‖ ^ 2 = z * (1 - q ^ 2 - q ^ 2 * z) :=
    norm_radialGradient_sq hu x
  have hbracket :
      0 ≤ (c + 1) * ‖g‖ ^ 2 - 2 * (33 / 16 : ℝ) * ⟪x, g⟫_ℝ := by
    rw [hinner]
    by_cases hq0 : q ≤ 0
    · have hg0 : 0 ≤ ‖g‖ ^ 2 := sq_nonneg ‖g‖
      have hc1 : 0 ≤ c + 1 := by linarith
      have hfirst : 0 ≤ (c + 1) * ‖g‖ ^ 2 := mul_nonneg hc1 hg0
      have hqz : q * z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq0 hz.le
      have hsecond : 0 ≤ -(2 * (33 / 16 : ℝ) * (q * z)) := by
        nlinarith
      linarith
    · have hqpos : 0 < q := lt_of_not_ge hq0
      have hqle : q ≤ 9 / 32 := hq
      have hqSq : q ^ 2 ≤ (9 / 32 : ℝ) ^ 2 := by
        nlinarith [mul_self_le_mul_self hqpos.le hqle]
      have hAq : 0 ≤ 1 - q ^ 2 := hz.le.trans hzupper
      have hAb : 0 ≤ 1 - (9 / 32 : ℝ) ^ 2 := by norm_num
      have hAorder : 1 - (9 / 32 : ℝ) ^ 2 ≤ 1 - q ^ 2 := by linarith
      have hAsq : (1 - (9 / 32 : ℝ) ^ 2) ^ 2 ≤ (1 - q ^ 2) ^ 2 := by
        nlinarith [mul_self_le_mul_self hAb hAorder]
      have hconst : 0 <
          (1 - (9 / 32 : ℝ) ^ 2) ^ 2 - (33 / 16 : ℝ) * (9 / 32) := by
        norm_num
      have hprofile : 0 < (1 - q ^ 2) ^ 2 - (33 / 16 : ℝ) * q := by
        nlinarith
      have hfactor : (1 - q ^ 2) ^ 2 ≤ 1 - q ^ 2 - q ^ 2 * z := by
        have hnonneg : 0 ≤ q ^ 2 * ((1 - q ^ 2) - z) :=
          mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hzupper)
        nlinarith
      have hgLower : z * (1 - q ^ 2) ^ 2 ≤ ‖g‖ ^ 2 := by
        rw [hg]
        exact mul_le_mul_of_nonneg_left hfactor hz.le
      have hcTwo : 2 ≤ c + 1 := by linarith
      have hscaled : 2 * ‖g‖ ^ 2 ≤ (c + 1) * ‖g‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcTwo (sq_nonneg ‖g‖)
      have hpositive : 0 ≤ 2 * z * ((1 - q ^ 2) ^ 2 - (33 / 16 : ℝ) * q) :=
        mul_nonneg (mul_nonneg (by norm_num) hz.le) hprofile.le
      nlinarith
  have hsq : ‖(33 / 16 : ℝ) • x - g‖ ^ 2 ≤
      ‖(33 / 16 : ℝ) • x - c • g‖ ^ 2 := by
    have hid := norm_smul_sub_smul_sq_sub (33 / 16 : ℝ) c x g
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hbracket]
  dsimp [g] at hsq ⊢
  nlinarith [norm_nonneg ((33 / 16 : ℝ) • x - radialGradient u x),
    norm_nonneg ((33 / 16 : ℝ) • x - c • radialGradient u x)]

/-- The full lower bound in Lemma `lem:radial-gradient` for coefficient one. -/
theorem radialGradient_barrier
    {u : E} (hu : ‖u‖ = 1) (x : E)
    (hq : radialCoordinate u x ≤ 9 / 32) :
    radialBarrierConstant ≤ ‖(33 / 16 : ℝ) • x - radialGradient u x‖ := by
  let q : ℝ := radialCoordinate u x
  let z : ℝ := radialZeta x
  let g : E := radialGradient u x
  let lam : ℝ := 33 / 16
  have hz : 0 < z := radialZeta_pos x
  have hzOne : z ≤ 1 := radialZeta_le_one x
  have hzupper : z ≤ 1 - q ^ 2 := radialZeta_le_one_sub_sq hu x
  have hinner : ⟪x, g⟫_ℝ = q * z := inner_radialGradient u x
  have hg : ‖g‖ ^ 2 = z * (1 - q ^ 2 - q ^ 2 * z) :=
    norm_radialGradient_sq hu x
  have hzgap : z * ‖x‖ ^ 2 = 1 - z := radialZeta_mul_norm_sq x
  have hnormsq : ‖lam • x - g‖ ^ 2 =
      lam ^ 2 * ‖x‖ ^ 2 - 2 * lam * q * z +
        z * (1 - q ^ 2 - q ^ 2 * z) := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ lam),
      real_inner_smul_left, hinner, hg]
    ring
  by_cases hq0 : q ≤ 0
  · have hfactor : z ^ 2 ≤ 1 - q ^ 2 - q ^ 2 * z := by
      have hnonneg : 0 ≤ (1 + z) * ((1 - q ^ 2) - z) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hzupper)
      nlinarith
    have hgLower : z ^ 3 ≤ ‖g‖ ^ 2 := by
      rw [hg]
      nlinarith [mul_le_mul_of_nonneg_left hfactor hz.le]
    have hcross : 0 ≤ -(2 * lam * q * z) := by
      have : q * z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq0 hz.le
      dsimp [lam]
      nlinarith
    have hmain : lam ^ 2 * ‖x‖ ^ 2 + z ^ 3 ≤ ‖lam • x - g‖ ^ 2 := by
      rw [hnormsq]
      rw [← hg]
      linarith
    have hbern : 1 - z ^ 3 ≤ 3 * (1 - z) := by
      have hnonneg : 0 ≤ (1 - z) ^ 2 * (z + 2) := by positivity
      nlinarith
    have hgap_le : 1 - z ≤ ‖x‖ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hzOne (sq_nonneg ‖x‖)
      rw [one_mul, hzgap] at hmul
      exact hmul
    have hscale : 3 * ‖x‖ ^ 2 ≤ lam ^ 2 * ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖x‖)
      norm_num [lam]
    have hone : 1 ≤ ‖lam • x - g‖ ^ 2 := by linarith
    have hnormOne : 1 ≤ ‖lam • x - g‖ := by
      nlinarith [norm_nonneg (lam • x - g)]
    exact (radialBarrierConstant_lt_one.le.trans hnormOne)
  · have hqpos : 0 < q := lt_of_not_ge hq0
    have hqle : q ≤ 9 / 32 := hq
    let A : ℝ := 1 - q ^ 2
    let H : ℝ := A ^ 2 - lam * q
    have hA : 0 < A := by
      dsimp [A]
      nlinarith [mul_self_le_mul_self hqpos.le hqle]
    have hAOne : A ≤ 1 := by dsimp [A]; nlinarith [sq_nonneg q]
    have hzA : z ≤ A := hzupper
    have hr2 : ‖x‖ ^ 2 = z⁻¹ - 1 := by
      calc
        ‖x‖ ^ 2 = (1 - z) / z := by
          apply (eq_div_iff hz.ne').2
          nlinarith [hzgap]
        _ = z⁻¹ - 1 := by field_simp
    have hAzPos : 0 < A * z := mul_pos hA hz
    have hAzOne : A * z ≤ 1 := by
      calc
        A * z ≤ 1 * 1 := mul_le_mul hAOne hzOne hz.le (by norm_num)
        _ = 1 := by ring
    have hInv : 1 ≤ (A * z)⁻¹ := (one_le_inv₀ hAzPos).2 hAzOne
    have hLamDiv : lam ^ 2 ≤ lam ^ 2 / (A * z) := by
      rw [div_eq_mul_inv]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hInv (sq_nonneg lam)
    have hcore : 0 ≤ lam ^ 2 / (A * z) - A := by
      have : 1 < lam ^ 2 := by norm_num [lam]
      linarith
    have hbracket : 0 ≤
        lam ^ 2 / (A * z) + 2 * lam * q - A + q ^ 2 * (z + A) := by
      have hqterm : 0 ≤ 2 * lam * q := by positivity
      have hsquareTerm : 0 ≤ q ^ 2 * (z + A) :=
        mul_nonneg (sq_nonneg q) (by positivity)
      linarith
    have hfactorEq :
        (lam ^ 2 * (z⁻¹ - 1) - 2 * lam * q * z +
            z * (A - q ^ 2 * z)) - H ^ 2 / A =
          (A - z) *
            (lam ^ 2 / (A * z) + 2 * lam * q - A + q ^ 2 * (z + A)) := by
      have hA0 : 1 - q ^ 2 ≠ 0 := by
        dsimp [A] at hA
        exact hA.ne'
      dsimp [A, H]
      field_simp [hA0, hz.ne']
      ring
    have hprofileSq : radialBarrierProfile q ^ 2 = H ^ 2 / A := by
      simpa [A, H, lam] using radialBarrierProfile_sq hA
    have hsquareLower : radialBarrierProfile q ^ 2 ≤ ‖lam • x - g‖ ^ 2 := by
      rw [hprofileSq, hnormsq, hr2]
      have hprod := mul_nonneg (sub_nonneg.mpr hzA) hbracket
      dsimp [A] at hfactorEq ⊢
      linarith
    have hconstPos : 0 < radialBarrierConstant :=
      (by linarith [radialBarrierConstant_gt] : 0 < radialBarrierConstant)
    have hprofileGe : radialBarrierConstant ≤ radialBarrierProfile q :=
      radialBarrierProfile_ge_constant hqpos.le hqle
    have hprofilePos : 0 < radialBarrierProfile q := hconstPos.trans_le hprofileGe
    have hprofileNorm : radialBarrierProfile q ≤ ‖lam • x - g‖ := by
      nlinarith [norm_nonneg (lam • x - g)]
    exact hprofileGe.trans hprofileNorm

/-- Lemma `lem:radial-gradient` with the manuscript's arbitrary coefficient `c ≥ 1`. -/
theorem radialGradient_comparison
    {u : E} (hu : ‖u‖ = 1) (x : E) {c : ℝ} (hc : 1 ≤ c)
    (hq : radialCoordinate u x ≤ 9 / 32) :
    ‖(33 / 16 : ℝ) • x - radialGradient u x‖ ≤
        ‖(33 / 16 : ℝ) • x - c • radialGradient u x‖ ∧
      radialBarrierConstant ≤ ‖(33 / 16 : ℝ) • x - radialGradient u x‖ :=
  ⟨radialGradient_coefficient_monotone hu x hc hq,
    radialGradient_barrier hu x hq⟩

theorem radialCoordinateGradient_comparison
    {u : E} (hu : ‖u‖ = 1) (x : E) {c : ℝ} (hc : 1 ≤ c)
    (hq : radialCoordinate u x ≤ 9 / 32) :
    ‖(33 / 16 : ℝ) • x - radialCoordinateGradient u x‖ ≤
        ‖(33 / 16 : ℝ) • x - c • radialCoordinateGradient u x‖ ∧
      (5 / 18 : ℝ) < ‖(33 / 16 : ℝ) • x - radialCoordinateGradient u x‖ := by
  rw [← radialGradient_eq]
  refine ⟨(radialGradient_comparison hu x hc hq).1, ?_⟩
  exact radialBarrierConstant_gt.trans_le (radialGradient_comparison hu x hc hq).2

/-- The dimension-free first-derivative bound in Lemma `lem:radial-third`. -/
theorem norm_radialCoordinateGradient_le_one
    {u : E} (hu : ‖u‖ = 1) (x : E) :
    ‖radialCoordinateGradient u x‖ ≤ 1 := by
  rw [← radialGradient_eq]
  let q : ℝ := radialCoordinate u x
  let z : ℝ := radialZeta x
  let g : E := radialGradient u x
  have hz : 0 < z := radialZeta_pos x
  have hzOne : z ≤ 1 := radialZeta_le_one x
  have hg : ‖g‖ ^ 2 = z * (1 - q ^ 2 - q ^ 2 * z) :=
    norm_radialGradient_sq hu x
  have hfactor : 1 - q ^ 2 - q ^ 2 * z ≤ 1 := by
    have : 0 ≤ q ^ 2 * (1 + z) := mul_nonneg (sq_nonneg q) (by positivity)
    nlinarith
  have hsq : ‖g‖ ^ 2 ≤ 1 := by
    calc
      ‖g‖ ^ 2 = z * (1 - q ^ 2 - q ^ 2 * z) := hg
      _ ≤ z * 1 := mul_le_mul_of_nonneg_left hfactor hz.le
      _ ≤ 1 := by simpa using hzOne
  dsimp [g] at hsq ⊢
  nlinarith [norm_nonneg (radialGradient u x)]

end CoefficientComparison

end NCConcave16991.DenseSmooth
