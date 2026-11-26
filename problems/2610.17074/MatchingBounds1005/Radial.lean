import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The actual radial confinement map from `ana:thm:confinement`.

All definitions below are concrete functions on real inner-product spaces.
The derivative formula is proved by the chain and product rules.
-/

namespace MatchingBounds1005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radialScale (R : ℝ) (x : E) : ℝ :=
  (Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2))⁻¹

noncomputable def radial (R : ℝ) (x : E) : E := radialScale R x • x

omit [InnerProductSpace ℝ E] in
theorem radial_argument_pos (R : ℝ) (x : E) : 0 < 1 + ‖x‖ ^ 2 / R ^ 2 := by
  positivity

omit [InnerProductSpace ℝ E] in
theorem radialScale_pos (R : ℝ) (x : E) : 0 < radialScale R x := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (radial_argument_pos R x))

omit [InnerProductSpace ℝ E] in
theorem radialScale_le_one (R : ℝ) (x : E) : radialScale R x ≤ 1 := by
  unfold radialScale
  have hs : 1 ≤ Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt (radial_argument_pos R x))]
    have h : 0 ≤ ‖x‖ ^ 2 / R ^ 2 := by positivity
    nlinarith
  exact inv_le_one_of_one_le₀ hs

omit [InnerProductSpace ℝ E] in
theorem radialScale_sq_identity (R : ℝ) (x : E) :
    radialScale R x ^ 2 * (1 + ‖x‖ ^ 2 / R ^ 2) = 1 := by
  have hs := Real.sq_sqrt (radial_argument_pos R x).le
  have hn : Real.sqrt (1 + ‖x‖ ^ 2 / R ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (radial_argument_pos R x))
  unfold radialScale
  rw [← hs]
  field_simp

omit [InnerProductSpace ℝ E] in
theorem radialScale_cubic_identity (R : ℝ) (x : E) :
    radialScale R x - radialScale R x ^ 3 / R ^ 2 * ‖x‖ ^ 2 =
      radialScale R x ^ 3 := by
  have h := congrArg (fun t : ℝ => radialScale R x * t) (radialScale_sq_identity R x)
  dsimp at h
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith [h]

theorem radial_norm (R : ℝ) (x : E) : ‖radial R x‖ = radialScale R x * ‖x‖ := by
  rw [radial, norm_smul, Real.norm_eq_abs, abs_of_pos (radialScale_pos R x)]

theorem radial_norm_le (R : ℝ) (x : E) : ‖radial R x‖ ≤ ‖x‖ := by
  rw [radial_norm]
  simpa using mul_le_mul_of_nonneg_right (radialScale_le_one R x) (norm_nonneg x)

/-- Every finite point is sent strictly inside the radius-`R` ball. -/
theorem radial_norm_lt {R : ℝ} (hR : 0 < R) (x : E) : ‖radial R x‖ < R := by
  have hsq := radialScale_sq_identity R x
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hid : radialScale R x ^ 2 * (R ^ 2 + ‖x‖ ^ 2) = R ^ 2 := by
    field_simp at hsq
    nlinarith
  have hpos : 0 < radialScale R x ^ 2 * R ^ 2 := by
    exact mul_pos (sq_pos_of_pos (radialScale_pos R x)) (sq_pos_of_pos hR)
  rw [radial_norm]
  nlinarith [mul_nonneg (radialScale_pos R x).le (norm_nonneg x)]

noncomputable def radialDerivative (R : ℝ) (x : E) : E →L[ℝ] E :=
  radialScale R x • ContinuousLinearMap.id ℝ E -
    (radialScale R x ^ 3 / R ^ 2) • (innerSL ℝ x).smulRight x

theorem radialDerivative_apply (R : ℝ) (x v : E) :
    radialDerivative R x v = radialScale R x • v -
      (radialScale R x ^ 3 / R ^ 2 * inner (𝕜 := ℝ) x v) • x := by
  simp [radialDerivative, smul_smul]

/-- Exact Fréchet derivative of the scalar factor. -/
theorem radialScale_hasFDerivAt (R : ℝ) (x : E) :
    HasFDerivAt (radialScale R : E → ℝ)
      ((-(radialScale R x ^ 3) / R ^ 2) • innerSL ℝ x) x := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hb : HasFDerivAt (fun y : E => 1 + ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := by
    convert (hn.const_smul ((R ^ 2)⁻¹)).const_add 1 using 1
    funext y
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hs := hb.sqrt (ne_of_gt (radial_argument_pos R x))
  have hr := (hasDerivAt_inv
    (ne_of_gt (Real.sqrt_pos.mpr (radial_argument_pos R x)))).comp_hasFDerivAt x hs
  convert hr using 1
  ext v
  simp [radialScale, smul_smul, div_eq_mul_inv]
  ring

/-- Exact Fréchet derivative of the actual nonlinear radial map. -/
theorem radial_hasFDerivAt (R : ℝ) (x : E) :
    HasFDerivAt (radial R : E → E) (radialDerivative R x) x := by
  have h := (radialScale_hasFDerivAt R x).smul (hasFDerivAt_id x)
  convert h using 1
  ext v
  simp [radialDerivative, smul_smul, sub_eq_add_neg, neg_smul, add_comm,
    neg_div, neg_mul]

theorem radial_fderiv (R : ℝ) (x : E) :
    fderiv ℝ (radial R : E → E) x = radialDerivative R x :=
  (radial_hasFDerivAt R x).fderiv

/-- The smallest stretching factor is at least the cube of the scalar
radial factor, with no restriction on the query norm. -/
theorem radialDerivative_norm_lower (R : ℝ) (x v : E) :
    radialScale R x ^ 3 * ‖v‖ ≤ ‖radialDerivative R x v‖ := by
  have hcoeff : 0 ≤ radialScale R x ^ 3 / R ^ 2 := by
    exact div_nonneg (pow_nonneg (radialScale_pos R x).le _) (sq_nonneg R)
  have hcs : inner (𝕜 := ℝ) x v ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := abs_real_inner_le_norm x v
    have hs := sq_abs (inner (𝕜 := ℝ) x v)
    nlinarith [abs_nonneg (inner (𝕜 := ℝ) x v), norm_nonneg x, norm_nonneg v]
  have hmul := mul_le_mul_of_nonneg_left hcs hcoeff
  have heq : inner (𝕜 := ℝ) (radialDerivative R x v) v =
      radialScale R x * ‖v‖ ^ 2 -
        (radialScale R x ^ 3 / R ^ 2) * inner (𝕜 := ℝ) x v ^ 2 := by
    rw [radialDerivative_apply, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hid := congrArg (fun t : ℝ => t * ‖v‖ ^ 2) (radialScale_cubic_identity R x)
  dsimp at hid
  have hlo : radialScale R x ^ 3 * ‖v‖ ^ 2 ≤
      inner (𝕜 := ℝ) (radialDerivative R x v) v := by
    rw [heq]
    nlinarith [hmul, hid]
  have hup := real_inner_le_norm (radialDerivative R x v) v
  by_cases hz : ‖v‖ = 0
  · simp [hz]
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hz)
    nlinarith

/-- The derivative is a contraction, more precisely with norm at most the
scalar radial factor. -/
theorem radialDerivative_norm_upper (R : ℝ) (x v : E) :
    ‖radialDerivative R x v‖ ≤ radialScale R x * ‖v‖ := by
  let q := radialScale R x
  let c := q ^ 3 / R ^ 2
  let b := inner (𝕜 := ℝ) x v
  have hq : 0 < q := radialScale_pos R x
  have hc : 0 ≤ c := div_nonneg (pow_nonneg hq.le _) (sq_nonneg R)
  have hid : q - c * ‖x‖ ^ 2 = q ^ 3 := radialScale_cubic_identity R x
  have heq : ‖radialDerivative R x v‖ ^ 2 =
      q ^ 2 * ‖v‖ ^ 2 - c * (q + q ^ 3) * b ^ 2 := by
    rw [radialDerivative_apply, norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm x v]
    change q ^ 2 * ‖v‖ ^ 2 - 2 * (c * b * (q * b)) +
      c ^ 2 * b ^ 2 * ‖x‖ ^ 2 = _
    have hm := congrArg (fun t : ℝ => c * b ^ 2 * t) hid
    dsimp at hm
    nlinarith [hm]
  have hd : 0 ≤ c * (q + q ^ 3) * b ^ 2 := by positivity
  have hn : 0 ≤ q * ‖v‖ := mul_nonneg hq.le (norm_nonneg v)
  change ‖radialDerivative R x v‖ ≤ q * ‖v‖
  nlinarith [norm_nonneg (radialDerivative R x v)]

theorem radial_fderiv_norm_le_one (R : ℝ) (x : E) :
    ‖fderiv ℝ (radial R : E → E) x‖ ≤ 1 := by
  rw [radial_fderiv]
  apply (radialDerivative R x).opNorm_le_bound (by norm_num)
  intro v
  exact (radialDerivative_norm_upper R x v).trans
    (mul_le_mul_of_nonneg_right (radialScale_le_one R x) (norm_nonneg v))

omit [InnerProductSpace ℝ E] in
theorem radialScale_inside {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    1 / (2 * Real.sqrt 2) ≤ radialScale R x ^ 3 := by
  have hr : ‖x‖ ^ 2 / R ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hR)).mpr
    nlinarith [norm_nonneg x]
  have hq := radialScale_pos R x
  have hi := radialScale_sq_identity R x
  have hsq : (1 / 2 : ℝ) ≤ radialScale R x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (sq_nonneg (radialScale R x))]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hl : Real.sqrt 2 / 2 ≤ radialScale R x := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hq.le
  have he : (1 : ℝ) / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
    field_simp
    nlinarith
  rw [he]
  nlinarith [hm]

/-- The manuscript's `1 / (2 sqrt 2)` lower singular-value bound inside
the confinement radius, stated directly as an inequality for every vector. -/
theorem radial_fderiv_inside {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R)
    (v : E) : (1 / (2 * Real.sqrt 2)) * ‖v‖ ≤ ‖fderiv ℝ (radial R) x v‖ := by
  rw [radial_fderiv]
  exact (mul_le_mul_of_nonneg_right (radialScale_inside hR hx) (norm_nonneg v)).trans
    (radialDerivative_norm_lower R x v)

theorem radialDerivative_self (R : ℝ) (x : E) :
    radialDerivative R x x = radialScale R x ^ 3 • x := by
  rw [radialDerivative_apply, real_inner_self_eq_norm_sq, ← sub_smul,
    radialScale_cubic_identity]

theorem radialDerivative_symmetric (R : ℝ) (x v w : E) :
    inner (𝕜 := ℝ) (radialDerivative R x v) w =
      inner (𝕜 := ℝ) v (radialDerivative R x w) := by
  simp only [radialDerivative_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v x]
  ring

/-- The radial pairing identity used in the exterior stationarity argument. -/
theorem radial_fderiv_radial_pairing (R : ℝ) (x v : E) :
    inner (𝕜 := ℝ) x (fderiv ℝ (radial R) x v) =
      radialScale R x ^ 3 * inner (𝕜 := ℝ) x v := by
  rw [radial_fderiv, ← radialDerivative_symmetric, radialDerivative_self,
    real_inner_smul_left]

/-- The confinement map is smooth to every finite order and to order infinity. -/
theorem radial_contDiff (R : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (radial R : E → E) := by
  have hb : ContDiff ℝ n (fun x : E => 1 + ‖x‖ ^ 2 / R ^ 2) := by
    convert (contDiff_const : ContDiff ℝ n (fun _ : E => (1 : ℝ))).add
      ((contDiff_norm_sq ℝ (E := E) (n := n)).const_smul ((R ^ 2)⁻¹)) using 1
    funext y
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hs := hb.sqrt (fun x => ne_of_gt (radial_argument_pos R x))
  have hr := hs.inv (fun x => ne_of_gt (Real.sqrt_pos.mpr (radial_argument_pos R x)))
  exact hr.smul contDiff_id

end MatchingBounds1005
