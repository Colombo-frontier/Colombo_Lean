import LeanArticleAudit.Pilot.Model

open Set
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def correctionConstant (p : ℕ) : ℝ :=
  ((2 * p + 1 : ℕ) : ℝ) * (3 : ℝ) ^ p / p.factorial

theorem monotone_normal_pair_nonneg
    (X : Set E) (G : E → E) (y z n : E)
    (hy : y ∈ X) (hz : z ∈ X)
    (hmono : ∀ a ∈ X, ∀ b ∈ X,
      0 ≤ inner ℝ (G a - G b) (a - b))
    (hzvi : ∀ w ∈ X, 0 ≤ inner ℝ (G z) (w - z))
    (hn : n ∈ normalCone X y) :
    0 ≤ inner ℝ (G y + n) (y - z) := by
  have hG := hmono y hy z hz
  have hsol := hzvi y hy
  have hnormal := hn z hz
  rw [show z - y = -(y - z) by abel, inner_neg_right] at hnormal
  simp only [inner_add_left, inner_sub_left] at hG ⊢
  linarith

theorem correction_radius_scalar
    (p : ℕ) (hp : 2 ≤ p) (c q r : ℝ)
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r)
    (hkey : (2 * (p : ℝ) * c) * q ^ p * (q - r) ≤
      c * q ^ p * (q + r)) :
    q ≤ 3 * r := by
  have hqp : 0 < q ^ p := pow_pos hq p
  have hpc : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hfac : 0 < c * q ^ p := mul_pos hc hqp
  have hratio : (2 * (p : ℝ)) * (q - r) ≤ q + r := by
    nlinarith
  nlinarith

theorem modelCorrection_bounds
    (X : Set E) (G : E → E) (p : ℕ) (hp : 2 ≤ p)
    (Lp r : ℝ) (hLp : 0 < Lp)
    (x y zStar n err : E)
    (hy : y ∈ X) (hz : zStar ∈ X)
    (hzvi : ∀ w ∈ X, 0 ≤ inner ℝ (G zStar) (w - zStar))
    (hmono : ∀ a ∈ X, ∀ b ∈ X,
      0 ≤ inner ℝ (G a - G b) (a - b))
    (hradius : ‖x - zStar‖ ≤ r)
    (hn : n ∈ normalCone X y)
    (hmodel : G y + n = err -
      ((2 * (p : ℝ) / p.factorial) * Lp * ‖y - x‖ ^ (p - 1)) • (y - x))
    (htaylor : ‖err‖ ≤ Lp / p.factorial * ‖y - x‖ ^ p) :
    ‖y - x‖ ≤ 3 * r ∧
      ‖G y + n‖ ≤ correctionConstant p * Lp * r ^ p := by
  let s := y - x
  let q := ‖s‖
  let c := Lp / p.factorial
  have hfact : (0 : ℝ) < p.factorial := by positivity
  have hc : 0 < c := div_pos hLp hfact
  have hpair : 0 ≤ inner ℝ (G y + n) (y - zStar) :=
    monotone_normal_pair_nonneg X G y zStar n hy hz hmono hzvi hn
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hradius
  have hstep : ‖y - x‖ ≤ 3 * r := by
    by_cases hq0 : q = 0
    · simpa [q, s, hq0] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hr0
    · have hq : 0 < q := lt_of_le_of_ne (norm_nonneg s) (Ne.symm hq0)
      have hinner_lower : q ^ 2 - q * r ≤ inner ℝ s (y - zStar) := by
        have hdist : ‖x - zStar‖ ≤ r := hradius
        have hcs : -(‖s‖ * ‖x - zStar‖) ≤ inner ℝ s (x - zStar) := by
          exact neg_le_of_abs_le (abs_real_inner_le_norm s (x - zStar))
        have hsr : -(q * r) ≤ inner ℝ s (x - zStar) := by
          dsimp [q]
          nlinarith [norm_nonneg s]
        rw [show y - zStar = s + (x - zStar) by simp only [s]; abel,
          inner_add_right]
        rw [real_inner_self_eq_norm_sq]
        linarith
      have hdist_upper : ‖y - zStar‖ ≤ q + r := by
        calc
          ‖y - zStar‖ = ‖s + (x - zStar)‖ := by
            congr 1
            simp only [s]
            abel
          _ ≤ ‖s‖ + ‖x - zStar‖ := norm_add_le _ _
          _ ≤ q + r := by dsimp [q]; linarith
      have herr_inner : inner ℝ err (y - zStar) ≤
          c * q ^ p * (q + r) := by
        calc
          inner ℝ err (y - zStar) ≤ ‖err‖ * ‖y - zStar‖ :=
            real_inner_le_norm _ _
          _ ≤ (c * q ^ p) * (q + r) := by
            have he : ‖err‖ ≤ c * q ^ p := by simpa [c, q, s] using htaylor
            exact mul_le_mul he hdist_upper (norm_nonneg _) (by positivity)
      have hbeta : 0 ≤ (2 * (p : ℝ) * c) * q ^ (p - 1) := by positivity
      have hraw : (2 * (p : ℝ) * c) * q ^ (p - 1) *
          (q ^ 2 - q * r) ≤ c * q ^ p * (q + r) := by
        have hpairs : 0 ≤ inner ℝ
            (err - ((2 * (p : ℝ) * c) * q ^ (p - 1)) • s)
            (y - zStar) := by
          have hcoefmodel : (2 * (p : ℝ) / p.factorial) * Lp *
              ‖y - x‖ ^ (p - 1) =
              (2 * (p : ℝ) * c) * q ^ (p - 1) := by
            dsimp [c, q, s]
            ring
          rw [hmodel, hcoefmodel] at hpair
          simpa [s] using hpair
        simp only [inner_sub_left, real_inner_smul_left] at hpairs
        have hmul := mul_le_mul_of_nonneg_left hinner_lower hbeta
        linarith
      have hpow : q ^ (p - 1) * q = q ^ p := by
        rw [← pow_succ]
        congr
        omega
      have hkey : (2 * (p : ℝ) * c) * q ^ p * (q - r) ≤
          c * q ^ p * (q + r) := by
        calc
          (2 * (p : ℝ) * c) * q ^ p * (q - r) =
              (2 * (p : ℝ) * c) * q ^ (p - 1) *
                (q ^ 2 - q * r) := by rw [← hpow]; ring
          _ ≤ c * q ^ p * (q + r) := hraw
      simpa [q, s] using correction_radius_scalar p hp c q r hc hq hr0 hkey
  refine ⟨hstep, ?_⟩
  have hv : ‖G y + n‖ ≤ (2 * (p : ℝ) + 1) * c * ‖y - x‖ ^ p := by
    rw [hmodel]
    calc
      ‖err - ((2 * (p : ℝ) / p.factorial) * Lp *
          ‖y - x‖ ^ (p - 1)) • (y - x)‖ ≤
          ‖err‖ + ‖((2 * (p : ℝ) / p.factorial) * Lp *
            ‖y - x‖ ^ (p - 1)) • (y - x)‖ := norm_sub_le _ _
      _ ≤ c * ‖y - x‖ ^ p +
          (2 * (p : ℝ) * c) * ‖y - x‖ ^ p := by
            rw [norm_smul, Real.norm_eq_abs]
            have hcoef : 0 ≤ (2 * (p : ℝ) / p.factorial) * Lp := by positivity
            rw [abs_of_nonneg (mul_nonneg hcoef (pow_nonneg (norm_nonneg _) _))]
            have hpow : ‖y - x‖ ^ (p - 1) * ‖y - x‖ = ‖y - x‖ ^ p := by
              rw [← pow_succ]
              congr
              omega
            have he : ‖err‖ ≤ c * ‖y - x‖ ^ p := by simpa [c] using htaylor
            have hcoefeq : (2 * (p : ℝ) / p.factorial) * Lp =
                2 * (p : ℝ) * c := by dsimp [c]; ring
            have hterm : (2 * (p : ℝ) / p.factorial) * Lp *
                ‖y - x‖ ^ (p - 1) * ‖y - x‖ =
                (2 * (p : ℝ) * c) * ‖y - x‖ ^ p := by
              rw [hcoefeq]
              calc
                2 * (p : ℝ) * c * ‖y - x‖ ^ (p - 1) * ‖y - x‖ =
                    (2 * (p : ℝ) * c) *
                      (‖y - x‖ ^ (p - 1) * ‖y - x‖) := by ring
                _ = _ := by rw [hpow]
            rw [hterm]
            linarith
      _ = (2 * (p : ℝ) + 1) * c * ‖y - x‖ ^ p := by ring
  have hpowstep : ‖y - x‖ ^ p ≤ (3 * r) ^ p :=
    pow_le_pow_left₀ (norm_nonneg _) hstep p
  calc
    ‖G y + n‖ ≤ (2 * (p : ℝ) + 1) * c * ‖y - x‖ ^ p := hv
    _ ≤ (2 * (p : ℝ) + 1) * c * (3 * r) ^ p := by gcongr <;> positivity
    _ = correctionConstant p * Lp * r ^ p := by
      dsimp [correctionConstant, c]
      norm_num [Nat.cast_add, Nat.cast_mul, mul_pow]
      ring




/-- Source-facing headline for `lem:correction`.  The model-existence and
Taylor lemmas supply `hn`, `hmodel`, and `htaylor`; all remaining geometry and
the exact constant `A_p` are proved here. -/
theorem lem_correction
    (X : Set E) (G : E → E) (p : ℕ) (hp : 2 ≤ p)
    (Lp r : ℝ) (hLp : 0 < Lp)
    (x y zStar n err : E)
    (hy : y ∈ X) (hz : zStar ∈ X)
    (hzvi : ∀ w ∈ X, 0 ≤ inner ℝ (G zStar) (w - zStar))
    (hmono : ∀ a ∈ X, ∀ b ∈ X,
      0 ≤ inner ℝ (G a - G b) (a - b))
    (hradius : ‖x - zStar‖ ≤ r)
    (hn : n ∈ normalCone X y)
    (hmodel : G y + n = err -
      ((2 * (p : ℝ) / p.factorial) * Lp * ‖y - x‖ ^ (p - 1)) • (y - x))
    (htaylor : ‖err‖ ≤ Lp / p.factorial * ‖y - x‖ ^ p) :
    ‖y - x‖ ≤ 3 * r ∧
      ‖G y + n‖ ≤ correctionConstant p * Lp * r ^ p :=
  modelCorrection_bounds X G p hp Lp r hLp x y zStar n err hy hz hzvi hmono
    hradius hn hmodel htaylor

theorem projection_step_energy
    (x y xp u Gy : E) (lambda : ℝ)
    (hproj : inner ℝ (x - lambda • Gy - xp) (u - xp) ≤ 0) :
    2 * lambda * inner ℝ Gy (y - u) ≤
      ‖x - u‖ ^ 2 - ‖xp - u‖ ^ 2 - ‖xp - x‖ ^ 2 +
        2 * lambda * inner ℝ Gy (y - xp) := by
  have henergy : 2 * lambda * inner ℝ Gy (xp - u) ≤
      ‖x - u‖ ^ 2 - ‖xp - u‖ ^ 2 - ‖xp - x‖ ^ 2 := by
    have hinner : lambda * inner ℝ Gy (xp - u) ≤
        inner ℝ (x - xp) (xp - u) := by
      rw [show xp - u = -(u - xp) by abel, inner_neg_right, inner_neg_right]
      simp only [inner_sub_left, real_inner_smul_left] at hproj ⊢
      linarith
    have hid : ‖x - u‖ ^ 2 - ‖xp - u‖ ^ 2 - ‖xp - x‖ ^ 2 =
        2 * inner ℝ (x - xp) (xp - u) := by
      rw [show x - u = (x - xp) + (xp - u) by abel, norm_add_sq_real]
      rw [show xp - x = -(x - xp) by abel, norm_neg]
      ring
    rw [hid]
    linarith
  rw [show y - u = (y - xp) + (xp - u) by abel, inner_add_right]
  linarith

theorem relative_error_quadratic
    (s a b e : E) (hs : s = a + b) (he : ‖e‖ ≤ ‖s‖ / 2) :
    -‖a‖ ^ 2 + 2 * inner ℝ (-s + e) b ≤ -(3 / 4 : ℝ) * ‖s‖ ^ 2 := by
  have hyoung : 2 * inner ℝ e b ≤ ‖e‖ ^ 2 + ‖b‖ ^ 2 := by
    have hnonneg : 0 ≤ ‖e - b‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at hnonneg
    linarith
  have he0 : 0 ≤ ‖e‖ := norm_nonneg _
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg _
  have hesq : ‖e‖ ^ 2 ≤ (‖s‖ / 2) ^ 2 := by nlinarith
  subst s
  have hesq4 : 4 * ‖e‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by nlinarith
  rw [norm_add_sq_real] at hesq4
  rw [norm_add_sq_real]
  simp only [inner_add_left, inner_neg_left]
  rw [real_inner_self_eq_norm_sq]
  nlinarith

/-- Source-facing algebraic core of `lem:teg-energy`.  `hprojection` is the
standard variational characterization of `xp = Proj (x - lambda • G y)`, and
`hrelative` is exactly Equation `eq:teg-relative`. -/
theorem tensorExtragradient_energy
    (X : Set E) (G : E → E) (x y xp u n err : E) (lambda : ℝ)
    (hy : y ∈ X) (hxp : xp ∈ X) (hu : u ∈ X)
    (hlambda : 0 ≤ lambda)
    (hn : n ∈ normalCone X y)
    (hprojection : inner ℝ (x - lambda • G y - xp) (u - xp) ≤ 0)
    (hrelative : lambda • (G y + n) = -(y - x) + err)
    (herr : ‖err‖ ≤ ‖y - x‖ / 2) :
    2 * lambda * inner ℝ (G y) (y - u) ≤
      ‖x - u‖ ^ 2 - ‖xp - u‖ ^ 2 - (3 / 4 : ℝ) * ‖y - x‖ ^ 2 := by
  have hbase := projection_step_energy x y xp u (G y) lambda hprojection
  have hn' : 0 ≤ inner ℝ n (y - xp) := by
    have := hn xp hxp
    rw [show xp - y = -(y - xp) by abel, inner_neg_right] at this
    linarith
  have hv : lambda * inner ℝ (G y) (y - xp) ≤
      inner ℝ (lambda • (G y + n)) (y - xp) := by
    simp only [inner_add_left, real_inner_smul_left]
    nlinarith
  let s := y - x
  let a := xp - x
  let b := y - xp
  have hs : s = a + b := by simp only [s, a, b]; abel
  have hquad := relative_error_quadratic s a b err hs (by simpa [s] using herr)
  have htail : -‖xp - x‖ ^ 2 +
      2 * lambda * inner ℝ (G y) (y - xp) ≤
      -(3 / 4 : ℝ) * ‖y - x‖ ^ 2 := by
    calc
      -‖xp - x‖ ^ 2 + 2 * lambda * inner ℝ (G y) (y - xp) ≤
          -‖xp - x‖ ^ 2 + 2 * inner ℝ (lambda • (G y + n)) (y - xp) := by
            linarith
      _ = -‖a‖ ^ 2 + 2 * inner ℝ (-s + err) b := by
            rw [hrelative]
      _ ≤ -(3 / 4 : ℝ) * ‖s‖ ^ 2 := hquad
      _ = -(3 / 4 : ℝ) * ‖y - x‖ ^ 2 := by rfl
  exact le_trans hbase (by linarith)



theorem tensorExtragradient_relative_from_model
    (p : ℕ) (hp : 2 ≤ p) (Lp : ℝ) (hLp : 0 < Lp)
    (G : E → E) (x y n err : E) (hxy : y ≠ x)
    (hmodel : G y + n = err -
      ((2 * (p : ℝ) / p.factorial) * Lp * ‖y - x‖ ^ (p - 1)) • (y - x))
    (htaylor : ‖err‖ ≤ Lp / p.factorial * ‖y - x‖ ^ p) :
    let beta := (2 * (p : ℝ) / p.factorial) * Lp
    let lambda := 1 / (beta * ‖y - x‖ ^ (p - 1))
    0 ≤ lambda ∧
      lambda • (G y + n) = -(y - x) + lambda • err ∧
      ‖lambda • err‖ ≤ ‖y - x‖ / 2 := by
  dsimp
  let q := ‖y - x‖
  let c := Lp / p.factorial
  let beta := 2 * (p : ℝ) * c
  have hq : 0 < q := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hden : 0 < beta * q ^ (p - 1) := mul_pos hbeta (pow_pos hq _)
  have hbeta_eq : (2 * (p : ℝ) / p.factorial) * Lp = beta := by
    dsimp [beta, c]
    ring
  have hlambda : 0 ≤ 1 / (beta * q ^ (p - 1)) := (one_div_pos.mpr hden).le
  have hscale : (1 / (beta * q ^ (p - 1))) *
      (beta * q ^ (p - 1)) = 1 := by field_simp
  refine ⟨by simpa [beta, q, hbeta_eq] using hlambda, ?_, ?_⟩
  · rw [hmodel, smul_sub, smul_smul]
    rw [hbeta_eq]
    change (1 / (beta * q ^ (p - 1))) • err -
        ((1 / (beta * q ^ (p - 1))) * (beta * q ^ (p - 1))) • (y - x) = _
    rw [hscale, one_smul]
    abel
  · rw [norm_smul, Real.norm_eq_abs, hbeta_eq]
    change |1 / (beta * q ^ (p - 1))| * ‖err‖ ≤ q / 2
    rw [abs_of_nonneg hlambda]
    have he : ‖err‖ ≤ c * q ^ p := by simpa [c, q] using htaylor
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hpow : q ^ p = q ^ (p - 1) * q := by
      rw [← pow_succ]
      congr
      omega
    have he' : (1 / (beta * q ^ (p - 1))) * ‖err‖ ≤ q / (2 * (p : ℝ)) := by
      calc
        (1 / (beta * q ^ (p - 1))) * ‖err‖ ≤
            (1 / (beta * q ^ (p - 1))) * (c * q ^ p) := by gcongr
        _ = q / (2 * (p : ℝ)) := by
          rw [hpow]
          dsimp [beta]
          field_simp
    exact he'.trans (by
      have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hpR
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hp0) (by norm_num)]
      nlinarith
    )

theorem lem_teg_energy
    (X : Set E) (G : E → E) (p : ℕ) (hp : 2 ≤ p)
    (Lp : ℝ) (hLp : 0 < Lp) (x y xp u n err : E)
    (hxy : y ≠ x) (hy : y ∈ X) (hxp : xp ∈ X) (hu : u ∈ X)
    (hn : n ∈ normalCone X y)
    (hmodel : G y + n = err -
      ((2 * (p : ℝ) / p.factorial) * Lp * ‖y - x‖ ^ (p - 1)) • (y - x))
    (htaylor : ‖err‖ ≤ Lp / p.factorial * ‖y - x‖ ^ p)
    (hprojection : inner ℝ
      (x - (1 / (((2 * (p : ℝ) / p.factorial) * Lp) *
        ‖y - x‖ ^ (p - 1))) • G y - xp) (u - xp) ≤ 0) :
    2 * (1 / (((2 * (p : ℝ) / p.factorial) * Lp) *
        ‖y - x‖ ^ (p - 1))) * inner ℝ (G y) (y - u) ≤
      ‖x - u‖ ^ 2 - ‖xp - u‖ ^ 2 - (3 / 4 : ℝ) * ‖y - x‖ ^ 2 := by
  obtain ⟨hlambda, hrelative, herr⟩ :=
    tensorExtragradient_relative_from_model p hp Lp hLp G x y n err hxy hmodel htaylor
  exact tensorExtragradient_energy X G x y xp u n
    ((1 / (((2 * (p : ℝ) / p.factorial) * Lp) *
      ‖y - x‖ ^ (p - 1))) • err)
    (1 / (((2 * (p : ℝ) / p.factorial) * Lp) *
      ‖y - x‖ ^ (p - 1))) hy hxp hu hlambda hn hprojection hrelative herr

/-- Finite-interval telescoping consequence of `lem_teg_energy` under strong
monotonicity.  This is the energy estimate used by `prop:halving`. -/
theorem tensorExtragradient_energy_sum
    (T : ℕ) (x y s : ℕ → E) (G : E → E) (lambda : ℕ → ℝ)
    (zStar : E) (mu r : ℝ)
    (hmu : 0 ≤ mu) (hlambda : ∀ i < T, 0 ≤ lambda i)
    (hx0 : ‖x 0 - zStar‖ ≤ r)
    (hstrong : ∀ i < T,
      mu * ‖y i - zStar‖ ^ 2 ≤ inner ℝ (G (y i)) (y i - zStar))
    (henergy : ∀ i < T,
      2 * lambda i * inner ℝ (G (y i)) (y i - zStar) ≤
        ‖x i - zStar‖ ^ 2 - ‖x (i + 1) - zStar‖ ^ 2 -
          (3 / 4 : ℝ) * ‖s i‖ ^ 2) :
    2 * mu * (∑ i ∈ Finset.range T, lambda i * ‖y i - zStar‖ ^ 2) +
        (3 / 4 : ℝ) * (∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ≤ r ^ 2 := by
  have hstep : ∀ i < T,
      2 * mu * (lambda i * ‖y i - zStar‖ ^ 2) +
          (3 / 4 : ℝ) * ‖s i‖ ^ 2 ≤
        ‖x i - zStar‖ ^ 2 - ‖x (i + 1) - zStar‖ ^ 2 := by
    intro i hi
    have hs := mul_le_mul_of_nonneg_left (hstrong i hi) (hlambda i hi)
    have he := henergy i hi
    nlinarith
  have hsum : (∑ i ∈ Finset.range T,
      (2 * mu * (lambda i * ‖y i - zStar‖ ^ 2) +
        (3 / 4 : ℝ) * ‖s i‖ ^ 2)) ≤
      ∑ i ∈ Finset.range T,
        (‖x i - zStar‖ ^ 2 - ‖x (i + 1) - zStar‖ ^ 2) := by
    exact Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_sub'] at hsum
  have hxT : 0 ≤ ‖x T - zStar‖ ^ 2 := sq_nonneg _
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hx0
  have hx02 : ‖x 0 - zStar‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [norm_nonneg (x 0 - zStar)]
  linarith

end LeanArticleAudit.Pilot
