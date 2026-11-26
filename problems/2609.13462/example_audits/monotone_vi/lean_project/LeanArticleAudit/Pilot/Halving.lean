import LeanArticleAudit.Pilot.UpperCorrectionEnergy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set
open scoped BigOperators

namespace LeanArticleAudit.Pilot

/-- The negative real powers used in the halving proof are convex on the
positive half-line. -/
theorem convexOn_rpow_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ x ^ a) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
  · intro x hx
    exact (Real.continuousAt_rpow_const x a (Or.inl (ne_of_gt hx))).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hpow := Real.hasDerivAt_rpow_const (x := x) (p := a - 1)
      (Or.inl (ne_of_gt hx))
    simpa only [sub_sub, mul_assoc] using (hpow.const_mul a).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hpowpos : 0 < x ^ (a - 2) := Real.rpow_pos_of_pos hx _
    have hcoef : 0 ≤ a * (a - 1) :=
      mul_nonneg_of_nonpos_of_nonpos ha (by linarith)
    rw [← mul_assoc]
    have hpoweq : x ^ (a - (1 + 1)) = x ^ (a - 2) := by
      congr 1
      ring
    rw [hpoweq]
    exact mul_nonneg hcoef hpowpos.le

/-- Uniform-weight Jensen inequality for a negative real power. -/
theorem inverse_power_jensen
    (T : ℕ) (hT : 0 < T) (q : ℕ → ℝ) (a : ℝ) (ha : a ≤ 0)
    (hq : ∀ i < T, 0 < q i) :
    (T : ℝ) * (((1 / (T : ℝ)) * ∑ i ∈ Finset.range T, q i) ^ a) ≤
      ∑ i ∈ Finset.range T, (q i) ^ a := by
  let w : ℕ → ℝ := fun _ ↦ 1 / (T : ℝ)
  have hw : ∀ i ∈ Finset.range T, 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hw_sum : ∑ i ∈ Finset.range T, w i = 1 := by
    simp [w, hT.ne']
  have hJ := (convexOn_rpow_of_nonpos ha).map_sum_le hw hw_sum
    (fun i hi ↦ hq i (Finset.mem_range.mp hi))
  simp only [smul_eq_mul] at hJ
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  calc
    (T : ℝ) * (((1 / (T : ℝ)) * ∑ i ∈ Finset.range T, q i) ^ a) =
        (T : ℝ) * ((∑ i ∈ Finset.range T, w i * q i) ^ a) := by
          congr 2
          simp [w, Finset.mul_sum]
    _ ≤ (T : ℝ) * (∑ i ∈ Finset.range T, w i * (q i) ^ a) := by
          exact mul_le_mul_of_nonneg_left hJ hTpos.le
    _ = ∑ i ∈ Finset.range T, (q i) ^ a := by
          simp [w, Finset.mul_sum, hT.ne']

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convexOn_univ_norm_sq :
    ConvexOn ℝ (Set.univ : Set E) (fun x : E ↦ ‖x‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hn := norm_add_le (a • x) (b • y)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] at hn
  have hleft : 0 ≤ ‖a • x + b • y‖ := norm_nonneg _
  have hright : 0 ≤ a * ‖x‖ + b * ‖y‖ := by positivity
  have hsquare : ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 := by
    nlinarith
  calc
    ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 := hsquare
    _ ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
      have hvar : 0 ≤ a * b * (‖x‖ - ‖y‖) ^ 2 := by positivity
      nlinarith

/-- Squared-distance Jensen inequality for the weighted average returned by
the halving routine. -/
theorem weighted_average_norm_sq
    (T : ℕ) (y : ℕ → E) (lambda : ℕ → ℝ) (zStar : E)
    (hlambda : ∀ i < T, 0 ≤ lambda i)
    (Lambda : ℝ) (hLambda : Lambda = ∑ i ∈ Finset.range T, lambda i)
    (hLambdaPos : 0 < Lambda) :
    ‖(1 / Lambda) • (∑ i ∈ Finset.range T, lambda i • y i) - zStar‖ ^ 2 ≤
      (1 / Lambda) * ∑ i ∈ Finset.range T, lambda i * ‖y i - zStar‖ ^ 2 := by
  let w : ℕ → ℝ := fun i ↦ lambda i / Lambda
  have hw : ∀ i ∈ Finset.range T, 0 ≤ w i := by
    intro i hi
    exact div_nonneg (hlambda i (Finset.mem_range.mp hi)) hLambdaPos.le
  have hw_sum : ∑ i ∈ Finset.range T, w i = 1 := by
    simp only [w]
    rw [← Finset.sum_div]
    rw [← hLambda, div_self hLambdaPos.ne']
  have hJ := convexOn_univ_norm_sq.map_sum_le hw hw_sum
    (fun i hi ↦ Set.mem_univ (y i - zStar))
  simp only [smul_eq_mul] at hJ
  have havg :
      (1 / Lambda) • (∑ i ∈ Finset.range T, lambda i • y i) - zStar =
        ∑ i ∈ Finset.range T, w i • (y i - zStar) := by
    simp only [w, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw_sum, one_smul]
    rw [Finset.smul_sum]
    apply congrArg (fun v : E ↦ v - zStar)
    apply Finset.sum_congr rfl
    intro i hi
    simp only [one_mul, div_eq_mul_inv]
    rw [smul_smul, mul_comm Lambda⁻¹ (lambda i)]
  rw [havg]
  calc
    ‖∑ i ∈ Finset.range T, w i • (y i - zStar)‖ ^ 2 ≤
        ∑ i ∈ Finset.range T, w i * ‖y i - zStar‖ ^ 2 := hJ
    _ = (1 / Lambda) * ∑ i ∈ Finset.range T,
        lambda i * ‖y i - zStar‖ ^ 2 := by
      simp only [w, div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The first Jensen line in the proof of `prop:halving`, specialized to the
squared step norms. -/
theorem halving_inverse_power_jensen
    (p T : ℕ) (hp : 1 ≤ p) (hT : 0 < T) (s : ℕ → E)
    (hs : ∀ i < T, s i ≠ 0) :
    (T : ℝ) * (((1 / (T : ℝ)) *
        ∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ^
          (-(((p : ℝ) - 1) / 2))) ≤
      ∑ i ∈ Finset.range T,
        (‖s i‖ ^ 2) ^ (-(((p : ℝ) - 1) / 2)) := by
  apply inverse_power_jensen T hT (fun i ↦ ‖s i‖ ^ 2)
      (-(((p : ℝ) - 1) / 2))
  · have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  · intro i hi
    exact sq_pos_of_pos (norm_pos_iff.mpr (hs i hi))

/-- Combining the energy bound on the steps with inverse-power Jensen gives
the quantitative lower bound before converting from real powers to the
algorithmic stepsizes. -/
theorem halving_inverse_power_lower_of_energy
    (p T : ℕ) (hp : 1 ≤ p) (hT : 0 < T) (s : ℕ → E)
    (r : ℝ) (hr : 0 < r) (hs : ∀ i < T, s i ≠ 0)
    (hsteps : (3 / 4 : ℝ) *
      (∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ≤ r ^ 2) :
    (T : ℝ) * (((4 * r ^ 2) / (3 * (T : ℝ))) ^
        (-(((p : ℝ) - 1) / 2))) ≤
      ∑ i ∈ Finset.range T,
        (‖s i‖ ^ 2) ^ (-(((p : ℝ) - 1) / 2)) := by
  let a : ℝ := -(((p : ℝ) - 1) / 2)
  let mean : ℝ := (1 / (T : ℝ)) *
    ∑ i ∈ Finset.range T, ‖s i‖ ^ 2
  have hJ := halving_inverse_power_jensen p T hp hT s hs
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsumpos : 0 < ∑ i ∈ Finset.range T, ‖s i‖ ^ 2 := by
    have h0 : 0 ∈ Finset.range T := Finset.mem_range.mpr hT
    calc
      0 < ‖s 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (hs 0 hT))
      _ ≤ ∑ i ∈ Finset.range T, ‖s i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i ↦ ‖s i‖ ^ 2)
          (fun i hi ↦ sq_nonneg _) h0
  have hmeanpos : 0 < mean := by dsimp [mean]; positivity
  have hmeanle : mean ≤ (4 * r ^ 2) / (3 * (T : ℝ)) := by
    dsimp [mean]
    have hsumle : ∑ i ∈ Finset.range T, ‖s i‖ ^ 2 ≤ (4 / 3 : ℝ) * r ^ 2 := by
      nlinarith
    rw [div_eq_mul_inv]
    calc
      (1 / (T : ℝ)) * ∑ i ∈ Finset.range T, ‖s i‖ ^ 2 ≤
          (1 / (T : ℝ)) * ((4 / 3 : ℝ) * r ^ 2) := by gcongr
      _ = 4 * r ^ 2 * (3 * (T : ℝ))⁻¹ := by field_simp
  have ha : a ≤ 0 := by
    dsimp [a]
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hmeanpos hmeanle ha
  calc
    (T : ℝ) * (((4 * r ^ 2) / (3 * (T : ℝ))) ^
        (-(((p : ℝ) - 1) / 2))) =
        (T : ℝ) * (((4 * r ^ 2) / (3 * (T : ℝ))) ^ a) := by rfl
    _ ≤ (T : ℝ) * mean ^ a := mul_le_mul_of_nonneg_left hpow hTpos.le
    _ ≤ ∑ i ∈ Finset.range T,
        (‖s i‖ ^ 2) ^ (-(((p : ℝ) - 1) / 2)) := by
          simpa [mean, a] using hJ

/-- Conversion between the real-power expression used by Jensen and the
inverse natural power appearing in the algorithmic stepsize. -/
theorem inverse_power_rpow_sq
    (p : ℕ) (hp : 1 ≤ p) (q : ℝ) (hq : 0 < q) :
    (q ^ 2) ^ (-(((p : ℝ) - 1) / 2)) = (q ^ (p - 1))⁻¹ := by
  have hk : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp]
    norm_num
  calc
    (q ^ 2) ^ (-(((p : ℝ) - 1) / 2)) =
        q ^ ((2 : ℝ) * (-(((p : ℝ) - 1) / 2))) := by
          rw [← Real.rpow_natCast_mul hq.le]
          norm_num
    _ = q ^ (-((p - 1 : ℕ) : ℝ)) := by
          congr 1
          rw [hk]
          ring
    _ = (q ^ ((p - 1 : ℕ) : ℝ))⁻¹ := Real.rpow_neg hq.le _
    _ = (q ^ (p - 1))⁻¹ := by rw [Real.rpow_natCast]

/-- Raw accumulated-stepsize lower bound, with no asymptotic notation and no
unproved Jensen or power-conversion step. -/
theorem halving_lambda_sum_lower_raw
    (p T : ℕ) (hp : 1 ≤ p) (hT : 0 < T) (s : ℕ → E)
    (r beta : ℝ) (hr : 0 < r) (hbeta : 0 < beta)
    (hs : ∀ i < T, s i ≠ 0)
    (lambda : ℕ → ℝ)
    (hlambda : ∀ i < T,
      lambda i = 1 / (beta * ‖s i‖ ^ (p - 1)))
    (hsteps : (3 / 4 : ℝ) *
      (∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ≤ r ^ 2) :
    (1 / beta) * (T : ℝ) *
        (((4 * r ^ 2) / (3 * (T : ℝ))) ^
          (-(((p : ℝ) - 1) / 2))) ≤
      ∑ i ∈ Finset.range T, lambda i := by
  have hpower := halving_inverse_power_lower_of_energy p T hp hT s r hr hs hsteps
  have hfac : 0 ≤ 1 / beta := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hpower hfac
  calc
    (1 / beta) * (T : ℝ) *
        (((4 * r ^ 2) / (3 * (T : ℝ))) ^
          (-(((p : ℝ) - 1) / 2))) =
        (1 / beta) * ((T : ℝ) *
          (((4 * r ^ 2) / (3 * (T : ℝ))) ^
            (-(((p : ℝ) - 1) / 2)))) := by ring
    _ ≤ (1 / beta) * (∑ i ∈ Finset.range T,
        (‖s i‖ ^ 2) ^ (-(((p : ℝ) - 1) / 2))) := hscaled
    _ = ∑ i ∈ Finset.range T, lambda i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hsi : 0 < ‖s i‖ := norm_pos_iff.mpr
        (hs i (Finset.mem_range.mp hi))
      rw [inverse_power_rpow_sq p hp _ hsi,
        hlambda i (Finset.mem_range.mp hi)]
      field_simp

/-- Exact normalization of the raw Jensen constant into Equation
`eq:lambda-sum`. -/
theorem halving_raw_constant_normalize
    (p : ℕ) (hp : 1 ≤ p) (T : ℕ) (hT : 0 < T) (r : ℝ) (hr : 0 < r) :
    (T : ℝ) * (((4 * r ^ 2) / (3 * (T : ℝ))) ^
        (-(((p : ℝ) - 1) / 2))) =
      ((3 / 4 : ℝ) ^ (((p : ℝ) - 1) / 2)) *
        ((T : ℝ) ^ (((p : ℝ) + 1) / 2)) / r ^ (p - 1) := by
  let a : ℝ := ((p : ℝ) - 1) / 2
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have h4r : 0 < 4 * r ^ 2 := by positivity
  have h3T : 0 < 3 * (T : ℝ) := by positivity
  have hk : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp]
    norm_num
  have hrpow : (r ^ 2) ^ a = r ^ (p - 1) := by
    calc
      (r ^ 2) ^ a = r ^ ((2 : ℝ) * a) := by
        rw [← Real.rpow_natCast_mul hr.le]
        norm_num
      _ = r ^ ((p - 1 : ℕ) : ℝ) := by
        congr 1
        dsimp [a]
        rw [hk]
        ring
      _ = r ^ (p - 1) := Real.rpow_natCast _ _
  have hTpow : (T : ℝ) * (T : ℝ) ^ a =
      (T : ℝ) ^ (((p : ℝ) + 1) / 2) := by
    calc
      (T : ℝ) * (T : ℝ) ^ a = (T : ℝ) ^ (1 : ℝ) * (T : ℝ) ^ a := by
        rw [Real.rpow_one]
      _ = (T : ℝ) ^ ((1 : ℝ) + a) := (Real.rpow_add hTp _ _).symm
      _ = (T : ℝ) ^ (((p : ℝ) + 1) / 2) := by
        congr 1
        dsimp [a]
        ring
  dsimp [a] at hrpow hTpow ⊢
  rw [Real.rpow_neg (by positivity : 0 ≤ (4 * r ^ 2) / (3 * (T : ℝ)))]
  rw [Real.div_rpow h4r.le h3T.le]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg r)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTp.le]
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 4)]
  rw [hrpow]
  field_simp
  rw [hTpow]

/-- Feasibility and the weighted squared-distance estimate following the
finite energy sum. -/
theorem weighted_average_feasible_distance
    (X : Set E) (hX : Convex ℝ X)
    (T : ℕ) (y s : ℕ → E) (lambda : ℕ → ℝ) (zStar : E)
    (mu r Lambda : ℝ) (hmu : 0 < mu)
    (hy : ∀ i < T, y i ∈ X)
    (hlambda : ∀ i < T, 0 ≤ lambda i)
    (hLambda : Lambda = ∑ i ∈ Finset.range T, lambda i)
    (hLambdaPos : 0 < Lambda)
    (henergySum :
      2 * mu * (∑ i ∈ Finset.range T,
        lambda i * ‖y i - zStar‖ ^ 2) +
          (3 / 4 : ℝ) * (∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ≤ r ^ 2) :
    let ybar := (1 / Lambda) •
      (∑ i ∈ Finset.range T, lambda i • y i)
    ybar ∈ X ∧ ‖ybar - zStar‖ ^ 2 ≤ r ^ 2 / (2 * mu * Lambda) := by
  dsimp
  let w : ℕ → ℝ := fun i ↦ lambda i / Lambda
  have hw : ∀ i ∈ Finset.range T, 0 ≤ w i := by
    intro i hi
    exact div_nonneg (hlambda i (Finset.mem_range.mp hi)) hLambdaPos.le
  have hw_sum : ∑ i ∈ Finset.range T, w i = 1 := by
    simp only [w]
    rw [← Finset.sum_div, ← hLambda, div_self hLambdaPos.ne']
  have havg :
      (1 / Lambda) • (∑ i ∈ Finset.range T, lambda i • y i) =
        ∑ i ∈ Finset.range T, w i • y i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, div_eq_mul_inv]
    rw [smul_smul]
    congr 1
    ring
  refine ⟨havg ▸ hX.sum_mem hw hw_sum
    (fun i hi ↦ hy i (Finset.mem_range.mp hi)), ?_⟩
  have hnorm := weighted_average_norm_sq T y lambda zStar hlambda Lambda
    hLambda hLambdaPos
  have hsteps : 0 ≤ ∑ i ∈ Finset.range T, ‖s i‖ ^ 2 := by positivity
  have hweighted :
      2 * mu * (∑ i ∈ Finset.range T,
        lambda i * ‖y i - zStar‖ ^ 2) ≤ r ^ 2 := by
    nlinarith
  have hbound : (1 / Lambda) *
      (∑ i ∈ Finset.range T, lambda i * ‖y i - zStar‖ ^ 2) ≤
        r ^ 2 / (2 * mu * Lambda) := by
    have hden : 0 < 2 * mu * Lambda := by positivity
    rw [le_div_iff₀ hden]
    calc
      (1 / Lambda) *
          (∑ i ∈ Finset.range T, lambda i * ‖y i - zStar‖ ^ 2) *
            (2 * mu * Lambda) =
          2 * mu * (∑ i ∈ Finset.range T,
            lambda i * ‖y i - zStar‖ ^ 2) := by
              field_simp
      _ ≤ r ^ 2 := hweighted
  exact hnorm.trans hbound

/-- Once the accumulated stepsize is at least `2 / μ`, the returned weighted
average is feasible and halves the promised radius. -/
theorem weighted_average_halves
    (X : Set E) (hX : Convex ℝ X)
    (T : ℕ) (y s : ℕ → E) (lambda : ℕ → ℝ) (zStar : E)
    (mu r Lambda : ℝ) (hmu : 0 < mu) (hr : 0 ≤ r)
    (hy : ∀ i < T, y i ∈ X)
    (hlambda : ∀ i < T, 0 ≤ lambda i)
    (hLambda : Lambda = ∑ i ∈ Finset.range T, lambda i)
    (hLambdaLower : 2 / mu ≤ Lambda)
    (henergySum :
      2 * mu * (∑ i ∈ Finset.range T,
        lambda i * ‖y i - zStar‖ ^ 2) +
          (3 / 4 : ℝ) * (∑ i ∈ Finset.range T, ‖s i‖ ^ 2) ≤ r ^ 2) :
    let ybar := (1 / Lambda) •
      (∑ i ∈ Finset.range T, lambda i • y i)
    ybar ∈ X ∧ ‖ybar - zStar‖ ≤ r / 2 := by
  have hLambdaPos : 0 < Lambda :=
    lt_of_lt_of_le (div_pos (by norm_num) hmu) hLambdaLower
  have h := weighted_average_feasible_distance X hX T y s lambda zStar mu r Lambda
    hmu hy hlambda hLambda hLambdaPos henergySum
  dsimp at h ⊢
  refine ⟨h.1, ?_⟩
  have hnorm0 : 0 ≤ ‖(1 / Lambda) •
      (∑ i ∈ Finset.range T, lambda i • y i) - zStar‖ := norm_nonneg _
  have hfrac : r ^ 2 / (2 * mu * Lambda) ≤ (r / 2) ^ 2 := by
    have hmul : 2 ≤ mu * Lambda := by
      calc
        2 = mu * (2 / mu) := by field_simp
        _ ≤ mu * Lambda := mul_le_mul_of_nonneg_left hLambdaLower hmu.le
    have hmL : 4 ≤ 2 * mu * Lambda := by nlinarith
    rw [show (r / 2) ^ 2 = r ^ 2 / 4 by ring]
    exact div_le_div_of_nonneg_left (sq_nonneg r) (by norm_num) hmL
  nlinarith [h.2.trans hfrac]

/-- The source coefficient `b_p = 2p/p!`. -/
noncomputable def tensorBetaCoefficient (p : ℕ) : ℝ :=
  2 * (p : ℝ) / p.factorial

/-- The real expression inside the ceiling in Equation `eq:halving-count`. -/
noncomputable def halvingThreshold (p : ℕ) (Lp r mu : ℝ) : ℝ :=
  (2 * tensorBetaCoefficient p * (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2) *
    Lp * r ^ (p - 1) / mu) ^ (2 / ((p : ℝ) + 1))

/-- Exact scheduled iteration count `T_p(r,μ)` from the source. -/
noncomputable def halvingIterationCount (p : ℕ) (Lp r mu : ℝ) : ℕ :=
  max 1 ⌈halvingThreshold p Lp r mu⌉₊

theorem halvingIterationCount_pos (p : ℕ) (Lp r mu : ℝ) :
    0 < halvingIterationCount p Lp r mu := by
  simp [halvingIterationCount]

theorem halvingThreshold_le_count
    (p : ℕ) (Lp r mu : ℝ) :
    halvingThreshold p Lp r mu ≤
      (halvingIterationCount p Lp r mu : ℝ) := by
  have hmax : ⌈halvingThreshold p Lp r mu⌉₊ ≤
      max 1 ⌈halvingThreshold p Lp r mu⌉₊ := Nat.le_max_right _ _
  exact (Nat.le_ceil _).trans (by
    dsimp [halvingIterationCount]
    exact_mod_cast hmax)

theorem halvingIterationCount_power_lower
    (p : ℕ) (hp : 2 ≤ p) (Lp r mu : ℝ)
    (hLp : 0 < Lp) (hr : 0 < r) (hmu : 0 < mu) :
    2 * tensorBetaCoefficient p *
        (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2) *
        Lp * r ^ (p - 1) / mu ≤
      (halvingIterationCount p Lp r mu : ℝ) ^
        (((p : ℝ) + 1) / 2) := by
  let q := 2 * tensorBetaCoefficient p *
    (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2) *
    Lp * r ^ (p - 1) / mu
  let c := ((p : ℝ) + 1) / 2
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hc : 0 < c := by dsimp [c]; linarith
  have hbeta : 0 < tensorBetaCoefficient p := by
    dsimp [tensorBetaCoefficient]
    positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hthreshold : q ^ (1 / c) ≤
      (halvingIterationCount p Lp r mu : ℝ) := by
    simpa [halvingThreshold, q, c, div_eq_mul_inv, mul_comm] using
      halvingThreshold_le_count p Lp r mu
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hq.le _) hthreshold hc.le
  calc
    q = (q ^ (1 / c)) ^ c := by
      rw [← Real.rpow_mul hq.le]
      have hc0 : c ≠ 0 := hc.ne'
      rw [one_div, inv_mul_cancel₀ hc0, Real.rpow_one]
    _ ≤ (halvingIterationCount p Lp r mu : ℝ) ^ c := hpow

/-- The explicit ceiling schedule forces the accumulated stepsize threshold
needed by `weighted_average_halves`. -/
theorem halving_count_forces_lambda_lower
    (p : ℕ) (hp : 2 ≤ p) (Lp r mu Lambda : ℝ)
    (hLp : 0 < Lp) (hr : 0 < r) (hmu : 0 < mu)
    (hLambda :
      (1 / (tensorBetaCoefficient p * Lp)) *
          (3 / 4 : ℝ) ^ (((p : ℝ) - 1) / 2) *
          (halvingIterationCount p Lp r mu : ℝ) ^
            (((p : ℝ) + 1) / 2) / r ^ (p - 1) ≤ Lambda) :
    2 / mu ≤ Lambda := by
  have hpow := halvingIterationCount_power_lower p hp Lp r mu hLp hr hmu
  let a := ((p : ℝ) - 1) / 2
  have hbeta : 0 < tensorBetaCoefficient p := by
    dsimp [tensorBetaCoefficient]
    positivity
  have hrpow : 0 < r ^ (p - 1) := pow_pos hr _
  have hrecip : (3 / 4 : ℝ) ^ a * (4 / 3 : ℝ) ^ a = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    norm_num
  have hscale : 0 < (1 / (tensorBetaCoefficient p * Lp)) *
      (3 / 4 : ℝ) ^ a / r ^ (p - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpow hscale.le
  apply hLambda.trans' ?_
  dsimp [a] at hmul ⊢
  calc
    2 / mu =
        ((1 / (tensorBetaCoefficient p * Lp)) *
          (3 / 4 : ℝ) ^ (((p : ℝ) - 1) / 2) / r ^ (p - 1)) *
        (2 * tensorBetaCoefficient p *
          (4 / 3 : ℝ) ^ (((p : ℝ) - 1) / 2) *
          Lp * r ^ (p - 1) / mu) := by
            dsimp [a] at hrecip
            field_simp
            nlinarith
    _ ≤ ((1 / (tensorBetaCoefficient p * Lp)) *
          (3 / 4 : ℝ) ^ (((p : ℝ) - 1) / 2) / r ^ (p - 1)) *
        (halvingIterationCount p Lp r mu : ℝ) ^
          (((p : ℝ) + 1) / 2) := hmul
    _ = (1 / (tensorBetaCoefficient p * Lp)) *
          (3 / 4 : ℝ) ^ (((p : ℝ) - 1) / 2) *
          (halvingIterationCount p Lp r mu : ℝ) ^
            (((p : ℝ) + 1) / 2) / r ^ (p - 1) := by ring

end LeanArticleAudit.Pilot
