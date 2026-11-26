import MatchingBounds1005.Radial
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Stationarity transfer through the actual confinement map

These are conditional analytic assembly theorems. Their hypotheses are the
base-function gradient certificate, gradient regularity, and perturbation
bounds. The confined objective and its gradient are concrete; the gradient
formula is proved by differentiation, not postulated.
-/

namespace MatchingBounds1005.Confinement

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def objective (V : E → ℝ) (R η : ℝ) (x : E) : ℝ :=
  V (radial R x) + (η / 2) * ‖x‖ ^ 2

private theorem gradient_of_pairing {f : E → ℝ} {L : E →L[ℝ] ℝ} {g x : E}
    (hf : HasFDerivAt f L x) (hL : ∀ v, L v = inner (𝕜 := ℝ) g v) :
    HasGradientAt f g x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have heq : L = toDual ℝ E g := by ext v; exact hL v
  rwa [← heq]

theorem objective_hasGradientAt {V : E → ℝ} {R η : ℝ} {x g : E}
    (hV : HasGradientAt V g (radial R x)) :
    HasGradientAt (objective V R η) (radialDerivative R x g + η • x) x := by
  have hc := hV.hasFDerivAt.comp x (radial_hasFDerivAt R x)
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (η / 2)
  apply gradient_of_pairing (hc.add hq)
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    toDual_apply, ContinuousLinearMap.smul_apply, innerSL_apply,
    smul_eq_mul, inner_add_left, real_inner_smul_left]
  rw [← radialDerivative_symmetric R x g v]
  ring

theorem objective_gradient {V : E → ℝ} (R η : ℝ) (x : E)
    (hV : DifferentiableAt ℝ V (radial R x)) :
    gradient (objective V R η) x =
      radialDerivative R x (gradient V (radial R x)) + η • x :=
  (objective_hasGradientAt hV.hasGradientAt).gradient

theorem gradient_add_at {F P : E → ℝ} {y : E}
    (hF : DifferentiableAt ℝ F y) (hP : DifferentiableAt ℝ P y) :
    gradient (fun z => F z + P z) y = gradient F y + gradient P y := by
  apply HasGradientAt.gradient
  apply gradient_of_pairing (hF.hasGradientAt.hasFDerivAt.add hP.hasGradientAt.hasFDerivAt)
  intro v
  simp only [ContinuousLinearMap.add_apply, toDual_apply, inner_add_left]

/-- Lipschitz gradient transports the zero-hyperplane obstruction to a
nearby readout. The readout is normalized to unit length. -/
theorem near_hyperplane_gradient (F : E → ℝ) (a y : E) (b ε : ℝ)
    (ha : ‖a‖ = 1) (hb : 0 < b)
    (hlip : ∀ u v, ‖gradient F u - gradient F v‖ ≤ b * ‖u - v‖)
    (hcert : ∀ z, inner (𝕜 := ℝ) a z = 0 → 32 * ε ≤ ‖gradient F z‖)
    (hread : |inner (𝕜 := ℝ) a y| ≤ 16 * ε / b) :
    16 * ε ≤ ‖gradient F y‖ := by
  let y₀ := y - inner (𝕜 := ℝ) a y • a
  have hz : inner (𝕜 := ℝ) a y₀ = 0 := by
    simp [y₀, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha]
  have hd : ‖y₀ - y‖ = |inner (𝕜 := ℝ) a y| := by
    have heq : y₀ - y = -(inner (𝕜 := ℝ) a y • a) := by dsimp [y₀]; abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, ha, mul_one]
  have hl := hlip y₀ y
  rw [hd] at hl
  have hr := (le_div_iff₀ hb).mp hread
  have ht := norm_sub_norm_le (gradient F y₀) (gradient F y)
  have hc := hcert y₀ hz
  nlinarith only [hl, hr, ht, hc]

/-- Interior stationarity obstruction for the actual confined objective.
The regularization hypotheses include the manuscript choice `η=4ε/R`. -/
theorem interior_stationarity (F P : E → ℝ) (a x : E) (R η b ε : ℝ)
    (hF : Differentiable ℝ F) (hP : Differentiable ℝ P)
    (hR : 0 < R) (hε : 0 < ε) (hη : 0 ≤ η) (hηR : η * R ≤ 4 * ε)
    (ha : ‖a‖ = 1) (hb : 0 < b)
    (hlip : ∀ u v, ‖gradient F u - gradient F v‖ ≤ b * ‖u - v‖)
    (hcert : ∀ z, inner (𝕜 := ℝ) a z = 0 → 32 * ε ≤ ‖gradient F z‖)
    (hnoise : ∀ y, ‖y‖ ≤ R → ‖gradient P y‖ ≤ ε / 4)
    (hx : ‖x‖ ≤ R)
    (hread : |inner (𝕜 := ℝ) a (radial R x)| ≤ 16 * ε / b) :
    ε < ‖gradient (objective (fun y => F y + P y) R η) x‖ := by
  let y := radial R x
  let g := gradient F y + gradient P y
  have hbase := near_hyperplane_gradient F a y b ε ha hb hlip hcert hread
  have hpn := hnoise y (radial_norm_lt hR x).le
  have hg : 63 * ε / 4 ≤ ‖g‖ := by
    have ht := norm_sub_norm_le (gradient F y) (-gradient P y)
    simpa only [norm_neg, sub_neg_eq_add] using
      (show 63 * ε / 4 ≤ ‖gradient F y - -gradient P y‖ by
        rw [norm_neg] at ht
        linarith only [hbase, hpn, ht])
  have hj := radial_fderiv_inside hR hx g
  rw [radial_fderiv] at hj
  have hquad : ‖η • x‖ ≤ 4 * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    exact (mul_le_mul_of_nonneg_left hx hη).trans hηR
  have hgrad : gradient (objective (fun z => F z + P z) R η) x =
      radialDerivative R x g + η • x := by
    rw [objective_gradient R η x ((hF y).add (hP y)), gradient_add_at (hF y) (hP y)]
  rw [hgrad]
  have ht := norm_sub_norm_le (radialDerivative R x g) (-η • x)
  have hn : ‖-η • x‖ = ‖η • x‖ := by rw [neg_smul, norm_neg]
  rw [hn, neg_smul, sub_neg_eq_add] at ht
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcoeff : (5 : ℝ) < (1 / (2 * Real.sqrt 2)) * (63 / 4) := by
    have hsupper : Real.sqrt 2 < 3 / 2 := by nlinarith only [hs, hspos]
    have heq : (1 / (2 * Real.sqrt 2)) * (63 / 4) = 63 / (8 * Real.sqrt 2) := by ring
    rw [heq]
    apply (lt_div_iff₀ (show 0 < 8 * Real.sqrt 2 by positivity)).mpr
    nlinarith only [hsupper]
  have hmul := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ 1 / (2 * Real.sqrt 2) by positivity)
  have hstrict := mul_lt_mul_of_pos_right hcoeff hε
  nlinarith only [hmul, hstrict, hj, hquad, ht]

/-- Exact radial pairing for the actual scalar objective. -/
theorem objective_radial_pairing {V : E → ℝ} (R η : ℝ) (x : E)
    (hV : DifferentiableAt ℝ V (radial R x)) :
    inner (𝕜 := ℝ) x (gradient (objective V R η) x) =
      radialScale R x ^ 2 * inner (𝕜 := ℝ) (radial R x) (gradient V (radial R x)) +
        η * ‖x‖ ^ 2 := by
  rw [objective_gradient R η x hV, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [← radial_fderiv, radial_fderiv_radial_pairing]
  simp only [radial, real_inner_smul_left]
  ring

/-- Exterior stationarity obstruction; `εR ≥ 1` includes all `C_R ≥ 1`
and `ηR ≥ 4ε` includes the manuscript's regularization. -/
theorem exterior_stationarity (V : E → ℝ) (x : E) (R η ε : ℝ)
    (hV : Differentiable ℝ V) (hR : 0 < R) (hε : 0 < ε)
    (hη : 0 ≤ η) (hηR : 4 * ε ≤ η * R) (hεR : 1 ≤ ε * R)
    (hpair : ∀ y, ‖y‖ ≤ R → -(145 / 256 : ℝ) ≤ inner (𝕜 := ℝ) y (gradient V y))
    (hx : R ≤ ‖x‖) :
    3 * ε < ‖gradient (objective V R η) x‖ := by
  have hp := hpair (radial R x) (radial_norm_lt hR x).le
  have hs := radialScale_sq_identity R x
  have hratio : 1 ≤ ‖x‖ ^ 2 / R ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith only [hx, hR]
  have hq : radialScale R x ^ 2 ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hratio (sq_nonneg (radialScale R x))
    nlinarith only [hm, hs]
  have hpairmul := mul_le_mul_of_nonneg_left hp (sq_nonneg (radialScale R x))
  have htpos : 0 < ‖x‖ := lt_of_lt_of_le hR hx
  have het : 1 ≤ ε * ‖x‖ := hεR.trans (mul_le_mul_of_nonneg_left hx hε.le)
  have hηt : 4 * ε ≤ η * ‖x‖ := hηR.trans (mul_le_mul_of_nonneg_left hx hη)
  have hηt2 := mul_le_mul_of_nonneg_right hηt (norm_nonneg x)
  have hid := objective_radial_pairing R η x (hV (radial R x))
  have hcs := real_inner_le_norm x (gradient (objective V R η) x)
  nlinarith only [hpairmul, hq, het, hηt2, hid, hcs, htpos]

/-- The robust readout obstruction after choosing the manuscript's actual
regularization `η = 4ε/R`, uniformly over unrestricted query locations. -/
theorem confined_stationarity (F P : E → ℝ) (a x : E) (R b ε : ℝ)
    (hF : Differentiable ℝ F) (hP : Differentiable ℝ P)
    (hR : 0 < R) (hε : 0 < ε) (hεR : 1 ≤ ε * R)
    (ha : ‖a‖ = 1) (hb : 0 < b)
    (hlip : ∀ u v, ‖gradient F u - gradient F v‖ ≤ b * ‖u - v‖)
    (hcert : ∀ z, inner (𝕜 := ℝ) a z = 0 → 32 * ε ≤ ‖gradient F z‖)
    (hnoise : ∀ y, ‖y‖ ≤ R → ‖gradient P y‖ ≤ ε / 4)
    (hpair : ∀ y, ‖y‖ ≤ R → -(145 / 256 : ℝ) ≤
      inner (𝕜 := ℝ) y (gradient (fun z => F z + P z) y))
    (hread : |inner (𝕜 := ℝ) a (radial R x)| ≤ 16 * ε / b) :
    ε < ‖gradient (objective (fun y => F y + P y) R (4 * ε / R)) x‖ := by
  have hη : 0 ≤ 4 * ε / R := by positivity
  have hηR : (4 * ε / R) * R = 4 * ε := div_mul_cancel₀ _ (ne_of_gt hR)
  by_cases hx : ‖x‖ ≤ R
  · exact interior_stationarity F P a x R (4 * ε / R) b ε hF hP hR hε hη
      hηR.le ha hb hlip hcert hnoise hx hread
  · have hout := exterior_stationarity (fun y => F y + P y) x R (4 * ε / R) ε
      (hF.add hP) hR hε hη hηR.ge hεR hpair (le_of_lt (lt_of_not_ge hx))
    linarith only [hout, hε]

end MatchingBounds1005.Confinement
