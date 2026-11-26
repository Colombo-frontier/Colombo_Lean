import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import HeavyTail.Envelope

/-!
The deterministic loss-to-testing reduction in `heavy tail.tex`, lines 819–829.
The coefficient `b` is the manuscript's `a / sqrt k`; no probabilistic lower
bound or adaptive transcript claim is assumed or asserted here.
-/

namespace HeavyTail

noncomputable section

def scalarSignLoss (b μ ρ x : ℝ) : ℝ :=
  b * |x - ρ| + μ / 2 * x ^ 2

theorem scalarSignLoss_at_center (b μ ρ : ℝ) :
    scalarSignLoss b μ ρ ρ = μ / 2 * ρ ^ 2 := by
  simp [scalarSignLoss]

theorem scalarSignLoss_minimizer {b μ ρ : ℝ}
    (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hb : μ * ρ ≤ b) (x : ℝ) :
    scalarSignLoss b μ ρ ρ ≤ scalarSignLoss b μ ρ x := by
  have hm : 0 ≤ μ * ρ := mul_nonneg hμ hρ
  have h1 := mul_le_mul_of_nonneg_right hb (abs_nonneg (x - ρ))
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (x - ρ)) hm
  have h3 := mul_nonneg hμ (sq_nonneg (x - ρ))
  rw [scalarSignLoss_at_center]
  unfold scalarSignLoss
  nlinarith

theorem scalarSignLoss_wrong_halfline {b μ ρ x : ℝ}
    (hb : 0 ≤ b) (hμ : 0 ≤ μ) (_hρ : 0 ≤ ρ) (hx : x ≤ 0) :
    b * ρ - μ / 2 * ρ ^ 2 ≤
      scalarSignLoss b μ ρ x - scalarSignLoss b μ ρ ρ := by
  have h1 : ρ ≤ |x - ρ| := by
    have := neg_le_abs (x - ρ)
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hb
  have h3 := mul_nonneg hμ (sq_nonneg x)
  rw [scalarSignLoss_at_center]
  unfold scalarSignLoss
  nlinarith

def coordinateSignLoss (b μ ρ v x : ℝ) : ℝ :=
  b * |x - ρ * v| + μ / 2 * x ^ 2

theorem coordinateSignLoss_reflect (b μ ρ v x : ℝ)
    (hv : v = -1 ∨ v = 1) :
    coordinateSignLoss b μ ρ v x = scalarSignLoss b μ ρ (v * x) := by
  rcases hv with rfl | rfl
  · have he : -1 * x - ρ = -(x - ρ * -1) := by ring
    simp only [coordinateSignLoss, scalarSignLoss, he, abs_neg]
    ring
  · simp [coordinateSignLoss, scalarSignLoss]

theorem coordinateSignLoss_at_center (b μ ρ v : ℝ)
    (hv : v = -1 ∨ v = 1) :
    coordinateSignLoss b μ ρ v (ρ * v) = μ / 2 * ρ ^ 2 := by
  rcases hv with rfl | rfl <;> simp [coordinateSignLoss]

theorem coordinateSignLoss_minimizer {b μ ρ v : ℝ}
    (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hb : μ * ρ ≤ b)
    (hv : v = -1 ∨ v = 1) (x : ℝ) :
    coordinateSignLoss b μ ρ v (ρ * v) ≤ coordinateSignLoss b μ ρ v x := by
  rw [coordinateSignLoss_at_center b μ ρ v hv,
    coordinateSignLoss_reflect b μ ρ v x hv]
  simpa only [scalarSignLoss_at_center] using
    scalarSignLoss_minimizer hμ hρ hb (v * x)

theorem coordinateSignLoss_wrong_halfline {b μ ρ v x : ℝ}
    (hb : 0 ≤ b) (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hv : v = -1 ∨ v = 1) (hx : x * v ≤ 0) :
    b * ρ - μ / 2 * ρ ^ 2 ≤ coordinateSignLoss b μ ρ v x -
      coordinateSignLoss b μ ρ v (ρ * v) := by
  rw [coordinateSignLoss_at_center b μ ρ v hv,
    coordinateSignLoss_reflect b μ ρ v x hv]
  simpa only [scalarSignLoss_at_center] using
    scalarSignLoss_wrong_halfline hb hμ hρ (by simpa only [mul_comm] using hx)

/-- The manuscript resolves zero to the negative sign. -/
noncomputable def decodeSign (x : ℝ) : ℝ := if x ≤ 0 then -1 else 1

theorem decodeSign_wrong_imp_nonpos {x v : ℝ} (hv : v = -1 ∨ v = 1)
    (h : decodeSign x ≠ v) : x * v ≤ 0 := by
  unfold decodeSign at h
  rcases hv with rfl | rfl
  · split_ifs at h with hx
    · exact (h rfl).elim
    · have : 0 < x := lt_of_not_ge hx
      linarith
  · split_ifs at h with hx
    · simpa using hx
    · exact (h rfl).elim

noncomputable def signObjective {k : ℕ} (b μ ρ : ℝ) (v x : Fin k → ℝ) : ℝ :=
  ∑ j, coordinateSignLoss b μ ρ (v j) (x j)

theorem signObjective_minimizer {k : ℕ} {b μ ρ : ℝ} {v : Fin k → ℝ}
    (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hb : μ * ρ ≤ b)
    (hv : ∀ j, v j = -1 ∨ v j = 1) (x : Fin k → ℝ) :
    signObjective b μ ρ v (fun j => ρ * v j) ≤ signObjective b μ ρ v x := by
  exact Finset.sum_le_sum fun j _ => coordinateSignLoss_minimizer hμ hρ hb (hv j) (x j)

noncomputable def signHamming {k : ℕ} (v x : Fin k → ℝ) : ℕ :=
  (Finset.univ.filter fun j => decodeSign (x j) ≠ v j).card

theorem signObjective_loss_hamming {k : ℕ} {b μ ρ : ℝ} {v : Fin k → ℝ}
    (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hb : μ * ρ ≤ b)
    (hv : ∀ j, v j = -1 ∨ v j = 1) (x : Fin k → ℝ) :
    (b * ρ - μ / 2 * ρ ^ 2) * (signHamming v x : ℝ) ≤
      signObjective b μ ρ v x - signObjective b μ ρ v (fun j => ρ * v j) := by
  classical
  have hb0 : 0 ≤ b := le_trans (mul_nonneg hμ hρ) hb
  have hi (j : Fin k) :
      (if decodeSign (x j) ≠ v j then b * ρ - μ / 2 * ρ ^ 2 else 0) ≤
        coordinateSignLoss b μ ρ (v j) (x j) -
        coordinateSignLoss b μ ρ (v j) (ρ * v j) := by
    split_ifs with h
    · exact coordinateSignLoss_wrong_halfline hb0 hμ hρ (hv j)
        (decodeSign_wrong_imp_nonpos (hv j) h)
    · exact sub_nonneg.mpr (coordinateSignLoss_minimizer hμ hρ hb (hv j) (x j))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hi j)
  rw [Finset.sum_sub_distrib] at hs
  rw [← Finset.sum_filter] at hs
  simpa only [Finset.sum_const, nsmul_eq_mul, signObjective, signHamming, mul_comm] using hs

theorem signRadius_curvature_le {μ D a : ℝ} (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    μ * envelopeRadius μ D a ≤ a := by
  by_cases hz : μ = 0
  · simpa [hz] using ha
  · have hp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
    unfold envelopeRadius
    rw [if_neg hz]
    have := mul_le_mul_of_nonneg_left (min_le_right D (a / μ)) hμ
    simpa only [mul_div_cancel₀ a hz] using this

theorem manuscript_sign_coefficient {k : ℕ} (hk : 0 < k) (μ D a : ℝ) :
    (a / Real.sqrt (k : ℝ)) * (envelopeRadius μ D a / Real.sqrt (k : ℝ)) -
      μ / 2 * (envelopeRadius μ D a / Real.sqrt (k : ℝ)) ^ 2 =
        envelope μ D a / k := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [div_mul_div_comm, div_pow, Real.sq_sqrt hk0, Real.mul_self_sqrt hk0]
  unfold envelope radialObjective
  ring

theorem manuscript_sign_minimizer {k : ℕ} (hk : 0 < k) {μ D a : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    {v : Fin k → ℝ} (hv : ∀ j, v j = -1 ∨ v j = 1) (x : Fin k → ℝ) :
    signObjective (a / Real.sqrt (k : ℝ)) μ
      (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v
      (fun j => envelopeRadius μ D a / Real.sqrt (k : ℝ) * v j) ≤
    signObjective (a / Real.sqrt (k : ℝ)) μ
      (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v x := by
  apply signObjective_minimizer hμ
    (div_nonneg (envelopeRadius_nonneg hμ hD ha) (Real.sqrt_nonneg _))
    _ hv x
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (signRadius_curvature_le hμ ha) (Real.sqrt_nonneg (k : ℝ))

/-- Equation (loss-hamming), with the exact manuscript coefficient H(a)/k. -/
theorem manuscript_loss_hamming {k : ℕ} (hk : 0 < k) {μ D a : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    {v : Fin k → ℝ} (hv : ∀ j, v j = -1 ∨ v j = 1) (x : Fin k → ℝ) :
    envelope μ D a / k * (signHamming v x : ℝ) ≤
      signObjective (a / Real.sqrt (k : ℝ)) μ
        (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v x -
      signObjective (a / Real.sqrt (k : ℝ)) μ
        (envelopeRadius μ D a / Real.sqrt (k : ℝ)) v
        (fun j => envelopeRadius μ D a / Real.sqrt (k : ℝ) * v j) := by
  have hb : μ * (envelopeRadius μ D a / Real.sqrt (k : ℝ)) ≤
      a / Real.sqrt (k : ℝ) := by
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (signRadius_curvature_le hμ ha) (Real.sqrt_nonneg (k : ℝ))
  have hr : 0 ≤ envelopeRadius μ D a / Real.sqrt (k : ℝ) :=
    div_nonneg (envelopeRadius_nonneg hμ hD ha) (Real.sqrt_nonneg _)
  have h := signObjective_loss_hamming hμ hr hb hv x
  rw [manuscript_sign_coefficient hk] at h
  exact h

theorem manuscript_center_squared_radius {k : ℕ} (hk : 0 < k) (μ D a : ℝ)
    {v : Fin k → ℝ} (hv : ∀ j, v j = -1 ∨ v j = 1) :
    (∑ j, (envelopeRadius μ D a / Real.sqrt (k : ℝ) * v j) ^ 2) =
      (envelopeRadius μ D a) ^ 2 := by
  have hv2 (j : Fin k) : (v j) ^ 2 = 1 := by
    rcases hv j with h | h <;> rw [h] <;> norm_num
  simp only [mul_pow, hv2, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  field_simp

theorem manuscript_center_initialization {k : ℕ} (hk : 0 < k) {μ D a : ℝ}
    (hμ : 0 ≤ μ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    {v : Fin k → ℝ} (hv : ∀ j, v j = -1 ∨ v j = 1) :
    (∑ j, (envelopeRadius μ D a / Real.sqrt (k : ℝ) * v j) ^ 2) ≤ D ^ 2 := by
  rw [manuscript_center_squared_radius hk μ D a hv]
  have hR0 := envelopeRadius_nonneg hμ hD ha
  have hRD := envelopeRadius_le (μ := μ) (D := D) (a := a)
  nlinarith

end

end HeavyTail
