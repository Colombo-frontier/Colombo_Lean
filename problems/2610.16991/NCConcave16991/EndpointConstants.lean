import NCConcave16991.PipeEnergy
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.Rev

/-!
# Hyperbolic Green column of the actual massive Neumann path

This file verifies the hyperbolic profile against the already constructed
tridiagonal operator, and identifies it with the actual inverse column by
invertibility. Closed-form identities are proved, rather than assumed as an
interface for endpoint estimates.
-/

namespace NCConcave16991
namespace EndpointConstants

open PipeEnergy Matrix
open scoped BigOperators Matrix

theorem cosh_three_term (x t : ℝ) :
    2 * Real.cosh t * Real.cosh x - Real.cosh (x - t) - Real.cosh (x + t) = 0 := by
  rw [Real.cosh_sub, Real.cosh_add]
  ring

theorem cosh_root_identity (t : ℝ) :
    (2 * Real.cosh t - 1) * Real.cosh (t / 2) - Real.cosh (3 * t / 2) = 0 := by
  have hh := cosh_three_term (t / 2) t
  rw [show t / 2 - t = -(t / 2) by ring, Real.cosh_neg,
    show t / 2 + t = 3 * t / 2 by ring] at hh
  linarith

theorem cosh_terminal_identity (N t : ℝ) :
    (2 * Real.cosh t - 1) * Real.cosh ((N - 1 / 2) * t) -
      Real.cosh ((N - 3 / 2) * t) =
      2 * Real.sinh (N * t) * Real.sinh (t / 2) := by
  have hh := cosh_three_term ((N - 1 / 2) * t) t
  rw [show (N - 1 / 2) * t - t = (N - 3 / 2) * t by ring,
    show (N - 1 / 2) * t + t = (N + 1 / 2) * t by ring] at hh
  have hd : Real.cosh ((N + 1 / 2) * t) - Real.cosh ((N - 1 / 2) * t) =
      2 * Real.sinh (N * t) * Real.sinh (t / 2) := by
    rw [show (N + 1 / 2) * t = N * t + t / 2 by ring,
      show (N - 1 / 2) * t = N * t - t / 2 by ring,
      Real.cosh_add, Real.cosh_sub]
    ring
  linarith

noncomputable def coshProfile (N t x : ℝ) : ℝ :=
  Real.cosh ((x + 1 / 2) * t) / (2 * Real.sinh (N * t) * Real.sinh (t / 2))

theorem profile_denominator_pos {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    0 < 2 * Real.sinh (N * t) * Real.sinh (t / 2) := by
  apply mul_pos
  · exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (mul_pos hN ht))
  · exact Real.sinh_pos_iff.mpr (by linarith)

theorem coshProfile_root {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    ((2 * Real.cosh t - 2) + 1) * coshProfile N t 0 - coshProfile N t 1 = 0 := by
  have hD := profile_denominator_pos hN ht
  unfold coshProfile
  rw [show (0 + 1 / 2 : ℝ) * t = t / 2 by ring,
    show (1 + 1 / 2 : ℝ) * t = 3 * t / 2 by ring]
  field_simp [ne_of_gt hD]
  rw [show t * 3 / 2 = 3 * t / 2 by ring]
  nlinarith [cosh_root_identity t]

theorem coshProfile_terminal {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    ((2 * Real.cosh t - 2) + 1) * coshProfile N t (N - 1) -
      coshProfile N t (N - 2) = 1 := by
  have hD := profile_denominator_pos hN ht
  unfold coshProfile
  rw [show (N - 1 + 1 / 2) * t = (N - 1 / 2) * t by ring,
    show (N - 2 + 1 / 2) * t = (N - 3 / 2) * t by ring]
  field_simp [ne_of_gt hD]
  rw [show (2 * N - 1) * t / 2 = (N - 1 / 2) * t by ring,
    show t * (2 * N - 3) / 2 = (N - 3 / 2) * t by ring]
  nlinarith [cosh_terminal_identity N t]

theorem coshProfile_interior {N t : ℝ} (hN : 0 < N) (ht : 0 < t) (x : ℝ) :
    ((2 * Real.cosh t - 2) + 2) * coshProfile N t x -
      coshProfile N t (x - 1) - coshProfile N t (x + 1) = 0 := by
  have hD := profile_denominator_pos hN ht
  unfold coshProfile
  rw [show (x - 1 + 1 / 2) * t = (x + 1 / 2) * t - t by ring,
    show (x + 1 + 1 / 2) * t = (x + 1 / 2) * t + t by ring]
  field_simp [ne_of_gt hD]
  rw [show (2 * x + 1) * t / 2 = (x + 1 / 2) * t by ring,
    show t * (2 * x + 1 - 2) / 2 = (x + 1 / 2) * t - t by ring,
    show t * (2 * x + 1 + 2) / 2 = (x + 1 / 2) * t + t by ring]
  nlinarith [cosh_three_term ((x + 1 / 2) * t) t]

noncomputable def profileVector (m : ℕ) (t : ℝ) : Fin (m + 2) → ℝ :=
  fun j => coshProfile ((m : ℝ) + 2) t j.val

theorem profileVector_root (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (massPath (m + 1) (2 * Real.cosh t - 2) *ᵥ profileVector m t) 0 = 0 := by
  rw [massPath_root_recurrence]
  simpa only [profileVector, Fin.val_zero, Fin.val_succ, Nat.cast_zero, zero_add,
    Nat.cast_one] using coshProfile_root (show 0 < (m : ℝ) + 2 by positivity) ht

theorem profileVector_last (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (massPath (m + 1) (2 * Real.cosh t - 2) *ᵥ profileVector m t)
      (Fin.last (m + 1)) = 1 := by
  rw [massPath_last_recurrence]
  have hh := coshProfile_terminal (show 0 < (m : ℝ) + 2 by positivity) ht
  rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring,
    show (m : ℝ) + 2 - 2 = (m : ℝ) by ring] at hh
  simpa only [profileVector, Fin.val_last, Fin.val_castSucc, Nat.cast_add,
    Nat.cast_one] using hh

theorem profileVector_interior (m : ℕ) {t : ℝ} (ht : 0 < t) (j : Fin (m + 1)) :
    (massPath (m + 2) (2 * Real.cosh t - 2) *ᵥ profileVector (m + 1) t)
      j.succ.castSucc = 0 := by
  rw [massPath_interior_recurrence]
  have hh := coshProfile_interior (show 0 < ((m + 1 : ℕ) : ℝ) + 2 by positivity)
    ht ((j.val : ℝ) + 1)
  rw [show (j.val : ℝ) + 1 - 1 = (j.val : ℝ) by ring] at hh
  simpa only [profileVector, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    using hh

/-- The proposed profile satisfies the actual finite matrix equation at every
vertex, including both Neumann boundaries. -/
theorem profileVector_equation (m : ℕ) {t : ℝ} (ht : 0 < t) :
    massPath (m + 1) (2 * Real.cosh t - 2) *ᵥ profileVector m t =
      Pi.single (Fin.last (m + 1)) 1 := by
  ext j
  by_cases hz : j = 0
  · subst j
    rw [profileVector_root m ht]
    have hne : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]
    simp [hne]
  by_cases hl : j = Fin.last (m + 1)
  · subst j
    rw [profileVector_last m ht]
    simp
  cases m with
  | zero =>
    have hj := j.isLt
    have hzero : j.val ≠ 0 := fun h => hz (Fin.ext h)
    have hlast : j.val ≠ 1 := fun h => hl (Fin.ext h)
    omega
  | succ m =>
    have hj := j.isLt
    have hzero : j.val ≠ 0 := fun h => hz (Fin.ext h)
    have hlast : j.val ≠ m + 2 := fun h => hl (Fin.ext h)
    let k : Fin (m + 1) := ⟨j.val - 1, by omega⟩
    have hk : k.succ.castSucc = j := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ, k]
      omega
    rw [← hk, profileVector_interior m ht]
    simp [Fin.castSucc_ne_last]

/-- The closed form is identified with the actual inverse terminal column
using the proved invertibility of the path matrix. -/
theorem terminalGreen_hyperbolic (m : ℕ) {t : ℝ} (ht : 0 < t) :
    terminalGreen m (2 * Real.cosh t - 2) = profileVector m t := by
  have hmass : 0 < 2 * Real.cosh t - 2 := by
    have hh := Real.one_lt_cosh.mpr (ne_of_gt ht)
    linarith
  apply Matrix.mulVec_injective_of_isUnit (massPath_isUnit (m + 1) hmass)
  rw [profileVector_equation m ht]
  exact optimizer_equation (massPath_posDef (m + 1) hmass) _

theorem cosh_one_lt_eight_fifths : Real.cosh 1 < (8 / 5 : ℝ) := by
  have helo : (5 / 2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hehi : Real.exp 1 < (11 / 4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hinv : Real.exp (-1) < (2 / 5 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
    linarith
  rw [Real.cosh_eq]
  linarith

theorem sinh_one_lt_two : Real.sinh 1 < 2 := by
  have hehi : Real.exp 1 < (11 / 4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [Real.sinh_eq]
  linarith [Real.exp_pos (-1)]

noncomputable def theta (N : ℝ) : ℝ := 2 * Real.arsinh (1 / (2 * N))

theorem theta_pos {N : ℝ} (hN : 0 < N) : 0 < theta N := by
  unfold theta
  exact mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by positivity))

theorem theta_mass {N : ℝ} (hN : 0 < N) :
    2 * Real.cosh (theta N) - 2 = 1 / N ^ 2 := by
  unfold theta
  rw [Real.cosh_two_mul, Real.cosh_sq, Real.sinh_arsinh]
  field_simp
  ring

theorem theta_small {N : ℝ} (hN : 0 < N) : N * theta N < 1 := by
  have hx : 0 < 1 / (2 * N) := by positivity
  have ha := Real.arsinh_pos_iff.mpr hx
  have hh := Real.self_lt_sinh_iff.mpr ha
  rw [Real.sinh_arsinh] at hh
  have hmul := mul_lt_mul_of_pos_left hh (show 0 < 2 * N by positivity)
  have hcancel : (2 * N) * (1 / (2 * N)) = 1 := by field_simp
  rw [hcancel] at hmul
  dsimp [theta]
  nlinarith

theorem theta_half_sinh {N : ℝ} : Real.sinh (theta N / 2) = 1 / (2 * N) := by
  unfold theta
  rw [show 2 * Real.arsinh (1 / (2 * N)) / 2 = Real.arsinh (1 / (2 * N)) by ring]
  exact Real.sinh_arsinh _

/-- The paper's actual normalized Green column in its hyperbolic closed form. -/
theorem normalized_terminalGreen_closed_form (m : ℕ) :
    terminalGreen m (1 / ((m : ℝ) + 2) ^ 2) = profileVector m (theta ((m : ℝ) + 2)) := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  simpa only [theta_mass hN] using terminalGreen_hyperbolic m (theta_pos hN)

def reverseVector {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := fun j => v j.rev

theorem dotProduct_reverse {n : ℕ} (u v : Fin n → ℝ) :
    reverseVector u ⬝ᵥ v = u ⬝ᵥ reverseVector v := by
  unfold reverseVector dotProduct
  exact Fintype.sum_equiv Fin.revPerm _ _ (by intro j; simp)

theorem incidence_reverse (m : ℕ) (v : Fin (m + 1) → ℝ) :
    incidence m *ᵥ reverseVector v = -reverseVector (incidence m *ᵥ v) := by
  ext j
  simp only [incidence_mulVec, reverseVector, Pi.neg_apply, Fin.rev_succ, Fin.rev_castSucc]
  ring

theorem massPath_bilinear (m : ℕ) (μ : ℝ) (u v : Fin (m + 1) → ℝ) :
    u ⬝ᵥ (massPath m μ *ᵥ v) =
      μ * (u ⬝ᵥ v) + (incidence m *ᵥ u) ⬝ᵥ (incidence m *ᵥ v) := by
  unfold massPath pathLaplacian
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

theorem massPath_bilinear_reverse (m : ℕ) (μ : ℝ) (u v : Fin (m + 1) → ℝ) :
    u ⬝ᵥ (massPath m μ *ᵥ reverseVector v) =
      reverseVector u ⬝ᵥ (massPath m μ *ᵥ v) := by
  rw [massPath_bilinear, massPath_bilinear, incidence_reverse, incidence_reverse]
  simp only [dotProduct_neg, neg_dotProduct]
  rw [dotProduct_reverse u v, dotProduct_reverse]

/-- Reflection symmetry of the actual operator is proved from the incidence
matrix, before making any assertion about inverse endpoint entries. -/
theorem massPath_reverse (m : ℕ) (μ : ℝ) (v : Fin (m + 1) → ℝ) :
    massPath m μ *ᵥ reverseVector v = reverseVector (massPath m μ *ᵥ v) := by
  ext j
  have hh := massPath_bilinear_reverse m μ (Pi.single j 1) v
  rw [dotProduct_reverse] at hh
  simpa using hh

theorem reverseVector_single {n : ℕ} (j : Fin n) (a : ℝ) :
    reverseVector (Pi.single j a) = Pi.single j.rev a := by
  ext i
  simp [reverseVector, Pi.single_apply, Fin.rev_eq_iff]

theorem rootGreen_reverse (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    optimizer (massPath (m + 1) μ) (Pi.single 0 1) = reverseVector (terminalGreen m μ) := by
  have hM := massPath_posDef (m + 1) hμ
  have he : massPath (m + 1) μ *ᵥ terminalGreen m μ =
      Pi.single (Fin.last (m + 1)) 1 := optimizer_equation hM _
  apply Matrix.mulVec_injective_of_isUnit hM.isUnit
  rw [optimizer_equation hM, massPath_reverse, he, reverseVector_single]
  simp

theorem inverse_endpoint_diagonal_eq (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (massPath (m + 1) μ)⁻¹ 0 0 = terminalGreen m μ (Fin.last (m + 1)) := by
  have hh := congrArg (fun v : Fin (m + 2) → ℝ => v 0) (rootGreen_reverse m hμ)
  simpa [optimizer, reverseVector, Matrix.mulVec_single_one] using hh

noncomputable def endpointK (m : ℕ) : ℝ :=
  (massPath (m + 1) (1 / ((m : ℝ) + 2) ^ 2))⁻¹ 0 (Fin.last (m + 1))

noncomputable def endpointC (m : ℕ) : ℝ :=
  (massPath (m + 1) (1 / ((m : ℝ) + 2) ^ 2))⁻¹ 0 0 / endpointK m

noncomputable def endpointD (m : ℕ) : ℝ := (2 - endpointC m) / 2

theorem endpointK_eq_green (m : ℕ) :
    endpointK m = terminalGreen m (1 / ((m : ℝ) + 2) ^ 2) 0 := by
  simp [endpointK, terminalGreen, optimizer]

/-- The endpoint Green formula is a consequence of the actual inverse-column
identification and the arsinh normalization. -/
theorem endpointK_formula (m : ℕ) :
    endpointK m = ((m : ℝ) + 2) * Real.cosh (theta ((m : ℝ) + 2) / 2) /
      Real.sinh (((m : ℝ) + 2) * theta ((m : ℝ) + 2)) := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  have ht := theta_pos hN
  have hs : 0 < Real.sinh (((m : ℝ) + 2) * theta ((m : ℝ) + 2)) :=
    Real.sinh_pos_iff.mpr (mul_pos hN ht)
  rw [endpointK_eq_green, normalized_terminalGreen_closed_form]
  simp only [profileVector, coshProfile, Fin.val_zero, Nat.cast_zero, zero_add]
  rw [show (1 / 2 : ℝ) * theta ((m : ℝ) + 2) = theta ((m : ℝ) + 2) / 2 by ring,
    theta_half_sinh]
  field_simp [ne_of_gt hN, ne_of_gt hs]

theorem endpointC_formula (m : ℕ) :
    endpointC m =
      Real.cosh ((((m : ℝ) + 2) - 1 / 2) * theta ((m : ℝ) + 2)) /
      Real.cosh (theta ((m : ℝ) + 2) / 2) := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  have ht := theta_pos hN
  have hD := profile_denominator_pos hN ht
  have hhalf := Real.cosh_pos (theta ((m : ℝ) + 2) / 2)
  unfold endpointC
  rw [inverse_endpoint_diagonal_eq m (show 0 < 1 / ((m : ℝ) + 2) ^ 2 by positivity),
    endpointK_eq_green, normalized_terminalGreen_closed_form]
  simp only [profileVector, coshProfile, Fin.val_last, Fin.val_zero, Nat.cast_zero,
    zero_add, Nat.cast_add, Nat.cast_one]
  rw [show ((m : ℝ) + 1 + 1 / 2) * theta ((m : ℝ) + 2) =
      (((m : ℝ) + 2) - 1 / 2) * theta ((m : ℝ) + 2) by ring,
    show (1 / 2 : ℝ) * theta ((m : ℝ) + 2) = theta ((m : ℝ) + 2) / 2 by ring]
  field_simp [ne_of_gt hD, ne_of_gt hhalf]

theorem endpointK_lower (m : ℕ) : ((m : ℝ) + 2) / 2 < endpointK m := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  have ht := theta_pos hN
  have hs : 0 < Real.sinh (((m : ℝ) + 2) * theta ((m : ℝ) + 2)) :=
    Real.sinh_pos_iff.mpr (mul_pos hN ht)
  have hslt : Real.sinh (((m : ℝ) + 2) * theta ((m : ℝ) + 2)) < 2 :=
    (Real.sinh_lt_sinh.mpr (theta_small hN)).trans sinh_one_lt_two
  have hc : 1 ≤ Real.cosh (theta ((m : ℝ) + 2) / 2) := Real.one_le_cosh _
  rw [endpointK_formula]
  apply (lt_div_iff₀ hs).mpr
  have hh := mul_lt_mul_of_pos_left hslt (show 0 < ((m : ℝ) + 2) / 2 by positivity)
  have hcosh := mul_le_mul_of_nonneg_left hc hN.le
  nlinarith

theorem normalized_green_minimum (m : ℕ) (j : Fin (m + 2)) :
    endpointK m ≤ terminalGreen m (1 / ((m : ℝ) + 2) ^ 2) j := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  have ht := theta_pos hN
  have hD := profile_denominator_pos hN ht
  rw [endpointK_eq_green, normalized_terminalGreen_closed_form]
  simp only [profileVector, coshProfile, Fin.val_zero, Nat.cast_zero, zero_add]
  apply div_le_div_of_nonneg_right _ hD.le
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) * theta ((m : ℝ) + 2)),
    abs_of_nonneg (by positivity : 0 ≤ ((j.val : ℝ) + 1 / 2) * theta ((m : ℝ) + 2))]
  nlinarith [show 0 ≤ (j.val : ℝ) by positivity]

theorem endpointK_upper (m : ℕ) : endpointK m ≤ (m : ℝ) + 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin (m + 2)) _ => normalized_green_minimum m j)
  rw [terminalGreen_sum_normalized] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat] at hh
  have hN : 0 < (m : ℝ) + 2 := by positivity
  nlinarith

theorem endpointC_lower (m : ℕ) : 1 ≤ endpointC m := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  have ht := theta_pos hN
  have hcoef : 0 ≤ ((m : ℝ) + 2) - 1 / 2 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [endpointC_formula]
  apply (one_le_div (Real.cosh_pos _)).mpr
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (by positivity : 0 ≤ theta ((m : ℝ) + 2) / 2),
    abs_of_nonneg (mul_nonneg hcoef ht.le)]
  nlinarith [show 0 ≤ (m : ℝ) * theta ((m : ℝ) + 2) by positivity]

theorem endpointC_upper (m : ℕ) : endpointC m < Real.cosh 1 := by
  have hN : 0 < (m : ℝ) + 2 := by positivity
  have ht := theta_pos hN
  have hsmall := theta_small hN
  have hcoef : 0 ≤ ((m : ℝ) + 2) - 1 / 2 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have harg : 0 ≤ (((m : ℝ) + 2) - 1 / 2) * theta ((m : ℝ) + 2) := mul_nonneg hcoef ht.le
  have harglt : (((m : ℝ) + 2) - 1 / 2) * theta ((m : ℝ) + 2) < 1 := by nlinarith
  have hnum : Real.cosh ((((m : ℝ) + 2) - 1 / 2) * theta ((m : ℝ) + 2)) <
      Real.cosh 1 := by
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_nonneg harg, abs_one] using harglt
  rw [endpointC_formula]
  apply lt_of_le_of_lt _ hnum
  apply (div_le_iff₀ (Real.cosh_pos _)).mpr
  exact le_mul_of_one_le_right (Real.cosh_pos _).le (Real.one_le_cosh _)

theorem endpointD_bounds (m : ℕ) : (1 / 5 : ℝ) < endpointD m ∧ endpointD m ≤ 1 / 2 := by
  unfold endpointD
  have hcL := endpointC_lower m
  have hcU := (endpointC_upper m).trans cosh_one_lt_eight_fifths
  constructor <;> linarith

/-- The uniform endpoint constants of Lemma E.11, for every `N=m+2 ≥ 2`,
using the actual inverse entries from its definition. -/
theorem uniform_endpoint_constants (m : ℕ) :
    (((m : ℝ) + 2) / 2 < endpointK m ∧ endpointK m ≤ (m : ℝ) + 2) ∧
    (1 ≤ endpointC m ∧ endpointC m < Real.cosh 1) ∧
    ((1 / 5 : ℝ) < endpointD m ∧ endpointD m ≤ 1 / 2) :=
  ⟨⟨endpointK_lower m, endpointK_upper m⟩,
    ⟨endpointC_lower m, endpointC_upper m⟩, endpointD_bounds m⟩

/-- The same result stated for an arbitrary prescribed integer `N ≥ 2`.
The matrix has `N-1` path edges and therefore exactly `N` vertices. -/
theorem uniform_endpoint_constants_for_dimension (N : ℕ) (hN : 2 ≤ N) :
    let M := massPath (N - 1) (1 / (N : ℝ) ^ 2)
    let k := M⁻¹ 0 (Fin.last (N - 1))
    let c := M⁻¹ 0 0 / k
    let d := (2 - c) / 2
    ((N : ℝ) / 2 < k ∧ k ≤ N) ∧
      (1 ≤ c ∧ c < Real.cosh 1) ∧
      ((1 / 5 : ℝ) < d ∧ d ≤ 1 / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  subst N
  have hs : (m + 2) - 1 = m + 1 := by omega
  dsimp only
  rw [hs]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  exact uniform_endpoint_constants m

end EndpointConstants
end NCConcave16991
