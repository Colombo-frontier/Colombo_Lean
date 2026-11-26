import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# The normalized hypercube hard family

This file formalizes the central algebraic novelty in the lower bound of
`2401.tex`: after flipping every hidden coordinate in turn, the squared
signals add to a Euclidean norm.  The result is pointwise, so it remains valid
at an adaptively chosen query after conditioning on the history.
-/

open scoped BigOperators RealInnerProductSpace

namespace NoisyZO

noncomputable section

/-- The Euclidean query space used in dimension `d`. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Flip coordinate `i` of a real sign vector. -/
def flip {d : ℕ} (s : Fin d → ℝ) (i : Fin d) : Fin d → ℝ :=
  fun j => if j = i then -s j else s j

@[simp] theorem flip_same {d : ℕ} (s : Fin d → ℝ) (i : Fin d) :
    flip s i i = -s i := by
  simp [flip]

@[simp] theorem flip_other {d : ℕ} (s : Fin d → ℝ) (i j : Fin d)
    (hji : j ≠ i) : flip s i j = s j := by
  simp [flip, hji]

/-- The unnormalized signed linear functional. -/
def signedSum {d : ℕ} (s : Fin d → ℝ) (x : Point d) : ℝ :=
  ∑ i : Fin d, s i * x i

theorem signedSum_flip {d : ℕ} (s : Fin d → ℝ) (i : Fin d)
    (x : Point d) :
    signedSum s x - signedSum (flip s i) x = 2 * s i * x i := by
  classical
  simp only [signedSum]
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ j : Fin d, (s j * x j - flip s i j * x j) =
        ∑ j : Fin d, if j = i then 2 * s i * x i else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [flip]
            ring
          · simp [flip, hji]
    _ = 2 * s i * x i := by simp

/-- A scalar hard hypothesis.  In the manuscript,
`ρ = a h^(β-1) / sqrt d` and `cutoff x = χ (‖x‖² / h²)`. -/
def hardValue {d : ℕ} (cutoff : Point d → ℝ) (ρ : ℝ)
    (s : Fin d → ℝ) (x : Point d) : ℝ :=
  ‖x‖ ^ 2 - ρ * signedSum s x * cutoff x

theorem hardValue_continuous {d : ℕ} {cutoff : Point d → ℝ}
    (hcutoff : Continuous cutoff) (ρ : ℝ) (s : Fin d → ℝ) :
    Continuous (hardValue cutoff ρ s) := by
  unfold hardValue signedSum
  fun_prop

theorem hardValue_neighbor_difference {d : ℕ} (cutoff : Point d → ℝ)
    (ρ : ℝ) (s : Fin d → ℝ) (i : Fin d) (x : Point d) :
    hardValue cutoff ρ s x - hardValue cutoff ρ (flip s i) x =
      -(2 * ρ * s i * x i * cutoff x) := by
  calc
    hardValue cutoff ρ s x - hardValue cutoff ρ (flip s i) x =
        -ρ * (signedSum s x - signedSum (flip s i) x) * cutoff x := by
          simp only [hardValue]
          ring
    _ = -(2 * ρ * s i * x i * cutoff x) := by
          rw [signedSum_flip]
          ring

/-- Exact summed-signal identity before the `1/sqrt d` normalization is
substituted.  This is equation (3.7) of the manuscript at its algebraic core. -/
theorem summed_neighbor_signal_sq {d : ℕ} (cutoff : Point d → ℝ)
    (ρ : ℝ) (s : Fin d → ℝ) (hs : ∀ i, s i ^ 2 = 1)
    (x : Point d) :
    (∑ i : Fin d,
        (hardValue cutoff ρ s x - hardValue cutoff ρ (flip s i) x) ^ 2) =
      4 * ρ ^ 2 * ‖x‖ ^ 2 * (cutoff x) ^ 2 := by
  classical
  simp_rw [hardValue_neighbor_difference]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i : Fin d, (-(2 * ρ * s i * x i * cutoff x)) ^ 2 =
        ∑ i : Fin d, (4 * ρ ^ 2 * (cutoff x) ^ 2) * (x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            (-(2 * ρ * s i * x i * cutoff x)) ^ 2 =
                4 * ρ ^ 2 * (s i) ^ 2 * (cutoff x) ^ 2 * (x i) ^ 2 := by ring
            _ = (4 * ρ ^ 2 * (cutoff x) ^ 2) * (x i) ^ 2 := by
              rw [hs i]
              ring
    _ = 4 * ρ ^ 2 * (∑ i : Fin d, (x i) ^ 2) * (cutoff x) ^ 2 := by
          calc
            ∑ i : Fin d, (4 * ρ ^ 2 * (cutoff x) ^ 2) * (x i) ^ 2 =
                (4 * ρ ^ 2 * (cutoff x) ^ 2) *
                  (∑ i : Fin d, (x i) ^ 2) := by
                    rw [Finset.mul_sum]
            _ = 4 * ρ ^ 2 * (∑ i : Fin d, (x i) ^ 2) * (cutoff x) ^ 2 := by
                  ring

/-- Uniform support bound for the summed signal. -/
theorem summed_neighbor_signal_le {d : ℕ} (cutoff : Point d → ℝ)
    (ρ h : ℝ) (hh : 0 ≤ h) (s : Fin d → ℝ)
    (hs : ∀ i, s i ^ 2 = 1) (x : Point d)
    (hx : ‖x‖ ≤ h) (hcut : |cutoff x| ≤ 1) :
    (∑ i : Fin d,
        (hardValue cutoff ρ s x - hardValue cutoff ρ (flip s i) x) ^ 2) ≤
      4 * ρ ^ 2 * h ^ 2 := by
  rw [summed_neighbor_signal_sq cutoff ρ s hs x]
  have hρ : 0 ≤ 4 * ρ ^ 2 := by positivity
  have hnorm : ‖x‖ ^ 2 ≤ h ^ 2 := by nlinarith [norm_nonneg x]
  have hcut_sq : (cutoff x) ^ 2 ≤ 1 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (cutoff x)) (by norm_num : (0 : ℝ) ≤ 1)).2 hcut
    simpa only [sq_abs, one_pow] using hsquare
  calc
    4 * ρ ^ 2 * ‖x‖ ^ 2 * (cutoff x) ^ 2 ≤
        4 * ρ ^ 2 * h ^ 2 * (cutoff x) ^ 2 := by
          gcongr
    _ ≤ 4 * ρ ^ 2 * h ^ 2 := by
          nlinarith [mul_nonneg hρ (sq_nonneg h)]

/-- Manuscript normalization: a query in the support has total neighboring
signal at most `4 a² h^(2β) / d`.  The analytic power `a h^(β-1)` is abstracted
as `c`; setting `c = a h^(β-1)` gives the displayed paper formula. -/
theorem normalized_summed_neighbor_signal_le {d : ℕ} (hd : 0 < d)
    (cutoff : Point d → ℝ) (c h : ℝ) (hh : 0 ≤ h)
    (s : Fin d → ℝ) (hs : ∀ i, s i ^ 2 = 1) (x : Point d)
    (hx : ‖x‖ ≤ h) (hcut : |cutoff x| ≤ 1) :
    (∑ i : Fin d,
        (hardValue cutoff (c / Real.sqrt d) s x -
          hardValue cutoff (c / Real.sqrt d) (flip s i) x) ^ 2) ≤
      4 * c ^ 2 * h ^ 2 / d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsqrt_sq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt (le_of_lt hdR)
  have hbase := summed_neighbor_signal_le cutoff (c / Real.sqrt d) h hh s hs x hx hcut
  calc
    (∑ i : Fin d,
        (hardValue cutoff (c / Real.sqrt d) s x -
          hardValue cutoff (c / Real.sqrt d) (flip s i) x) ^ 2) ≤
        4 * (c / Real.sqrt d) ^ 2 * h ^ 2 := hbase
    _ = 4 * c ^ 2 * h ^ 2 / d := by
      calc
        4 * (c / Real.sqrt d) ^ 2 * h ^ 2 =
            4 * c ^ 2 * h ^ 2 / (Real.sqrt d) ^ 2 := by
              field_simp [ne_of_gt hsqrt]
        _ = 4 * c ^ 2 * h ^ 2 / d := by rw [hsqrt_sq]

end

end NoisyZO
