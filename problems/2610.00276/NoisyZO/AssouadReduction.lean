import NoisyZO.HardFamily

/-!
# Deterministic Assouad decoding step

This module proves the pathwise part of the manuscript's conversion from
Hamming error to optimization loss.  The probabilistic Assouad/Pinsker bound
can be plugged into this theorem after integration.
-/

open scoped BigOperators

namespace NoisyZO

noncomputable section

def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem boolSign_true : boolSign true = 1 := by rfl
@[simp] theorem boolSign_false : boolSign false = -1 := by rfl

def decode {d : ℕ} (x : Point d) (i : Fin d) : Bool :=
  if 0 ≤ x i then true else false

/-- Real-valued Hamming loss, convenient for expectation and finite sums. -/
def hammingLoss {d : ℕ} (s : Fin d → Bool) (x : Point d) : ℝ :=
  ∑ i : Fin d, if decode x i = s i then 0 else 1

/-- The minimizer location in the hard family, with `c ≥ 0` its coordinate
magnitude. -/
def signCenter {d : ℕ} (c : ℝ) (s : Fin d → Bool) : Point d :=
  WithLp.toLp 2 (fun i => c * boolSign (s i))

@[simp] theorem signCenter_apply {d : ℕ} (c : ℝ) (s : Fin d → Bool)
    (i : Fin d) : signCenter c s i = c * boolSign (s i) := rfl

private theorem coordinate_error_sq {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (s : Fin d → Bool) (x : Point d) (i : Fin d) :
    c ^ 2 * (if decode x i = s i then 0 else 1) ≤
      (x i - signCenter c s i) ^ 2 := by
  unfold decode
  by_cases hx : 0 ≤ x i <;> cases hs : s i <;>
    simp [hx, hs, signCenter, boolSign] <;> nlinarith

/-- Every incorrectly decoded coordinate costs at least `c²` in squared
Euclidean distance. -/
theorem hamming_le_distance_sq {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (s : Fin d → Bool) (x : Point d) :
    c ^ 2 * hammingLoss s x ≤ ‖x - signCenter c s‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [hammingLoss, Finset.mul_sum, PiLp.sub_apply, signCenter_apply]
  exact Finset.sum_le_sum (fun i _ => coordinate_error_sq hc s x i)

/-- Strong convexity turns the preceding squared-distance lower bound into
the loss bound used after Assouad's lemma. -/
theorem hamming_to_stronglyConvex_loss {d : ℕ} {c gap : ℝ} (hc : 0 ≤ c)
    (s : Fin d → Bool) (x : Point d)
    (hstrong : (1 / 2 : ℝ) * ‖x - signCenter c s‖ ^ 2 ≤ gap) :
    (c ^ 2 / 2) * hammingLoss s x ≤ gap := by
  have hdist := hamming_le_distance_sq hc s x
  calc
    (c ^ 2 / 2) * hammingLoss s x =
        (1 / 2 : ℝ) * (c ^ 2 * hammingLoss s x) := by ring
    _ ≤ (1 / 2 : ℝ) * ‖x - signCenter c s‖ ^ 2 := by gcongr
    _ ≤ gap := hstrong

end

end NoisyZO
