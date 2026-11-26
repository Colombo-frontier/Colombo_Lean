import LowRank.MeasurableKernelVector
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Measurable orthonormal frames inside rectangular matrix kernels

The frame is constructed, not assumed: repeatedly select the measurable unit
kernel vector of the matrix consisting of the original rows and all previously
selected vectors. The added rows enforce orthogonality. Rank-nullity ensures
that the kernel remains nontrivial for every required selection.
-/

namespace Matvec
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

/-- A rectangular matrix with fewer rows than columns has a nonzero kernel vector. -/
theorem rectangular_nonzero_kernel {a k : ℕ} (A : Matrix (Fin a) (Fin k) ℝ)
    (h : a < k) : ∃ z : Fin k → ℝ, z ≠ 0 ∧ A *ᵥ z = 0 := by
  have hdim : Module.finrank ℝ (Fin a → ℝ) < Module.finrank ℝ (Fin k → ℝ) := by
    simpa using h
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := A.mulVecLin) hdim
  obtain ⟨z, hz, hne⟩ := (Submodule.ne_bot_iff _).mp hk
  exact ⟨z, hne, hz⟩

/-- Add previously selected unit vectors as additional row constraints. -/
def kernelConstraints {q k : ℕ} (A : Matrix (Fin q) (Fin k) ℝ) :
    (n : ℕ) → Matrix (Fin (q + n)) (Fin k) ℝ
  | 0 => A
  | n + 1 => Fin.cons (LowRank.kernelUnitVector (kernelConstraints A n)) (kernelConstraints A n)

/-- The next vector is the canonical measurable kernel vector of the current constraints. -/
def kernelVectorAt {q k : ℕ} (A : Matrix (Fin q) (Fin k) ℝ) (n : ℕ) : Fin k → ℝ :=
  LowRank.kernelUnitVector (kernelConstraints A n)

theorem kernelConstraints_kernel_previous {q k n : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (z : Fin k → ℝ)
    (h : kernelConstraints A (n + 1) *ᵥ z = 0) : kernelConstraints A n *ᵥ z = 0 := by
  ext i
  have hi := congrFun h i.succ
  simpa only [kernelConstraints, Matrix.mulVec, Fin.cons_succ, Pi.zero_apply] using hi

theorem kernelConstraints_kernel_latest {q k n : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (z : Fin k → ℝ)
    (h : kernelConstraints A (n + 1) *ᵥ z = 0) : kernelVectorAt A n ⬝ᵥ z = 0 := by
  have hi := congrFun h 0
  simpa only [kernelConstraints, Matrix.mulVec, Fin.cons_zero, Pi.zero_apply, kernelVectorAt]
    using hi

theorem kernelConstraints_kernel_original {q k : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (n : ℕ) (z : Fin k → ℝ)
    (h : kernelConstraints A n *ᵥ z = 0) : A *ᵥ z = 0 := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (kernelConstraints_kernel_previous A z h)

theorem kernelConstraints_kernel_earlier {q k : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (n : ℕ) (z : Fin k → ℝ)
    (h : kernelConstraints A n *ᵥ z = 0) :
    ∀ i < n, kernelVectorAt A i ⬝ᵥ z = 0 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases heq : i = n
    · subst i; exact kernelConstraints_kernel_latest A z h
    · exact ih (kernelConstraints_kernel_previous A z h) i (by omega)

theorem kernelVectorAt_in_kernel {q k : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (n : ℕ) : A *ᵥ kernelVectorAt A n = 0 :=
  kernelConstraints_kernel_original A n _ (LowRank.kernelUnitVector_in_kernel _)

theorem kernelVectorAt_dot_self {q k : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (n : ℕ) (h : q + n < k) :
    kernelVectorAt A n ⬝ᵥ kernelVectorAt A n = 1 :=
  LowRank.kernelUnitVector_dot_self _ (rectangular_nonzero_kernel _ h)

theorem kernelVectorAt_dot_eq_zero {q k : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (i j : ℕ) (hij : i < j) :
    kernelVectorAt A i ⬝ᵥ kernelVectorAt A j = 0 :=
  kernelConstraints_kernel_earlier A j _ (LowRank.kernelUnitVector_in_kernel _) i hij

theorem measurable_kernelConstraints (q k : ℕ) : ∀ n,
    Measurable (fun A : Matrix (Fin q) (Fin k) ℝ => kernelConstraints A n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [kernelConstraints, Fin.cons_zero] using
        (LowRank.measurable_kernelUnitVector (q + n) k).comp ih
    · simpa only [kernelConstraints, Fin.cons_succ] using (measurable_pi_apply j).comp ih

theorem measurable_kernelVectorAt (q k n : ℕ) :
    Measurable (fun A : Matrix (Fin q) (Fin k) ℝ => kernelVectorAt A n) :=
  (LowRank.measurable_kernelUnitVector (q + n) k).comp (measurable_kernelConstraints q k n)

/-- A total measurable matrix-valued frame selector. The dimension hypothesis
is needed only for its orthonormality, not for measurability or annihilation. -/
def kernelFrame {q k : ℕ} (A : Matrix (Fin q) (Fin k) ℝ) (ℓ : ℕ) :
    Matrix (Fin k) (Fin ℓ) ℝ := fun i j => kernelVectorAt A j.val i

theorem measurable_kernelFrame (q k ℓ : ℕ) :
    Measurable (fun A : Matrix (Fin q) (Fin k) ℝ => kernelFrame A ℓ) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply i).comp (measurable_kernelVectorAt q k j.val)

theorem mul_kernelFrame {q k : ℕ} (A : Matrix (Fin q) (Fin k) ℝ) (ℓ : ℕ) :
    A * kernelFrame A ℓ = 0 := by
  ext i j
  exact congrFun (kernelVectorAt_in_kernel A j.val) i

/-- The constructed frame has orthonormal columns whenever the dimension
bound leaves enough kernel directions. -/
theorem kernelFrame_orthonormal {q k ℓ : ℕ} (A : Matrix (Fin q) (Fin k) ℝ)
    (hdim : q + ℓ ≤ k) : (kernelFrame A ℓ)ᵀ * kernelFrame A ℓ = 1 := by
  ext i j
  change kernelVectorAt A i.val ⬝ᵥ kernelVectorAt A j.val = (1 : Matrix (Fin ℓ) (Fin ℓ) ℝ) i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    exact kernelVectorAt_dot_self A i.val (by omega)
  · rw [Matrix.one_apply_ne hij]
    have hne : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact kernelVectorAt_dot_eq_zero A i.val j.val hlt
    · rw [dotProduct_comm]
      exact kernelVectorAt_dot_eq_zero A j.val i.val hgt

/-- Natural-subtraction formulation, including the empty frame when `k < q`. -/
theorem kernelFrame_orthonormal_of_le_sub {q k ℓ : ℕ}
    (A : Matrix (Fin q) (Fin k) ℝ) (hdim : ℓ ≤ k - q) :
    (kernelFrame A ℓ)ᵀ * kernelFrame A ℓ = 1 := by
  by_cases hq : q ≤ k
  · exact kernelFrame_orthonormal A (by omega)
  · have hℓ : ℓ = 0 := by omega
    subst ℓ
    ext i j
    exact Fin.elim0 i

/-- Requested kernel-frame existence, proved by the explicit selector above. -/
theorem exists_measurable_kernelFrame (q k ℓ : ℕ) (hdim : q + ℓ ≤ k) :
    ∃ V : Matrix (Fin q) (Fin k) ℝ → Matrix (Fin k) (Fin ℓ) ℝ,
      Measurable V ∧ (∀ A, A * V A = 0) ∧ (∀ A, (V A)ᵀ * V A = 1) :=
  ⟨fun A => kernelFrame A ℓ, measurable_kernelFrame q k ℓ,
    fun A => mul_kernelFrame A ℓ, fun A => kernelFrame_orthonormal A hdim⟩

/-- A measurable orthonormal kernel frame under exactly the nullity lower
bound stated in the manuscript. -/
theorem exists_measurable_kernelFrame_of_le_sub (q k ℓ : ℕ) (hdim : ℓ ≤ k - q) :
    ∃ V : Matrix (Fin q) (Fin k) ℝ → Matrix (Fin k) (Fin ℓ) ℝ,
      Measurable V ∧ (∀ A, A * V A = 0) ∧ (∀ A, (V A)ᵀ * V A = 1) :=
  ⟨fun A => kernelFrame A ℓ, measurable_kernelFrame q k ℓ,
    fun A => mul_kernelFrame A ℓ, fun A => kernelFrame_orthonormal_of_le_sub A hdim⟩

end
end Matvec
