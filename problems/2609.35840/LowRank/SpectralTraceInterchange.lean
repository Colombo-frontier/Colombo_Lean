import LowRank.KrylovMatrixPolynomial
import LowRank.SpectralPowers
import Mathlib.LinearAlgebra.Lagrange

/-! The nonzero spectra of rectangular products have identical spectral
sums. Finite polynomial interpolation reduces arbitrary functions vanishing
at zero to cyclic trace identities, including singular and empty matrices. -/

namespace LowRank
open Matrix Polynomial
open scoped Matrix BigOperators
noncomputable section

theorem rectangular_mul_pow_intertwine {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin a) ℝ) (n : ℕ) :
    A * (B * A) ^ n = (A * B) ^ n * A := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc A, ih]
    simp only [Matrix.mul_assoc]

theorem rectangular_mul_aeval_intertwine {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin a) ℝ) (f : ℝ[X]) :
    A * aeval (B * A) f = aeval (A * B) f * A := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hf, hg]
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def, Matrix.mul_smul, Matrix.smul_mul,
      rectangular_mul_pow_intertwine]

theorem trace_rectangular_mul_aeval {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin a) ℝ) (f : ℝ[X]) :
    ((B * A) * aeval (B * A) f).trace = ((A * B) * aeval (A * B) f).trace := by
  rw [Matrix.mul_assoc, rectangular_mul_aeval_intertwine]
  calc
    _ = ((aeval (A * B) f * A) * B).trace := Matrix.trace_mul_comm _ _
    _ = (aeval (A * B) f * (A * B)).trace := by rw [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

theorem OrderedMatrixSpectrum.trace_mul_aeval {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (sp : OrderedMatrixSpectrum H) (f : ℝ[X]) :
    (H * aeval H f).trace = ∑ i, sp.value i * f.eval (sp.value i) := by
  have h := congrArg Matrix.trace (sp.diagonalizes_aeval (X * f))
  rw [Matrix.trace_mul_cycle, sp.orthogonal_right, Matrix.one_mul, Matrix.trace_diagonal] at h
  simpa only [map_mul, aeval_X, eval_mul, eval_X] using h

theorem spectral_sum_rectangular_mul_comm {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin a) ℝ)
    (spBA : OrderedMatrixSpectrum (B * A)) (spAB : OrderedMatrixSpectrum (A * B))
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    (∑ i, φ (spBA.value i)) = ∑ j, φ (spAB.value j) := by
  classical
  let S := Finset.univ.image spBA.value ∪ Finset.univ.image spAB.value
  let f := Lagrange.interpolate S id (fun x => φ x / x)
  have hf (x : ℝ) (hx : x ∈ S) : x * f.eval x = φ x := by
    have he : f.eval x = φ x / x :=
      Lagrange.eval_interpolate_at_node (fun x => φ x / x) Function.injective_id.injOn hx
    rw [he]
    by_cases hx0 : x = 0
    · simp [hx0, hφ]
    · exact mul_div_cancel₀ _ hx0
  have h := trace_rectangular_mul_aeval A B f
  rw [spBA.trace_mul_aeval, spAB.trace_mul_aeval] at h
  have hleft (i : Fin b) : spBA.value i * f.eval (spBA.value i) = φ (spBA.value i) :=
    hf _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hright (j : Fin a) : spAB.value j * f.eval (spAB.value j) = φ (spAB.value j) :=
    hf _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  simpa only [hleft, hright] using h

end
end LowRank
