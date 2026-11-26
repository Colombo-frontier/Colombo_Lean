import RandomizedFO2003.ScalarQuadraticEpoch
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace RandomizedFO2003.Accelerated

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def vectorQuadratic (A : E →L[ℝ] E) (g x : E) : ℝ :=
  inner (𝕜 := ℝ) g x + (1 / 2) * inner (𝕜 := ℝ) (A x) x

def vectorAGDStep (A : E →L[ℝ] E) (g : E) (θ : ℝ) (e p x : E) : E :=
  let y := x + (1 - θ) • (x - p)
  y - (A y + g + e)

theorem coordinate_square_sum (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i, (inner (𝕜 := ℝ) (b i) x) ^ 2 = ‖x‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner x

theorem coordinate_inner_sum (b : OrthonormalBasis ι ℝ E) (x y : E) :
    ∑ i, inner (𝕜 := ℝ) (b i) x * inner (𝕜 := ℝ) (b i) y = inner (𝕜 := ℝ) x y := by
  simpa only [real_inner_comm (b _) x] using b.sum_inner_mul_inner x y

theorem vectorQuadratic_eq_sum (A : E →L[ℝ] E) (g : E)
    (b : OrthonormalBasis ι ℝ E) (κ : ι → ℝ)
    (hdiag : ∀ v i, inner (𝕜 := ℝ) (b i) (A v) = κ i * inner (𝕜 := ℝ) (b i) v)
    (x : E) :
    vectorQuadratic A g x =
      ∑ i, scalarQuadratic (κ i) (inner (𝕜 := ℝ) (b i) g) (inner (𝕜 := ℝ) (b i) x) := by
  have he (i : ι) :
      scalarQuadratic (κ i) (inner (𝕜 := ℝ) (b i) g) (inner (𝕜 := ℝ) (b i) x) =
        inner (𝕜 := ℝ) (b i) g * inner (𝕜 := ℝ) (b i) x +
          (1 / 2) * (inner (𝕜 := ℝ) (b i) (A x) * inner (𝕜 := ℝ) (b i) x) := by
    rw [hdiag]
    unfold scalarQuadratic
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, coordinate_inner_sum, coordinate_inner_sum]
  rfl

/-- Summing the proved scalar certificates in an orthonormal diagonal basis.
The recurrence premises describe the actual perturbed quadratic iteration. -/
theorem diagonal_quadratic_epoch (A : E →L[ℝ] E) (g : E)
    (b : OrthonormalBasis ι ℝ E) (κ : ι → ℝ)
    (hdiag : ∀ v i, inner (𝕜 := ℝ) (b i) (A v) = κ i * inner (𝕜 := ℝ) (b i) v)
    (hlow : ∀ i, -2 ≤ κ i) (hhigh : ∀ i, κ i ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (e p x : ℕ → E) (hp0 : p 0 = x 0) (hp : ∀ n, p (n + 1) = x n)
    (hx : ∀ n, x (n + 1) = vectorAGDStep A g θ (e n) (p n) (x n)) (N : ℕ) :
    8 * θ * (vectorQuadratic A g (x N) - vectorQuadratic A g (x 0)) +
      3 * θ ^ 2 * ∑ k ∈ Finset.range N, ‖x (k + 1) - x k‖ ^ 2 ≤
        16 * ∑ k ∈ Finset.range N, ‖e k‖ ^ 2 := by
  have hc (i : ι) := scalar_quadratic_epoch (c := inner (𝕜 := ℝ) (b i) g)
    (fun n => inner (𝕜 := ℝ) (b i) (e n))
    (fun n => inner (𝕜 := ℝ) (b i) (p n))
    (fun n => inner (𝕜 := ℝ) (b i) (x n))
    (congrArg (fun v => inner (𝕜 := ℝ) (b i) v) hp0)
    (fun n => congrArg (fun v => inner (𝕜 := ℝ) (b i) v) (hp n))
    (by
      intro n
      dsimp only
      rw [hx n]
      simp only [vectorAGDStep, scalarAGDStep, inner_sub_right, inner_add_right,
        inner_smul_right, hdiag])
    hθ hθ1 (hlow i) (hhigh i) N
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  rw [← vectorQuadratic_eq_sum A g b κ hdiag, ← vectorQuadratic_eq_sum A g b κ hdiag] at hs
  have hsteps : (∑ i, ∑ k ∈ Finset.range N,
      (inner (𝕜 := ℝ) (b i) (x (k + 1)) - inner (𝕜 := ℝ) (b i) (x k)) ^ 2) =
      ∑ k ∈ Finset.range N, ‖x (k + 1) - x k‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← inner_sub_right, coordinate_square_sum]
  have herr : (∑ i, ∑ k ∈ Finset.range N, (inner (𝕜 := ℝ) (b i) (e k)) ^ 2) =
      ∑ k ∈ Finset.range N, ‖e k‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [coordinate_square_sum]
  rwa [hsteps, herr] at hs

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Spectral decomposition is confined to the proof; it is not an oracle
operation used by the accelerated iteration. -/
theorem vector_quadratic_epoch (A : E →L[ℝ] E) (g : E)
    (hA : IsSelfAdjoint A) (hnorm : ‖A‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (e p x : ℕ → E) (hp0 : p 0 = x 0) (hp : ∀ n, p (n + 1) = x n)
    (hx : ∀ n, x (n + 1) = vectorAGDStep A g θ (e n) (p n) (x n)) (N : ℕ) :
    8 * θ * (vectorQuadratic A g (x N) - vectorQuadratic A g (x 0)) +
      3 * θ ^ 2 * ∑ k ∈ Finset.range N, ‖x (k + 1) - x k‖ ^ 2 ≤
        16 * ∑ k ∈ Finset.range N, ‖e k‖ ^ 2 := by
  let b := hA.isSymmetric.eigenvectorBasis rfl
  let κ := hA.isSymmetric.eigenvalues rfl
  have hdiag (v : E) (i : Fin (Module.finrank ℝ E)) :
      inner (𝕜 := ℝ) (b i) (A v) = κ i * inner (𝕜 := ℝ) (b i) v := by
    simpa only [OrthonormalBasis.repr_apply_apply] using
      hA.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
  have heig (i : Fin (Module.finrank ℝ E)) : |κ i| ≤ 1 := by
    have he : A (b i) = κ i • b i := hA.isSymmetric.apply_eigenvectorBasis rfl i
    have hh := A.le_opNorm (b i)
    rw [he, norm_smul, b.norm_eq_one, mul_one, mul_one, Real.norm_eq_abs] at hh
    exact hh.trans hnorm
  exact diagonal_quadratic_epoch A g b κ hdiag
    (fun i => by have hh := (abs_le.mp (heig i)).1; linarith)
    (fun i => (abs_le.mp (heig i)).2) hθ hθ1 e p x hp0 hp hx N

end

end RandomizedFO2003.Accelerated
