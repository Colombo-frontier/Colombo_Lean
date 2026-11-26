import LowRank.MeasurableSpectralBasis
import LowRank.OptimalSpectralColumns

/-! A single measurable orthonormal column selector attains the optimum
for every finite positive Schatten exponent, including repeated singular values. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def symmetricRightGram {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : RealSymmetricMatrix b :=
  ⟨Aᵀ * A, (rightGram_posSemidef A).isHermitian⟩

theorem measurable_symmetricRightGram (a b : ℕ) : Measurable (symmetricRightGram (a := a) (b := b)) := by
  apply Measurable.subtype_mk
  exact (show Continuous (fun A : Matrix (Fin a) (Fin b) ℝ => Aᵀ * A) by fun_prop).measurable

theorem exists_measurable_optimal_columns (a b k : ℕ) (hk : k ≤ b) :
    ∃ f : Matrix (Fin a) (Fin b) ℝ → Matrix (Fin b) (Fin k) ℝ,
      Measurable f ∧ (∀ A, (f A)ᵀ * f A = 1) ∧
      (∀ A (p : ℝ), 0 < p → schattenNorm p (A * (1 - f A * (f A)ᵀ)) = optimalSchattenNorm p A k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  let f := fun A : Matrix (Fin a) (Fin (m + k)) ℝ =>
    (canonicalOrderedSpectrum (m + k) (symmetricRightGram A)).basis.submatrix id (Fin.natAdd m)
  refine ⟨f, ?_, ?_, ?_⟩
  · have hU := (measurable_canonical_spectral_basis (m + k)).comp (measurable_symmetricRightGram a (m + k))
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (j.natAdd m)).comp ((measurable_pi_apply i).comp hU)
  · intro A
    exact orthogonal_subcolumns _ (canonicalOrderedSpectrum (m + k) (symmetricRightGram A)).orthogonal
      _ (Fin.natAddEmb m).injective
  · intro A p hp
    exact ordered_tail_columns_optimal_norm hp A (canonicalOrderedSpectrum (m + k) (symmetricRightGram A))

def lastColumnIndex (b k : ℕ) (hk : k ≤ b) (j : Fin k) : Fin b :=
  ⟨b - k + j.val, by omega⟩

theorem lastColumnIndex_injective (b k : ℕ) (hk : k ≤ b) :
    Function.Injective (lastColumnIndex b k hk) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  dsimp only [lastColumnIndex] at he
  omega

theorem lastColumnIndex_add (m k : ℕ) (hk : k ≤ m + k) :
    lastColumnIndex (m + k) k hk = Fin.natAdd m := by
  funext j
  apply Fin.ext
  simp [lastColumnIndex]

def optimalColumnSelector (a b k : ℕ) (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) : Matrix (Fin b) (Fin k) ℝ :=
  (canonicalOrderedSpectrum b (symmetricRightGram A)).basis.submatrix id (lastColumnIndex b k hk)

theorem measurable_optimalColumnSelector (a b k : ℕ) (hk : k ≤ b) :
    Measurable (optimalColumnSelector a b k hk) := by
  have hU := (measurable_canonical_spectral_basis b).comp (measurable_symmetricRightGram a b)
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply (lastColumnIndex b k hk j)).comp ((measurable_pi_apply i).comp hU)

theorem optimalColumnSelector_orthogonal {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) :
    (optimalColumnSelector a b k hk A)ᵀ * optimalColumnSelector a b k hk A = 1 :=
  orthogonal_subcolumns _ (canonicalOrderedSpectrum b (symmetricRightGram A)).orthogonal
    _ (lastColumnIndex_injective b k hk)

theorem optimalColumnSelector_residual {a b k : ℕ} (hk : k ≤ b)
    (A : Matrix (Fin a) (Fin b) ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNorm p (A * (1 - optimalColumnSelector a b k hk A * (optimalColumnSelector a b k hk A)ᵀ)) =
      optimalSchattenNorm p A k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa only [optimalColumnSelector, lastColumnIndex_add] using
    ordered_tail_columns_optimal_norm hp A (canonicalOrderedSpectrum (m + k) (symmetricRightGram A))

end
end LowRank
