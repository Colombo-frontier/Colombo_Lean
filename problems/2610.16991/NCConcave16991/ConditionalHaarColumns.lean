import NCConcave16991.ConditionalHaarSymmetry
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual Haar conditional moments after revealing fixed input columns

The observation is the literal collection of images of basis vectors in A.
Right reflections and right swaps of unrevealed input coordinates preserve
this observation. Their conditional symmetry is proved from Haar measure,
rather than assumed as a conditional-law specification.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.Haar

noncomputable section

def basisVector {k : ℕ} (j : Fin k) : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j 1

def entry {k : ℕ} (Q : OrthogonalGroup k) (i j : Fin k) : ℝ :=
  orthogonalLinearIsometryEquiv Q (basisVector j) i

def observeColumns {k : ℕ} (A : Finset (Fin k)) (Q : OrthogonalGroup k) :
    A → EuclideanSpace ℝ (Fin k) :=
  fun j ↦ orthogonalLinearIsometryEquiv Q (basisVector j.val)

@[reducible] def columnSigma {k : ℕ} (A : Finset (Fin k)) : MeasurableSpace (OrthogonalGroup k) :=
  (inferInstance : MeasurableSpace (A → EuclideanSpace ℝ (Fin k))).comap (observeColumns A)

theorem observeColumns_measurable {k : ℕ} (A : Finset (Fin k)) : Measurable (observeColumns A) :=
  measurable_pi_iff.mpr (fun j ↦ (continuous_orthogonalLinearIsometryEquiv_apply (basisVector j.val)).measurable)

theorem columnSigma_le {k : ℕ} (A : Finset (Fin k)) :
    columnSigma A ≤ (inferInstance : MeasurableSpace (OrthogonalGroup k)) :=
  (observeColumns_measurable A).comap_le

def signFlip {k : ℕ} (j : Fin k) : OrthogonalGroup k :=
  ⟨Matrix.diagonal (fun i ↦ if i=j then (-1:ℝ) else 1), by
    have hs : star (Matrix.diagonal (fun i : Fin k ↦ if i=j then (-1:ℝ) else 1)) =
        Matrix.diagonal (fun i : Fin k ↦ if i=j then (-1:ℝ) else 1) := by
      simp [Matrix.star_eq_conjTranspose]
    change star (Matrix.diagonal (fun i : Fin k ↦ if i=j then (-1:ℝ) else 1)) *
      Matrix.diagonal (fun i : Fin k ↦ if i=j then (-1:ℝ) else 1) = 1 ∧
      Matrix.diagonal (fun i : Fin k ↦ if i=j then (-1:ℝ) else 1) *
      star (Matrix.diagonal (fun i : Fin k ↦ if i=j then (-1:ℝ) else 1)) = 1
    rw [hs]
    constructor <;> rw [Matrix.diagonal_mul_diagonal] <;> ext i l <;>
      by_cases hil : i=l <;> simp [Matrix.diagonal, Matrix.one_apply, hil] <;> split_ifs <;> norm_num⟩

theorem signFlip_action {k : ℕ} (j : Fin k) (v : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    orthogonalLinearIsometryEquiv (signFlip j) v i = (if i=j then (-1:ℝ) else 1) * v i := by
  change ((Matrix.diagonal (fun l ↦ if l=j then (-1:ℝ) else 1)).mulVec (WithLp.ofLp v)) i = _
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

theorem signFlip_basis {k : ℕ} (j l : Fin k) :
    orthogonalLinearIsometryEquiv (signFlip j) (basisVector l) =
      if l=j then -(basisVector l) else basisVector l := by
  ext i
  rw [signFlip_action]
  by_cases hil : i=l
  · subst i
    by_cases hlj : l=j <;> simp [basisVector, hlj]
  · by_cases hlj : l=j
    · subst l
      simp [basisVector, hil]
    · simp [basisVector, hil, hlj]

theorem observeColumns_signFlip {k : ℕ} (A : Finset (Fin k)) (j : Fin k) (hj : j ∉ A)
    (Q : OrthogonalGroup k) : observeColumns A (Q * signFlip j) = observeColumns A Q := by
  funext l
  change orthogonalLinearIsometryEquiv (Q * signFlip j) (basisVector l.val) = _
  rw [action_mul, signFlip_basis]
  have hl : l.val ≠ j := by intro h; exact hj (h ▸ l.property)
  rw [ite_eq_right hl]
  rfl

theorem entry_signFlip {k : ℕ} (Q : OrthogonalGroup k) (i j : Fin k) :
    entry (Q * signFlip j) i j = -entry Q i j := by
  change orthogonalLinearIsometryEquiv (Q * signFlip j) (basisVector j) i =
    -(orthogonalLinearIsometryEquiv Q (basisVector j) i)
  rw [action_mul, signFlip_basis, ite_eq_left (Eq.refl j), map_neg]
  rfl

theorem entry_integrable {k : ℕ} (i j : Fin k) : Integrable (fun Q ↦ entry Q i j) (haarLaw k) :=
  action_coordinate_integrable (basisVector j) i

theorem entry_sq_integrable {k : ℕ} (i j : Fin k) : Integrable (fun Q ↦ entry Q i j ^ 2) (haarLaw k) :=
  action_coordinate_sq_integrable (basisVector j) i

/-- A genuinely unrevealed column has conditional mean zero given the actual
previously observed columns. -/
theorem conditional_entry_mean_zero {k : ℕ} (A : Finset (Fin k)) (i j : Fin k) (hj : j ∉ A) :
    (haarLaw k)[(fun Q ↦ entry Q i j) | columnSigma A] =ᵐ[haarLaw k] fun _ ↦ (0:ℝ) :=
  conditional_zero_of_right_negation (observeColumns A) (observeColumns_measurable A)
    (signFlip j) (observeColumns_signFlip A j hj) (entry_integrable i j)
    (fun Q ↦ entry_signFlip Q i j)

theorem permutation_basis {k : ℕ} (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    orthogonalLinearIsometryEquiv (permutationOrthogonal σ) (basisVector j) =
      basisVector (σ.symm j) := by
  ext i
  rw [action_permutation]
  simp only [basisVector, EuclideanSpace.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

theorem observeColumns_swap {k : ℕ} (A : Finset (Fin k)) (j l : Fin k)
    (hj : j ∉ A) (hl : l ∉ A) (Q : OrthogonalGroup k) :
    observeColumns A (Q * permutationOrthogonal (Equiv.swap j l)) = observeColumns A Q := by
  funext r
  change orthogonalLinearIsometryEquiv (Q * permutationOrthogonal (Equiv.swap j l)) (basisVector r.val) = _
  rw [action_mul, permutation_basis]
  have hrj : r.val ≠ j := by intro h; exact hj (h ▸ r.property)
  have hrl : r.val ≠ l := by intro h; exact hl (h ▸ r.property)
  simp only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hrj hrl]
  rfl

theorem entry_swap {k : ℕ} (Q : OrthogonalGroup k) (i j l : Fin k) :
    entry (Q * permutationOrthogonal (Equiv.swap j l)) i j = entry Q i l := by
  change orthogonalLinearIsometryEquiv (Q * permutationOrthogonal (Equiv.swap j l)) (basisVector j) i =
    orthogonalLinearIsometryEquiv Q (basisVector l) i
  rw [action_mul, permutation_basis]
  simp only [Equiv.symm_swap, Equiv.swap_apply_left]

/-- Conditional second moments of any two unrevealed columns agree. -/
theorem conditional_entry_sq_eq {k : ℕ} (A : Finset (Fin k)) (i j l : Fin k)
    (hj : j ∉ A) (hl : l ∉ A) :
    (haarLaw k)[(fun Q ↦ entry Q i j ^ 2) | columnSigma A] =ᵐ[haarLaw k]
      (haarLaw k)[(fun Q ↦ entry Q i l ^ 2) | columnSigma A] :=
  conditional_right_symmetry (observeColumns A) (observeColumns_measurable A)
    (permutationOrthogonal (Equiv.swap j l)) (observeColumns_swap A j l hj hl)
    (entry_sq_integrable i j) (entry_sq_integrable i l) (fun Q ↦ by rw [entry_swap])

end

end NCConcave16991.Haar
