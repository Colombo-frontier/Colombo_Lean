import MatchingBounds1005.GaussianVector
import Mathlib.Algebra.BigOperators.Fin

/-!
# Splitting an actual standard Gaussian into independent blocks

This identifies a single Euclidean Gaussian seed with two independent
coordinate blocks. It permits simultaneous tensor channels to be encoded
in one latent vector without inserting an additional adaptive decision.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatchingBounds1005.GaussianProduct
open GaussianVector

def splitEquiv (a b : ℕ) : Vec (a + b) ≃ᵐ (Vec a × Vec b) :=
  (EuclideanSpace.measurableEquiv (Fin (a + b))).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin a ⊕ Fin b => ℝ) finSumFinEquiv.symm).trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)).trans
        ((EuclideanSpace.measurableEquiv (Fin a)).symm.prodCongr
          (EuclideanSpace.measurableEquiv (Fin b)).symm)))

/-- The two coordinate blocks have the actual independent product law. -/
theorem standardGaussian_split (a b : ℕ) :
    (standardGaussian (a + b)).map (splitEquiv a b) =
      (standardGaussian a).prod (standardGaussian b) := by
  have h₀ : MeasurePreserving (EuclideanSpace.measurableEquiv (Fin (a + b)))
      (standardGaussian (a + b)) (Measure.pi (fun _ : Fin (a + b) => gaussianReal 0 1)) :=
    ⟨(EuclideanSpace.measurableEquiv _).measurable, standardGaussian_coordinate_law _⟩
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin a ⊕ Fin b => gaussianReal 0 1) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).symm
  have h₂ := measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => gaussianReal 0 1)
  have hA : MeasurePreserving (EuclideanSpace.measurableEquiv (Fin a)).symm
      (Measure.pi (fun _ : Fin a => gaussianReal 0 1)) (standardGaussian a) :=
    ⟨(EuclideanSpace.measurableEquiv _).symm.measurable, rfl⟩
  have hB : MeasurePreserving (EuclideanSpace.measurableEquiv (Fin b)).symm
      (Measure.pi (fun _ : Fin b => gaussianReal 0 1)) (standardGaussian b) :=
    ⟨(EuclideanSpace.measurableEquiv _).symm.measurable, rfl⟩
  exact ((hA.prod hB).comp (h₂.comp (h₁.comp h₀))).map_eq

theorem splitEquiv_fst (a b : ℕ) (z : Vec (a + b)) (i : Fin a) :
    (splitEquiv a b z).1 i = z (Fin.castAdd b i) := by
  simp [splitEquiv, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.prodCongr, EuclideanSpace.measurableEquiv]

theorem splitEquiv_snd (a b : ℕ) (z : Vec (a + b)) (i : Fin b) :
    (splitEquiv a b z).2 i = z (Fin.natAdd a i) := by
  simp [splitEquiv, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.prodCongr, EuclideanSpace.measurableEquiv]

theorem splitEquiv_norm_sq (a b : ℕ) (z : Vec (a + b)) :
    ‖z‖ ^ 2 = ‖(splitEquiv a b z).1‖ ^ 2 + ‖(splitEquiv a b z).2‖ ^ 2 := by
  simp only [norm_sq_coordinates, splitEquiv_fst, splitEquiv_snd]
  exact Fin.sum_univ_add (fun i : Fin (a + b) => z i ^ 2)

theorem standardGaussian_join (a b : ℕ) :
    ((standardGaussian a).prod (standardGaussian b)).map (splitEquiv a b).symm =
      standardGaussian (a + b) := by
  rw [← standardGaussian_split, Measure.map_map (splitEquiv a b).symm.measurable
    (splitEquiv a b).measurable]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id']

end MatchingBounds1005.GaussianProduct
