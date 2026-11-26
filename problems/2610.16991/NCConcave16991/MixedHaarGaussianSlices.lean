import NCConcave16991.MixedHaarGaussianReservoir
import NCConcave16991.BranchOracleFormalLayer
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Actual independent Gaussian law of every formal word slice -/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

theorem pi_stdGaussian_map_toLp :
    (Measure.pi (fun i ↦ stdGaussian (E i))).map (WithLp.toLp 2) = stdGaussian (PiLp 2 E) := by
  apply Measure.ext_of_charFun (E := PiLp 2 E)
  ext t
  simp_rw [charFun_pi,charFun_stdGaussian,← Complex.exp_sum]
  congr 1
  simp_rw [← Complex.ofReal_pow]
  rw [PiLp.norm_sq_eq_of_L2]
  rw [Complex.ofReal_sum,← Finset.sum_div,Finset.sum_neg_distrib]

theorem gaussian_slices_preserving :
    MeasurePreserving (WithLp.ofLp : PiLp 2 E → ∀ i, E i)
      (stdGaussian (PiLp 2 E)) (Measure.pi (fun i ↦ stdGaussian (E i))) := by
  refine ⟨WithLp.measurable_ofLp _ _,?_⟩
  rw [← pi_stdGaussian_map_toLp,
    Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _)]
  change (Measure.pi (fun i ↦ stdGaussian (E i))).map id = _
  exact Measure.map_id

theorem formal_word_slices_preserving (n t D : ℕ) :
    MeasurePreserving
      (WithLp.ofLp : BranchOracle.FormalLayer (ι := Fin n) (Space D) t →
        BranchOracle.Word (Fin n) t → Space D)
      (stdGaussian (BranchOracle.FormalLayer (ι := Fin n) (Space D) t))
      (Measure.pi (fun _ : BranchOracle.Word (Fin n) t ↦ stdGaussian (Space D))) :=
  gaussian_slices_preserving

section Families

variable {J : I → Type*} [∀ i, Fintype (J i)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_dependent_slices_preserving
    {A : (i : I) → J i → Type*} [∀ i j, NormedAddCommGroup (A i j)]
    [∀ i j, InnerProductSpace ℝ (A i j)] [∀ i j, FiniteDimensional ℝ (A i j)]
    [∀ i j, MeasurableSpace (A i j)] [∀ i j, BorelSpace (A i j)] :
    MeasurePreserving
      (fun f : ∀ i, PiLp 2 (A i) ↦ fun ij : Sigma J ↦ f ij.1 ij.2)
      (Measure.pi (fun i ↦ stdGaussian (PiLp 2 (A i))))
      (Measure.pi (fun ij : Sigma J ↦ stdGaussian (A ij.1 ij.2))) := by
  let U := LinearIsometryEquiv.piLpCurry ℝ 2 A
  have h1 : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi (fun i ↦ stdGaussian (PiLp 2 (A i))))
      (stdGaussian (PiLp 2 (fun i ↦ PiLp 2 (A i)))) :=
    ⟨WithLp.measurable_toLp _ _,pi_stdGaussian_map_toLp⟩
  have h2 : MeasurePreserving U.symm
      (stdGaussian (PiLp 2 (fun i ↦ PiLp 2 (A i))))
      (stdGaussian (PiLp 2 (fun ij : Sigma J ↦ A ij.1 ij.2))) :=
    ⟨U.symm.continuous.measurable,stdGaussian_map U.symm⟩
  have hh := gaussian_slices_preserving.comp (h2.comp h1)
  convert hh using 1
  funext f ij
  rcases ij with ⟨i,j⟩
  rfl

theorem gaussian_nested_product_preserving
    {A : (i : I) → J i → Type*} [∀ i j, NormedAddCommGroup (A i j)]
    [∀ i j, InnerProductSpace ℝ (A i j)] [∀ i j, FiniteDimensional ℝ (A i j)]
    [∀ i j, MeasurableSpace (A i j)] [∀ i j, BorelSpace (A i j)] :
    MeasurePreserving
      (fun f : ∀ i j, A i j ↦ fun ij : Sigma J ↦ f ij.1 ij.2)
      (Measure.pi (fun i ↦ Measure.pi (fun j ↦ stdGaussian (A i j))))
      (Measure.pi (fun ij : Sigma J ↦ stdGaussian (A ij.1 ij.2))) := by
  have hInner : MeasurePreserving (fun f : ∀ i j, A i j ↦ fun i ↦ WithLp.toLp 2 (f i))
      (Measure.pi (fun i ↦ Measure.pi (fun j ↦ stdGaussian (A i j))))
      (Measure.pi (fun i ↦ stdGaussian (PiLp 2 (A i)))) :=
    measurePreserving_pi _ _ (fun _ ↦ ⟨WithLp.measurable_toLp _ _,pi_stdGaussian_map_toLp⟩)
  exact gaussian_dependent_slices_preserving.comp hInner

theorem gaussian_family_slices_preserving :
    MeasurePreserving
      (fun f : ∀ i, PiLp 2 (fun _ : J i ↦ V) ↦ fun ij : Sigma J ↦ f ij.1 ij.2)
      (Measure.pi (fun i ↦ stdGaussian (PiLp 2 (fun _ : J i ↦ V))))
      (Measure.pi (fun _ : Sigma J ↦ stdGaussian V)) := by
  let U := LinearIsometryEquiv.piLpCurry ℝ 2 (fun (i : I) (_ : J i) ↦ V)
  have h1 : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi (fun i ↦ stdGaussian (PiLp 2 (fun _ : J i ↦ V))))
      (stdGaussian (PiLp 2 (fun i ↦ PiLp 2 (fun _ : J i ↦ V)))) :=
    ⟨WithLp.measurable_toLp _ _,pi_stdGaussian_map_toLp⟩
  have h2 : MeasurePreserving U.symm
      (stdGaussian (PiLp 2 (fun i ↦ PiLp 2 (fun _ : J i ↦ V))))
      (stdGaussian (PiLp 2 (fun _ : Sigma J ↦ V))) :=
    ⟨U.symm.continuous.measurable,stdGaussian_map U.symm⟩
  have hh := gaussian_slices_preserving.comp (h2.comp h1)
  convert hh using 1
  funext f ij
  rcases ij with ⟨i,j⟩
  rfl

theorem gaussian_family_enumerated_preserving
    (e : Sigma J ≃ Fin (Fintype.card (Sigma J))) :
    MeasurePreserving
      (fun f : ∀ i, PiLp 2 (fun _ : J i ↦ V) ↦
        fun a : Fin (Fintype.card (Sigma J)) ↦ f (e.symm a).1 (e.symm a).2)
      (Measure.pi (fun i ↦ stdGaussian (PiLp 2 (fun _ : J i ↦ V))))
      (Measure.pi (fun _ : Fin (Fintype.card (Sigma J)) ↦ stdGaussian V)) := by
  have he := measurePreserving_piCongrLeft
    (fun _ : Fin (Fintype.card (Sigma J)) ↦ stdGaussian V) e
  have hh := he.comp (gaussian_family_slices_preserving (I := I) (J := J) (V := V))
  convert hh using 1
  funext f a
  simp only [Function.comp_def,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,cast_eq]

end Families

end NCConcave16991.MixedHaar
