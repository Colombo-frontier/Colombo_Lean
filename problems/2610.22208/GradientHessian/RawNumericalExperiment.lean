import GradientHessian.RawMarkFactor
import GradientHessian.RawFactorSeed
import GradientHessian.ForkMachineBound

/-! The original hierarchy law with private randomness is exactly the
conditioned-matrix fork experiment, with one fresh target mark and every
other mark/coefficient in the independent auxiliary seed. -/

noncomputable section
namespace GradientHessian.RawNumericalExperiment
open Classical MeasureTheory ProbabilityTheory Matrix LowRank HigherHierarchy RawHierarchy
  ProductRearrangement

abbrev Auxiliary (d n r J : ℕ) (E : Type) (H : ℕ → Type) (t : ℕ) (Seed : Type*) :=
  (Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) × (RawLeafFactor.Rest d n r J E H t × Seed)

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type} {Seed : Type*}
variable [MeasurableSpace E] [∀ t,MeasurableSpace (H t)] [MeasurableSpace Seed]

def factorCore (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    Raw d n r J E H t × Seed ≃ᵐ
      (Matrix (Fin d) (Fin n) ℝ × Auxiliary d n r J E H t Seed) × EuclideanSpace ℝ (Fin r) :=
  (RawFactorSeed.factor (RawLeafFactor.factor t i)).trans
    ((((MeasurableEquiv.refl (Matrix (Fin d) (Fin n) ℝ)).prodCongr (split j)).prodCongr
      (MeasurableEquiv.refl (RawLeafFactor.Rest d n r J E H t × Seed))).trans
      (MeasurableEquiv.prodAssoc.trans
        (((MeasurableEquiv.refl (Matrix (Fin d) (Fin n) ℝ)).prodCongr MeasurableEquiv.prodAssoc).trans
          (((MeasurableEquiv.refl (Matrix (Fin d) (Fin n) ℝ)).prodCongr MeasurableEquiv.prodComm).trans
            MeasurableEquiv.prodAssoc.symm))))

def factor (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    Raw d n r J E H t × Seed ≃ᵐ ForkMachineBound.Input d n r (Auxiliary d n r J E H t Seed) PUnit :=
  (factorCore t i j).trans
    ((MeasurableEquiv.refl (Matrix (Fin d) (Fin n) ℝ × Auxiliary d n r J E H t Seed)).prodCongr
      MeasurableEquiv.prodPUnit.symm)

theorem factor_matrix (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (w : Raw d n r J E H t × Seed) :
    (factor t i j w).1.1=(RawLeafFactor.leafNumerical t w.1 i).1 := by
  change (RawLeafFactor.factor t i w.1).1.1=_
  rw [RawLeafFactor.factor_target]

theorem factor_mark (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (w : Raw d n r J E H t × Seed) :
    (factor t i j w).2.1=(RawLeafFactor.leafNumerical t w.1 i).2 j := by
  change (RawLeafFactor.factor t i w.1).1.2 j=_
  rw [RawLeafFactor.factor_target]

theorem factor_other_mark (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (w : Raw d n r J E H t × Seed) (k : Fin (4096*J^2)) :
    (factor t i j w).1.2.1 k=(RawLeafFactor.leafNumerical t w.1 i).2 (j.succAbove k) := by
  change (RawLeafFactor.factor t i w.1).1.2 (j.succAbove k)=_
  rw [RawLeafFactor.factor_target]

theorem factor_external (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (w : Raw d n r J E H t × Seed) :
    (factor t i j w).1.2.2.1=(RawLeafFactor.factor t i w.1).2 := rfl

theorem factor_seed (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (w : Raw d n r J E H t × Seed) : (factor t i j w).1.2.2.2=w.2 := rfl

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t,NormedAddCommGroup (H t)] [∀ t,InnerProductSpace ℝ (H t)]
  [∀ t,BorelSpace (H t)] [∀ t,FiniteDimensional ℝ (H t)]
variable (P : Matrix (Fin d) (Fin d) ℝ)
  [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
  (σ : Measure Seed) [IsProbabilityMeasure σ]

def auxiliaryLaw (t : ℕ) : Measure (Auxiliary d n r J E H t Seed) :=
  (Measure.pi (fun _ : Fin (4096*J^2) => SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))).prod
    ((RawLeafFactor.restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ)

instance auxiliaryLaw_probability (t : ℕ) :
    IsProbabilityMeasure (auxiliaryLaw (n := n) (r := r) (J := J) (E := E) (H := H) P σ t) := by
  letI := RawLeafFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  unfold auxiliaryLaw
  infer_instance

theorem factorCore_preserving (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    MeasurePreserving (factorCore (Seed := Seed) (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i j)
      ((RawHierarchy.law P t).prod σ)
      (((ConditionedSource.sourceLaw P J).prod (auxiliaryLaw P σ t)).prod
        (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))) := by
  let μ := ConditionedSource.sourceLaw (n := n) P J
  let ν := SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))
  let ρ := Measure.pi (fun _ : Fin (4096*J^2) => ν)
  let τ := RawLeafFactor.restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t
  letI : IsProbabilityMeasure τ := RawLeafFactor.restLaw_probability P t
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  letI := RawFirstFactor.targetLaw_probability (n := n) (r := r) P (J := J)
  have hbase := RawFactorSeed.factor_preserving (RawLeafFactor.factor t i)
    (RawHierarchy.law P t) (RawFirstFactor.targetLaw (n := n) P J r) τ σ
    (RawLeafFactor.factor_preserving P t i)
  have hsplit := (((MeasurePreserving.id μ).prod (split_preserving j ν)).prod
    (MeasurePreserving.id (τ.prod σ))).comp hbase
  have ha := (measurePreserving_prodAssoc μ (ν.prod ρ) (τ.prod σ)).comp hsplit
  have hb := ((MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ρ (τ.prod σ))).comp ha
  have hc := ((MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := ρ.prod (τ.prod σ)))).comp hb
  exact ((measurePreserving_prodAssoc μ (ρ.prod (τ.prod σ)) ν).symm MeasurableEquiv.prodAssoc).comp hc

theorem factor_preserving (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    MeasurePreserving (factor (Seed := Seed) (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i j)
      ((RawHierarchy.law P t).prod σ)
      (((ConditionedSource.sourceLaw P J).prod (auxiliaryLaw P σ t)).prod
        ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod (Measure.dirac PUnit.unit))) := by
  have hu : MeasurePreserving
      (MeasurableEquiv.prodPUnit.symm : EuclideanSpace ℝ (Fin r) ≃ᵐ EuclideanSpace ℝ (Fin r) × PUnit)
      (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))
      ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod (Measure.dirac PUnit.unit)) := by
    refine ⟨MeasurableEquiv.measurable _,?_⟩
    rw [Measure.prod_dirac]
    rfl
  exact ((MeasurePreserving.id _).prod hu).comp (factorCore_preserving P σ t i j)

theorem experimentLaw_eq (t : ℕ) :
    ForkMachineBound.experimentLaw (r := r) J P (gaussianMatrixLaw d n)
      (auxiliaryLaw (n := n) (r := r) (J := J) (E := E) (H := H) P σ t) (Measure.dirac PUnit.unit) =
      ((ConditionedSource.sourceLaw P J).prod (auxiliaryLaw P σ t)).prod
        ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod (Measure.dirac PUnit.unit)) := by
  rw [ForkMachineBound.experimentLaw,ForkChronologicalProbability.commonGood_eq,
    ConditionedSource.condition_matrix_only _ _ (MatrixKernelConcentration.measurableSet_sourceGoodEvent P J)]
  rfl

theorem factor_experiment_preserving (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    MeasurePreserving (factor (Seed := Seed) (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i j)
      ((RawHierarchy.law P t).prod σ)
      (ForkMachineBound.experimentLaw (r := r) J P (gaussianMatrixLaw d n)
        (auxiliaryLaw P σ t) (Measure.dirac PUnit.unit)) := by
  rw [experimentLaw_eq]
  exact factor_preserving P σ t i j

theorem recombine_experiment_preserving (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    MeasurePreserving (factor (Seed := Seed) (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i j).symm
      (ForkMachineBound.experimentLaw (r := r) J P (gaussianMatrixLaw d n)
        (auxiliaryLaw P σ t) (Measure.dirac PUnit.unit))
      ((RawHierarchy.law P t).prod σ) :=
  (factor_experiment_preserving P σ t i j).symm (factor t i j)

end GradientHessian.RawNumericalExperiment
