import GradientHessian.RawLeafFactor

/-! Isolating one future mark from the actual hierarchy law. Its matrix and
all other marks remain in the independent external-data factor. -/

noncomputable section
namespace GradientHessian.RawMarkFactor
open MeasureTheory Matrix ProductRearrangement RawHierarchy HigherHierarchy

abbrev Rest (d n r J : ℕ) (E : Type) (H : ℕ → Type) (t : ℕ) :=
  Matrix (Fin d) (Fin n) ℝ × (Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) ×
    RawLeafFactor.Rest d n r J E H t

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def factor (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    Raw d n r J E H t ≃ᵐ EuclideanSpace ℝ (Fin r) × Rest d n r J E H t :=
  (RawLeafFactor.factor t i).trans
    ((((MeasurableEquiv.refl (Matrix (Fin d) (Fin n) ℝ)).prodCongr (split j)).prodCongr
      (MeasurableEquiv.refl (RawLeafFactor.Rest d n r J E H t))).trans
      (MeasurableEquiv.prodAssoc.trans
        (((MeasurableEquiv.refl (Matrix (Fin d) (Fin n) ℝ)).prodCongr MeasurableEquiv.prodAssoc).trans
          swapFront)))

theorem factor_mark (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) (x : Raw d n r J E H t) :
    (factor t i j x).1=(RawLeafFactor.leafNumerical t x i).2 j := by
  change (RawLeafFactor.factor t i x).1.2 j=_
  rw [RawLeafFactor.factor_target]

theorem factor_matrix (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) (x : Raw d n r J E H t) :
    (factor t i j x).2.1=(RawLeafFactor.leafNumerical t x i).1 := by
  change (RawLeafFactor.factor t i x).1.1=_
  rw [RawLeafFactor.factor_target]

def replace (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) : Raw d n r J E H t :=
  (factor t i j).symm (z,(factor t i j x).2)

theorem factor_replace (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) :
    factor t i j (replace t i j z x)=(z,(factor t i j x).2) := (factor t i j).apply_symm_apply _

theorem replace_matrix (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) :
    (RawLeafFactor.leafNumerical t (replace t i j z x) i).1=
      (RawLeafFactor.leafNumerical t x i).1 := by
  rw [← factor_matrix t i j, factor_replace, factor_matrix]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

def restLaw (P : Matrix (Fin d) (Fin d) ℝ) (t : ℕ) : Measure (Rest d n r J E H t) :=
  (ConditionedSource.sourceLaw (n := n) P J).prod
    ((Measure.pi (fun _ : Fin (4096*J^2) => SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))).prod
      (RawLeafFactor.restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t))

theorem restLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (t : ℕ) :
    IsProbabilityMeasure (restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t) := by
  letI := RawLeafFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  unfold restLaw
  infer_instance

theorem factor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i j)
      (RawHierarchy.law P t) ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod (restLaw P t)) := by
  let μ := ConditionedSource.sourceLaw (n := n) P J
  let ν := SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))
  let ρ := Measure.pi (fun _ : Fin (4096*J^2) => ν)
  let σ := RawLeafFactor.restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t
  letI : IsProbabilityMeasure σ := RawLeafFactor.restLaw_probability P t
  exact (swapFront_preserving μ ν (ρ.prod σ)).comp
    (((MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ρ σ)).comp
      ((measurePreserving_prodAssoc μ (ν.prod ρ) σ).comp
        ((((MeasurePreserving.id μ).prod (split_preserving j ν)).prod (MeasurePreserving.id σ)).comp
          (RawLeafFactor.factor_preserving P t i))))

theorem recombine_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1)) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i j).symm
      ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod (restLaw P t)) (RawHierarchy.law P t) :=
  (factor_preserving P t i j).symm (factor t i j)

end GradientHessian.RawMarkFactor
