import GradientHessian.RawFirstFactor
import GradientHessian.RawHierarchy
import GradientHessian.HigherHierarchyLeafData

/-! A measure-preserving factorization of the complete presampled hierarchy
around an arbitrary leaf's matrix and all of its marks. No conditioning on
algorithmic histories or misses is used. -/

noncomputable section
namespace GradientHessian.RawLeafFactor
open MeasureTheory Matrix RawHierarchy ProductRearrangement HigherHierarchy

variable (d n r J : ℕ) (E : Type) (H : ℕ → Type)

def Rest : ℕ → Type
  | 0 => RawFirstFactor.Rest d n r J E
  | t+1 => Rest t × (Fin 7 → Raw d n r J E H t) × (Fin 8 → H t)

variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def restMeasurable : (t : ℕ) → MeasurableSpace (Rest d n r J E H t)
  | 0 => inferInstanceAs (MeasurableSpace (RawFirstFactor.Rest d n r J E))
  | t+1 => by
    letI := restMeasurable t
    exact inferInstanceAs (MeasurableSpace
      (Rest d n r J E H t × (Fin 7 → Raw d n r J E H t) × (Fin 8 → H t)))
attribute [instance] restMeasurable

variable {d n r J E H}

def factor : (t : ℕ) → LeafSlot t →
    Raw d n r J E H t ≃ᵐ RawFirstFactor.Target d n r J × Rest d n r J E H t
  | 0, i => RawFirstFactor.factor i
  | t+1, i =>
    ((split i.1).prodCongr (MeasurableEquiv.refl (Fin 8 → H t))).trans
      (MeasurableEquiv.prodAssoc.trans
        (((factor t i.2).prodCongr
          (MeasurableEquiv.refl ((Fin 7 → Raw d n r J E H t) × (Fin 8 → H t)))).trans
            MeasurableEquiv.prodAssoc))

def leafNumerical : (t : ℕ) → Raw d n r J E H t → LeafSlot t → RawFirstFactor.Target d n r J
  | 0, x, i => (x.1 i,x.2.1 i)
  | t+1, x, i => leafNumerical t (x.1 i.1) i.2

theorem factor_target : ∀ t (i : LeafSlot t) (x : Raw d n r J E H t),
    (factor t i x).1=leafNumerical t x i
  | 0, _i, _x => rfl
  | t+1, i, x => factor_target t i.2 (x.1 i.1)

theorem leafNumerical_measurable (t : ℕ) (i : LeafSlot t) :
    Measurable (fun x : Raw d n r J E H t => leafNumerical t x i) := by
  simpa only [Function.comp_def, factor_target] using measurable_fst.comp (factor (d := d) (n := n)
    (r := r) (J := J) (E := E) (H := H) t i).measurable

def replace (t : ℕ) (i : LeafSlot t) (z : RawFirstFactor.Target d n r J) (x : Raw d n r J E H t) :
    Raw d n r J E H t := (factor t i).symm (z,(factor t i x).2)

theorem factor_replace (t : ℕ) (i : LeafSlot t) (z : RawFirstFactor.Target d n r J)
    (x : Raw d n r J E H t) : factor t i (replace t i z x)=(z,(factor t i x).2) :=
  (factor t i).apply_symm_apply _

theorem replace_target (t : ℕ) (i : LeafSlot t) (z : RawFirstFactor.Target d n r J)
    (x : Raw d n r J E H t) : leafNumerical t (replace t i z x) i=z := by
  rw [← factor_target, factor_replace]

theorem replace_measurable (t : ℕ) (i : LeafSlot t) :
    Measurable (fun p : RawFirstFactor.Target d n r J × Raw d n r J E H t => replace t i p.1 p.2) :=
  (factor t i).symm.measurable.comp (measurable_fst.prodMk
    (measurable_snd.comp ((factor t i).measurable.comp measurable_snd)))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

def restLaw (P : Matrix (Fin d) (Fin d) ℝ) : (t : ℕ) → Measure (Rest d n r J E H t)
  | 0 => RawFirstFactor.restLaw P J r
  | t+1 => (restLaw P t).prod
    ((Measure.pi (fun _ : Fin 7 => RawHierarchy.law (n := n) (r := r) (J := J)
      (E := E) (H := H) P t)).prod (Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H t))))

theorem restLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ t, IsProbabilityMeasure (restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t)
  | 0 => RawFirstFactor.restLaw_probability P
  | t+1 => by
    letI := restLaw_probability P t
    letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
    change IsProbabilityMeasure ((restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod
      ((Measure.pi (fun _ : Fin 7 => RawHierarchy.law P t)).prod
        (Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H t)))))
    infer_instance

theorem factor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ t (i : LeafSlot t), MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i)
      (RawHierarchy.law P t)
      ((RawFirstFactor.targetLaw (n := n) P J r).prod (restLaw P t))
  | 0, i => RawFirstFactor.factor_preserving P i
  | t+1, i => by
    let μ := RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t
    let ν := Measure.pi (fun _ : Fin 7 => μ)
    let ρ := Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H t))
    let τ := RawFirstFactor.targetLaw (n := n) P J r
    let σ := restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P t
    letI : IsProbabilityMeasure μ := RawHierarchy.law_probability P t
    letI : IsProbabilityMeasure τ := RawFirstFactor.targetLaw_probability P
    letI : IsProbabilityMeasure σ := restLaw_probability P t
    exact (measurePreserving_prodAssoc τ σ (ν.prod ρ)).comp
      (((factor_preserving P t i.2).prod (MeasurePreserving.id (ν.prod ρ))).comp
        ((measurePreserving_prodAssoc μ ν ρ).comp
          ((split_preserving i.1 μ).prod (MeasurePreserving.id ρ))))

theorem recombine_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (t : ℕ) (i : LeafSlot t) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) t i).symm
      ((RawFirstFactor.targetLaw (n := n) P J r).prod (restLaw P t)) (RawHierarchy.law P t) :=
  (factor_preserving P t i).symm (factor t i)

end GradientHessian.RawLeafFactor
