import GradientHessian.RawLeafFactor
import Mathlib.Data.Fin.Tuple.Basic

/-! Isolate a coefficient subtree at any depth as an independent factor.
The physical coordinates are unaffected: this operation rearranges raw data. -/

noncomputable section
namespace GradientHessian.RawSubtreeFactor
open MeasureTheory Matrix RawHierarchy ProductRearrangement

abbrev Word (depth : ℕ) := Fin depth → Fin 8

variable (d n r J : ℕ) (E : Type) (H : ℕ → Type) (h : ℕ)

def Rest : ℕ → Type
  | 0 => PUnit
  | depth+1 => Rest depth × (Fin 7 → Raw d n r J E H (h+depth)) × (Fin 8 → H (h+depth))

variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def restMeasurable : (depth : ℕ) → MeasurableSpace (Rest d n r J E H h depth)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | depth+1 => by
    letI := restMeasurable depth
    exact inferInstanceAs (MeasurableSpace (Rest d n r J E H h depth ×
      (Fin 7 → Raw d n r J E H (h+depth)) × (Fin 8 → H (h+depth))))
attribute [instance] restMeasurable

variable {d n r J E H}

def factor : (depth : ℕ) → Word depth →
    Raw d n r J E H (h+depth) ≃ᵐ Raw d n r J E H h × Rest d n r J E H h depth
  | 0, _ => MeasurableEquiv.prodPUnit.symm
  | depth+1, w =>
    ((split (w 0)).prodCongr (MeasurableEquiv.refl (Fin 8 → H (h+depth)))).trans
      (MeasurableEquiv.prodAssoc.trans
        (((factor depth (Fin.tail w)).prodCongr
          (MeasurableEquiv.refl ((Fin 7 → Raw d n r J E H (h+depth)) × (Fin 8 → H (h+depth))))).trans
            MeasurableEquiv.prodAssoc))

def selectedRaw : (depth : ℕ) → Word depth → Raw d n r J E H (h+depth) → Raw d n r J E H h
  | 0, _, x => x
  | depth+1, w, x => selectedRaw depth (Fin.tail w) (x.1 (w 0))

theorem factor_target : ∀ depth (w : Word depth) (x : Raw d n r J E H (h+depth)),
    (factor h depth w x).1=selectedRaw h depth w x
  | 0, _w, _x => rfl
  | depth+1, w, x => factor_target depth (Fin.tail w) (x.1 (w 0))

theorem selectedRaw_measurable (depth : ℕ) (w : Word depth) :
    Measurable (selectedRaw (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w) := by
  simpa only [Function.comp_def, factor_target] using measurable_fst.comp
    (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w).measurable

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

def restLaw (P : Matrix (Fin d) (Fin d) ℝ) : (depth : ℕ) → Measure (Rest d n r J E H h depth)
  | 0 => Measure.dirac PUnit.unit
  | depth+1 => (restLaw P depth).prod
    ((Measure.pi (fun _ : Fin 7 => RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (h+depth))).prod
      (Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H (h+depth)))))

theorem restLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ depth, IsProbabilityMeasure (restLaw (n := n) (r := r) (J := J) (E := E) (H := H) h P depth)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | depth+1 => by
    letI := restLaw_probability P depth
    letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P (h+depth)
    change IsProbabilityMeasure ((restLaw (n := n) (r := r) (J := J) (E := E) (H := H) h P depth).prod
      ((Measure.pi (fun _ : Fin 7 => RawHierarchy.law P (h+depth))).prod
        (Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H (h+depth))))))
    infer_instance

theorem factor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ depth (w : Word depth), MeasurePreserving
      (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w)
      (RawHierarchy.law P (h+depth)) ((RawHierarchy.law P h).prod (restLaw h P depth))
  | 0, _w => by
    letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P h
    refine ⟨measurable_prodMk_right, ?_⟩
    exact (Measure.prod_dirac (μ := RawHierarchy.law P h) PUnit.unit).symm
  | depth+1, w => by
    let μ := RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (h+depth)
    let ν := Measure.pi (fun _ : Fin 7 => μ)
    let ρ := Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H (h+depth)))
    let τ := RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P h
    let σ := restLaw (n := n) (r := r) (J := J) (E := E) (H := H) h P depth
    letI : IsProbabilityMeasure μ := RawHierarchy.law_probability P (h+depth)
    letI : IsProbabilityMeasure τ := RawHierarchy.law_probability P h
    letI : IsProbabilityMeasure σ := restLaw_probability h P depth
    exact (measurePreserving_prodAssoc τ σ (ν.prod ρ)).comp
      (((factor_preserving P depth (Fin.tail w)).prod (MeasurePreserving.id (ν.prod ρ))).comp
        ((measurePreserving_prodAssoc μ ν ρ).comp
          ((split_preserving (w 0) μ).prod (MeasurePreserving.id ρ))))

theorem recombine_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (depth : ℕ) (w : Word depth) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w).symm
      ((RawHierarchy.law P h).prod (restLaw h P depth)) (RawHierarchy.law P (h+depth)) :=
  (factor_preserving h P depth w).symm (factor h depth w)

end GradientHessian.RawSubtreeFactor
