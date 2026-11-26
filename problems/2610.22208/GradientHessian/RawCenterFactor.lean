import GradientHessian.RawSubtreeFactor

/-! Isolate any localized-center direction as a genuine sphere factor of
the original presampled hierarchy. -/

noncomputable section
namespace GradientHessian.RawCenterFactor
open MeasureTheory Matrix RawHierarchy ProductRearrangement

abbrev LocalRest (d n r J : ℕ) (E : Type) (H : ℕ → Type) (h : ℕ) :=
  (Fin 8 → Raw d n r J E H h) × (Fin 7 → H h)

abbrev Rest (d n r J : ℕ) (E : Type) (H : ℕ → Type) (h depth : ℕ) :=
  LocalRest d n r J E H h × RawSubtreeFactor.Rest d n r J E H (h+1) depth

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def localFactor (h : ℕ) (i : Fin 8) : Raw d n r J E H (h+1) ≃ᵐ H h × LocalRest d n r J E H h :=
  ((MeasurableEquiv.refl (Fin 8 → Raw d n r J E H h)).prodCongr (split i)).trans swapFront

theorem localFactor_direction (h : ℕ) (i : Fin 8) (x : Raw d n r J E H (h+1)) :
    (localFactor h i x).1=x.2 i := rfl

def factor (h depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8) :
    Raw d n r J E H (h+1+depth) ≃ᵐ H h × Rest d n r J E H h depth :=
  (RawSubtreeFactor.factor (h+1) depth w).trans
    (((localFactor h i).prodCongr (MeasurableEquiv.refl
      (RawSubtreeFactor.Rest d n r J E H (h+1) depth))).trans MeasurableEquiv.prodAssoc)

theorem factor_direction (h depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8)
    (x : Raw d n r J E H (h+1+depth)) :
    (factor h depth w i x).1=(RawSubtreeFactor.selectedRaw (h+1) depth w x).2 i := by
  change (RawSubtreeFactor.factor (h+1) depth w x).1.2 i=_
  rw [RawSubtreeFactor.factor_target]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

def localRestLaw (P : Matrix (Fin d) (Fin d) ℝ) (h : ℕ) : Measure (LocalRest d n r J E H h) :=
  (Measure.pi (fun _ : Fin 8 => RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P h)).prod
    (Measure.pi (fun _ : Fin 7 => SphereGaussian.sphereLaw (H h)))

def restLaw (P : Matrix (Fin d) (Fin d) ℝ) (h depth : ℕ) : Measure (Rest d n r J E H h depth) :=
  (localRestLaw P h).prod (RawSubtreeFactor.restLaw (h+1) P depth)

theorem localRestLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (h : ℕ) :
    IsProbabilityMeasure (localRestLaw (n := n) (r := r) (J := J) (E := E) (H := H) P h) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P h
  unfold localRestLaw
  infer_instance

theorem restLaw_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (h depth : ℕ) :
    IsProbabilityMeasure (restLaw (n := n) (r := r) (J := J) (E := E) (H := H) P h depth) := by
  letI := localRestLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) P h
  letI := RawSubtreeFactor.restLaw_probability (n := n) (r := r) (J := J) (E := E) (H := H) (h+1) P depth
  unfold restLaw
  infer_instance

theorem localFactor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] (h : ℕ) (i : Fin 8) :
    MeasurePreserving (localFactor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h i)
      (RawHierarchy.law P (h+1)) ((SphereGaussian.sphereLaw (H h)).prod (localRestLaw P h)) := by
  let μ := Measure.pi (fun _ : Fin 8 => RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P h)
  let ν := SphereGaussian.sphereLaw (H h)
  let ρ := Measure.pi (fun _ : Fin 7 => ν)
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P h
  exact (swapFront_preserving μ ν ρ).comp ((MeasurePreserving.id μ).prod (split_preserving i ν))

theorem factor_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (h depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w i)
      (RawHierarchy.law P (h+1+depth)) ((SphereGaussian.sphereLaw (H h)).prod (restLaw P h depth)) := by
  let μ := SphereGaussian.sphereLaw (H h)
  let ν := localRestLaw (n := n) (r := r) (J := J) (E := E) (H := H) P h
  let ρ := RawSubtreeFactor.restLaw (n := n) (r := r) (J := J) (E := E) (H := H) (h+1) P depth
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P (h+1)
  letI : IsProbabilityMeasure ν := localRestLaw_probability P h
  letI : IsProbabilityMeasure ρ := RawSubtreeFactor.restLaw_probability (h+1) P depth
  exact (measurePreserving_prodAssoc μ ν ρ).comp
    (((localFactor_preserving P h i).prod (MeasurePreserving.id ρ)).comp
      (RawSubtreeFactor.factor_preserving (h+1) P depth w))

theorem recombine_preserving (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (h depth : ℕ) (w : RawSubtreeFactor.Word depth) (i : Fin 8) :
    MeasurePreserving (factor (d := d) (n := n) (r := r) (J := J) (E := E) (H := H) h depth w i).symm
      ((SphereGaussian.sphereLaw (H h)).prod (restLaw P h depth)) (RawHierarchy.law P (h+1+depth)) :=
  (factor_preserving P h depth w i).symm (factor h depth w i)

end GradientHessian.RawCenterFactor
