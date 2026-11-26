import SecondOrder.OrderedBudgetRun
import SecondOrder.IndependentDraws

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem signLaw_eq_pi (N : ℕ) :
    signLaw N=Measure.pi (fun _ : Fin N => (PMF.uniformOfFintype Bool).toMeasure) := by
  apply Measure.ext_of_singleton
  intro v
  have he : ({v} : Set (Fin N → Bool))=Set.univ.pi (fun i => {v i}) := by
    ext w
    simp [Set.mem_pi,funext_iff]
  conv_rhs => rw [he,Measure.pi_pi]
  simp only [signLaw,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    Finset.prod_const,Finset.card_univ,ENNReal.inv_pow]
  simp only [Nat.cast_pow,ENNReal.inv_pow]

def orderedStepSplit {Ω : Type} {d L : ℕ} {P : Parameters} {γ τ δ : ℝ}
    (w : OrderedStepTape Ω d L P γ τ δ) :
    TrackingStepTape Ω (BranchedOjaDraws Ω d P γ δ) P L τ δ × Bool := ((w.1,w.2.2),w.2.1)

def orderedDrawsSplit {Ω : Type} {d L : ℕ} {P : Parameters} {γ τ δ : ℝ}
    (N : ℕ) (w : Draws (OrderedStepTape Ω d L P γ τ δ) N) :
    Draws (TrackingStepTape Ω (BranchedOjaDraws Ω d P γ δ) P L τ δ) N × Draws Bool N :=
  drawsUnzip N (drawsMap orderedStepSplit N w)

def orderedTapeToOriginal {Ω : Type} {d L : ℕ} {P : Parameters} {γ τ δ : ℝ}
    (N : ℕ) (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ × Draws (OrderedStepTape Ω d L P γ τ δ) N) :
    FiniteTrackingTape Ω (BranchedOjaDraws Ω d P γ δ) P L τ δ N × (Fin N → Bool) :=
  ((w.1,(orderedDrawsSplit N w.2).1),drawsVector id N (orderedDrawsSplit N w.2).2)

variable {Ω : Type} [MeasurableSpace Ω]

theorem orderedStepSplit_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (d L : ℕ) {γ : ℝ} (hγ : 0<γ) (τ δ : ℝ) :
    MeasurePreserving (@orderedStepSplit Ω d L P γ τ δ) (orderedStepLaw μ P d L hγ τ δ)
      ((trackingStepLaw μ (branchedOjaLaw μ P d hγ δ) P L τ δ).prod
        (PMF.uniformOfFintype Bool).toMeasure) := by
  have h₁ := (MeasurePreserving.id (branchedOjaLaw μ P d hγ δ)).prod
    (Measure.measurePreserving_swap (μ := (PMF.uniformOfFintype Bool).toMeasure)
      (ν := postMoveLaw μ P L τ δ))
  have h₂ := (measurePreserving_prodAssoc (branchedOjaLaw μ P d hγ δ)
    (postMoveLaw μ P L τ δ) (PMF.uniformOfFintype Bool).toMeasure).symm MeasurableEquiv.prodAssoc
  exact h₂.comp h₁

theorem orderedDrawsSplit_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (d L : ℕ) {γ : ℝ} (hγ : 0<γ) (τ δ : ℝ) (N : ℕ) :
    MeasurePreserving (@orderedDrawsSplit Ω d L P γ τ δ N)
      (drawsLaw (orderedStepLaw μ P d L hγ τ δ) N)
      ((drawsLaw (trackingStepLaw μ (branchedOjaLaw μ P d hγ δ) P L τ δ) N).prod
        (drawsLaw (PMF.uniformOfFintype Bool).toMeasure N)) :=
  (drawsUnzip_measurePreserving _ _ N).comp
    (drawsMap_measurePreserving (orderedStepSplit_measurePreserving μ P d L hγ τ δ) N)

theorem orderedTapeToOriginal_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (d L : ℕ) {γ : ℝ} (hγ : 0<γ) (τ δ : ℝ) (N : ℕ) :
    MeasurePreserving (@orderedTapeToOriginal Ω d L P γ τ δ N)
      ((localLaw μ (P.gradientNoise^2) (τ/4) δ).prod (drawsLaw (orderedStepLaw μ P d L hγ τ δ) N))
      ((finiteTrackingLaw μ (branchedOjaLaw μ P d hγ δ) P L τ δ N).prod (signLaw N)) := by
  have hs := drawsVector_measurePreserving (PMF.uniformOfFintype Bool).toMeasure N
  rw [←signLaw_eq_pi N] at hs
  have ht := ((MeasurePreserving.id
    (drawsLaw (trackingStepLaw μ (branchedOjaLaw μ P d hγ δ) P L τ δ) N)).prod hs).comp
      (orderedDrawsSplit_measurePreserving μ P d L hγ τ δ N)
  have ha := (MeasurePreserving.id (localLaw μ (P.gradientNoise^2) (τ/4) δ)).prod ht
  have hb := (measurePreserving_prodAssoc (localLaw μ (P.gradientNoise^2) (τ/4) δ)
    (drawsLaw (trackingStepLaw μ (branchedOjaLaw μ P d hγ δ) P L τ δ) N) (signLaw N)).symm
      MeasurableEquiv.prodAssoc
  exact hb.comp ha

end
end SecondOrder
