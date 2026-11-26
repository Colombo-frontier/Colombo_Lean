import SecondOrder.DrawsLawTransport

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

theorem product_rotate_seed (μ : Measure A) (η : Measure B) (θ : Measure C) (ζ : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    [IsProbabilityMeasure θ] [IsProbabilityMeasure ζ] :
    MeasurePreserving (fun w : ((A × B) × C) × D => ((w.1.1.2,w.1.2),(w.1.1.1,w.2)))
      (((μ.prod η).prod θ).prod ζ) ((η.prod θ).prod (μ.prod ζ)) := by
  have h₁ := (measurePreserving_prodAssoc μ η θ).prod (MeasurePreserving.id ζ)
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := η.prod θ)).prod (MeasurePreserving.id ζ)
  exact (measurePreserving_prodAssoc (η.prod θ) μ ζ).comp (h₂.comp h₁)

theorem product_swap_first (μ : Measure A) (η : Measure B) (θ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure θ] :
    MeasurePreserving (fun w : A × (B × C) => (w.2.1,(w.1,w.2.2)))
      (μ.prod (η.prod θ)) (η.prod (μ.prod θ)) := by
  have h₁ := (measurePreserving_prodAssoc μ η θ).symm MeasurableEquiv.prodAssoc
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := η)).prod (MeasurePreserving.id θ)
  exact (measurePreserving_prodAssoc η μ θ).comp (h₂.comp h₁)

theorem product_interleave (μ : Measure A) (η : Measure B) (θ : Measure C) (ζ : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    [IsProbabilityMeasure θ] [IsProbabilityMeasure ζ] :
    MeasurePreserving (fun w : (A × B) × (C × D) => ((w.1.1,w.2.1),(w.1.2,w.2.2)))
      ((μ.prod η).prod (θ.prod ζ)) ((μ.prod θ).prod (η.prod ζ)) := by
  have h₁ := measurePreserving_prodAssoc μ η (θ.prod ζ)
  have h₂ := (MeasurePreserving.id μ).prod (product_swap_first η θ ζ)
  have h₃ := (measurePreserving_prodAssoc μ θ (η.prod ζ)).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

def drawsUnzip {A B : Type} : (n : ℕ) → Draws (A × B) n → Draws A n × Draws B n
  | 0, _ => (PUnit.unit,PUnit.unit)
  | n+1, w =>
    let u := drawsUnzip n w.1
    ((u.1,w.2.1),(u.2,w.2.2))

theorem drawsUnzip_measurable (n : ℕ) : Measurable (@drawsUnzip A B n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((ih.fst.comp measurable_fst).prodMk measurable_snd.fst).prodMk
      ((ih.snd.comp measurable_fst).prodMk measurable_snd.snd)

/-- Independent paired samples can be regrouped into independent sample
arrays. This separates private randomness from unknown oracle samples. -/
theorem drawsUnzip_measurePreserving (μ : Measure A) (η : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (n : ℕ) :
    MeasurePreserving (drawsUnzip n) (drawsLaw (μ.prod η) n)
      ((drawsLaw μ n).prod (drawsLaw η n)) := by
  induction n with
  | zero =>
    refine ⟨measurable_const,?_⟩
    change Measure.map (fun _ : PUnit => (PUnit.unit,PUnit.unit)) (Measure.dirac PUnit.unit)=
      (Measure.dirac PUnit.unit).prod (Measure.dirac PUnit.unit)
    rw [Measure.dirac_prod_dirac,Measure.map_dirac measurable_const]
  | succ n ih =>
    exact (product_interleave (drawsLaw μ n) (drawsLaw η n) μ η).comp
      (ih.prod (MeasurePreserving.id (μ.prod η)))

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem drawsVector_unzip_fst (n : ℕ) (w : Draws (A × B) n) (i : Fin n) :
    drawsVector id n (drawsUnzip n w).1 i=(drawsVector id n w i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [drawsUnzip,drawsVector,Fin.snoc_last,id_eq]
    · simpa only [drawsUnzip,drawsVector,Fin.snoc_castSucc] using ih w.1 j

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem drawsVector_unzip_snd (n : ℕ) (w : Draws (A × B) n) (i : Fin n) :
    drawsVector id n (drawsUnzip n w).2 i=(drawsVector id n w i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [drawsUnzip,drawsVector,Fin.snoc_last,id_eq]
    · simpa only [drawsUnzip,drawsVector,Fin.snoc_castSucc] using ih w.1 j

end
end SecondOrder
