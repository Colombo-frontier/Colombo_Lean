import SecondOrder.OracleHistory
import SecondOrder.RepeatedTrials

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {A B Ω : Type}

def historyDraws : (n : ℕ) → FiniteHistory Unit Ω n → Draws Ω n
  | 0, _ => PUnit.unit
  | n+1, w => (historyDraws n w.1,w.2)

theorem historyDraws_measurable [MeasurableSpace Ω] (n : ℕ) :
    Measurable (@historyDraws Ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).prodMk measurable_snd

/-- The standard oracle history and the batch representation have the same
ordered independent sample law; only their empty-history types differ. -/
theorem historyDraws_measurePreserving [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (historyDraws n) (oracleHistoryLaw μ n) (drawsLaw μ n) := by
  induction n with
  | zero => exact ⟨measurable_const,Measure.map_dirac measurable_const ()⟩
  | succ n ih => exact ih.prod (MeasurePreserving.id μ)

def drawsMap (f : A → B) : (n : ℕ) → Draws A n → Draws B n
  | 0, _ => PUnit.unit
  | n+1, w => (drawsMap f n w.1,f w.2)

def drawsHistory : (n : ℕ) → Draws Ω n → FiniteHistory Unit Ω n
  | 0, _ => ()
  | n+1, w => (drawsHistory n w.1,w.2)

theorem drawsHistory_measurable [MeasurableSpace Ω] (n : ℕ) :
    Measurable (@drawsHistory Ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).prodMk measurable_snd

theorem drawsHistory_measurePreserving [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (drawsHistory n) (drawsLaw μ n) (oracleHistoryLaw μ n) := by
  induction n with
  | zero => exact ⟨measurable_const,Measure.map_dirac measurable_const PUnit.unit⟩
  | succ n ih => exact ih.prod (MeasurePreserving.id μ)

theorem historyDraws_drawsHistory (n : ℕ) (w : Draws Ω n) :
    historyDraws n (drawsHistory n w)=w := by
  induction n with
  | zero => exact Subsingleton.elim (α := PUnit) _ _
  | succ n ih => exact Prod.ext (ih w.1) rfl

theorem drawsHistory_historyDraws (n : ℕ) (w : FiniteHistory Unit Ω n) :
    drawsHistory n (historyDraws n w)=w := by
  induction n with
  | zero => exact Subsingleton.elim (α := Unit) _ _
  | succ n ih => exact Prod.ext (ih w.1) rfl

theorem finiteHistoryTape_historyDraws (a₀ : Ω) (n : ℕ) (w : FiniteHistory Unit Ω n) (i : Fin n) :
    finiteHistoryTape a₀ n w i=drawsVector id n (historyDraws n w) i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.val_last,finiteHistoryTape_succ_at,historyDraws,drawsVector,Fin.snoc_last,id_eq]
    · simpa only [Fin.coe_castSucc,finiteHistoryTape_succ_lt a₀ n w j j.isLt,
        historyDraws,drawsVector,Fin.snoc_castSucc] using ih w.1 j

theorem drawsMap_measurable [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} (hf : Measurable f) (n : ℕ) : Measurable (drawsMap f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).prodMk (hf.comp measurable_snd)

theorem drawsMap_measurePreserving [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {η : Measure B} [IsProbabilityMeasure μ] {f : A → B}
    (hf : MeasurePreserving f μ η) (n : ℕ) :
    MeasurePreserving (drawsMap f n) (drawsLaw μ n) (drawsLaw η n) := by
  induction n with
  | zero => exact ⟨measurable_const,Measure.map_dirac measurable_const PUnit.unit⟩
  | succ n ih => exact ih.prod hf

theorem drawsVector_drawsMap (f : A → B) (n : ℕ) (w : Draws A n) (i : Fin n) :
    drawsVector id n (drawsMap f n w) i=f (drawsVector id n w i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [drawsMap,drawsVector,Fin.snoc_last,id_eq]
    · simpa only [drawsMap,drawsVector,Fin.snoc_castSucc] using ih w.1 j

def drawsAppend (n : ℕ) : (m : ℕ) → Draws Ω n → Draws Ω m → Draws Ω (n+m)
  | 0, u, _ => u
  | m+1, u, w => (drawsAppend n m u w.1,w.2)

theorem drawsAppend_measurable [MeasurableSpace Ω] (n m : ℕ) :
    Measurable (fun w : Draws Ω n × Draws Ω m => drawsAppend n m w.1 w.2) := by
  induction m with
  | zero => exact measurable_fst
  | succ m ih =>
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd

/-- Concatenating independent blocks yields precisely the fresh sample
law for the sum of their lengths. No assumptions on the sample space beyond
measurability are needed. -/
theorem drawsAppend_measurePreserving [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n m : ℕ) :
    MeasurePreserving (fun w : Draws Ω n × Draws Ω m => drawsAppend n m w.1 w.2)
      ((drawsLaw μ n).prod (drawsLaw μ m)) (drawsLaw μ (n+m)) := by
  induction m with
  | zero =>
    refine ⟨measurable_fst,?_⟩
    change Measure.map Prod.fst ((drawsLaw μ n).prod (drawsLaw μ 0))=drawsLaw μ n
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  | succ m ih =>
    have ha := (measurePreserving_prodAssoc (drawsLaw μ n) (drawsLaw μ m) μ).symm
      MeasurableEquiv.prodAssoc
    exact (ih.prod (MeasurePreserving.id μ)).comp ha

end
end SecondOrder
