import SecondOrder.OrderedTapeTransport

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

theorem orderedBudgetRun_matches {Ω : Type} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (N : ℕ)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (w : Draws (OrderedStepTape Ω d L P γ τ δ) N)
    (β : ℕ → Bool) (hβ : ∀ i : Fin N, β i=drawsVector id N (orderedDrawsSplit N w).2 i) :
    orderedBudgetRun P f q Q Lip s τ ρ γ δ N (a,w)=
      budgetedTrackedRun P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
        (fun x t => branchedOjaReply P f x γ δ t) a β N (orderedDrawsSplit N w).1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hpre : ∀ i : Fin N, β i=drawsVector id N (orderedDrawsSplit N w.1).2 i := by
      intro i
      simpa only [orderedDrawsSplit,drawsMap,drawsUnzip,drawsVector,Fin.snoc_castSucc,Fin.coe_castSucc]
        using hβ i.castSucc
    have hlast : β N=w.2.2.1 := by
      simpa only [orderedDrawsSplit,drawsMap,drawsUnzip,drawsVector,Fin.snoc_last,
        Fin.val_last,orderedStepSplit,id_eq] using hβ (Fin.last N)
    change orderedBudgetStep P f q Q Lip s τ ρ γ δ
      (orderedBudgetRun P f q Q Lip s τ ρ γ δ N (a,w.1)) w.2=_
    rw [ih w.1 hpre]
    simp only [budgetedTrackedRun,orderedDrawsSplit,drawsMap,drawsUnzip,orderedStepSplit,hlast,
      orderedBudgetStep]

theorem orderedBudgetRun_original {Ω : Type} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (N : ℕ)
    (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ × Draws (OrderedStepTape Ω d L P γ τ δ) N) :
    orderedBudgetRun P f q Q Lip s τ ρ γ δ N w=
      finiteBudgetedRun P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
        (fun x t => branchedOjaReply P f x γ δ t) N (orderedTapeToOriginal N w) := by
  apply orderedBudgetRun_matches P f q Q Lip s τ ρ γ δ N w.1 w.2
  intro i
  simp only [extendSigns,dif_pos i.isLt,orderedTapeToOriginal]

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The entire reply-only program and original finite sampler have the
same joint budget-state law, with all signs, refusals and samples included. -/
theorem CommonLoss.budgetRunProgram_original_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q Q : ℕ) (Lip s τ ρ : ℝ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (N : ℕ) :
    budgetRunOutputLaw μ P q Q Lip s τ ρ γ δ (trackingProgramSeedLaw P d L hγ δ)
      (fun q a => hvpReply f a q) N=
      Measure.map
        (finiteBudgetedRun (Ψ := (BranchedOjaDraws Ω d P γ δ : Type)) P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
          (fun x t => branchedOjaReply P f x γ δ t) N)
        ((finiteTrackingLaw μ (branchedOjaLaw μ P d hγ δ) P L τ δ N).prod (signLaw N)) := by
  rw [h.budgetRunProgram_ordered_outputLaw a₀ q Q Lip s τ ρ hγ δ N]
  have ht := orderedTapeToOriginal_measurePreserving μ P d L hγ τ δ N
  have hm := h.finiteBudgetedRun_measurable (L := L) (Ψ := (BranchedOjaDraws Ω d P γ δ : Type)) q Q (branchedOjaQueryCount P d γ δ)
    Lip s τ ρ δ (routine := fun x t => branchedOjaReply P f x γ δ t)
    (h.branchedOjaReply_measurable γ δ) N
  rw [←ht.map_eq,Measure.map_map hm ht.measurable]
  apply congrArg (fun k : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ ×
      Draws (OrderedStepTape Ω d L P γ τ δ) N → BudgetTracker d L =>
    Measure.map k ((localLaw μ (P.gradientNoise^2) (τ/4) δ).prod
      (drawsLaw (orderedStepLaw μ P d L hγ τ δ) N)))
  funext w
  exact orderedBudgetRun_original P f q Q Lip s τ ρ γ δ N w

end
end SecondOrder
