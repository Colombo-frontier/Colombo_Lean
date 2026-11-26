import SecondOrder.OjaAverageAccuracy

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

/-- The N actual query directions, each recorded before its new HVP. -/
def ojaDirections {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → Fin N → Point d
  | 0, _ => Fin.elim0
  | N+1, w => Fin.snoc (ojaDirections P f η x v N w.1) (ojaHvpRun P f η x v N w.1)

theorem ojaDirections_mean_sum {Ω : Type*} {d : ℕ} (P : Parameters)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ)
    (w : Draws Ω N) :
    (∑ i, ⟪shiftedHessian (eigenHessianBound P) (hessian F x) (ojaDirections P f η x v N w i),
      ojaDirections P f η x v N w i⟫_ℝ) = ojaMeanRayleighSum P F f η x v N w := by
  induction N with
  | zero => simp [ojaMeanRayleighSum]
  | succ N ih =>
    simp only [ojaDirections,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,ih,
      ojaMeanRayleighSum]

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaDirections_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : (Point d × Point d) × Draws Ω N =>
      ojaDirections P f η w.1.1 w.1.2 N w.2) := by
  induction N with
  | zero => exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ N ih =>
    have hp : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        (w.1,w.2.1)) := measurable_fst.prodMk measurable_snd.fst
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [ojaDirections,Fin.snoc_last] using (h.ojaHvpRun_measurable η N).comp hp
    · simpa only [ojaDirections,Fin.snoc_castSucc] using ((measurable_pi_apply j).comp ih).comp hp

theorem CommonLoss.ojaDirections_ae_norm (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ∀ (x v : Point d), ‖v‖ = 1 →
      ∀ i, ‖ojaDirections P f η x v N w i‖ = 1 := by
  induction N with
  | zero => filter_upwards with w x v hv i; exact Fin.elim0 i
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hu := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae
      (h.ojaHvpRun_ae_norm hη N)
    filter_upwards [hp,hu] with w hw hu
    intro x v hv i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [ojaDirections,Fin.snoc_last] using hu x v hv
    · simpa only [ojaDirections,Fin.snoc_castSucc] using hw x v hv j

end
end SecondOrder
