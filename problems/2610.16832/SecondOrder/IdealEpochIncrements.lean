import SecondOrder.IdealIncrementMoments
import SecondOrder.PredictableReindex
import SecondOrder.EpochMeasurability

open MeasureTheory
open scoped Classical BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

theorem isGradientMove_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    {z : A → IdealState d} {a : A → IdealMove d} (hz : Measurable z) (ha : Measurable a) :
    Measurable (fun w => isGradientMove (z w) (a w)) := by
  have he (w) : isGradientMove (z w) (a w) =
      if (z w).running then if moveTag (a w) = 1 then true else false else false := by
    cases hr : (z w).running <;> cases ht : a w <;> simp [isGradientMove,moveTag,hr]
  simp_rw [he]
  exact Measurable.ite ((state_measurable_fields.mp hz).2.1 (measurableSet_singleton true))
    (Measurable.ite ((moveTag_measurable.comp ha) (measurableSet_singleton 1))
      measurable_const measurable_const) measurable_const

theorem idealPath_from_finite_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M t : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealPath L s (policy w.1) (extendSigns w.2) t) :=
  (idealRun_measurable L s hm t).comp (measurable_fst.prodMk
    ((measurable_of_countable (fun w : Fin M → Bool => fun i : Fin t => extendSigns w i.val)).comp measurable_snd))

theorem idealGradientFlag_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M t : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealGradientFlag L s (policy w.1) (extendSigns w.2) t) := by
  have hz := idealPath_from_finite_measurable L s hm M t
  have hp : Measurable (fun w : Ξ × (Fin M → Bool) => (w.1,fun i : Fin t => extendSigns w.2 i.val)) :=
    measurable_fst.prodMk
    ((measurable_of_countable (fun w : Fin M → Bool => fun i : Fin t => extendSigns w i.val)).comp measurable_snd)
  exact isGradientMove_measurable hz ((hm t).comp (hp.prodMk hz))

/-- The next move's epoch and local offset, computed using only the past. -/
def idealEpochAddress {d : ℕ} (q : ℕ) (L s : ℝ) (policy : IdealPolicy d)
    (t : ℕ) (past : Fin t → Bool) : ℕ × ℕ :=
  epochAddress q (idealGradientFlag L s policy (extendSigns past)) t

theorem idealEpochAddress_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d q : ℕ} (hq : 0 < q)
    (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (t : ℕ) :
    Measurable (fun w : Ξ × (Fin t → Bool) => idealEpochAddress q L s (policy w.1) t w.2) :=
  epochAddress_measurable hq (idealGradientFlag_measurable L s hm t) t

theorem idealEpochAddress_prefix {d M q : ℕ} (hq : 0 < q) (L s : ℝ) (policy : IdealPolicy d)
    (i : Fin M) (w : Fin M → Bool) :
    idealEpochAddress q L s policy i.val (signPrefix i w) =
      epochAddress q (idealGradientFlag L s policy (extendSigns w)) i.val := by
  have hh := idealEpochClock_predictable q L s policy (t := i.val)
    (w := extendSigns (signPrefix i w)) (v := extendSigns w) (fun j hj => by
      simp [extendSigns,signPrefix,hj,hj.trans i.isLt])
  simp only [idealEpochAddress,epochAddress,← epochClock_number hq]
  rw [hh]

theorem idealEpochAddress_injective {d M q : ℕ} (hq : 0 < q) (L s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) : Function.Injective (fun i : Fin M => idealEpochAddress q L s policy i.val (signPrefix i w)) := by
  intro i j he
  simp_rw [idealEpochAddress_prefix hq] at he
  exact Fin.ext (epochAddress_injective hq _ he)

def idealEpochInnovation {Ξ : Type*} {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (r : ℕ × ℕ) : Ξ × (Fin M → Bool) → Point d :=
  reindexedInnovation (fun ξ i => idealDirection L s (policy ξ) i.val)
    (fun ξ i => idealEpochAddress q L s (policy ξ) i.val) r

theorem idealEpochInnovation_eq {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (r : ℕ × ℕ) (w : Ξ × (Fin M → Bool)) :
    idealEpochInnovation q L s policy r w = ∑ i : Fin M,
      if epochAddress q (idealGradientFlag L s (policy w.1) (extendSigns w.2)) i.val = r then
        mixedIdealInnovation L s policy i w else 0 := by
  simp only [idealEpochInnovation,reindexedInnovation,mixedInnovation_selectedDirection,
    idealEpochAddress_prefix hq,mixedIdealInnovation]

theorem idealEpochAddress_selection_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d M q : ℕ}
    (hq : 0 < q) (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (r : ℕ × ℕ) (i : Fin M) :
    MeasurableSet {w : Ξ × (Fin M → Bool) | idealEpochAddress q L s (policy w.1) i.val (signPrefix i w.2) = r} :=
  (measurableSet_singleton r).preimage ((idealEpochAddress_measurable hq L s hm i.val).comp
    (measurable_fst.prodMk ((measurable_of_countable (signPrefix i)).comp measurable_snd)))

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealEpochInnovation_moments (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) (r : ℕ × ℕ) :
    Integrable (idealEpochInnovation (M := M) q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r)
      (η.prod (signLaw M)) ∧
    Integrable (fun w => ‖idealEpochInnovation q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r w‖^2)
      (η.prod (signLaw M)) := by
  have hl := idealEpochAddress_selection_measurable (M := M) hq P.gradientLip
    (curvatureRadius P.hessianHolder ν γ) hm r
  have hi := fun i : Fin M => (h.idealIncrement_integrable (η := η) hτ hγ hm hv i).2
  have hi2 := fun i : Fin M => (h.idealIncrement_second_moments (η := η) hτ hγ hm hv i).2
  exact ⟨reindexedInnovation_integrable _ _ r hl hi,reindexedInnovation_second_moment _ _ r hl hi hi2⟩

/-- Orthogonality survives the actual history-dependent epoch restart and
local-time reindexing. No conditional independence of completed nodes is assumed. -/
theorem CommonLoss.idealEpochInnovation_orthogonal (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) (r s : ℕ × ℕ) (hrs : r ≠ s) :
    (∫ w, ⟪idealEpochInnovation q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r w,
      idealEpochInnovation q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy s w⟫_ℝ
      ∂η.prod (signLaw M)) = 0 := by
  exact reindexedInnovation_orthogonal _ _
    (idealEpochAddress_selection_measurable hq _ _ hm)
    (fun i => (h.idealIncrement_integrable hτ hγ hm hv i).2)
    (fun i => (h.idealIncrement_second_moments hτ hγ hm hv i).2) r s hrs

end
end SecondOrder
