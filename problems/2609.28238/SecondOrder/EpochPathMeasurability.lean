import SecondOrder.EpochPath
import SecondOrder.TreeCostEnergy

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem idealEpochBegin_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d q : ℕ} (hq : 0 < q)
    (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M e : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealEpochBegin q L s (policy w.1) w.2 e) :=
  epochBoundary_measurable hq (idealPhysicalLength_measurable L s hm M) (idealGradientFlag_measurable L s hm M) e

theorem idealEpochLength_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d q : ℕ} (hq : 0 < q)
    (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M e : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealEpochLength q L s (policy w.1) w.2 e) :=
  epochLength_measurable hq (idealPhysicalLength_measurable L s hm M) (idealGradientFlag_measurable L s hm M) e

theorem idealPath_variable_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M : ℕ)
    {T : Ξ × (Fin M → Bool) → ℕ} (hT : Measurable T) :
    Measurable (fun w => idealPath L s (policy w.1) (extendSigns w.2) (T w)) := by
  have ht : Measurable (fun w : (Ξ × (Fin M → Bool)) × ℕ =>
      idealPath L s (policy w.1.1) (extendSigns w.1.2) w.2) := by
    apply measurable_from_prod_countable
    exact idealPath_from_finite_measurable L s hm M
  exact ht.comp (measurable_id.prodMk hT)

theorem idealEpochPath_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d q : ℕ} (hq : 0 < q)
    (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (M e k : ℕ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealEpochPath q L s (policy w.1) w.2 e k) := by
  have ht := (idealEpochBegin_measurable hq L s hm M e).add
    ((measurable_const (a := k)).min (idealEpochLength_measurable hq L s hm M e))
  exact (state_measurable_fields.mp (idealPath_variable_measurable L s hm M ht)).1

/-- Every completed local node is the actual direct chord between shifted
physical endpoints, and equals the sum of its reindexed physical increments. -/
theorem idealEpoch_completed_chord {Ξ : Type*} {d M q L : ℕ} (hq : 0 < q) (Lip s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (e : ℕ) (i : Fin L × Fin M)
    (hi : nodeRight (paddedNode i) ≤ idealEpochLength q Lip s (policy w.1) w.2 e) :
    (∑ k ∈ dyadicBlock M i.1.val i.2,
      (idealEpochDrift q Lip s policy (e,k.val) w+idealEpochInnovation q Lip s policy (e,k.val) w)) =
      (idealPath Lip s (policy w.1) (extendSigns w.2)
        (idealEpochBegin q Lip s (policy w.1) w.2 e+nodeRight (paddedNode i))).point-
      (idealPath Lip s (policy w.1) (extendSigns w.2)
        (idealEpochBegin q Lip s (policy w.1) w.2 e+nodeLeft (paddedNode i))).point := by
  have hh := dyadicBlock_telescopes (idealEpochPath q Lip s (policy w.1) w.2 e) i
    (hi.trans (idealEpochLength_le q Lip s (policy w.1) w.2 e))
  simp_rw [idealEpochPath_displacement hq] at hh
  rw [idealEpochPath_endpoint q Lip s (policy w.1) w.2 e _ hi,
    idealEpochPath_endpoint q Lip s (policy w.1) w.2 e _ ((nodeLeft_lt_right _).le.trans hi)] at hh
  exact hh

end
end SecondOrder
