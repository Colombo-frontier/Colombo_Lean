import SecondOrder.IdealDisplacements

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

theorem stepDrift_measurable {A : Type*} [MeasurableSpace A] {d : ℕ} (L : ℝ)
    {z : A → IdealState d} {a : A → IdealMove d} (hz : Measurable z) (ha : Measurable a) :
    Measurable (fun w => stepDrift L (z w) (a w)) := by
  have he (w) : stepDrift L (z w) (a w) =
      if (z w).running then if moveTag (a w) = 1 then (-1/(4*L))•moveVector (a w) else 0 else 0 := by
    cases hr : (z w).running <;> cases ht : a w <;> simp [stepDrift,moveTag,moveVector,hr]
  simp_rw [he]
  exact Measurable.ite ((state_measurable_fields.mp hz).2.1 (measurableSet_singleton true))
    (Measurable.ite ((moveTag_measurable.comp ha) (measurableSet_singleton 1))
      (measurable_const.smul (moveVector_measurable.comp ha)) measurable_const) measurable_const

theorem stepDirection_measurable {A : Type*} [MeasurableSpace A] {d : ℕ} (s : ℝ)
    {z : A → IdealState d} {a : A → IdealMove d} (hz : Measurable z) (ha : Measurable a) :
    Measurable (fun w => stepDirection s (z w) (a w)) := by
  have he (w) : stepDirection s (z w) (a w) =
      if (z w).running then if moveTag (a w) = 2 then s•moveVector (a w) else 0 else 0 := by
    cases hr : (z w).running <;> cases ht : a w <;> simp [stepDirection,moveTag,moveVector,hr]
  simp_rw [he]
  exact Measurable.ite ((state_measurable_fields.mp hz).2.1 (measurableSet_singleton true))
    (Measurable.ite ((moveTag_measurable.comp ha) (measurableSet_singleton 2))
      (measurable_const.smul (moveVector_measurable.comp ha)) measurable_const) measurable_const

theorem idealDrift_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (t : ℕ) :
    Measurable (fun w : Ξ × (Fin t → Bool) => idealDrift L s (policy w.1) t w.2) := by
  have hz := idealRun_measurable L s hm t
  exact stepDrift_measurable L hz ((hm t).comp (measurable_id.prodMk hz))

theorem idealDirection_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (t : ℕ) :
    Measurable (fun w : Ξ × (Fin t → Bool) => idealDirection L s (policy w.1) t w.2) := by
  have hz := idealRun_measurable L s hm t
  exact stepDirection_measurable s hz ((hm t).comp (measurable_id.prodMk hz))

def mixedIdealDrift {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (i : Fin M) (w : Ξ × (Fin M → Bool)) : Point d :=
  idealDrift L s (policy w.1) i.val (signPrefix i w.2)

def mixedIdealInnovation {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (i : Fin M) : Ξ × (Fin M → Bool) → Point d :=
  mixedInnovation (fun ξ i => idealDirection L s (policy ξ) i.val) i

theorem mixedIdealDrift_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d M : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (i : Fin M) :
    Measurable (mixedIdealDrift L s policy i) :=
  (idealDrift_measurable L s hm i.val).comp
    (measurable_fst.prodMk ((measurable_of_countable (signPrefix i)).comp measurable_snd))

theorem mixedIdealInnovation_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d M : ℕ} (L s : ℝ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (i : Fin M) :
    Measurable (mixedIdealInnovation L s policy i) :=
  ((measurable_of_countable (fun w : Fin M → Bool => signValue (w i))).comp measurable_snd).smul
    ((idealDirection_measurable L s hm i.val).comp
      (measurable_fst.prodMk ((measurable_of_countable (signPrefix i)).comp measurable_snd)))

theorem signPrefix_eq_extend {M : ℕ} (i : Fin M) (w : Fin M → Bool) :
    signPrefix i w = (fun j : Fin i.val => extendSigns w j.val) := by
  funext j
  simp [signPrefix,extendSigns,j.isLt.trans i.isLt]

theorem mixedIdealDrift_eq_path {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (i : Fin M) (w : Ξ × (Fin M → Bool)) :
    mixedIdealDrift L s policy i w = pathDrift L s (policy w.1) (extendSigns w.2) i.val := by
  unfold mixedIdealDrift pathDrift
  rw [signPrefix_eq_extend]

theorem mixedIdealInnovation_eq_path {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (i : Fin M) (w : Ξ × (Fin M → Bool)) :
    mixedIdealInnovation L s policy i w = pathInnovation L s (policy w.1) (extendSigns w.2) i.val := by
  change signValue (w.2 i)•idealDirection L s (policy w.1) i.val (signPrefix i w.2) = _
  rw [signPrefix_eq_extend]
  simp only [pathInnovation,extendSigns,dif_pos i.isLt]

theorem mixedIdealDrift_energy {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (w : Ξ × (Fin M → Bool)) :
    (∑ i, ‖mixedIdealDrift L s policy i w‖^2) = (idealRun L s (policy w.1) M w.2).gradientEnergy := by
  simp_rw [mixedIdealDrift_eq_path]
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖pathDrift L s (policy w.1) (extendSigns w.2) k‖^2),
    idealPath_gradientEnergy,idealPath_extendSigns]

theorem mixedIdealInnovation_energy {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (w : Ξ × (Fin M → Bool)) :
    (∑ i, ‖mixedIdealInnovation L s policy i w‖^2) = (idealRun L s (policy w.1) M w.2).curvatureEnergy := by
  simp_rw [mixedIdealInnovation_eq_path]
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖pathInnovation L s (policy w.1) (extendSigns w.2) k‖^2),
    idealPath_curvatureEnergy,idealPath_extendSigns]

theorem mixedIdealDrift_sq_le_energy {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (i : Fin M) (w : Ξ × (Fin M → Bool)) :
    ‖mixedIdealDrift L s policy i w‖^2 ≤ (idealRun L s (policy w.1) M w.2).gradientEnergy := by
  rw [← mixedIdealDrift_energy L s policy w]
  exact Finset.single_le_sum (f := fun j : Fin M => ‖mixedIdealDrift L s policy j w‖^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem mixedIdealInnovation_sq_le_energy {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (i : Fin M) (w : Ξ × (Fin M → Bool)) :
    ‖mixedIdealInnovation L s policy i w‖^2 ≤ (idealRun L s (policy w.1) M w.2).curvatureEnergy := by
  rw [← mixedIdealInnovation_energy L s policy w]
  exact Finset.single_le_sum (f := fun j : Fin M => ‖mixedIdealInnovation L s policy j w‖^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem mixedIdeal_displacement {Ξ : Type*} {d M : ℕ} (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (w : Ξ × (Fin M → Bool)) (i : Fin M) :
    (idealPath L s (policy w.1) (extendSigns w.2) (i.val+1)).point-
      (idealPath L s (policy w.1) (extendSigns w.2) i.val).point =
        mixedIdealDrift L s policy i w+mixedIdealInnovation L s policy i w := by
  rw [mixedIdealDrift_eq_path,mixedIdealInnovation_eq_path]
  exact idealPath_displacement L s _ _ _

end
end SecondOrder
