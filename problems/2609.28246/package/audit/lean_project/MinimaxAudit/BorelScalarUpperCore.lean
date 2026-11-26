import MinimaxAudit.BorelHistory
import MinimaxAudit.ScalarUpper

/-! Borel measurability of the concrete executable scalar upper policies.
No measurability of the upper algorithm is assumed as an extra hypothesis. -/
open Set MeasureTheory
namespace MinimaxAudit.BorelScalarUpper
open VIReference.Pilot ScalarUpper BorelHistory
attribute [local instance] BorelStoppingPolicy.seedMeasurable
noncomputable section

variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

/-- Permutation symmetry is a closed tensor condition. -/
theorem symmetric_tensors_closed (k : ℕ) :
    IsClosed {A : ContinuousMultilinearMap ℝ (fun _ : Fin k => SaddleSpace dx dy)
      (SaddleSpace dx dy) | IsSymmetricContinuousMultilinearMap (SaddleSpace dx dy) A} := by
  simp only [IsSymmetricContinuousMultilinearMap, setOf_forall]
  apply isClosed_iInter
  intro sigma
  exact isClosed_eq (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ
    (SaddleSpace dx dy) (SaddleSpace dx dy) sigma).continuous continuous_id

/-- Even the nonsymmetric-history fallback in the actual old compiler is Borel. -/
theorem makeSymmetric_measurable (k : ℕ) :
    Measurable (makeSymmetric :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => SaddleSpace dx dy) (SaddleSpace dx dy) →
      SymmetricContinuousMultilinearMap (SaddleSpace dx dy) k) := by
  classical
  apply Measurable.subtype_mk
  have heq : (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => SaddleSpace dx dy) (SaddleSpace dx dy) =>
      (makeSymmetric A).1) = fun A => if IsSymmetricContinuousMultilinearMap (SaddleSpace dx dy) A then A else 0 := by
    funext A
    by_cases h : IsSymmetricContinuousMultilinearMap (SaddleSpace dx dy) A <;> simp [makeSymmetric, h]
  change Measurable (fun A => (makeSymmetric A).1)
  rw [heq]
  exact Measurable.ite (symmetric_tensors_closed k).measurableSet measurable_id measurable_const

/-- Riesz/curry/sign tensor conversion is an isometry and hence continuous. -/
theorem scalarToSaddleTensor_continuous (k : ℕ) :
    Continuous (scalarToSaddleTensor (euclideanSaddleSign dx dy) (k := k)) := by
  have hi : Isometry (scalarToSaddleTensor (euclideanSaddleSign dx dy) (k := k)) := by
    intro A B
    simp only [edist_dist, dist_eq_norm, scalar_to_saddle_tensor_difference_norm]
  exact hi.continuous

theorem scalarJetToSymmetricOperatorJet_measurable (p dx dy : ℕ) :
    Measurable (scalarJetToSymmetricOperatorJet p (euclideanSaddleSign dx dy)) := by
  letI : BorelSpace (ScalarJet p (SaddleSpace dx dy)) := ⟨rfl⟩
  apply measurable_pi_lambda
  intro k
  letI : MeasurableSpace (ContinuousMultilinearMap ℝ
    (fun _ : Fin (k.1 + 1) => SaddleSpace dx dy) ℝ) := borel _
  letI : BorelSpace (ContinuousMultilinearMap ℝ
    (fun _ : Fin (k.1 + 1) => SaddleSpace dx dy) ℝ) := ⟨rfl⟩
  have hproj : Continuous (fun J : ScalarJet p (SaddleSpace dx dy) => J ⟨k.1 + 1, by omega⟩) :=
    continuous_apply _
  exact (makeSymmetric_measurable (dx := dx) (dy := dy) k.1).comp
    ((scalarToSaddleTensor_continuous (dx := dx) (dy := dy) k.1).measurable.comp hproj.measurable)

/-- The finite-history operator compiler is Borel on its full canonical
history space, including infeasible and over-budget fake histories. -/
theorem compiledAction_measurable {Answer : Type*} [MeasurableSpace Answer]
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (hconvert : Measurable convertAnswer) (hZ : MeasurableSet (productDomain X Y)) :
    Measurable (compiledAction P seed fill convertAnswer) := by
  classical
  apply (measurable_history_iff _).2
  intro n
  let valid : Set (Fin n → Entry p dx dy) := {v | ∀ i, (v i).1 ∈ productDomain X Y}
  have hvalid : MeasurableSet valid := by
    simp only [valid, setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurable_fst.comp (measurable_pi_apply i)) hZ
  by_cases hn : n ≤ N
  · let record : valid → OracleHistory (productDomain X Y) Answer n :=
      fun v i => (⟨(v.1 i).1, v.2 i⟩, convertAnswer (v.1 i).2)
    have hrecord : Measurable record := by
      apply measurable_pi_lambda
      intro i
      exact ((measurable_fst.comp ((measurable_pi_apply i).comp measurable_subtype_coe)).subtype_mk).prodMk
        (hconvert.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_subtype_coe)))
    have hgood : Measurable (fun v : valid => P.rule ⟨n, by omega⟩ (seed, record v)) := by
      exact (P.rule_measurable _).comp (measurable_const.prodMk hrecord)
    have hpiece := Measurable.dite hgood
      (measurable_const : Measurable (fun _ : ↥(validᶜ) => (Sum.inl fill : OracleAction (productDomain X Y)))) hvalid
    convert hpiece using 1
    funext v
    by_cases hv : v ∈ valid
    · rw [dif_pos hv]
      let hs : MeasurableExecution.FiniteHistory (p := p) X Y n :=
        fun i => (⟨(v i).1, hv i⟩, (v i).2)
      have he : MeasurableExecution.finiteHistoryList hs = List.ofFn v := rfl
      rw [← he, compiled_action_of_finite P seed fill convertAnswer hs hn]
    · rw [dif_neg hv]
      unfold compiledAction
      rw [dif_neg]
      intro hf
      apply hv
      intro i
      exact hf (v i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · have hconst : (fun v : Fin n → Entry p dx dy => compiledAction P seed fill convertAnswer (List.ofFn v)) =
        fun _ => (Sum.inl fill : OracleAction (productDomain X Y)) := by
      funext v
      unfold compiledAction
      split_ifs with hf
      · simp [boundedRule, convertedRecord, hn]
      · rfl
    rw [hconst]
    exact measurable_const

theorem compileScalarPolicy_borel {Answer : Type*} [MeasurableSpace Answer]
    (P : BorelStoppingPolicy (Answer := Answer) (productDomain X Y) N)
    (seed : P.Seed) (fill : productDomain X Y)
    (convertAnswer : ScalarJet p (SaddleSpace dx dy) → Answer)
    (hconvert : Measurable convertAnswer) (hZ : MeasurableSet (productDomain X Y)) :
    Measurable (compileScalarPolicy P seed fill convertAnswer).query ∧
    Measurable (compileScalarPolicy P seed fill convertAnswer).output := by
  have ha := compiledAction_measurable P seed fill convertAnswer hconvert hZ
  constructor
  · change Measurable[_, MeasurableSpace.comap optionPointEncoding inferInstance] _
    apply measurable_comap_iff.2
    have hm : Measurable (Sum.elim (fun _ : productDomain X Y => Sum.inl ())
        (fun q : productDomain X Y => (Sum.inr q.1 : Unit ⊕ SaddleSpace dx dy))) :=
      measurable_fun_sum measurable_const (measurable_inr.comp measurable_subtype_coe)
    convert hm.comp ha using 1
    funext h
    cases he : compiledAction P seed fill convertAnswer h <;> simp [Function.comp_def, compileScalarPolicy, optionPointEncoding, he]
  · have hm : Measurable (Sum.elim (fun out : productDomain X Y => out.1)
        (fun _ : productDomain X Y => fill.1)) :=
      measurable_fun_sum measurable_subtype_coe measurable_const
    convert hm.comp ha using 1
    funext h
    cases he : compiledAction P seed fill convertAnswer h <;> simp [Function.comp_def, compileScalarPolicy, he]


end
end MinimaxAudit.BorelScalarUpper
