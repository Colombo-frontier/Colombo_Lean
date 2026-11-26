import Bilevel.StatefulBounds

/-! Integral and exact original-call accounting laws of stateful composition. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Bilevel.Stateful.Procedure
variable {Param History Out Next : Type*} [MeasurableSpace Param]
  [MeasurableSpace History] [MeasurableSpace Out] [MeasurableSpace Next]

theorem pure_law (f : Param → Out) (hf : Measurable f) (p : Param) (h : History) :
    (pure f hf : Procedure Param History Out).law (p,h) = Measure.dirac (f p,h,0) := rfl

theorem integral_bind {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Procedure Param History Out) (Q : Procedure (Param × Out) History Next)
    (p : Param) (h : History) (f : Outcome Next History → E)
    (hf : StronglyMeasurable f) (hi : Integrable f ((P.bind Q).law (p,h))) :
    (∫ z, f z ∂(P.bind Q).law (p,h)) =
      ∫ z, ∫ w, f (combine (z,w)) ∂Q.law ((p,z.1),z.2.1) ∂P.law (p,h) := by
  rw [bind_law_eq] at hi ⊢
  rw [integral_map combine_measurable.aemeasurable hf.aestronglyMeasurable]
  exact Measure.integral_compProd
    ((integrable_map_measure hf.aestronglyMeasurable combine_measurable.aemeasurable).mp hi)

theorem ae_bind_iff (P : Procedure Param History Out) (Q : Procedure (Param × Out) History Next)
    (p : Param) (h : History) (R : Outcome Next History → Prop)
    (hR : MeasurableSet {z | R z}) :
    (∀ᵐ z ∂(P.bind Q).law (p,h), R z) ↔
      ∀ᵐ z ∂P.law (p,h), ∀ᵐ w ∂Q.law ((p,z.1),z.2.1), R (combine (z,w)) := by
  rw [bind_law_eq, ae_map_iff combine_measurable.aemeasurable hR]
  exact Measure.ae_compProd_iff (combine_measurable hR)

theorem calls_pure (f : Param → Out) (hf : Measurable f) :
    (pure f hf : Procedure Param History Out).CallsEq (fun _ => 0) := by
  intro p h
  rw [pure_law]
  have hp : MeasurableSet {z : Outcome Out History | z.2.2 = 0} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton 0)
  exact (ae_dirac_iff hp).mpr rfl

theorem CallsEq.bind (P : Procedure Param History Out)
    (Q : Procedure (Param × Out) History Next) (a b : Param → ℕ)
    (hP : P.CallsEq a) (hQ : Q.CallsEq (fun z => b z.1)) :
    (P.bind Q).CallsEq (fun p => a p + b p) := by
  intro p h
  have hp : MeasurableSet {z : Outcome Next History | z.2.2 = a p + b p} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton _)
  apply (ae_bind_iff P Q p h _ hp).mpr
  filter_upwards [hP p h] with z hz
  filter_upwards [hQ (p,z.1) z.2.1] with w hw
  exact congrArg₂ (· + ·) hz hw

theorem CallsEq.costBound (P : Procedure Param History Out) (a : Param → ℕ)
    (hP : P.CallsEq a) : P.CostBound (fun p => (a p : ℝ)) := by
  intro p h
  have he : (fun z : Outcome Out History => (z.2.2 : ℝ)) =ᵐ[P.law (p,h)]
      fun _ => (a p : ℝ) := (hP p h).mono (fun _ hz => congrArg Nat.cast hz)
  refine ⟨(integrable_const _).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const, measureReal_univ_eq_one, one_smul]

theorem map_law (P : Procedure Param History Out) (f : Param × Out → Next)
    (hf : Measurable f) (p : Param) (h : History) :
    (P.map f hf).law (p,h) = (P.law (p,h)).map (fun z => (f (p,z.1),z.2)) := by
  classical
  have hm : Measurable (fun z : Outcome Out History => (f (p,z.1),z.2)) :=
    (hf.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
  ext s hs
  rw [map, bind_law_eq, Measure.map_apply combine_measurable hs,
    Measure.compProd_apply (combine_measurable hs), Measure.map_apply hm hs]
  have he (z : Outcome Out History) :
      continuation (pure f hf) p z (Prod.mk z ⁻¹' (combine ⁻¹' s)) =
        (s.indicator (fun _ => (1 : ℝ≥0∞))) (f (p,z.1),z.2) := by
    change Measure.dirac (f (p,z.1),z.2.1,0) (Prod.mk z ⁻¹' (combine ⁻¹' s)) = _
    rw [Measure.dirac_apply' _ ((combine_measurable hs).preimage measurable_prodMk_left)]
    simp only [Set.indicator_apply, Set.mem_preimage, combine, Nat.add_zero, Pi.one_apply, Prod.eta]
  simp_rw [he]
  rw [← lintegral_indicator_one (hm hs)]
  rfl

theorem map_output_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Procedure Param History Out) (f : Param × Out → Next) (hf : Measurable f)
    (p : Param) (h : History) (g : Next → E) (hg : StronglyMeasurable g) :
    (∫ z, g z.1 ∂(P.map f hf).law (p,h)) =
      ∫ z, g (f (p,z.1)) ∂P.law (p,h) := by
  rw [map_law]
  exact integral_map
    ((hf.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd).aemeasurable
    (hg.comp_measurable measurable_fst).aestronglyMeasurable

theorem map_output_integrable_iff {E : Type*} [NormedAddCommGroup E]
    (P : Procedure Param History Out) (f : Param × Out → Next) (hf : Measurable f)
    (p : Param) (h : History) (g : Next → E) (hg : StronglyMeasurable g) :
    Integrable (fun z => g z.1) ((P.map f hf).law (p,h)) ↔
      Integrable (fun z => g (f (p,z.1))) (P.law (p,h)) := by
  rw [map_law]
  exact integrable_map_measure (hg.comp_measurable measurable_fst).aestronglyMeasurable
    ((hf.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd).aemeasurable

theorem CallsEq.map (P : Procedure Param History Out) (a : Param → ℕ) (hP : P.CallsEq a)
    (f : Param × Out → Next) (hf : Measurable f) : (P.map f hf).CallsEq a := by
  intro p h
  rw [map_law]
  have hp : MeasurableSet {z : Outcome Next History | z.2.2 = a p} :=
    (measurable_snd.comp measurable_snd) (measurableSet_singleton _)
  exact (ae_map_iff
    ((hf.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd).aemeasurable hp).mpr (hP p h)

theorem CallsEq.reparam {Input : Type*} [MeasurableSpace Input]
    (P : Procedure Param History Out) (a : Param → ℕ) (hP : P.CallsEq a)
    (f : Input → Param) (hf : Measurable f) : (P.reparam f hf).CallsEq (a ∘ f) :=
  fun p h => hP (f p) h

/-- A measurable input-dependent finite horizon. No infinite seed realization
or stopping-time integrability assumption is needed to define this kernel. -/
def choose (P : ℕ → Procedure Param History Out) (count : Param → ℕ)
    (hc : Measurable count) : Procedure Param History Out where
  law := {
    toFun := fun z => (P (count z.1)).law z
    measurable' := by
      have hm : Measurable (fun z : (Param × History) × ℕ => (P z.2).law z.1) := by
        apply measurable_from_prod_countable
        intro n
        exact (P n).law.measurable
      exact hm.comp (measurable_id.prodMk (hc.comp measurable_fst)) }
  markov := ⟨fun z => show IsProbabilityMeasure ((P (count z.1)).law z) from inferInstance⟩

theorem choose_law (P : ℕ → Procedure Param History Out) (count : Param → ℕ)
    (hc : Measurable count) (p : Param) (h : History) :
    (choose P count hc).law (p,h) = (P (count p)).law (p,h) := rfl

end Bilevel.Stateful.Procedure
