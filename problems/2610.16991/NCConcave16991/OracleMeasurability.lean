import NCConcave16991.Problem
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! # Measurability of the complete adaptive oracle execution -/

open Set MeasureTheory

namespace NCConcave16991

private theorem measurableEmbedding_sigmaMk {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (i : ι) : MeasurableEmbedding (Sigma.mk i : β i → Sigma β) := by
  classical
  have hinj : Function.Injective (Sigma.mk i : β i → Sigma β) := by
    intro x y hxy
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hxy
  refine ⟨hinj, ?_, ?_⟩
  · apply Measurable.of_le_map
    exact iInf_le (fun j => (inferInstance : MeasurableSpace (β j)).map (Sigma.mk j)) i
  · intro s hs
    change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (β j)).map (Sigma.mk j)]
      (Sigma.mk i '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro j
    change MeasurableSet (Sigma.mk j ⁻¹' (Sigma.mk i '' s))
    by_cases hij : j = i
    · subst j
      simpa only [hinj.preimage_image] using hs
    · have he : Sigma.mk j ⁻¹' (Sigma.mk i '' s) = ∅ := by
        ext x
        constructor
        · rintro ⟨y, hy, hxy⟩
          exact (hij (congrArg Sigma.fst hxy).symm).elim
        · intro hx
          exact hx.elim
      rw [he]
      exact MeasurableSet.empty

/-- A map on a product with a countable measurable disjoint union is measurable
when its restriction to every fiber is measurable. -/
private theorem measurable_from_prod_sigma {Ω ι γ : Type*} {β : ι → Type*}
    [MeasurableSpace Ω] [Countable ι] [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ]
    {f : Ω × Sigma β → γ}
    (hf : ∀ i, Measurable (fun a : Ω × β i => f (a.1, ⟨i, a.2⟩))) : Measurable f := by
  intro s hs
  have he : f ⁻¹' s = ⋃ i,
      (fun a : Ω × β i => (a.1, Sigma.mk i a.2)) ''
        ((fun a : Ω × β i => f (a.1, Sigma.mk i a.2)) ⁻¹' s) := by
    ext a
    constructor
    · intro ha
      exact mem_iUnion.mpr ⟨a.2.1, ⟨(a.1, a.2.2), ha, rfl⟩⟩
    · intro ha
      rcases mem_iUnion.mp ha with ⟨i, a', ha', rfl⟩
      exact ha'
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  exact ((MeasurableEmbedding.id (α := Ω)).prodMap (measurableEmbedding_sigmaMk i)).measurableSet_image'
    (hf i hs)

namespace OraclePolicy

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)

theorem appendHistory_measurable : Measurable (fun a :
    History K (n := n) (dx := dx) × Observation K (n := n) (dx := dx) =>
      appendHistory K a.1 a.2) := by
  have hc : Measurable (fun a : Observation K (n := n) (dx := dx) × History K =>
      appendHistory K a.2 a.1) := by
    apply measurable_from_prod_sigma
    intro t
    have hv : Measurable (fun a : Observation K (n := n) (dx := dx) ×
        (Fin t → Observation K (n := n) (dx := dx)) =>
          (Fin.snoc a.2 a.1 : Fin (t + 1) → Observation K (n := n) (dx := dx))) := by
      apply measurable_pi_iff.mpr
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last] using measurable_fst
      · simp only [Fin.snoc_castSucc]
        intro s hs
        exact measurable_snd ((measurable_pi_apply i) hs)
    exact (measurableEmbedding_sigmaMk (t + 1)).measurable.comp hv
  exact hc.comp measurable_swap

theorem runAux_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    {oracle : OracleQuery n dx K → OracleAnswer dx dy} (ho : Measurable oracle) (t : ℕ) :
    Measurable (fun a : Ω × History K => runAux K P oracle a.1 t a.2) := by
  induction t with
  | zero => exact P.final_measurable.prodMk measurable_snd
  | succ t ih =>
    let S := Ω × History K (n := n) (dx := dx)
    have hstop : Measurable (fun a : S × PrimalSpace dx => (a.2, a.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hquery : Measurable (fun a : S × OracleQuery n dx K =>
        runAux K P oracle a.1.1 t (appendHistory K a.1.2 (a.2, oracle a.2))) := by
      have hs : Measurable (fun a : S × OracleQuery n dx K =>
          (a.1.1, appendHistory K a.1.2 (a.2, oracle a.2))) := by
        apply Measurable.prodMk
        · exact measurable_fst.comp measurable_fst
        · have hm : Measurable (fun a : S × OracleQuery n dx K =>
              (a.1.2, (a.2, oracle a.2))) :=
            (measurable_snd.comp measurable_fst).prodMk
              (measurable_snd.prodMk (ho.comp measurable_snd))
          exact (appendHistory_measurable K).comp hm
      exact ih.comp hs
    have hbranch := (hstop.sumElim hquery).comp
      (MeasurableEquiv.prodSumDistrib S (PrimalSpace dx) (OracleQuery n dx K)).measurable
    have hc := hbranch.comp (measurable_id.prodMk P.next_measurable)
    convert hc using 1
    funext a
    cases he : P.next a.1 a.2 <;>
      simp [runAux, Function.comp_apply, Function.uncurry, he,
        MeasurableEquiv.prodSumDistrib, MeasurableEquiv.sumProdDistrib,
        MeasurableEquiv.prodComm, MeasurableEquiv.sumCongr, Equiv.sumProdDistrib, Equiv.sumCongr]

/-- The output and full transcript are measurable functions of the private seed. -/
theorem run_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    {oracle : OracleQuery n dx K → OracleAnswer dx dy} (ho : Measurable oracle) (budget : ℕ) :
    Measurable (fun seed => run K P oracle seed budget) :=
  (runAux_measurable K P ho budget).comp (measurable_id.prodMk measurable_const)

theorem output_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    {oracle : OracleQuery n dx K → OracleAnswer dx dy} (ho : Measurable oracle) (budget : ℕ) :
    Measurable (fun seed => (run K P oracle seed budget).1) :=
  measurable_fst.comp (run_measurable K P ho budget)

end OraclePolicy

end NCConcave16991
