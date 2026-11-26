import Bilevel.OracleCode

/-! Exact distributional semantics of the restricted oracle syntax. The
unconsumed iid suffix stays independent even when the number of calls depends
on past replies. Every assertion is proved by the causal constructors. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.OracleCode
open Stateful
variable {Q O A B C : Space} {Seed : Type*} [MeasurableSpace Seed]
variable (ν : Measure Seed) [IsProbabilityMeasure ν]
  (response : Q → Seed → O) (hr : Measurable (Function.uncurry response))
  (K : Kernel Q O) [IsMarkovKernel K]
  (hK : ∀ q,K q=ν.map (response q))

include hr hK in
omit [IsProbabilityMeasure ν] in
theorem call_law (q : Q) :
    (call K).law (q,())=ν.map (fun s => (response q s,(),1)) := by
  have hq : Measurable (response q) := hr.comp (measurable_const.prodMk measurable_id)
  rw [call,Kernel.map_apply _ (by fun_prop),Kernel.comap_apply,hK]
  rw [Measure.map_map (by fun_prop) hq]
  rfl

private theorem lintegral_bind {A B C : Space}
    (P : Procedure A Unit B) (R : Procedure (prod A B) Unit C) (a : A)
    (f : Outcome C Unit → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,f z ∂(P.bind R).law (a,()))=
      ∫⁻ u,∫⁻ v,f (Procedure.combine (u,v)) ∂R.law ((a,u.1),()) ∂P.law (a,()) := by
  rw [Procedure.bind_law_eq,lintegral_map hf Procedure.combine_measurable]
  rw [Measure.lintegral_compProd (f := fun z : Outcome B Unit × Outcome C Unit =>
    f (Procedure.combine z)) (hf.comp Procedure.combine_measurable)]
  congr 1

include hr hK in
set_option maxHeartbeats 600000 in
theorem eval_lintegral (c : Code Q O A B) (a : A)
    (f : Outcome B Unit × IndependentStream.Stream Seed → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s,f (eval response c (a,s)) ∂IndependentStream.law ν)=
      ∫⁻ z,∫⁻ s,f (z,s) ∂IndependentStream.law ν ∂(denote K c).law (a,()) := by
  induction c with
  | pure g hg =>
      change _=∫⁻ z,∫⁻ s,f (z,s) ∂IndependentStream.law ν ∂Measure.dirac (g a,(),0)
      rw [lintegral_dirac' _ hf.lintegral_prod_right']
      rfl
  | call =>
      have hm : Measurable (fun z : Seed × IndependentStream.Stream Seed =>
          f ((response a z.1,(),1),z.2)) :=
        hf.comp (((hr.comp (measurable_const.prodMk measurable_fst)).prodMk
          (measurable_const.prodMk measurable_const)).prodMk measurable_snd)
      have hs := (IndependentStream.split_preserves ν).lintegral_comp hm
      rw [lintegral_prod _ hm.aemeasurable] at hs
      rw [denote,call_law ν response hr K hK,
        lintegral_map hf.lintegral_prod_right' (by fun_prop)]
      exact hs
  | @bind A B C p q hp hq =>
      let F : Outcome B Unit × IndependentStream.Stream Seed → ℝ≥0∞ := fun z =>
        let v := eval response q ((a,z.1.1),z.2)
        f (Procedure.combine (z.1,v.1),v.2)
      have hargs : Measurable (fun z : Outcome B Unit × IndependentStream.Stream Seed =>
          ((a,z.1.1),z.2) : Outcome B Unit × IndependentStream.Stream Seed →
            (prod A B) × IndependentStream.Stream Seed) :=
        (measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk measurable_snd
      have hv := (eval_measurable response hr q).comp hargs
      have hF : Measurable F := hf.comp
        ((Procedure.combine_measurable.comp (measurable_fst.prodMk (measurable_fst.comp hv))).prodMk
          (measurable_snd.comp hv))
      have he := hp a F hF
      change (∫⁻ s,F (eval response p (a,s)) ∂IndependentStream.law ν)=_ at he
      change (∫⁻ s,F (eval response p (a,s)) ∂IndependentStream.law ν)=_
      rw [he,denote,lintegral_bind _ _ _ _ hf.lintegral_prod_right']
      apply lintegral_congr
      intro u
      exact hq (a,u.1) (fun z => f (Procedure.combine (u,z.1),z.2))
        (hf.comp ((Procedure.combine_measurable.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd))
  | reparam p g hg hp => exact hp (g a) f hf
  | choose p n hn hp => exact hp (n a) a f hf

include hr hK in
theorem eval_law (c : Code Q O A B) (a : A) :
    (IndependentStream.law ν).map (fun s => eval response c (a,s)) =
      ((denote K c).law (a,())).prod (IndependentStream.law ν) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun s => eval response c (a,s)) :=
    (eval_measurable response hr c).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hf hm,lintegral_prod _ hf.aemeasurable]
  exact eval_lintegral ν response hr K hK c a f hf

end Bilevel.OracleCode
