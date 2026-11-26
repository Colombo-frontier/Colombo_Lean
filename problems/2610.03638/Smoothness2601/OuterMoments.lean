import Bilevel.StatefulProcedureLaws

/-! Conditional bounds on the actual support of an entering execution law.
This permits deterministic travel invariants without assuming them globally. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Smoothness2601.OuterMoments
open Bilevel.Stateful

theorem nonnegative_bound_ae {State Out : Type*} [MeasurableSpace State] [MeasurableSpace Out]
    {π : Measure State} [IsProbabilityMeasure π] (K : Kernel State Out) [IsMarkovKernel K]
    (f : State × Out → ℝ) (hf : Measurable f) (hn : ∀ z, 0 ≤ f z)
    (b : State → ℝ) (hb : Integrable b π)
    (hi : ∀ᵐ s ∂π, Integrable (fun o => f (s,o)) (K s))
    (hbound : ∀ᵐ s ∂π, (∫ o, f (s,o) ∂K s) ≤ b s) :
    Integrable f (π ⊗ₘ K) ∧ (∫ z, f z ∂π ⊗ₘ K) ≤ ∫ s, b s ∂π := by
  have hm : StronglyMeasurable (fun s => ∫ o, ‖f (s,o)‖ ∂K s) :=
    hf.stronglyMeasurable.norm.integral_kernel_prod_right'
  have he (s : State) : (∫ o, ‖f (s,o)‖ ∂K s) = ∫ o, f (s,o) ∂K s := by
    apply integral_congr_ae
    filter_upwards with o
    exact Real.norm_of_nonneg (hn (s,o))
  have hb' : Integrable (fun s => ∫ o, ‖f (s,o)‖ ∂K s) π := by
    apply hb.mono' hm.aestronglyMeasurable
    filter_upwards [hbound] with s hs
    rw [Real.norm_of_nonneg (integral_nonneg (fun o => norm_nonneg _)),he]
    exact hs
  have hfull : Integrable f (π ⊗ₘ K) :=
    (Measure.integrable_compProd_iff hf.aestronglyMeasurable).mpr ⟨hi,hb'⟩
  refine ⟨hfull,?_⟩
  rw [Measure.integral_compProd hfull]
  have hslice : Integrable (fun s => ∫ o, f (s,o) ∂K s) π := by simpa only [he] using hb'
  exact integral_mono_ae hslice hb hbound

theorem bind_output_bound_ae {Param History Out Next : Type*} [MeasurableSpace Param]
    [MeasurableSpace History] [MeasurableSpace Out] [MeasurableSpace Next]
    (P : Procedure Param History Out) (Q : Procedure (Param × Out) History Next)
    (p : Param) (h : History) (f : Next → ℝ) (hf : Measurable f) (hn : ∀ o, 0 ≤ f o)
    (b : Out → ℝ) (hb : Integrable (fun z => b z.1) (P.law (p,h)))
    (hi : ∀ᵐ z ∂P.law (p,h), Integrable (fun w => f w.1) (Q.law ((p,z.1),z.2.1)))
    (hbound : ∀ᵐ z ∂P.law (p,h), (∫ w, f w.1 ∂Q.law ((p,z.1),z.2.1)) ≤ b z.1) :
    Integrable (fun z => f z.1) ((P.bind Q).law (p,h)) ∧
    (∫ z, f z.1 ∂(P.bind Q).law (p,h)) ≤ ∫ z, b z.1 ∂P.law (p,h) := by
  have hf' : Measurable (fun z : Outcome Out History × Outcome Next History =>
      f (Procedure.combine z).1) := hf.comp (measurable_fst.comp Procedure.combine_measurable)
  have hh := nonnegative_bound_ae (Procedure.continuation Q p) _ hf' (fun z => hn _)
    (fun z => b z.1) hb hi hbound
  rw [Procedure.bind_law_eq]
  have hm : Measurable (fun z : Outcome Next History => f z.1) := hf.comp measurable_fst
  refine ⟨(integrable_map_measure hm.aestronglyMeasurable Procedure.combine_measurable.aemeasurable).mpr hh.1,?_⟩
  rw [integral_map Procedure.combine_measurable.aemeasurable hm.aestronglyMeasurable]
  exact hh.2

end Smoothness2601.OuterMoments
