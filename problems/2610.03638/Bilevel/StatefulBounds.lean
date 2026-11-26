import Bilevel.StatefulProcedure
import Bilevel.StatefulMoments

/-! Compositional expectation bounds for actual stateful procedures. The
terminal history is threaded and original-call counters are added by bind. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful.Procedure
variable {Param History Out Next : Type*} [MeasurableSpace Param]
  [MeasurableSpace History] [MeasurableSpace Out] [MeasurableSpace Next]
  (P : Procedure Param History Out) (Q : Procedure (Param×Out) History Next)

def continuation (p : Param) : Kernel (Outcome Out History) (Outcome Next History) :=
  Q.law.comap (fun z => ((p,z.1),z.2.1))
    ((measurable_const.prodMk measurable_fst).prodMk (measurable_fst.comp measurable_snd))

instance continuation_markov (p : Param) : IsMarkovKernel (continuation Q p) := by
  unfold continuation
  infer_instance

theorem bind_law_eq (p : Param) (h : History) :
    (P.bind Q).law (p,h)=((P.law (p,h)) ⊗ₘ continuation Q p).map combine := by
  rw [bind,Kernel.map_apply _ combine_measurable,Kernel.compProd_apply_eq_compProd_sectR]
  rfl

/-- Integrate any nonnegative terminal potential through the actual bind.
The intermediate bound may depend on the complete preceding outcome. -/
theorem bind_nonnegative_bound (p : Param) (h : History)
    (f : Outcome Next History → ℝ) (hf : Measurable f) (hn : ∀ z,0≤f z)
    (b : Outcome Out History → ℝ) (hb : Integrable b (P.law (p,h)))
    (hi : ∀ z, Integrable (fun w => f (combine (z,w))) (Q.law ((p,z.1),z.2.1)))
    (hbound : ∀ z, (∫ w,f (combine (z,w)) ∂Q.law ((p,z.1),z.2.1))≤b z) :
    Integrable f ((P.bind Q).law (p,h)) ∧
      (∫ z,f z ∂(P.bind Q).law (p,h))≤∫ z,b z ∂P.law (p,h) := by
  have hcomp := StatefulMoments.nonnegative_integral_bound (π := P.law (p,h)) (continuation Q p)
    (f ∘ combine) (hf.comp combine_measurable) (fun z => hn _) b hb hi hbound
  rw [bind_law_eq]
  have hp : MeasurePreserving combine ((P.law (p,h)) ⊗ₘ continuation Q p)
      (((P.law (p,h)) ⊗ₘ continuation Q p).map combine) := ⟨combine_measurable,rfl⟩
  refine ⟨(hp.integrable_comp hf.aestronglyMeasurable).mp hcomp.1,?_⟩
  rw [integral_map combine_measurable.aemeasurable hf.aestronglyMeasurable]
  exact hcomp.2

/-- The same composition rule for a terminal output potential, which ignores
the history and counter but still samples from their joint law. -/
theorem bind_output_bound (p : Param) (h : History)
    (f : Next → ℝ) (hf : Measurable f) (hn : ∀ z,0≤f z)
    (b : Out → ℝ) (hb : Integrable (fun z => b z.1) (P.law (p,h)))
    (hi : ∀ z : Outcome Out History, Integrable (fun w => f w.1) (Q.law ((p,z.1),z.2.1)))
    (hbound : ∀ z : Outcome Out History, (∫ w,f w.1 ∂Q.law ((p,z.1),z.2.1))≤b z.1) :
    Integrable (fun z => f z.1) ((P.bind Q).law (p,h)) ∧
      (∫ z,f z.1 ∂(P.bind Q).law (p,h))≤∫ z,b z.1 ∂P.law (p,h) :=
  bind_nonnegative_bound P Q p h _ (hf.comp measurable_fst) (fun z => hn z.1) _ hb hi hbound

theorem bind_increment_bound (p : Param) (h : History)
    (V : Next → ℝ) (hV : Measurable V) (hpos : ∀ o,0≤V o)
    (W : Out → ℝ) (C c : ℝ)
    (hP : Integrable (fun z => W z.1) (P.law (p,h)) ∧
      (∫ z,W z.1 ∂P.law (p,h))≤C)
    (hQ : ∀ o h',Integrable (fun z => V z.1) (Q.law ((p,o),h')) ∧
      (∫ z,V z.1 ∂Q.law ((p,o),h'))≤W o+c) :
    Integrable (fun z => V z.1) ((P.bind Q).law (p,h)) ∧
      (∫ z,V z.1 ∂(P.bind Q).law (p,h))≤C+c := by
  have hh := bind_output_bound P Q p h V hV hpos (fun o => W o+c)
    (hP.1.add (integrable_const c)) (fun z => (hQ z.1 z.2.1).1) (fun z => (hQ z.1 z.2.1).2)
  refine ⟨hh.1,?_⟩
  have he := integral_add hP.1 (integrable_const c)
  simp only [Pi.add_apply,integral_const,measureReal_univ_eq_one,one_smul] at he
  rw [he] at hh
  exact hh.2.trans (add_le_add_right hP.2 c)

end Bilevel.Stateful.Procedure
