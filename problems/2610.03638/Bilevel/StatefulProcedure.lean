import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Measurable stateful procedures as direct Markov kernels. No realization by
an iid common seed is postulated. Every outcome carries the actual terminal
history and the integer number of original oracle calls. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Bilevel.Stateful

abbrev Outcome (Out History : Type*) := Out × History × ℕ

structure Procedure (Param History Out : Type*) [MeasurableSpace Param]
    [MeasurableSpace History] [MeasurableSpace Out] where
  law : Kernel (Param × History) (Outcome Out History)
  markov : IsMarkovKernel law

attribute [instance] Procedure.markov

namespace Procedure
variable {Param History Out Next : Type*} [MeasurableSpace Param]
  [MeasurableSpace History] [MeasurableSpace Out] [MeasurableSpace Next]

def pure (f : Param → Out) (hf : Measurable f) : Procedure Param History Out where
  law := Kernel.deterministic (fun z : Param × History => (f z.1, z.2, 0))
    ((hf.comp measurable_fst).prodMk (measurable_snd.prodMk measurable_const))
  markov := inferInstance

def nextInput (z : (Param × History) × Outcome Out History) : (Param × Out) × History :=
  ((z.1.1, z.2.1), z.2.2.1)

theorem nextInput_measurable : Measurable (nextInput (Param := Param) (History := History) (Out := Out)) :=
  ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_fst.comp (measurable_snd.comp measurable_snd))

def combine (z : Outcome Out History × Outcome Next History) : Outcome Next History :=
  (z.2.1, z.2.2.1, z.1.2.2 + z.2.2.2)

theorem combine_measurable : Measurable (combine (Out := Out) (Next := Next) (History := History)) := by
  unfold combine
  fun_prop

def bind (P : Procedure Param History Out) (Q : Procedure (Param × Out) History Next) :
    Procedure Param History Next where
  law := (P.law ⊗ₖ Q.law.comap nextInput nextInput_measurable).map combine
  markov := Kernel.IsMarkovKernel.map _ combine_measurable

def map (P : Procedure Param History Out) (f : Param × Out → Next) (hf : Measurable f) :
    Procedure Param History Next := P.bind (pure f hf)

def reparam {Input : Type*} [MeasurableSpace Input]
    (P : Procedure Param History Out) (f : Input → Param) (hf : Measurable f) : Procedure Input History Out where
  law := P.law.comap (fun z => (f z.1, z.2)) ((hf.comp measurable_fst).prodMk measurable_snd)
  markov := inferInstance

def CallsEq (P : Procedure Param History Out) (count : Param → ℕ) : Prop :=
  ∀ p h, ∀ᵐ z ∂P.law (p, h), z.2.2 = count p

def CostBound (P : Procedure Param History Out) (bound : Param → ℝ) : Prop :=
  ∀ p h, Integrable (fun z => (z.2.2 : ℝ)) (P.law (p, h)) ∧
    (∫ z, (z.2.2 : ℝ) ∂P.law (p, h)) ≤ bound p

def MSEBound [NormedAddCommGroup Out] (P : Procedure Param History Out)
    (truth : Param → Out) (radius : Param → ℝ) : Prop :=
  ∀ p h, Integrable (fun z => ‖z.1 - truth p‖ ^ 2) (P.law (p, h)) ∧
    (∫ z, ‖z.1 - truth p‖ ^ 2 ∂P.law (p, h)) ≤ (radius p) ^ 2

def Mean [NormedAddCommGroup Out] [NormedSpace ℝ Out] (P : Procedure Param History Out)
    (truth : Param → Out) : Prop :=
  ∀ p h, Integrable (fun z => z.1 - truth p) (P.law (p, h)) ∧
    (∫ z, z.1 - truth p ∂P.law (p, h)) = 0

end Procedure
end Bilevel.Stateful
