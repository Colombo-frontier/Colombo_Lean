import Bilevel.StatefulProcedureLaws
import Bilevel.ConditionalConfidenceTail

/-! Event bounds for actual history-threaded composition. Every continuation
bound is uniform in the complete entering history; no independence is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful.Procedure
open Bilevel.ConditionalConfidence

variable {Param History Out Next : Type*} [MeasurableSpace Param]
  [MeasurableSpace History] [MeasurableSpace Out] [MeasurableSpace Next]

theorem failure_integral (P : Procedure Param History Out) (p : Param) (h : History)
    (B : Set Out) (hB : MeasurableSet B) :
    (∫ z, flag B z.1 ∂P.law (p,h)) = (P.law (p,h)).real {z | z.1 ∈ B} := by
  simpa only [flag, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := P.law (p,h)) (1 : ℝ) (hB.preimage measurable_fst)

theorem map_failure_union_bound (P : Procedure Param History Out)
    (f : Param × Out → Next) (hf : Measurable f) (p : Param) (h : History)
    (B : Set Next) (hB : MeasurableSet B) (G : Set Out) (hG : MeasurableSet G)
    (prior : Prop) [Decidable prior] {β : ℝ}
    (hsub : ∀ o, f (p,o) ∈ B → prior ∨ o ∈ G)
    (hprob : (P.law (p,h)).real {z | z.1 ∈ G} ≤ β) :
    ((P.map f hf).law (p,h)).real {z | z.1 ∈ B} ≤ (if prior then 1 else 0) + β := by
  have hflag : StronglyMeasurable (flag B) :=
    (measurable_const.indicator hB).stronglyMeasurable
  rw [← failure_integral _ _ _ B hB,
    map_output_integral _ _ _ _ _ (flag B) hflag]
  have hi : Integrable (fun z : Outcome Out History => flag B (f (p,z.1))) (P.law (p,h)) :=
    (integrable_const 1).indicator
      (hB.preimage (hf.comp (measurable_const.prodMk measurable_fst)))
  have hj : Integrable (fun z : Outcome Out History => flag G z.1) (P.law (p,h)) :=
    (integrable_const 1).indicator (hG.preimage measurable_fst)
  have hp (z : Outcome Out History) : flag B (f (p,z.1)) ≤
      (if prior then (1 : ℝ) else 0) + flag G z.1 := by
    classical
    have hs := hsub z.1
    by_cases hb : f (p,z.1) ∈ B <;> by_cases hh : prior <;> by_cases hg : z.1 ∈ G <;>
      simp_all [flag, Set.indicator_apply]
  have hb := integral_mono hi ((integrable_const _).add hj) hp
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) hj, integral_const, measureReal_univ_eq_one,
    one_smul, failure_integral P p h G hG] at hb
  exact hb.trans (add_le_add_left hprob _)

theorem bind_failure_bound (P : Procedure Param History Out)
    (Q : Procedure (Param × Out) History Next) (p : Param) (h : History)
    (F : Set Out) (hF : MeasurableSet F) (B : Set Next) (hB : MeasurableSet B)
    {α β : ℝ} (hP : (P.law (p,h)).real {z | z.1 ∈ F} ≤ α)
    (hQ : ∀ o h', (Q.law ((p,o),h')).real {z | z.1 ∈ B} ≤ flag F o + β) :
    ((P.bind Q).law (p,h)).real {z | z.1 ∈ B} ≤ α + β := by
  have hi : Integrable (fun z : Outcome Out History => flag F z.1) (P.law (p,h)) :=
    (integrable_const 1).indicator (hF.preimage measurable_fst)
  have hb := bind_output_bound P Q p h (flag B) (measurable_const.indicator hB)
    (fun z => (flag_bounds B z).1) (fun o => flag F o + β)
    (hi.add (integrable_const _))
    (fun _ => (integrable_const 1).indicator (hB.preimage measurable_fst))
    (fun z => by rw [failure_integral Q (p,z.1) z.2.1 B hB]; exact hQ z.1 z.2.1)
  have hh := hb.2
  rw [failure_integral _ _ _ B hB, integral_add hi (integrable_const _),
    integral_const, measureReal_univ_eq_one, one_smul, failure_integral P p h F hF] at hh
  exact hh.trans (add_le_add_right hP β)

end Bilevel.Stateful.Procedure
