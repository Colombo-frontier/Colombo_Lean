import MatchingBounds1005.Model
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Measurability of actual exact-oracle policies and their success events. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.Model

theorem oracle_measurable_of_continuous {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
    {d : ℕ} {F : Ω → Space d → ℝ} (hF : Continuous F.uncurry) :
    Measurable (fun z : Ω × Space d => oracle (F z.1) z.2) := by
  have hg : Measurable (fun z : Ω × Space d => gradient (F z.1) z.2) :=
    (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp
      (measurable_fderiv_with_param ℝ hF)
  exact hF.measurable.prodMk hg

theorem transcript_measurable {Ω Seed : Type} [MeasurableSpace Ω]
    [MeasurableSpace Seed] {d : ℕ} (F : Ω → Space d → ℝ)
    (hF : Measurable (fun z : Ω × Space d => oracle (F z.1) z.2))
    (A : Algorithm d Seed) (T : ℕ) :
    Measurable (fun z : Ω × Seed => transcript A (F z.1) z.2 T) := by
  induction T with
  | zero => exact measurable_const
  | succ t ih =>
    have hq : Measurable (fun z : Ω × Seed =>
        A.query t z.2 (transcript A (F z.1) z.2 t)) :=
      (A.query_measurable t).comp (measurable_snd.prodMk ih)
    have hr : Measurable (fun z : Ω × Seed =>
        oracle (F z.1) (A.query t z.2 (transcript A (F z.1) z.2 t))) :=
      hF.comp (measurable_fst.prodMk hq)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [transcript, Fin.snoc_last] using hr
    · simpa only [transcript, Fin.snoc_castSucc] using (measurable_pi_apply j).comp ih

theorem success_measurable {Ω Seed : Type} [MeasurableSpace Ω]
    [MeasurableSpace Seed] {d : ℕ} (F : Ω → Space d → ℝ)
    (hF : Measurable (fun z : Ω × Space d => oracle (F z.1) z.2))
    (A : Algorithm d Seed) (ε : ℝ) (T : ℕ) :
    MeasurableSet {z : Ω × Seed | z.2 ∈ Success A (F z.1) ε T} := by
  have ht := transcript_measurable F hF A T
  have ho : Measurable (fun z : Ω × Seed =>
      A.output T z.2 (transcript A (F z.1) z.2 T)) :=
    (A.output_measurable T).comp (measurable_snd.prodMk ht)
  have hr := hF.comp (measurable_fst.prodMk ho)
  exact measurableSet_le hr.snd.norm measurable_const

end MatchingBounds1005.Model
