import Bilevel.GenieBudget

/-! Borel closure rules for actual finite adaptive protocol families. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.GenieProtocol
open EuclideanGaussian ProjectionPosterior

structure MeasurableFamily {d T m r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → Protocol d T m r) : Prop where
  joint_bad : ∀ b : ℝ, MeasurableSet {p : Ω × Frame d T | bad b (P p.1) p.2}
  regular : ∀ (b : ℝ) (ω : Ω), Regular b (P ω)

namespace MeasurableFamily
variable {d T m r : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem halt : MeasurableFamily (fun _ : Ω => (Protocol.halt : Protocol d T m r)) where
  joint_bad _ := MeasurableSet.empty
  regular _ _ := trivial

theorem comap {P : Ω → Protocol d T m r} (hP : MeasurableFamily P)
    (f : Ω' → Ω) (hf : Measurable f) : MeasurableFamily (fun ω => P (f ω)) where
  joint_bad b := (hf.prodMap measurable_id) (hP.joint_bad b)
  regular b ω := hP.regular b (f ω)

theorem query (w : Ω → Space d) (hw : Measurable w)
    (next : Ω × (Fin T → ℝ) → Protocol d T m r) (hnext : MeasurableFamily next) :
    MeasurableFamily (fun ω => Protocol.query (w ω) (fun y => next (ω,y))) := by
  have ho : Measurable (fun p : Ω × Frame d T => queryObservation d T (w p.1) p.2) := by
    apply measurable_pi_lambda
    intro i
    exact (continuous_fst.inner continuous_snd).measurable.comp
      ((hw.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  constructor
  · intro b
    have hhead : MeasurableSet {p : Ω × Frame d T | ∃ i : Fin T, b ≤ ⟪w p.1,p.2 i⟫^2} := by
      simp only [Set.setOf_exists]
      exact MeasurableSet.iUnion (fun i : Fin T => measurableSet_le measurable_const
        (((measurable_pi_apply i).comp ho).pow_const 2))
    have hm : Measurable (fun p : Ω × Frame d T => ((p.1,queryObservation d T (w p.1) p.2),p.2)) :=
      (measurable_fst.prodMk ho).prodMk measurable_snd
    exact hhead.union (hm (hnext.joint_bad b))
  · intro b ω
    have hm : Measurable (fun p : (Fin T → ℝ) × Frame d T => ((ω,p.1),p.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    exact ⟨hm (hnext.joint_bad b),fun y => hnext.regular b (ω,y)⟩

theorem reveal (j : Ω → Fin T) (hj : Measurable j)
    (next : Ω × Space d → Protocol d T m r) (hnext : MeasurableFamily next) :
    MeasurableFamily (fun ω => Protocol.reveal (j ω) (fun y => next (ω,y))) := by
  have heval : Measurable (fun p : Frame d T × Fin T => p.1 p.2) :=
    measurable_from_prod_countable (fun i => measurable_pi_apply i)
  have ho : Measurable (fun p : Ω × Frame d T => p.2 (j p.1)) :=
    heval.comp (measurable_snd.prodMk (hj.comp measurable_fst))
  constructor
  · intro b
    have hm : Measurable (fun p : Ω × Frame d T => ((p.1,p.2 (j p.1)),p.2)) :=
      (measurable_fst.prodMk ho).prodMk measurable_snd
    exact hm (hnext.joint_bad b)
  · intro b ω
    have hm : Measurable (fun p : Space d × Frame d T => ((ω,p.1),p.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    exact ⟨hm (hnext.joint_bad b),fun y => hnext.regular b (ω,y)⟩

theorem addQuery {P : Ω → Protocol d T m r} (hP : MeasurableFamily P) :
    MeasurableFamily (fun ω => GenieProtocol.addQuery (P ω)) := by
  constructor
  · intro b
    simpa only [bad_addQuery] using hP.joint_bad b
  · intro b ω
    exact (regular_addQuery (P ω) b).2 (hP.regular b ω)

open Classical in
theorem piecewise {P Q : Ω → Protocol d T m r} (hP : MeasurableFamily P)
    (hQ : MeasurableFamily Q) (s : Set Ω) (hs : MeasurableSet s) :
    MeasurableFamily (s.piecewise P Q) := by
  classical
  constructor
  · intro b
    have he : {p : Ω × Frame d T | bad b ((s.piecewise P Q) p.1) p.2} =
        ({p : Ω × Frame d T | p.1 ∈ s} ∩ {p | bad b (P p.1) p.2}) ∪
        ({p : Ω × Frame d T | p.1 ∉ s} ∩ {p | bad b (Q p.1) p.2}) := by
      ext p
      by_cases h : p.1 ∈ s <;> simp [Set.piecewise,h]
    rw [he]
    exact ((measurable_fst hs).inter (hP.joint_bad b)).union
      ((measurable_fst hs).compl.inter (hQ.joint_bad b))
  · intro b ω
    by_cases h : ω ∈ s
    · simpa [Set.piecewise,h] using hP.regular b ω
    · simpa [Set.piecewise,h] using hQ.regular b ω

end MeasurableFamily
end Bilevel.GenieProtocol
