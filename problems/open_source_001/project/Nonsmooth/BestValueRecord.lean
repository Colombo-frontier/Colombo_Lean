import Nonsmooth.MeasurableSimulation
import Mathlib.Tactic

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

abbrev BestValueRecord (X : Type) := Bool × X × ℝ

def updateBestValue {X : Type} (b : BestValueRecord X) (x : X) (y : ℝ) : BestValueRecord X :=
  if b.1 = true ∧ b.2.2 ≤ y then b else (true, x, y)

theorem updateBestValue_initialized {X : Type} (b : BestValueRecord X) (x : X) (y : ℝ) :
    (updateBestValue b x y).1 = true := by
  unfold updateBestValue
  split_ifs with h
  · exact h.1
  · rfl

theorem updateBestValue_value_exact {X : Type} (f : X → ℝ) (b : BestValueRecord X)
    (hb : b.1 = true → b.2.2 = f b.2.1) (x : X) :
    (updateBestValue b x (f x)).2.2 = f (updateBestValue b x (f x)).2.1 := by
  unfold updateBestValue
  split_ifs with h
  · exact hb h.1
  · rfl

theorem updateBestValue_le_new {X : Type} (b : BestValueRecord X) (x : X) (y : ℝ) :
    (updateBestValue b x y).2.2 ≤ y := by
  unfold updateBestValue
  split_ifs with h
  · exact h.2
  · exact le_rfl

theorem updateBestValue_le_old {X : Type} (b : BestValueRecord X) (hb : b.1 = true)
    (x : X) (y : ℝ) : (updateBestValue b x y).2.2 ≤ b.2.2 := by
  unfold updateBestValue
  split_ifs with h
  · exact le_rfl
  · exact (lt_of_not_ge (fun hn => h ⟨hb, hn⟩)).le

theorem updateBestValue_point_choice {X : Type} (b : BestValueRecord X) (x : X) (y : ℝ) :
    (updateBestValue b x y).2.1 = b.2.1 ∨ (updateBestValue b x y).2.1 = x := by
  unfold updateBestValue
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem updateBestValue_measurable {X : Type} [MeasurableSpace X] :
    Measurable (fun z : BestValueRecord X × X × ℝ => updateBestValue z.1 z.2.1 z.2.2) := by
  have hc : MeasurableSet {z : BestValueRecord X × X × ℝ | z.1.1 = true ∧ z.1.2.2 ≤ z.2.2} :=
    (measurable_fst.fst (MeasurableSet.singleton true)).inter
      (measurableSet_le measurable_fst.snd.snd measurable_snd.snd)
  exact Measurable.ite hc measurable_fst (measurable_const.prodMk measurable_snd)

end
end Nonsmooth
