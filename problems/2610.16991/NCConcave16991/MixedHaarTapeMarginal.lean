import NCConcave16991.MixedHaarAdaptiveLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Basic

/-! # The genuine independent marginal of every fresh adaptive-tape slot -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

universe u
variable {W Z : Type u} [MeasurableSpace W] [MeasurableSpace Z]

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def tapeFresh : (N : ℕ) → RevealTape W Z N → Fin N → W
  | 0, _ => Fin.elim0
  | N + 1, p => Fin.cons p.1 (tapeFresh N p.2)

theorem tapeFresh_measurable (N : ℕ) : Measurable (tapeFresh (W := W) (Z := Z) N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [tapeFresh,Fin.cons_zero] using
          (measurable_fst : Measurable (fun p : W × RevealTape W Z N ↦ p.1))
      · simpa only [tapeFresh,Fin.cons_succ,Function.comp_def] using
          (measurable_pi_apply j).comp (ih.comp measurable_snd)

theorem tapeFresh_preserving (τ : Measure W) (ν : Measure Z)
    [IsProbabilityMeasure τ] [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (tapeFresh (W := W) (Z := Z) N) (revealTapeLaw τ ν N)
      (Measure.pi (fun _ : Fin N ↦ τ)) := by
  induction N with
  | zero =>
      refine ⟨tapeFresh_measurable 0,?_⟩
      apply Measure.ext
      intro A hA
      rw [Measure.map_apply (tapeFresh_measurable 0) hA]
      have hall (f : Fin 0 → W) : f = Fin.elim0 := funext (fun i ↦ i.elim0)
      by_cases ha : (Fin.elim0 : Fin 0 → W) ∈ A
      · have he : A = univ := Set.eq_univ_of_forall (fun f ↦ by simpa only [hall f] using ha)
        rw [he]
        change ν univ = _
        simp
      · have he : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun f hf ↦ ha (by simpa only [hall f] using hf))
        rw [he]
        simp
  | succ N ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) ↦ W) 0
      have he := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) ↦ τ) (0 : Fin (N + 1))
      have hinv : MeasurePreserving e.symm
          (τ.prod (Measure.pi (fun _ : Fin N ↦ τ))) (Measure.pi (fun _ : Fin (N + 1) ↦ τ)) := by
        refine ⟨e.symm.measurable,?_⟩
        have hh := congrArg (fun μ ↦ μ.map e.symm) he.map_eq
        rw [Measure.map_map e.symm.measurable e.measurable] at hh
        simpa only [e.symm_comp_self,Measure.map_id] using hh.symm
      have hp := hinv.comp ((MeasurePreserving.id τ).prod ih)
      convert hp using 1
      funext p i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [tapeFresh,e,MeasurableEquiv.piFinSuccAbove]
      · simp [tapeFresh,e,MeasurableEquiv.piFinSuccAbove]
      all_goals rfl

end NCConcave16991.MixedHaar
