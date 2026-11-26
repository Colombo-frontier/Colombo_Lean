import NCConcave16991.MixedHaarCanonicalGroup
import Mathlib.MeasureTheory.Constructions.Pi

/-! # A measurable finite-rank public frame state and genuine tail Haar tape -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set MeasureTheory

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

abbrev FrameState (k : ℕ) := Fin (k + 1) × (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k)
abbrev FrameTape (k : ℕ) := ∀ r : Fin (k + 1), Haar.OrthogonalGroup (k - r.val)

def frameTapeLaw (k : ℕ) : Measure (FrameTape k) := Measure.pi (fun r ↦ Haar.haarLaw (k - r.val))

instance frameTapeLaw_probability (k : ℕ) : IsProbabilityMeasure (frameTapeLaw k) := by
  unfold frameTapeLaw
  infer_instance

def frameComplete {k : ℕ} (s : FrameState k) (z : FrameTape k) : Haar.OrthogonalGroup k :=
  s.2.2 * tailOrthogonal s.1 (z s.1) * s.2.1⁻¹

theorem measurable_finite_indexed {I X Y : Type*} [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y]
    (index : X → I) (hi : Measurable index) (f : I → X → Y) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ f (index x) x) := by
  intro A hA
  have he : (fun x ↦ f (index x) x) ⁻¹' A = ⋃ i : I, {x | index x = i} ∩ (f i) ⁻¹' A := by
    ext x
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_setOf_eq]
    constructor
    · intro hx
      exact ⟨index x,rfl,hx⟩
    · rintro ⟨i,hi,hx⟩
      simpa only [hi] using hx
  rw [he]
  exact MeasurableSet.iUnion (fun i ↦ (hi (measurableSet_singleton i)).inter (hf i hA))

theorem frameComplete_measurable {k : ℕ} : Measurable (fun p : FrameState k × FrameTape k ↦ frameComplete p.1 p.2) := by
  have ht : Measurable (fun p : FrameState k × FrameTape k ↦ tailOrthogonal p.1.1 (p.2 p.1.1)) :=
    measurable_finite_indexed (fun p : FrameState k × FrameTape k ↦ p.1.1)
      (measurable_fst.comp measurable_fst)
      (fun r p ↦ tailOrthogonal r (p.2 r))
      (fun r ↦ (tailOrthogonal_measurable r).comp ((measurable_pi_apply r).comp measurable_snd))
  exact ((measurable_snd.comp (measurable_snd.comp measurable_fst)).mul ht).mul
    (measurable_fst.comp (measurable_snd.comp measurable_fst)).inv

theorem orthogonal_action_inv {k : ℕ} (Q : Haar.OrthogonalGroup k) (x : EuclideanSpace ℝ (Fin k)) :
    Haar.orthogonalLinearIsometryEquiv Q⁻¹ x = (Haar.orthogonalLinearIsometryEquiv Q).symm x := by
  apply (Haar.orthogonalLinearIsometryEquiv Q).injective
  rw [← Haar.action_mul,mul_inv_cancel,Haar.action_one,LinearIsometryEquiv.apply_symm_apply]

theorem frameComplete_prefix {k : ℕ} (s : FrameState k) (z : FrameTape k) (x : prefixSpan s.1) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete s z)
      (Haar.orthogonalLinearIsometryEquiv s.2.1 (x : EuclideanSpace ℝ (Fin k))) =
      Haar.orthogonalLinearIsometryEquiv s.2.2 (x : EuclideanSpace ℝ (Fin k)) := by
  rw [frameComplete,Haar.action_mul,orthogonal_action_inv,LinearIsometryEquiv.symm_apply_apply,
    Haar.action_mul,tailOrthogonal_fixes_prefix]

def frameDomain {k : ℕ} (s : FrameState k) : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
  (prefixSpan s.1).map (Haar.orthogonalLinearIsometryEquiv s.2.1).toLinearEquiv.toLinearMap

def frameRange {k : ℕ} (s : FrameState k) : Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
  (prefixSpan s.1).map (Haar.orthogonalLinearIsometryEquiv s.2.2).toLinearEquiv.toLinearMap

def frameKnownIsometry {k : ℕ} (s : FrameState k) : frameDomain s ≃ₗᵢ[ℝ] frameRange s :=
  (LinearIsometryEquiv.submoduleMap (prefixSpan s.1) (Haar.orthogonalLinearIsometryEquiv s.2.1)).symm.trans
    (LinearIsometryEquiv.submoduleMap (prefixSpan s.1) (Haar.orthogonalLinearIsometryEquiv s.2.2))

theorem frameComplete_extends {k : ℕ} (s : FrameState k) (z : FrameTape k) :
    PartialIsometry.ExtendsPartial (frameDomain s) (frameRange s) (frameKnownIsometry s)
      (Haar.orthogonalLinearIsometryEquiv (frameComplete s z)) := by
  intro x
  obtain ⟨u,hu,hux⟩ := x.property
  let y : prefixSpan s.1 := ⟨u,hu⟩
  have he : x = LinearIsometryEquiv.submoduleMap (prefixSpan s.1)
      (Haar.orthogonalLinearIsometryEquiv s.2.1) y := Subtype.ext hux.symm
  rw [he]
  change Haar.orthogonalLinearIsometryEquiv (frameComplete s z)
    (Haar.orthogonalLinearIsometryEquiv s.2.1 y.val) =
      (LinearIsometryEquiv.submoduleMap (prefixSpan s.1) (Haar.orthogonalLinearIsometryEquiv s.2.2)
        ((LinearIsometryEquiv.submoduleMap (prefixSpan s.1) (Haar.orthogonalLinearIsometryEquiv s.2.1)).symm
          ((LinearIsometryEquiv.submoduleMap (prefixSpan s.1) (Haar.orthogonalLinearIsometryEquiv s.2.1)) y))).val
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact frameComplete_prefix s z y

end NCConcave16991.MixedHaar
