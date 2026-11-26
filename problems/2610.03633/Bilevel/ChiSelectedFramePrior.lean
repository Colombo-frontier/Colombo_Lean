import Bilevel.ChiHierarchyHaar
import Bilevel.ChiCanonicalHierarchy
import Bilevel.IndependentFrameContext

/-! Exact selected-frame factorization of the finite source prior. The
other-frame column context is reconstructed from the complementary
orientations alone; no selected full frame is stored in that context. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex

def succEnumeration (counts : ℕ → ℕ) (J : ℕ) :
    FrameIndex counts J ≃ Fin (Fintype.card (FrameIndex counts J)-1+1) :=
  Fintype.equivFinOfCardEq (Nat.sub_add_cancel (frame_count_positive counts J)).symm

def reindex {counts : ℕ → ℕ} {J D k : ℕ} (e : FrameIndex counts J ≃ Fin (k+1))
    (a : Orientations counts J D) : Fin (k+1) → OrthogonalHaar.Group D := fun j => a (e.symm j)

theorem reindex_preserving {counts : ℕ → ℕ} {J D k : ℕ} (e : FrameIndex counts J ≃ Fin (k+1)) :
    MeasurePreserving (reindex (D:=D) e) (law counts J D)
      (Measure.pi (fun _ : Fin (k+1) => OrthogonalHaar.law D)) := by
  convert measurePreserving_piCongrLeft (fun _ => OrthogonalHaar.law D) e using 1
  funext a i
  simp [reindex,MeasurableEquiv.coe_piCongrLeft]

def otherColumns {counts : ℕ → ℕ} {J D k : ℕ} (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ j : FrameIndex counts J, chainSize j+1 ≤ D) (i : FrameIndex counts J)
    (other : Fin k → OrthogonalHaar.Group D) : FiniteColumns counts J (EuclideanGaussian.Space D) :=
  fun j => HaarFrame.frame D (chainSize j+1) (hD j)
    (Fin.insertNth (α:=fun _ : Fin (k+1) => OrthogonalHaar.Group D) (e i) 1 other (e j))

theorem otherColumns_measurable {counts : ℕ → ℕ} {J D k : ℕ}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ j : FrameIndex counts J, chainSize j+1 ≤ D) (i : FrameIndex counts J) :
    Measurable (otherColumns e hD i) := by
  have hf : Measurable (fun other : Fin k → OrthogonalHaar.Group D =>
      Fin.insertNth (α:=fun _ : Fin (k+1) => OrthogonalHaar.Group D) (e i) 1 other) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => OrthogonalHaar.Group D) (e i)).symm.measurable.comp
      (measurable_const.prodMk measurable_id)
  apply measurable_pi_lambda
  intro j
  exact (HaarFrame.frame_measurable D _ (hD j)).comp ((measurable_pi_apply (e j)).comp hf)

theorem otherColumns_agree {counts : ℕ → ℕ} {J D k : ℕ}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ j : FrameIndex counts J, chainSize j+1 ≤ D) (i : FrameIndex counts J)
    (a : Orientations counts J D) (j : FrameIndex counts J) (hj : j ≠ i) :
    otherColumns e hD i (fun l => a (e.symm ((e i).succAbove l))) j = columns hD a j := by
  obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq (show e j ≠ e i from fun h => hj (e.injective h))
  unfold otherColumns columns
  rw [← hl,Fin.insertNth_apply_succAbove,hl,Equiv.symm_apply_apply]

def sourceExpose {C : Type*} {counts : ℕ → ℕ} {J D k : ℕ}
    (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ j : FrameIndex counts J, chainSize j+1 ≤ D) (i : FrameIndex counts J)
    (p : C × Orientations counts J D) :
    IndependentFrame.Context C D k × (Fin (chainSize i+1) → EuclideanGaussian.Space D) :=
  ((p.1,fun l => p.2 (e.symm ((e i).succAbove l))),columns hD p.2 i)

theorem sourceExpose_preserving {C : Type*} [MeasurableSpace C] (ρ : Measure C) [SFinite ρ]
    {counts : ℕ → ℕ} {J D k : ℕ} (e : FrameIndex counts J ≃ Fin (k+1))
    (hD : ∀ j : FrameIndex counts J, chainSize j+1 ≤ D) (i : FrameIndex counts J) :
    MeasurePreserving (sourceExpose (C:=C) e hD i) (ρ.prod (law counts J D))
      ((ρ.prod (Measure.pi (fun _ : Fin k => OrthogonalHaar.law D))).prod
        (HaarFrame.frameLaw D (chainSize i+1) (hD i))) := by
  have h := (IndependentFrame.expose_preserving ρ (hD i) (e i)).comp
    ((MeasurePreserving.id ρ).prod (reindex_preserving (D:=D) e))
  convert h using 1
  funext p
  simp [sourceExpose,IndependentFrame.expose,reindex,columns]

end Bilevel.ChiHierarchyHaar
