import NCBall.LatentCoordinates
import NCBall.GaussianHandleLaw

/-! # Separating the fixed hidden instance from reusable sample randomness -/

noncomputable section
open MeasureTheory
namespace NCBall

def handleCoordinateEquiv (n H : ℕ) :
    HandleLatent (Transverse n) H ≃ᵐ (Fin (H + 1) → Transverse n) := by
  let e : HandleLatent (Transverse n) H ≃L[ℝ] (Fin (H + 1) → Transverse n) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (H + 1) => Transverse n)
  exact {
    toEquiv := e.toEquiv
    measurable_toFun := e.continuous.measurable
    measurable_invFun := e.symm.continuous.measurable }

def splitHandleEquiv (n H : ℕ) :
    HandleLatent (Transverse n) H ≃ᵐ (Transverse n × (Fin H → Transverse n)) :=
  (handleCoordinateEquiv n H).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (H + 1) => Transverse n) 0)

theorem splitHandleEquiv_law (n H : ℕ) :
    MeasurePreserving (splitHandleEquiv n H)
      (euclideanGaussianLaw (HandleLatent (Transverse n) H))
      ((euclideanGaussianLaw (Transverse n)).prod
        (Measure.pi (fun _ : Fin H => euclideanGaussianLaw (Transverse n)))) := by
  let e := handleCoordinateEquiv n H
  have he : MeasurePreserving e (euclideanGaussianLaw (HandleLatent (Transverse n) H))
      (Measure.pi (fun _ : Fin (H + 1) => euclideanGaussianLaw (Transverse n))) :=
    ⟨e.measurable, gaussian_handle_blocks_independent (F := Transverse n) H⟩
  exact (measurePreserving_piFinSuccAbove
    (fun _ : Fin (H + 1) => euclideanGaussianLaw (Transverse n)) 0).comp he

abbrev HiddenTable (n M : ℕ) := Fin M → Transverse n
abbrev SampleTable (n H M : ℕ) := Fin M → Fin H → Transverse n

def hiddenTableLaw (n M : ℕ) : Measure (HiddenTable n M) :=
  Measure.pi (fun _ : Fin M => euclideanGaussianLaw (Transverse n))

def sampleTableLaw (n H M : ℕ) : Measure (SampleTable n H M) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin H => euclideanGaussianLaw (Transverse n)))

instance hiddenTableLaw_probability (n M : ℕ) : IsProbabilityMeasure (hiddenTableLaw n M) := by
  unfold hiddenTableLaw
  letI : ∀ _ : Fin M, IsProbabilityMeasure (euclideanGaussianLaw (Transverse n)) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

instance sampleTableLaw_probability (n H M : ℕ) : IsProbabilityMeasure (sampleTableLaw n H M) := by
  unfold sampleTableLaw
  letI : ∀ _ : Fin H, IsProbabilityMeasure (euclideanGaussianLaw (Transverse n)) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin H => euclideanGaussianLaw (Transverse n))) :=
    Measure.pi.instIsProbabilityMeasure _
  letI : ∀ _ : Fin M, IsProbabilityMeasure (Measure.pi (fun _ : Fin H => euclideanGaussianLaw (Transverse n))) :=
    fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

def splitRoomEquiv (n H M : ℕ) : RoomLatents n H M ≃ᵐ (HiddenTable n M × SampleTable n H M) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin M => splitHandleEquiv n H)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (Transverse n) (Fin H → Transverse n) (Fin M))

theorem splitRoomEquiv_law (n H M : ℕ) :
    MeasurePreserving (splitRoomEquiv n H M) (roomLatentLaw n H M)
      ((hiddenTableLaw n M).prod (sampleTableLaw n H M)) := by
  have hp := measurePreserving_pi _ _ (fun _ : Fin M => splitHandleEquiv_law n H)
  have hs := measurePreserving_arrowProdEquivProdArrow (Transverse n) (Fin H → Transverse n) (Fin M)
    (fun _ => euclideanGaussianLaw (Transverse n))
    (fun _ => Measure.pi (fun _ : Fin H => euclideanGaussianLaw (Transverse n)))
  exact hs.comp hp

theorem combineRoomEquiv_law (n H M : ℕ) :
    MeasurePreserving (splitRoomEquiv n H M).symm
      ((hiddenTableLaw n M).prod (sampleTableLaw n H M)) (roomLatentLaw n H M) :=
  (splitRoomEquiv_law n H M).symm

theorem combined_hidden_block (n H M : ℕ) (u : HiddenTable n M) (z : SampleTable n H M)
    (j : Fin M) : ((splitRoomEquiv n H M).symm (u, z) j) 0 = u j := by
  change Fin.insertNth (α := fun _ : Fin (H + 1) => Transverse n) 0 (u j) (z j) 0 = u j
  simp

theorem combined_noise_block (n H M : ℕ) (u : HiddenTable n M) (z : SampleTable n H M)
    (j : Fin M) (h : Fin H) : ((splitRoomEquiv n H M).symm (u, z) j) h.succ = z j h := by
  change Fin.insertNth (α := fun _ : Fin (H + 1) => Transverse n) 0 (u j) (z j) h.succ = z j h
  simp

end NCBall
