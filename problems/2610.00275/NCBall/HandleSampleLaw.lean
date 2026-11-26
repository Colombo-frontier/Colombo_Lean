import NCBall.FixedSampleLaw
import NCBall.IndependentTranspose

/-! # The retained handles are independent draws from the verified sample law -/

noncomputable section
open MeasureTheory
namespace NCBall

theorem fixed_sample_table_law (n K M : ℕ) :
    MeasurePreserving (fun z : SampleTable n K M => fun h => fixedSampleCoordinates h z)
      (sampleTableLaw n K M) (Measure.pi (fun _ : Fin K => gaussianRooms n M)) := by
  have ht := independent_transpose_law (ι := Fin M) (κ := Fin K)
    (euclideanGaussianLaw (Transverse n))
  have hc : MeasurePreserving (fun u : HiddenTable n M => fun j => normalizedTransverseCoordinates n (u j))
      (hiddenTableLaw n M) (gaussianRooms n M) :=
    measurePreserving_pi _ _ (fun _ : Fin M => normalizedTransverseCoordinates_law n)
  have hp := measurePreserving_pi _ _ (fun _ : Fin K => hc)
  exact hp.comp ht

end NCBall
