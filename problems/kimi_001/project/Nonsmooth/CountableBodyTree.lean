import Nonsmooth.LocalizationBody
import Nonsmooth.ActualNestedCircularPolicy

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

structure LocalizationHistory where
  entries : List CircularHistory
  deriving Encodable

instance localizationHistoryMeasurableSpace : MeasurableSpace LocalizationHistory := ⊤
instance localizationHistoryDiscreteMeasurableSpace : DiscreteMeasurableSpace LocalizationHistory :=
  inferInstanceAs (@DiscreteMeasurableSpace LocalizationHistory ⊤)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def localizationBodyTree {R : ℝ}
    (step : LocalizationBody E R → CircularHistory → LocalizationBody E R)
    (B0 : LocalizationBody E R) : List CircularHistory → LocalizationBody E R
  | [] => B0
  | h :: hs => step (localizationBodyTree step B0 hs) h

theorem localizationBodyTree_nil {R : ℝ}
    (step : LocalizationBody E R → CircularHistory → LocalizationBody E R)
    (B0 : LocalizationBody E R) : localizationBodyTree step B0 [] = B0 := rfl

theorem localizationBodyTree_cons {R : ℝ}
    (step : LocalizationBody E R → CircularHistory → LocalizationBody E R)
    (B0 : LocalizationBody E R) (h : CircularHistory) (hs : List CircularHistory) :
    localizationBodyTree step B0 (h :: hs) = step (localizationBodyTree step B0 hs) h := rfl

def localizationHistoryNext (h : LocalizationHistory) (st : CircularHistory × CyclicPeakState) :
    LocalizationHistory := ⟨st.1 :: h.entries⟩

theorem localizationHistoryNext_measurable (h : LocalizationHistory) :
    Measurable (localizationHistoryNext h) := by
  exact (measurable_of_countable (fun c : CircularHistory => (⟨c :: h.entries⟩ : LocalizationHistory))).comp measurable_fst

end
end Nonsmooth
