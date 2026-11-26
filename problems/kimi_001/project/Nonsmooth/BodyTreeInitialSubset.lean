import Nonsmooth.CountableBodyTree

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem localizationBodyTree_subset_initial {R : ℝ}
    (step : LocalizationBody E R → CircularHistory → LocalizationBody E R)
    (hstep : ∀ B h, (step B h).carrier ⊆ B.carrier) (B0 : LocalizationBody E R)
    (hs : List CircularHistory) : (localizationBodyTree step B0 hs).carrier ⊆ B0.carrier := by
  induction hs with
  | nil => exact Subset.rfl
  | cons h hs ih => exact (hstep (localizationBodyTree step B0 hs) h).trans ih

end
end Nonsmooth
