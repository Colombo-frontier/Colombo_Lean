import Nonsmooth.GeneralBodyNormalization
import Nonsmooth.ProtasovTransfer

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every controller body remains a full-dimensional compact convex subset of the original ball. -/
structure LocalizationBody (R : ℝ) where
  carrier : Set E
  convex : Convex ℝ carrier
  compact : IsCompact carrier
  interior_nonempty : (interior carrier).Nonempty
  feasible : carrier ⊆ Metric.closedBall (0 : E) R

variable {E}

def localizationBodyPoint {R : ℝ} (B : LocalizationBody E R) : Feasible E R :=
  ⟨B.interior_nonempty.choose,
    by simpa using B.feasible (interior_subset B.interior_nonempty.choose_spec)⟩

theorem localizationBodyPoint_mem {R : ℝ} (B : LocalizationBody E R) :
    (localizationBodyPoint B).val ∈ B.carrier := interior_subset B.interior_nonempty.choose_spec

variable [FiniteDimensional ℝ E]

def initialLocalizationBody (R : ℝ) (hR : 0 < R) : LocalizationBody E R where
  carrier := Metric.closedBall 0 R
  convex := convex_closedBall 0 R
  compact := isCompact_closedBall 0 R
  interior_nonempty := ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds 0 hR)⟩
  feasible := Subset.rfl

theorem initialLocalizationBody_carrier (R : ℝ) (hR : 0 < R) :
    (initialLocalizationBody (E := E) R hR).carrier = Metric.closedBall 0 R := rfl

end
end Nonsmooth
