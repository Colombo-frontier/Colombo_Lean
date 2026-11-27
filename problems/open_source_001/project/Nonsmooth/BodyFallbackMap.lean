import Nonsmooth.GeneralBodyVolumeAccuracy

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type}

def bodyFallbackMap (G : Set E) (x0 : G) (z : E) : G := by
  classical
  exact if hz : z ∈ G then ⟨z, hz⟩ else x0

theorem bodyFallbackMap_of_mem {G : Set E} (x0 : G) {z : E} (hz : z ∈ G) :
    (bodyFallbackMap G x0 z).val = z := by simp only [bodyFallbackMap, dif_pos hz]

theorem bodyFallbackMap_measurable [MeasurableSpace E] {G : Set E} (hG : MeasurableSet G)
    (x0 : G) : Measurable (bodyFallbackMap G x0) := by
  classical
  apply Measurable.subtype_mk
  change Measurable (fun z => (bodyFallbackMap G x0 z).val)
  have heq : (fun z => (bodyFallbackMap G x0 z).val) = fun z => if z ∈ G then z else x0.val := by
    funext z
    by_cases hz : z ∈ G <;> simp [bodyFallbackMap, hz]
  rw [heq]
  exact measurable_id.ite hG measurable_const

theorem body_extrema_fallback (G : Set E) (x0 : G) (f : E → ℝ) :
    bodyMinimum G (fun z => f (bodyFallbackMap G x0 z).val) = bodyMinimum G f ∧
      bodyMaximum G (fun z => f (bodyFallbackMap G x0 z).val) = bodyMaximum G f := by
  have heq : (fun z => f (bodyFallbackMap G x0 z).val) '' G = f '' G := by
    apply image_congr
    intro z hz
    rw [bodyFallbackMap_of_mem x0 hz]
  exact ⟨congrArg sInf heq, congrArg sSup heq⟩

end
end Nonsmooth
