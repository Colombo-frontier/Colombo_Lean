import Nonsmooth.LocalizationVolumeAccuracy

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type}

def bodyMinimum (G : Set E) (f : E → ℝ) : ℝ := sInf (f '' G)
def bodyMaximum (G : Set E) (f : E → ℝ) : ℝ := sSup (f '' G)

theorem bodyMinimum_eq {G : Set E} {f : E → ℝ} {x : E} (hx : x ∈ G)
    (hmin : ∀ y ∈ G, f x ≤ f y) : bodyMinimum G f = f x := by
  apply IsLeast.csInf_eq
  exact ⟨mem_image_of_mem f hx, by rintro _ ⟨y, hy, rfl⟩; exact hmin y hy⟩

theorem bodyMaximum_eq {G : Set E} {f : E → ℝ} {x : E} (hx : x ∈ G)
    (hmax : ∀ y ∈ G, f y ≤ f x) : bodyMaximum G f = f x := by
  apply IsGreatest.csSup_eq
  exact ⟨mem_image_of_mem f hx, by rintro _ ⟨y, hy, rfl⟩; exact hmax y hy⟩

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem body_relative_error_of_fractional_localization {G : Set E}
    (hconv : Convex ℝ G) (hcompact : IsCompact G) (hinterior : (interior G).Nonempty)
    {c η : ℝ} (hc : 0 < c) (hc1 : c < 1) (hη : 0 < η) (hη1 : η ≤ 1)
    {f : E → ℝ} (hcont : ContinuousOn f G) (hf : ConvexOn ℝ G f)
    (y : E) (K : ℕ → Set E) (hK0 : K 0 = G)
    (hstep : ∀ n < volumeLocalizationRounds (Module.finrank ℝ E) c η,
      volume (K (n + 1)) + ENNReal.ofReal c * volume (K n) ≤ volume (K n))
    (hkeep : ∀ z ∈ G, f z < f y → z ∈ K (volumeLocalizationRounds (Module.finrank ℝ E) c η)) :
    f y - bodyMinimum G f ≤ η * (bodyMaximum G f - bodyMinimum G f) := by
  have hGpos : 0 < volume G :=
    (isOpen_interior.measure_pos volume hinterior).trans_le (measure_mono interior_subset)
  have hfinite : volume G < ⊤ := hcompact.measure_lt_top
  have hsmall := volume_fraction_below_relative_threshold (fun n => volume (K n))
    (Module.finrank ℝ E) hc hc1 hη
    (by simpa only [hK0] using hGpos) (by simpa only [hK0] using hfinite) hstep
  rw [hK0] at hsmall
  have hne : G.Nonempty := hinterior.mono interior_subset
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hne hcont
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  rw [bodyMinimum_eq (f := f) hxmin (fun _ hz => hmin hz),
    bodyMaximum_eq (f := f) hxmax (fun _ hz => hmax hz)]
  exact convex_relative_error_of_small_retained_volume volume ⟨hconv, hf.2⟩ hxmin
    (fun _ hz => hmax hz) hη.le hη1 hkeep hsmall

end
end Nonsmooth
