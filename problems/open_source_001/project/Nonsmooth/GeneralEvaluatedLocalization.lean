import Nonsmooth.GeneralBodyVolumeAccuracy
import Nonsmooth.LocalizationRetention

open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem evaluatedLocalizationPolicy_body_relative_error {C S : Type}
    {G : Set E} (hG : Convex ℝ G) (hGc : IsCompact G) (hGi : (interior G).Nonempty)
    {R : ℝ} (hGR : G ⊆ Metric.closedBall (0 : E) R)
    (p : C → Policy Unit S (Feasible E R)) (T : ℕ) (next : C → S → C)
    (c0 : C) (x0 : Feasible E R) (K : C → Set E) (hK0 : K c0 = G)
    (c η : ℝ) (hc : 0 < c) (hc1 : c < 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (f : E → ℝ) (hcont : ContinuousOn f G) (hf : ConvexOn ℝ G f)
    (hkeep : ∀ a : C, ∀ z ∈ K a,
      f z < f ((p a).result (fun x => f x.val) () T).val →
        z ∈ K (next a ((p a).run (fun x => f x.val) () T)))
    (hvol : ∀ a : C,
      volume (K (next a ((p a).run (fun x => f x.val) () T))) +
        ENNReal.ofReal c * volume (K a) ≤ volume (K a)) :
    let N := volumeLocalizationRounds (Module.finrank ℝ E) c η
    let y := (evaluatedLocalizationPolicy p T next c0 x0).result (fun x => f x.val) () (N * (T + 1))
    f y.val - bodyMinimum G f ≤ η * (bodyMaximum G f - bodyMinimum G f) := by
  let ff : Feasible E R → ℝ := fun x => f x.val
  let a : ℕ → C := selectedBlockController p T next ff c0
  let N := volumeLocalizationRounds (Module.finrank ℝ E) c η
  let y := (evaluatedLocalizationPolicy p T next c0 x0).result ff () (N * (T + 1))
  have hretain : ∀ z ∈ G, f z < f y.val → z ∈ K (a N) := by
    intro z hz hbetter
    let zz : Feasible E R := ⟨z, by simpa using hGR hz⟩
    exact evaluatedLocalizationPolicy_retains_better_points p T next ff c0 x0
      (fun b => {x : Feasible E R | x.val ∈ K b})
      (fun b x hx hfx => hkeep b x.val hx hfx) N zz
      (by change z ∈ K c0; rw [hK0]; exact hz) hbetter
  have hstep : ∀ n < N, volume (K (a (n + 1))) + ENNReal.ofReal c * volume (K (a n)) ≤
      volume (K (a n)) := by
    intro n _
    exact hvol (a n)
  exact body_relative_error_of_fractional_localization hG hGc hGi hc hc1 hη hη1
    hcont hf y.val (fun n => K (a n)) hK0 hstep hretain

end
end Nonsmooth
