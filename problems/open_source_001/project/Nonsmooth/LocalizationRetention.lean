import Nonsmooth.LocalizationBestInvariant

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem selectedBlockController_retains_strict_sublevel {C S X : Type}
    (p : C → Policy Unit S X) (T : ℕ) (next : C → S → C) (f : X → ℝ)
    (c0 : C) (K : C → Set X)
    (hstep : ∀ c : C, ∀ z ∈ K c, f z < f ((p c).result f () T) →
      z ∈ K (next c ((p c).run f () T)))
    (B : ℝ) (m : ℕ)
    (hB : ∀ i < m, B ≤ f (localizationStagePoint p T next f c0 i))
    (z : X) (hz : z ∈ K c0) (hzB : f z < B) :
    z ∈ K (selectedBlockController p T next f c0 m) := by
  induction m with
  | zero => exact hz
  | succ m ih =>
    have hprev := ih (fun i hi => hB i (by omega))
    apply hstep _ z hprev
    exact hzB.trans_le (hB m (by omega))

theorem evaluatedLocalizationPolicy_retains_better_points {C S X : Type}
    (p : C → Policy Unit S X) (T : ℕ) (next : C → S → C) (f : X → ℝ)
    (c0 : C) (x0 : X) (K : C → Set X)
    (hstep : ∀ c : C, ∀ z ∈ K c, f z < f ((p c).result f () T) →
      z ∈ K (next c ((p c).run f () T)))
    (m : ℕ) (z : X) (hz : z ∈ K c0)
    (hbetter : f z < f ((evaluatedLocalizationPolicy p T next c0 x0).result f () (m * (T + 1)))) :
    z ∈ K (selectedBlockController p T next f c0 m) := by
  exact selectedBlockController_retains_strict_sublevel p T next f c0 K hstep _ m
    (fun i hi => evaluatedLocalizationPolicy_le_every_stage p T next f c0 x0 m i hi) z hz hbetter

end
end Nonsmooth
