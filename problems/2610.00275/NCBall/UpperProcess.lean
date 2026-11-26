import NCBall.UpperRegret
import NCBall.RandomSegment
import NCBall.CountablePool
import NCBall.Localization

/-! # The actual first-order process driven by independent sample pools

The two pools hold independent uniform segment parameters and oracle seeds.
The state at time t only uses coordinates strictly before t.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped unitInterval
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def upperState (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) : ℕ → E × E
  | 0 => (x₀, 0)
  | t + 1 =>
      let w := upperState D hD α G x₀ r ξ t
      (w.1 + w.2, ballProjection D hD (w.2 - α • G (w.1 + (r t : ℝ) • w.2) (ξ t)))

def upperLocation (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (t : ℕ) : E :=
  let w := upperState D hD α G x₀ r ξ t
  w.1 + (r t : ℝ) • w.2

def upperEstimate (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (t : ℕ) : E :=
  G (upperLocation D hD α G x₀ r ξ t) (ξ t)

theorem upper_increment_eq_clipped (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (t : ℕ) :
    (upperState D hD α G x₀ r ξ t).2 =
      clippedIncrement D hD α (upperEstimate D hD α G x₀ r ξ) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ballProjection D hD ((upperState D hD α G x₀ r ξ t).2 -
      α • upperEstimate D hD α G x₀ r ξ t) = _
    rw [ih]
    rfl

theorem upperState_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ξ] (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E)
    (hG : Measurable (fun xξ : E × Ξ => G xξ.1 xξ.2)) (x₀ : E) (t : ℕ) :
    Measurable (fun w : (ℕ → I) × (ℕ → Ξ) => upperState D hD α G x₀ w.1 w.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hr : Measurable (fun w : (ℕ → I) × (ℕ → Ξ) => (w.1 t : ℝ)) :=
      measurable_subtype_coe.comp ((measurable_pi_apply t).comp measurable_fst)
    have hξ : Measurable (fun w : (ℕ → I) × (ℕ → Ξ) => w.2 t) :=
      (measurable_pi_apply t).comp measurable_snd
    exact (ih.fst.add ih.snd).prodMk ((ballProjection_measurable D hD).comp
      (ih.snd.sub ((hG.comp ((ih.fst.add (hr.smul ih.snd)).prodMk hξ)).const_smul α)))

theorem upperLocation_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ξ] (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E)
    (hG : Measurable (fun xξ : E × Ξ => G xξ.1 xξ.2)) (x₀ : E) (t : ℕ) :
    Measurable (fun w : (ℕ → I) × (ℕ → Ξ) => upperLocation D hD α G x₀ w.1 w.2 t) := by
  have hs := upperState_measurable D hD α G hG x₀ t
  exact hs.fst.add ((measurable_subtype_coe.comp ((measurable_pi_apply t).comp measurable_fst)).smul hs.snd)

theorem upperEstimate_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ξ] (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E)
    (hG : Measurable (fun xξ : E × Ξ => G xξ.1 xξ.2)) (x₀ : E) (t : ℕ) :
    Measurable (fun w : (ℕ → I) × (ℕ → Ξ) => upperEstimate D hD α G x₀ w.1 w.2 t) :=
  hG.comp ((upperLocation_measurable D hD α G hG x₀ t).prodMk
    ((measurable_pi_apply t).comp measurable_snd))

theorem upperState_noise_refresh (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (j : ℕ) (z : Ξ) :
    ∀ t ≤ j, upperState D hD α G x₀ r (Function.update ξ j z) t = upperState D hD α G x₀ r ξ t := by
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro ht
    simp only [upperState, ih (by omega), Function.update_of_ne (show t ≠ j by omega)]

theorem upperState_segment_refresh (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (j : ℕ) (z : I) :
    ∀ t ≤ j, upperState D hD α G x₀ (Function.update r j z) ξ t = upperState D hD α G x₀ r ξ t := by
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro ht
    simp only [upperState, ih (by omega), Function.update_of_ne (show t ≠ j by omega)]

theorem upperLocation_noise_refresh (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (j : ℕ) (z : Ξ) {t : ℕ} (ht : t ≤ j) :
    upperLocation D hD α G x₀ r (Function.update ξ j z) t = upperLocation D hD α G x₀ r ξ t := by
  unfold upperLocation
  rw [upperState_noise_refresh D hD α G x₀ r ξ j z t ht]

theorem upperEstimate_noise_refresh (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (j : ℕ) (z : Ξ) :
    upperEstimate D hD α G x₀ r (Function.update ξ j z) j =
      G (upperLocation D hD α G x₀ r ξ j) z := by
  rw [upperEstimate, upperLocation_noise_refresh D hD α G x₀ r ξ j z le_rfl, Function.update_self]

theorem upperEstimate_past_noise_refresh (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (j : ℕ) (z : Ξ) {t : ℕ} (ht : t < j) :
    upperEstimate D hD α G x₀ r (Function.update ξ j z) t = upperEstimate D hD α G x₀ r ξ t := by
  rw [upperEstimate, upperLocation_noise_refresh D hD α G x₀ r ξ j z ht.le,
    Function.update_of_ne (ne_of_lt ht)]
  rfl

theorem upper_state_location_bound (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (t : ℕ) :
    ‖(upperState D hD α G x₀ r ξ t).1 - x₀‖ ≤ (t : ℝ) * D := by
  have hb := clipped_path_bound (D := D) (fun j => (upperState D hD α G x₀ r ξ j).1) t (fun j _ => ?_) t le_rfl
  · exact hb
  · simp only [upperState, add_sub_cancel_left, upper_increment_eq_clipped]
    exact clippedIncrement_norm_le D hD α _ j

theorem upper_sample_location_bound (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (t : ℕ) :
    ‖upperLocation D hD α G x₀ r ξ t - x₀‖ ≤ ((t : ℝ) + 1) * D := by
  have hv : ‖(r t : ℝ) • (upperState D hD α G x₀ r ξ t).2‖ ≤ D := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (r t).property.1, upper_increment_eq_clipped]
    exact (mul_le_mul_of_nonneg_left (clippedIncrement_norm_le D hD α _ t) (r t).property.1).trans
      (by nlinarith [(r t).property.2])
  have hb := perturbation_bound (upper_state_location_bound D hD α G x₀ r ξ t) hv
  convert hb using 1
  ring

end NCBall
