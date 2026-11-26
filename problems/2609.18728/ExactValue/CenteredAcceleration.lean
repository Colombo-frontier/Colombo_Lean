import ExactValue.SCModel
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace ExactValue
noncomputable section

/-- Translate the feasible domain so that an arbitrary starting point becomes zero. -/
def centeredDomain {d : ℕ} (K : ClosedConvexDomain d) (c : Euclid d) : ClosedConvexDomain d where
  carrier := {x | x + c ∈ K.carrier}
  nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact ⟨x - c, by simpa using hx⟩
  closed := K.closed.preimage (continuous_id.add continuous_const)
  convex := by
    intro x hx y hy a b ha hb hab
    have h := K.convex hx hy ha hb hab
    have heq : a • (x + c) + b • (y + c) = (a • x + b • y) + c := by
      simp only [smul_add]
      calc
        _ = (a • x + b • y) + (a + b) • c := by rw [add_smul]; abel
        _ = _ := by rw [hab, one_smul]
    simpa only [heq] using h

theorem project_eq_of_optimality {d : ℕ} (K : ClosedConvexDomain d) (x z : Euclid d)
    (hz : z ∈ K.carrier) (ho : ∀ y ∈ K.carrier, ⟪x - z, y - z⟫_ℝ ≤ 0) : K.project x = z := by
  have hp := K.project_optimality x z hz
  have hq := ho (K.project x) (K.project_mem x)
  have he : ⟪x - K.project x, z - K.project x⟫_ℝ + ⟪x - z, K.project x - z⟫_ℝ =
      ‖K.project x - z‖ ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, norm_sub_sq_real]
    simp only [real_inner_comm, real_inner_self_eq_norm_sq]
    ring
  have hn : ‖K.project x - z‖ = 0 := by nlinarith [norm_nonneg (K.project x - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem centeredDomain_project {d : ℕ} (K : ClosedConvexDomain d) (c x : Euclid d) :
    (centeredDomain K c).project x = K.project (x + c) - c := by
  apply project_eq_of_optimality
  · change K.project (x + c) - c + c ∈ K.carrier
    simpa using K.project_mem (x + c)
  · intro y hy
    have h := K.project_optimality (x + c) (y + c) hy
    convert h using 1 <;> congr 1 <;> abel

theorem shifted_derivative {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d}
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (c x : Euclid d) :
    HasFDerivAt (fun x => f (x + c)) (innerSL ℝ (G (x + c))) x := by
  convert (hder (x + c)).comp x ((hasFDerivAt_id x).add_const c) using 1

theorem shifted_convex {d : ℕ} {f : Euclid d → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (c : Euclid d) : ConvexOn ℝ Set.univ (fun x => f (x + c)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hf.2 (Set.mem_univ (x + c)) (Set.mem_univ (y + c)) ha hb hab
  have heq : a • (x + c) + b • (y + c) = (a • x + b • y) + c := by
    simp only [smul_add]
    calc
      _ = (a • x + b • y) + (a + b) • c := by rw [add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  simpa only [heq] using h

theorem centered_model {d : ℕ} {f : Euclid d → ℝ} {β R h δ : ℝ}
    (hf : AdmissibleObjective d β R f) (hβ : 0 < β) (hR : 0 < R) (hh : 0 < h)
    (hδ : β * h * Real.sqrt d / 2 ≤ δ) (c : Euclid d) :
    InexactModel (centeredDomain (ballDomain (R / 2) (by positivity)) c)
      (fun x => f (x + c)) (finiteGradient (fun x => f (x + c)) h)
      (2 * β) (R * δ) (δ ^ 2 / (2 * β)) := by
  obtain ⟨G, hder, hLip⟩ := hf.gradient_lipschitz
  have hd := shifted_derivative hder c
  have hl (x y : Euclid d) : ‖G (x + c) - G (y + c)‖ ≤ β * ‖x - y‖ := by
    simpa only [add_sub_add_right_eq_sub] using hLip (x + c) (y + c)
  have herr (y : Euclid d) :
      ‖finiteGradient (fun x => f (x + c)) h y - G (y + c)‖ ≤ δ :=
    (finiteGradient_error hβ.le hh hd hl y).trans hδ
  constructor
  · intro x hx y hy
    have hx' : ‖x + c‖ ≤ R / 2 := by simpa [centeredDomain, ballDomain] using hx
    have hy' : ‖y + c‖ ≤ R / 2 := by simpa [centeredDomain, ballDomain] using hy
    have hdiam : ‖x - y‖ ≤ R := by
      simpa only [add_sub_add_right_eq_sub] using ball_diameter hx' hy'
    exact inexact_oracle_lower (f := fun z => f (z + c)) (x := x) (y := y)
      (convex_supporting (f := fun z => f (z + c)) (G := fun z => G (z + c))
        (shifted_convex hf.convex c) hd x y)
      (herr y) hdiam
  · intro x _ y _
    have hr := smooth_remainder hd hl y (x - y)
    rw [add_sub_cancel] at hr
    have hup : f (x + c) ≤ f (y + c) + ⟪G (y + c), x - y⟫_ℝ + β / 2 * ‖x - y‖ ^ 2 := by
      have ht := (le_abs_self _).trans hr
      linarith
    exact inexact_oracle_upper (f := fun z => f (z + c)) (x := x) (y := y) hβ hup (herr y)

def centeredRun {d : ℕ} (K : ClosedConvexDomain d) (c : Euclid d)
    (f : Euclid d → ℝ) (L h : ℝ) (N : ℕ) : Euclid d :=
  (accelRun (centeredDomain K c) (fun x => f (x + c))
    (finiteGradient (fun x => f (x + c)) h) L N).x + c

theorem centeredRun_mem {d : ℕ} (K : ClosedConvexDomain d) {c : Euclid d}
    (hc : c ∈ K.carrier) (f : Euclid d → ℝ) {L : ℝ} (hL : 0 < L) (h : ℝ) (N : ℕ) :
    centeredRun K c f L h N ∈ K.carrier := by
  exact accelRun_mem (centeredDomain K c) (by simpa [centeredDomain] using hc)
    (fun x => f (x + c)) (finiteGradient (fun x => f (x + c)) h) hL N

/-- The paper's accelerated subroutine for an arbitrary initial point in the inner ball. -/
theorem centeredRun_error {d : ℕ} {f : Euclid d → ℝ} {β R h δ : ℝ}
    (hf : AdmissibleObjective d β R f) (hβ : 0 < β) (hR : 0 < R) (hh : 0 < h)
    (hδ : β * h * Real.sqrt d / 2 ≤ δ) {c xstar : Euclid d}
    (hc : ‖c‖ ≤ R / 2) (hx : ‖xstar‖ ≤ R / 2) {N : ℕ} (hN : 0 < N) :
    f (centeredRun (ballDomain (R / 2) (by positivity)) c f (2 * β) h N) - f xstar ≤
      4 * β * ‖xstar - c‖ ^ 2 / (N : ℝ) ^ 2 +
        (N + 1) * R * δ + N * δ ^ 2 / (2 * β) := by
  let K := centeredDomain (ballDomain (d := d) (R / 2) (by positivity)) c
  have hz : (0 : Euclid d) ∈ K.carrier := by simpa [K, centeredDomain, ballDomain] using hc
  have hxm : xstar - c ∈ K.carrier := by simpa [K, centeredDomain, ballDomain] using hx
  have hδ0 : 0 ≤ δ := (show 0 ≤ β * h * Real.sqrt d / 2 by positivity).trans hδ
  have herr := accelRun_error K hz (fun x => f (x + c)) (finiteGradient (fun x => f (x + c)) h)
    (show 0 < 2 * β by positivity) (show 0 ≤ R * δ by positivity)
    (show 0 ≤ δ ^ 2 / (2 * β) by positivity) (centered_model hf hβ hR hh hδ c) (xstar - c) hxm hN
  simp only [sub_add_cancel] at herr
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 < accelerationWeight (2 * β) N := accelerationWeight_pos (by positivity) hN
  have hweight := accelerationWeight_lower (show 0 < 2 * β by positivity) N
  have hwl : (N : ℝ) ^ 2 ≤ 8 * β * accelerationWeight (2 * β) N := by
    have h := (div_le_iff₀ (show 0 < 4 * (2 * β) by positivity)).mp hweight
    nlinarith
  have hfirst : ‖xstar - c‖ ^ 2 / (2 * accelerationWeight (2 * β) N) ≤
      4 * β * ‖xstar - c‖ ^ 2 / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hNp)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hwl (sq_nonneg ‖xstar - c‖)]
  change f (centeredRun _ c f (2 * β) h N) - f xstar ≤ _ at herr
  rw [← mul_div_assoc, ← mul_assoc] at herr
  linarith

theorem gradient_zero_at_min {d : ℕ} {f : Euclid d → ℝ} {G : Euclid d → Euclid d}
    {xstar : Euclid d} (hder : HasFDerivAt f (innerSL ℝ (G xstar)) xstar)
    (hmin : ∀ y, f xstar ≤ f y) : G xstar = 0 := by
  have hl : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  have h := hl.hasFDerivAt_eq_zero hder
  have hv := congrArg (fun l : Euclid d →L[ℝ] ℝ => l (G xstar)) h
  simp only [innerSL_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hv
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (G xstar)])

theorem sc_distance_to_min {d : ℕ} {f : Euclid d → ℝ} {μ β R Δ : ℝ}
    (hf : SCObjective d μ β R f) (hμ : 0 < μ) {x xstar : Euclid d}
    (hmin : ∀ y, f xstar ≤ f y) (hgap : f x - f xstar ≤ Δ) : ‖x - xstar‖ ^ 2 ≤ 2 * Δ / μ := by
  obtain ⟨G, hder, _⟩ := hf.gradient_lipschitz
  have hz := gradient_zero_at_min (hder xstar) hmin
  have hs := strong_supporting hf.strong hder x xstar
  rw [hz, inner_zero_left, add_zero] at hs
  apply (le_div_iff₀ hμ).mpr
  linarith

end
end ExactValue
