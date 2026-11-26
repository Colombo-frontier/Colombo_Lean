import ExactValue.CenteredBatch

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace ExactValue
noncomputable section

def scPhaseLength (μ β : ℝ) : ℕ := ⌈8 * Real.sqrt (β / μ)⌉₊

theorem scPhaseLength_bounds {μ β : ℝ} (hμ : 0 < μ) (hμβ : μ ≤ β) :
    0 < scPhaseLength μ β ∧ 64 * β ≤ μ * (scPhaseLength μ β : ℝ) ^ 2 ∧
      (scPhaseLength μ β : ℝ) ≤ 9 * Real.sqrt (β / μ) := by
  have hβ := hμ.trans_le hμβ
  have hk : 1 ≤ β / μ := (one_le_div hμ).mpr hμβ
  have hs : 1 ≤ Real.sqrt (β / μ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hk)
  have hlo : 8 * Real.sqrt (β / μ) ≤ (scPhaseLength μ β : ℝ) := Nat.le_ceil _
  have hN : 0 < scPhaseLength μ β := by
    have hn : (0 : ℝ) < scPhaseLength μ β := by linarith
    exact_mod_cast hn
  have hsq := Real.sq_sqrt (show 0 ≤ β / μ by positivity)
  have hp := pow_le_pow_left₀ (show 0 ≤ 8 * Real.sqrt (β / μ) by positivity) hlo 2
  have hpm := mul_le_mul_of_nonneg_left hp hμ.le
  have heq := div_mul_cancel₀ β hμ.ne'
  have hsμ := congrArg (fun v : ℝ => v * μ) hsq
  have hupper : (scPhaseLength μ β : ℝ) < 8 * Real.sqrt (β / μ) + 1 := Nat.ceil_lt_add_one (by positivity)
  exact ⟨hN, by nlinarith, by linarith⟩

def burninAccuracy (μ R : ℝ) (K : ℕ) : ℝ := μ * R / (128 * (K + 1))
def restartAccuracy (Δ R : ℝ) (K : ℕ) : ℝ := Δ / (16 * R * (K + 1))
def phaseStep (d : ℕ) (β δ : ℝ) : ℝ := 2 * δ / (β * Real.sqrt d)

theorem phaseStep_bounds {d : ℕ} (hd : 0 < d) {β R δ : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hδ : 0 < δ) (hδmax : δ ≤ β * R / 4) :
    0 < phaseStep d β δ ∧ phaseStep d β δ ≤ R / 2 ∧
      β * phaseStep d β δ * Real.sqrt d / 2 = δ := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsd : 1 ≤ Real.sqrt (d : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hd1)
  have hpos : 0 < phaseStep d β δ := by unfold phaseStep; positivity
  refine ⟨hpos, ?_, ?_⟩
  · unfold phaseStep
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hsd (show 0 ≤ β * R by positivity)
    nlinarith
  · unfold phaseStep
    field_simp
    ring

theorem burninAccuracy_bounds {μ β R : ℝ} (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (K : ℕ) :
    0 < burninAccuracy μ R K ∧ burninAccuracy μ R K ≤ β * R / 4 := by
  have hβ := hμ.trans_le hμβ
  constructor
  · unfold burninAccuracy
    positivity
  · unfold burninAccuracy
    apply (div_le_iff₀ (by positivity)).mpr
    have hn : (0 : ℝ) ≤ K := by positivity
    have hm := mul_le_mul_of_nonneg_right hμβ hR.le
    have hp : 0 ≤ β * R * (K : ℝ) := by positivity
    nlinarith

theorem restartAccuracy_bounds {μ β R Δ : ℝ} (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R)
    (hΔ : 0 < Δ) (hΔmax : Δ ≤ μ * R ^ 2 / 32) (K : ℕ) :
    0 < restartAccuracy Δ R K ∧ restartAccuracy Δ R K ≤ β * R / 4 := by
  have hβ := hμ.trans_le hμβ
  constructor
  · unfold restartAccuracy
    positivity
  · unfold restartAccuracy
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hμβ (sq_nonneg R)
    have hp : 0 ≤ β * R ^ 2 * (K : ℝ) := by positivity
    nlinarith

theorem burnin_error_terms {μ β R : ℝ} (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (K : ℕ) :
    (K + 1) * R * burninAccuracy μ R K = μ * R ^ 2 / 128 ∧
      K * burninAccuracy μ R K ^ 2 / (2 * β) ≤ μ * R ^ 2 / 2048 := by
  have hβ := hμ.trans_le hμβ
  have he : 0 < μ * R ^ 2 / 16 := by positivity
  have hemax : μ * R ^ 2 / 16 ≤ β * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right hμβ (sq_nonneg R)
    nlinarith [mul_pos hμ (sq_pos_of_pos hR)]
  have heq : burninAccuracy μ R K = upperGradientAccuracy R (μ * R ^ 2 / 16) K := by
    unfold burninAccuracy upperGradientAccuracy
    field_simp
    ring
  obtain ⟨hl, hu⟩ := upper_error_terms hβ hR he hemax K
  rw [heq]
  constructor
  · nlinarith [hl]
  · rw [← mul_div_assoc] at hu
    nlinarith [hu]

theorem restart_error_terms {μ β R Δ : ℝ} (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R)
    (hΔ : 0 < Δ) (hΔmax : Δ ≤ μ * R ^ 2 / 32) (K : ℕ) :
    (K + 1) * R * restartAccuracy Δ R K = Δ / 16 ∧
      K * restartAccuracy Δ R K ^ 2 / (2 * β) ≤ Δ / 256 := by
  have hβ := hμ.trans_le hμβ
  have he : 0 < Δ / 2 := by positivity
  have hemax : Δ / 2 ≤ β * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right hμβ (sq_nonneg R)
    linarith
  have heq : restartAccuracy Δ R K = upperGradientAccuracy R (Δ / 2) K := by
    unfold restartAccuracy upperGradientAccuracy
    field_simp <;> ring_nf <;> simp
  obtain ⟨hl, hu⟩ := upper_error_terms hβ hR he hemax K
  rw [heq]
  constructor
  · nlinarith [hl]
  · rw [← mul_div_assoc] at hu
    nlinarith [hu]

theorem sc_burnin {d : ℕ} (hd : 0 < d) {μ β R : ℝ} {f : Euclid d → ℝ}
    (hf : SCObjective d μ β R f) (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R)
    {xstar : Euclid d} (hx : ‖xstar‖ ≤ R / 2) :
    let K := scPhaseLength μ β
    let h := phaseStep d β (burninAccuracy μ R K)
    f (centeredRun (ballDomain (R / 2) (by positivity)) 0 f (2 * β) h K) - f xstar ≤ μ * R ^ 2 / 32 := by
  dsimp only
  let K := scPhaseLength μ β
  have hβ := hμ.trans_le hμβ
  obtain ⟨hK, hKsq, _⟩ := scPhaseLength_bounds hμ hμβ
  obtain ⟨hδ, hδmax⟩ := burninAccuracy_bounds hμ hμβ hR K
  obtain ⟨hh, _, heq⟩ := phaseStep_bounds hd hβ hR hδ hδmax
  have herr := centeredRun_error hf.toAdmissibleObjective hβ hR hh heq.le
    (c := 0) (by simpa using (show 0 ≤ R / 2 by positivity)) hx hK
  simp only [sub_zero] at herr
  have hKn : (0 : ℝ) < K := by exact_mod_cast hK
  have hn := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hfirst : 4 * β * ‖xstar‖ ^ 2 / (K : ℝ) ^ 2 ≤ μ * R ^ 2 / 64 := by
    apply (div_le_iff₀ (sq_pos_of_pos hKn)).mpr
    have hm := mul_le_mul_of_nonneg_right hKsq (sq_nonneg R)
    have hnβ := mul_le_mul_of_nonneg_left hn hβ.le
    nlinarith
  obtain ⟨hl, hu⟩ := burnin_error_terms hμ hμβ hR K
  change f (centeredRun _ 0 f (2 * β) _ K) - f xstar ≤ _ at herr
  linarith [mul_pos hμ (sq_pos_of_pos hR)]

theorem sc_restart_half {d : ℕ} (hd : 0 < d) {μ β R Δ : ℝ} {f : Euclid d → ℝ}
    (hf : SCObjective d μ β R f) (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R)
    (hΔ : 0 < Δ) (hΔmax : Δ ≤ μ * R ^ 2 / 32) {c xstar : Euclid d}
    (hc : ‖c‖ ≤ R / 2) (hx : ‖xstar‖ ≤ R / 2) (hmin : ∀ y, f xstar ≤ f y)
    (hgap : f c - f xstar ≤ Δ) :
    let K := scPhaseLength μ β
    let h := phaseStep d β (restartAccuracy Δ R K)
    f (centeredRun (ballDomain (R / 2) (by positivity)) c f (2 * β) h K) - f xstar ≤ Δ / 2 := by
  dsimp only
  let K := scPhaseLength μ β
  have hβ := hμ.trans_le hμβ
  obtain ⟨hK, hKsq, _⟩ := scPhaseLength_bounds hμ hμβ
  obtain ⟨hδ, hδmax⟩ := restartAccuracy_bounds hμ hμβ hR hΔ hΔmax K
  obtain ⟨hh, _, heq⟩ := phaseStep_bounds hd hβ hR hδ hδmax
  have herr := centeredRun_error hf.toAdmissibleObjective hβ hR hh heq.le hc hx hK
  have hKn : (0 : ℝ) < K := by exact_mod_cast hK
  have hdist := sc_distance_to_min hf hμ hmin hgap
  rw [norm_sub_rev] at hdist
  have hdμ := (le_div_iff₀ hμ).mp hdist
  have hfirst : 4 * β * ‖xstar - c‖ ^ 2 / (K : ℝ) ^ 2 ≤ Δ / 8 := by
    apply (div_le_iff₀ (sq_pos_of_pos hKn)).mpr
    have hnβ := mul_le_mul_of_nonneg_left hdμ hβ.le
    have hΔK := mul_le_mul_of_nonneg_right hKsq hΔ.le
    nlinarith
  obtain ⟨hl, hu⟩ := restart_error_terms hμ hμβ hR hΔ hΔmax K
  change f (centeredRun _ c f (2 * β) _ K) - f xstar ≤ _ at herr
  linarith

end
end ExactValue
