import MatchingBounds1005.CUPGPhase
import MatchingBounds1005.CUPGCalibration

/-! The calibrated finite sequence of actual accelerated phases. The only
objective assumptions here are the manuscript's function class conditions. -/
noncomputable section
open scoped ContDiff

namespace MatchingBounds1005.CUPG

def calibratedPhase {d : ℕ} (f : Model.Space d → ℝ) (ε : ℝ) (start : Model.Space d) : Model.Space d :=
  let r := rootParameter ε
  phasePoint f (r / 2) (r ^ 2) (r / 16) 4 ε start (phaseCap r ε)

theorem calibratedPhase_progress {d p : ℕ} {f : Model.Space d → ℝ}
    (hp : 3 ≤ p) (hf : Model.InFunctionClass p f) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (start : Model.Space d) (hstart : f start ≤ f 0) :
    f (calibratedPhase f ε start) ≤ f start ∧
      (ε < ‖gradient f (calibratedPhase f ε start)‖ →
        f (calibratedPhase f ε start) ≤ f start - (rootParameter ε) ^ 4 / 256) := by
  let r := rootParameter ε
  have hr : 0 < r := rootParameter_pos hε
  have hrone : r ≤ 1 := rootParameter_le_one hε.le hεone
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hrone
  have hsm1 : SmoothUpper f 1 := smoothUpper_of_directional hf.1
    (model_directional hf (by omega : 1 ≤ 1) (by omega : 1 ≤ p))
  have hsm : SmoothUpper f (4 - 2 * r ^ 2) := smoothUpper_mono hsm1 (by linarith)
  have hdir : DirectionalLip f 3 1 := model_directional hf (by norm_num) hp
  have hsum : (4 - 2 * r ^ 2) + 2 * r ^ 2 = 4 := by ring
  have hscale : ((4 - 2 * r ^ 2) + 2 * r ^ 2) * (r / 2) ^ 2 = r ^ 2 := by ring
  have hstep : (1 : ℝ) * (16 * (r / 16)) ^ 2 ≤ r ^ 2 := by nlinarith
  have hD : r ^ 4 / 256 ≤ r ^ 2 * (r / 16) ^ 2 := by nlinarith
  have hD' : r ^ 4 / 256 ≤ ε ^ 2 / (5 * r ^ 2) := calibrated_decrease hε
  have hgap (z : Model.Space d) : f start - f z ≤ 1 := by linarith [hf.2.1 z]
  have hcap : 2 * ((4 - 2 * r ^ 2) + 2 * r ^ 2) * 1 *
      Real.exp (-(r / 2) * phaseCap r ε) ≤ (ε / 10) ^ 2 := by
    simpa only [hsum, mul_one, show (2 : ℝ) * 4 = 8 by norm_num] using phaseCap_monitor hr hε
  have hh := phasePoint_progress hf.1 (by positivity : 0 < r ^ 2)
    (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 1) (by positivity : 0 < r / 16)
    hε (by norm_num : (0 : ℝ) ≤ 1) hscale hstep hsm hdir hD hD'
    (by positivity : 0 ≤ r ^ 4 / 256) start (phaseCap r ε) hgap hcap
  rw [hsum] at hh
  exact hh

def epochPoint {d : ℕ} (f : Model.Space d → ℝ) (ε : ℝ) : ℕ → Model.Space d
  | 0 => 0
  | k + 1 => calibratedPhase f ε (epochPoint f ε k)

theorem epochPoint_value {d p : ℕ} {f : Model.Space d → ℝ}
    (hp : 3 ≤ p) (hf : Model.InFunctionClass p f) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (k : ℕ) : f (epochPoint f ε k) ≤ f 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ((calibratedPhase_progress hp hf hε hεone _ ih).1).trans ih

theorem stationary_epoch_exists {d p : ℕ} {f : Model.Space d → ℝ}
    (hp : 3 ≤ p) (hf : Model.InFunctionClass p f) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ k < epochCap (rootParameter ε), ‖gradient f (epochPoint f ε (k + 1))‖ ≤ ε := by
  by_contra hn
  push_neg at hn
  let K := epochCap (rootParameter ε)
  let D := (rootParameter ε) ^ 4 / 256
  have hdec : ∀ k ≤ K, f (epochPoint f ε k) ≤ f 0 - (k : ℝ) * D := by
    intro k hk
    induction k with
    | zero => simp [epochPoint]
    | succ k ih =>
      have hkK : k < K := by omega
      have hi := ih (by omega)
      have hh := (calibratedPhase_progress hp hf hε hεone _
        (epochPoint_value hp hf hε hεone k)).2 (hn k hkK)
      change f (epochPoint f ε (k + 1)) ≤ f (epochPoint f ε k) - D at hh
      push_cast
      linarith
  have hh := hdec K le_rfl
  have hgap := hf.2.1 (epochPoint f ε K)
  have hK : 1 < (K : ℝ) * D := epochCap_decrease (rootParameter_pos hε)
  linarith

def epochOutput {d : ℕ} (f : Model.Space d → ℝ) (ε : ℝ) : Model.Space d :=
  bestPoint (fun x => ‖gradient f x‖) (epochPoint f ε 1)
    ((List.range (epochCap (rootParameter ε))).map (fun k => epochPoint f ε (k + 1)))

theorem epochOutput_stationary {d p : ℕ} {f : Model.Space d → ℝ}
    (hp : 3 ≤ p) (hf : Model.InFunctionClass p f) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ‖gradient f (epochOutput f ε)‖ ≤ ε := by
  obtain ⟨k, hk, hstationary⟩ := stationary_epoch_exists hp hf hε hεone
  have hm := bestPoint_le_mem (fun x => ‖gradient f x‖) (epochPoint f ε 1)
    ((List.range (epochCap (rootParameter ε))).map (fun k => epochPoint f ε (k + 1)))
    (epochPoint f ε (k + 1)) (List.mem_map_of_mem (List.mem_range.mpr hk))
  exact hm.trans hstationary

end MatchingBounds1005.CUPG
