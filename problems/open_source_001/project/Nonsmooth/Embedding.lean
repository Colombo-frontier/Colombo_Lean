import Nonsmooth.Scales

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

def embedRadius (g μ R : ℝ) : ℝ := min R (g / (2 * μ))
def embedAmplitude (g μ R : ℝ) : ℝ := g * embedRadius g μ R / 2

theorem embedding_scale_positive {g μ R : ℝ} (hg : 0 < g) (hμ : 0 < μ) (hR : 0 < R) :
    0 < embedRadius g μ R ∧ 0 < embedAmplitude g μ R := by
  have hs : 0 < embedRadius g μ R := lt_min hR (div_pos hg (by positivity))
  exact ⟨hs, by unfold embedAmplitude; positivity⟩

theorem embedding_scale_comparison {g μ R : ℝ} (hg : 0 < g) (hμ : 0 < μ) (hR : 0 < R) :
    3 / 2 * embedAmplitude g μ R ≤ energy g μ R ∧
      energy g μ R ≤ 2 * embedAmplitude g μ R := by
  by_cases hsmall : g ≤ μ * R
  · have hs : g / (2 * μ) ≤ R := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    rw [energy_interior hμ hsmall, embedAmplitude, embedRadius, min_eq_right hs]
    have hid : g * (g / (2 * μ)) / 2 = (g ^ 2 / (2 * μ)) / 2 := by ring
    rw [hid]
    have hp : 0 ≤ g ^ 2 / (2 * μ) := by positivity
    constructor <;> linarith
  · have hlarge : μ * R ≤ g := le_of_lt (lt_of_not_ge hsmall)
    rw [energy_boundary hμ hlarge]
    by_cases hmid : g ≤ 2 * μ * R
    · have hs : g / (2 * μ) ≤ R := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
      rw [embedAmplitude, embedRadius, min_eq_right hs]
      have hid : g * (g / (2 * μ)) / 2 = g ^ 2 / (4 * μ) := by ring
      rw [hid]
      constructor
      · have hp := mul_nonneg (show 0 ≤ 2 * μ * R - g by linarith)
          (show 0 ≤ 3 * g - 2 * μ * R by linarith)
        have he : 3 / 2 * (g ^ 2 / (4 * μ)) = 3 * g ^ 2 / (8 * μ) := by ring
        rw [he, div_le_iff₀ (by positivity : 0 < 8 * μ)]
        nlinarith only [hp]
      · have he : 2 * (g ^ 2 / (4 * μ)) = g ^ 2 / (2 * μ) := by ring
        rw [he, le_div_iff₀ (by positivity : 0 < 2 * μ)]
        nlinarith [sq_nonneg (g - μ * R)]
    · have hs : R ≤ g / (2 * μ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
      rw [embedAmplitude, embedRadius, min_eq_left hs]
      have hp := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hmid)) hR.le
      constructor <;> nlinarith [mul_nonneg hμ.le (sq_nonneg R)]

theorem embedding_curvature {g μ R : ℝ} (hg : 0 < g) (hμ : 0 < μ) (hR : 0 < R) :
    μ ≤ embedAmplitude g μ R / embedRadius g μ R ^ 2 := by
  have hs := (embedding_scale_positive hg hμ hR).1
  have hbound : embedRadius g μ R * (2 * μ) ≤ g :=
    (le_div_iff₀ (by positivity)).mp (min_le_right R (g / (2 * μ)))
  rw [le_div_iff₀ (sq_pos_of_pos hs), embedAmplitude]
  nlinarith [mul_le_mul_of_nonneg_right hbound hs.le]

def clip (z : ℝ) : ℝ := max (-1) (min 1 z)
def remainderExtension (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z < -1 then f (-1) - 1 / 2 - (z + 1)
  else if z ≤ 1 then f z - z ^ 2 / 2
  else f 1 - 1 / 2 + (z - 1)
def extended (f : ℝ → ℝ) (z : ℝ) : ℝ := z ^ 2 / 2 + remainderExtension f z

theorem clip_feasible (z : ℝ) : clip z ∈ Set.Icc (-1) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clip_eq {z : ℝ} (hz : z ∈ Set.Icc (-1) 1) : clip z = z := by
  rw [clip, min_eq_right hz.2, max_eq_right hz.1]

theorem extension_exact_reconstruction (f : ℝ → ℝ) (z : ℝ) :
    extended f z = z ^ 2 / 2 + f (clip z) - (clip z) ^ 2 / 2 + max (|z| - 1) 0 := by
  by_cases hl : z < -1
  · have hc : clip z = -1 := by
      rw [clip, min_eq_right (by linarith), max_eq_left (by linarith)]
    rw [extended, remainderExtension, if_pos hl, hc, abs_of_neg (by linarith),
      max_eq_left (by linarith)]
    ring
  · by_cases hr : z ≤ 1
    · have hz : z ∈ Set.Icc (-1) 1 := ⟨by linarith, hr⟩
      rw [extended, remainderExtension, if_neg hl, if_pos hr, clip_eq hz,
        max_eq_right (by have := (abs_le.mpr hz); linarith)]
      ring
    · have hc : clip z = 1 := by
        rw [clip, min_eq_left (by linarith), max_eq_right (by norm_num)]
      rw [extended, remainderExtension, if_neg hl, if_neg hr, hc,
        abs_of_pos (by linarith), max_eq_left (by linarith)]
      ring

theorem extension_agrees (f : ℝ → ℝ) {z : ℝ} (hz : z ∈ Set.Icc (-1) 1) :
    extended f z = f z := by
  rw [extension_exact_reconstruction, clip_eq hz,
    max_eq_right (by have := abs_le.mpr hz; linarith)]
  ring

theorem extension_loss (f : ℝ → ℝ) (z : ℝ) : f (clip z) ≤ extended f z := by
  rw [extension_exact_reconstruction]
  have hm : 0 ≤ max (|z| - 1) 0 := le_max_right _ _
  have hsq : (clip z) ^ 2 ≤ z ^ 2 := by
    by_cases hz : z ∈ Set.Icc (-1) 1
    · rw [clip_eq hz]
    · have hc := clip_feasible z
      have hcle : (clip z) ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      simp only [Set.mem_Icc, not_and_or, not_le] at hz
      rcases hz with hz | hz <;> nlinarith
  linarith

theorem extension_preserves_minimum {f : ℝ → ℝ} {zstar : ℝ}
    (hz : zstar ∈ Set.Icc (-1) 1)
    (hm : ∀ z ∈ Set.Icc (-1) 1, f zstar ≤ f z) :
    extended f zstar = f zstar ∧ ∀ z, f zstar ≤ extended f z := by
  exact ⟨extension_agrees f hz, fun z => (hm _ (clip_feasible z)).trans (extension_loss f z)⟩

theorem extension_add_constant (f : ℝ → ℝ) (c z : ℝ) :
    extended (fun x => f x + c) z = extended f z + c := by
  rw [extension_exact_reconstruction, extension_exact_reconstruction]
  ring

end
end Nonsmooth
