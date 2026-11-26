import FreshGradientMinimax.ProximalStability
import FreshGradientMinimax.RecursiveInitialization

/-! Joint continuity of the genuine proximal gap and starting energy,
including the proximal center as a variable. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
namespace NCObjective
variable {dx dy : ℕ} {L μ : ℝ} (F : NCObjective dx dy L μ)

theorem proximal_slice_center_lip (c c' : Euclid dx) (v : Euclid dy) :
    ‖(F.proximalObjective c).sliceMin v - (F.proximalObjective c').sliceMin v‖ ≤ 2 * ‖c - c'‖ := by
  have hr := (F.proximalObjective c).slice_residual_distance ((F.proximalObjective c').sliceMin v) v
  change L * _ ≤ ‖F.regularizedX c ((F.proximalObjective c').sliceMin v) v‖ at hr
  rw [F.regularizedX_shift c c'] at hr
  have hz : F.regularizedX c' ((F.proximalObjective c').sliceMin v) v = 0 :=
    (F.proximalObjective c').slice_gradient_zero v
  rw [hz, zero_add, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by have := F.L_pos; positivity : 0 < 2 * L), norm_sub_rev c' c] at hr
  rw [norm_sub_rev] at hr
  apply (mul_le_mul_left F.L_pos).mp
  nlinarith only [hr]

theorem proximal_slice_joint_continuous :
    Continuous (fun p : Euclid dx × Euclid dy => (F.proximalObjective p.1).sliceMin p.2) := by
  apply (show LipschitzWith 5 (fun p : Euclid dx × Euclid dy => (F.proximalObjective p.1).sliceMin p.2) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hc := F.proximal_slice_center_lip p.1 q.1 p.2
  have hv := (F.proximalObjective q.1).sliceMin_lip p.2 q.2
  have hratio : (3 * L) / L = 3 := by field_simp [ne_of_gt F.L_pos]
  change ‖_ - _‖ ≤ ((3 * L) / L) * ‖p.2 - q.2‖ at hv
  rw [hratio] at hv
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((F.proximalObjective p.1).sliceMin p.2) ((F.proximalObjective q.1).sliceMin p.2)
    ((F.proximalObjective q.1).sliceMin q.2)
  simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, NNReal.coe_ofNat]
  have hx := le_max_left ‖p.1 - q.1‖ ‖p.2 - q.2‖
  have hy := le_max_right ‖p.1 - q.1‖ ‖p.2 - q.2‖
  linarith

def proximalGap (p : Euclid dx × Joint dx dy) : ℝ := (F.proximalObjective p.1).gap p.2.1 p.2.2

theorem proximalGap_nonneg (p : Euclid dx × Joint dx dy) : 0 ≤ F.proximalGap p :=
  (F.proximalObjective p.1).gap_nonneg p.2.1 p.2.2

theorem proximalGap_continuous : Continuous F.proximalGap := by
  have hf : Continuous (fun z : Joint dx dy => F.f z.1 z.2) :=
    continuous_iff_continuousAt.mpr (fun z => (F.derivative z).continuousAt)
  have hv : Continuous F.value :=
    continuous_iff_continuousAt.mpr (fun u => (F.value_hasFDerivAt u).continuousAt)
  have hm : Continuous (fun p : Euclid dx × Joint dx dy => (F.proximalObjective p.1).sliceMin p.2.2) :=
    F.proximal_slice_joint_continuous.comp
      (f := fun p : Euclid dx × Joint dx dy => (p.1, p.2.2))
      (continuous_fst.prodMk continuous_snd.snd)
  have he : F.proximalGap = fun p : Euclid dx × Joint dx dy =>
      (F.value p.2.1 + L * ‖p.2.1 - p.1‖ ^ 2) -
        (F.f ((F.proximalObjective p.1).sliceMin p.2.2) p.2.2 +
          L * ‖(F.proximalObjective p.1).sliceMin p.2.2 - p.1‖ ^ 2) := by
    funext p
    rw [proximalGap, SCObjective.gap, F.proximalObjective_value, SCObjective.dualValue_eq_min]
    rfl
  rw [he]
  exact ((hv.comp continuous_snd.fst).add
    (continuous_const.mul ((continuous_snd.fst.sub continuous_fst).norm.pow 2))).sub
      ((hf.comp (hm.prodMk continuous_snd.snd)).add
        (continuous_const.mul ((hm.sub continuous_fst).norm.pow 2)))

def proximalStartEnergy (p : Euclid dx × Joint dx dy) : ℝ :=
  (F.proximalObjective p.1).saddleStartEnergy p.2

theorem proximalStartEnergy_continuous : Continuous F.proximalStartEnergy := by
  have he : F.proximalStartEnergy = fun p : Euclid dx × Joint dx dy =>
      3 * L * ‖p.2.1 - F.proxPoint p.1‖ ^ 2 + μ * ‖p.2.2 - F.dualMax (F.proxPoint p.1)‖ ^ 2 := by
    funext p
    simp only [proximalStartEnergy, SCObjective.saddleStartEnergy,
      F.proximalObjective_saddleU, F.proximalObjective_saddleV]
  rw [he]
  exact (continuous_const.mul ((continuous_snd.fst.sub (F.proxPoint_continuous.comp continuous_fst)).norm.pow 2)).add
    (continuous_const.mul ((continuous_snd.snd.sub
      (F.dualMax_continuous.comp (F.proxPoint_continuous.comp continuous_fst))).norm.pow 2))

end NCObjective
end FreshGradientMinimax
