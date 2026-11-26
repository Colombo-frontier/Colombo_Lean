import SampleReuse.PopulationGradient

open SecondOrder

namespace SampleReuse
noncomputable section

def slowAmplitude (d : ℕ) (ε : ℝ) : ℝ :=
  4*ε*slowAlpha d/firstOrderGradientConstant

theorem slowAmplitude_pos {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    0 < slowAmplitude d ε := by
  unfold slowAmplitude
  exact div_pos (mul_pos (mul_pos (by norm_num) hε) (slowAlpha_pos hd))
    firstOrderGradientConstant_pos

theorem slowAmplitude_scale {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    slowAmplitude d ε * slowDilation d * firstOrderGradientConstant = 4*ε := by
  unfold slowAmplitude slowDilation
  field_simp [ne_of_gt (slowAlpha_pos hd), ne_of_gt firstOrderGradientConstant_pos]
  ring

/-- With the manuscript's amplitude, every epsilon-stationary point activates
all hidden blocks, even if the point was never queried. -/
theorem calibrated_stationary_all_blocks {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (x : Point (FirstOrderDimension d T))
    (hx : ‖gradient (scaledFirstOrderPopulation Θ (slowAmplitude d ε) (slowDilation d)) x‖ ≤ ε) :
    ∀ j, 1/2 < slowEncoding (Θ j) ((firstOrderCoordinates d T x) j) := by
  apply slow_stationary_all_blocks Θ hd (slowAmplitude_pos hd hε).le _ x hx
  rw [slowAmplitude_scale hd]
  linarith

theorem calibrated_hessian_lipschitz {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (x y : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderPopulation Θ (slowAmplitude d ε) (slowDilation d)) x -
      hessian (scaledFirstOrderPopulation Θ (slowAmplitude d ε) (slowDilation d)) y‖ ≤
      (4*ε*firstOrderGeometryConstant/firstOrderGradientConstant)*‖x-y‖ := by
  have hh := scaledFirstOrderPopulation_hessian_lipschitz Θ hd
    (slowAmplitude_pos hd hε).le
    (show 0 ≤ slowDilation d from inv_nonneg.mpr (slowAlpha_pos hd).le) x y
  have he : slowAmplitude d ε * slowDilation d^3 *
      (firstOrderGeometryConstant*Real.sqrt d) =
      4*ε*firstOrderGeometryConstant/firstOrderGradientConstant := by
    calc
      _ = slowAmplitude d ε*(slowDilation d^3*Real.sqrt d)*firstOrderGeometryConstant := by ring
      _ = slowAmplitude d ε*slowDilation d*firstOrderGeometryConstant := by
        rw [slowDilation_cubic hd]
      _ = _ := by
        unfold slowAmplitude slowDilation
        field_simp [ne_of_gt (slowAlpha_pos hd), ne_of_gt firstOrderGradientConstant_pos]
        ring
  rwa [he] at hh

end
end SampleReuse
