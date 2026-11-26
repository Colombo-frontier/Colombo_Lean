import Bilevel.ChiUniformWidthCalibration
import Bilevel.ChiSourcePhysicalScales
import Bilevel.ChiNoiseLogRate

/-! The informative radius of the actual independent-width construction
has the manuscript's noise scale. Constants and the logarithmic exponent
are fixed before all public budgets, dimensions and hidden frames. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiRecursive ChiBoundedChain ChiIndependentWidths

theorem independent_source_force {Cb ε K L₀ t η b T : ℝ}
    (hK : 0<K) (hL : 0<L₀) (ht : 0<t) (hη : 0<η) (hb : 0<b)
    (hT : 1≤T) (J : ℕ) :
    (parentScale ⟨L₀,b⟩ (sourceRatio T)
      (resolution η (b/middleWidth Cb ε K L₀ (t*η) J)) (J+1)).force=
      Cb*ε/(K*t^J) := by
  rw [source_force_formula _ _ (sourceRatio_ge_one hT)]
  simp only [Scale.force,middleWidth,mul_pow]
  field_simp
  ring

set_option maxHeartbeats 300000 in
theorem uniform_signal_log_rate {Bs Cf t Cb cms η η₀ : ℝ}
    (hBs : 0<Bs) (hCf : 0<Cf) (ht : 0<t) (hCb : 0<Cb) (hcms : 0<cms)
    (hη : 0<η) (hη₀ : 0<η₀) :
    ∃ C : ℝ,0<C ∧ ∃ q : ℕ,
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (L μ κ θ ε b T A Kminus ζ cn CR : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 0<κ → κ=L/μ → 1≤θ → 0<ε → 0<b → 1≤T →
      let J := chosenDepth θ
      let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      ∀ (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      let v := fineParameter (θ*μ) (3*μ/2) (D J []).ell (normalCoefficient L J) Cf J
      1≤J → 1≤v →
      let W := ZeroChainSchedule.width cms (D J []).width v (ZeroChainSchedule.levels v)
      4*μ*(2*SmallGapLiftSupport.C*Bs^(J+2)*(D J []).ell*(D J []).width*W/normalCoefficient L J)≤
        C*(Real.log (2+θ))^q*ε^2/(L*θ*κ^3) := by
  obtain ⟨C,hC,q,hq⟩ := exists_informative_log_factor hBs hCf ht hCb hcms
  refine ⟨C,hC,q,?_⟩
  intro F _ _ _ L μ κ θ ε b T A Kminus ζ cn CR weight hL hμ hκ hκeq hθ hε hb hT
  dsimp only
  let J := chosenDepth θ
  let h := middleWidth Cb ε (κ/6) (η₀*L) (t*η) J
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  intro V
  let D : Geometry F := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  intro hJ hv
  have hK : 0<κ/6 := by positivity
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hKg : 0<Kg := div_pos hb hhp
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg)
    (mul_pos hη₀ hL) hb (sourceRatio_ge_one hT) (base_resolution_positive hη hKg) (J+1)
  have hell : 0<(D J []).ell := hp.1
  have hβ : 0<(D J []).width := hp.2
  have hforce : (D J []).ell*(D J []).width=Cb*ε/((κ/6)*t^J) :=
    independent_source_force hK (mul_pos hη₀ hL) ht hη hb hT J
  have hμeq : μ=L/κ := by
    apply (eq_div_iff hκ.ne').mpr
    rw [hκeq]
    field_simp
  have hh := fine_informative_source_rate hL hμ hκ (by linarith only [hθ]) hell hβ hCf hcms hBs.le
    ht hμeq J hJ hforce hv
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_right (hq θ hθ) (show 0≤ε^2/(L*θ*κ^3) by positivity)
  convert hs using 1
  ring

end Bilevel.ChiExtensionCalibration
