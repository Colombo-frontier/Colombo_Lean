import Bilevel.CachedParameterCost
import Bilevel.ChiRefinementRates
import Bilevel.CachedCostRate

/-! Normalization of the actual cached upper cost. Zero Hessian variation
and zero noise are included; only the final D+U+G absorption needs theta≥1. -/
noncomputable section
namespace Bilevel.CachedNormalizedRate

theorem normalized_parameters {μ L Lf Lg Cf θ : ℝ}
    (hμ : 0<μ) (hL : 0<L) (hLf : 0≤Lf) (hLg : 0≤Lg) (hCf : 0≤Cf)
    (hLfL : Lf≤L) (hLgL : Lg≤L) (hCfL : Cf≤L) (hθ : 0≤θ) (hκ : 1≤L/μ) :
    max L ((1+Lg/μ)^2*(Lf+(θ*μ)*Cf/μ)) ≤ 4*L*(1+θ)*(L/μ)^2 ∧
      Lf*(1+Lg/μ)^2 ≤ 4*L*(L/μ)^2 ∧
      (1+Lg/μ)*(θ*μ)*Cf^2/(2*μ^2) ≤ L*θ*(L/μ)^2 := by
  have hk0 : 0≤Lg/μ := div_nonneg hLg hμ.le
  have hκ0 : 0≤L/μ := by positivity
  have hkκ : Lg/μ≤L/μ := div_le_div_of_nonneg_right hLgL hμ.le
  have hk : 1+Lg/μ≤2*(L/μ) := by linarith
  have hsq : (1+Lg/μ)^2≤(2*(L/μ))^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hk
  have hcf : Cf^2≤L^2 := (sq_le_sq₀ hCf hL.le).mpr hCfL
  have hfactor : Lf+(θ*μ)*Cf/μ≤(1+θ)*L := by
    have he : (θ*μ)*Cf/μ=θ*Cf := by field_simp; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hCfL hθ]
  have hf0 : 0≤Lf+(θ*μ)*Cf/μ := by positivity
  have hcurv := mul_le_mul hsq hfactor hf0 (sq_nonneg (2*(L/μ)))
  have hanchor := mul_le_mul hLfL hsq (sq_nonneg (1+Lg/μ)) hL.le
  have hκ2 : 1≤(L/μ)^2 := one_le_pow₀ hκ
  have hLbound : L≤4*L*(1+θ)*(L/μ)^2 := by
    have hc : 1≤(1+θ)*(L/μ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc hL.le]
  refine ⟨max_le hLbound (by nlinarith [hcurv]),by nlinarith [hanchor],?_⟩
  have hb := mul_le_mul hk hcf (sq_nonneg Cf) (by positivity : 0≤2*(L/μ))
  have hb' := mul_le_mul_of_nonneg_right hb hθ
  have hd := div_le_div_of_nonneg_right hb' (by positivity : 0≤2*μ)
  convert hd using 1 <;> field_simp <;> ring

theorem normalized_bias_zero {μ Lg Cf : ℝ} :
    (1+Lg/μ)*((0:ℝ)*μ)*Cf^2/(2*μ^2)=0 := by ring

private theorem first_bracket {k κ I a b c A : ℝ}
    (hκ : 1≤κ) (hkκ : k≤κ)
    (hI : I≤A) (hA : 1≤A) (hb : 0≤b) (hc : 0≤c)
    (hnoise : a≤b+4096*c) :
    1+Real.sqrt k*I+a ≤ 4096*A*(Real.sqrt κ+b+c) := by
  have hs : 1≤Real.sqrt κ := Real.one_le_sqrt.mpr hκ
  have hs0 : 0≤Real.sqrt k := Real.sqrt_nonneg k
  have hA0 : 0≤A := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hI hs0
  have hm2 := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hkκ) hA0
  have hsb : b≤A*b := le_mul_of_one_le_left hb hA
  have hsc : c≤A*c := le_mul_of_one_le_left hc hA
  have has : 1≤A*Real.sqrt κ := by nlinarith
  nlinarith

theorem lower_noise_normalized {k κ E L θ ε σ : ℝ}
    (hk : 0≤k) (hκ : 0≤κ) (hkκ : k≤κ) (hE : 0≤E)
    (hL : 0≤L) (hθ : 0≤θ) (hEb : E≤L*θ*κ^2) :
    k^2*σ^2/(ε^2*(CachedParameterChoice.tilt E ε)^2) ≤
      κ^2*σ^2/ε^2+4096*(L^2*θ^2*κ^6*σ^2/ε^4) := by
  have ht := mul_le_mul_of_nonneg_left (CachedParameterChoice.inverse_tilt_sq E ε)
    (by positivity : 0≤k^2*σ^2/ε^2)
  have hksq : k^2≤κ^2 := (sq_le_sq₀ hk hκ).mpr hkκ
  have hEsq : E^2≤(L*θ*κ^2)^2 := (sq_le_sq₀ hE (by positivity)).mpr hEb
  have hm : k^2*E^2≤L^2*θ^2*κ^6 := by
    calc
      _ ≤ κ^2*(L*θ*κ^2)^2 := mul_le_mul hksq hEsq (sq_nonneg E) (sq_nonneg κ)
      _ = _ := by ring
  have hbase := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hksq (sq_nonneg σ)) (sq_nonneg ε)
  have hhigh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm (sq_nonneg σ)) (by positivity : 0≤ε^4)
  have he : (k^2*σ^2/ε^2)*(1+(64*E/ε)^2) =
      k^2*σ^2/ε^2+4096*(k^2*E^2*σ^2/ε^4) := by ring
  have he' : (k^2*σ^2/ε^2)*(1/(CachedParameterChoice.tilt E ε)^2) =
      k^2*σ^2/(ε^2*(CachedParameterChoice.tilt E ε)^2) := by ring
  rw [he,he'] at ht
  nlinarith

private theorem second_bracket {k l κ ε σf σg : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hκ : 1≤κ) (hkκ : k≤κ) (hlκ : l≤κ) :
    1+(1+k)^2*σf^2/ε^2+(1+k)^2*l^2*σg^2/ε^2 ≤
      4*(1+κ^2*σf^2/ε^2+κ^4*σg^2/ε^2) := by
  have hs : (1+k)^2≤4*κ^2 := by nlinarith [sq_nonneg (κ-k)]
  have hl2 : l^2≤κ^2 := (sq_le_sq₀ hl (by linarith)).mpr hlκ
  have hm : (1+k)^2*l^2≤4*κ^4 := by
    have hh := mul_le_mul hs hl2 (sq_nonneg l) (by positivity : 0≤4*κ^2)
    nlinarith
  have hf := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (sq_nonneg σf)) (sq_nonneg ε)
  have hg := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm (sq_nonneg σg)) (sq_nonneg ε)
  convert add_le_add (add_le_add (show (1:ℝ)≤4 by norm_num) hf) hg using 1
  ring

private theorem factor_bound {a b Δ ε : ℝ} (hΔ : 0≤Δ) (ha : a≤4*b) :
    1+a*Δ/ε^2≤4*(1+b*Δ/ε^2) := by
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha hΔ) (sq_nonneg ε)
  convert add_le_add (show (1:ℝ)≤4 by norm_num) hh using 1
  ring

set_option maxHeartbeats 800000 in
/-- Normalize the actual core while retaining its public initialization
logarithm. The hypotheses are scalar budget bounds, proved above for the
source choices; no rate is assumed about an oracle procedure. -/
theorem core_le_normalizedExpansion {μ L Lf Lg E Λ La θ κ Δ ε D σf σg : ℝ}
    (hμ : 0<μ) (hL : 0≤L) (hLf : 0≤Lf) (hLg : 0≤Lg)
    (hE : 0≤E) (hθ : 0≤θ) (hκ : 1≤κ) (hΔ : 0≤Δ)
    (hLgκ : Lg/μ≤κ) (hLfκ : Lf/μ≤κ)
    (hEb : E≤L*θ*κ^2) (hΛb : Λ≤4*L*(1+θ)*κ^2) (hLab : La≤4*L*κ^2) :
    let I := CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg (Lg/μ) E ε)
    CachedCostRate.core μ Lf Lg E Λ La Δ ε D σf σg ≤
      16384*max 1 I*ChiRefinementRates.normalizedExpansion L θ κ σf σg Δ ε := by
  let k := Lg/μ
  let I := CachedOracleCost.initializationLog μ Lg D
    (CachedParameterChoice.anchorRadius Lf Lg k E ε)
  let A := max 1 I
  let N := 1+(1+θ)*(L*κ^2*Δ/ε^2)
  let B := 1+L*κ^2*Δ/ε^2
  let V := Real.sqrt κ+κ^2*σg^2/ε^2+L^2*θ^2*κ^6*σg^2/ε^4
  let W := 1+κ^2*σf^2/ε^2+κ^4*σg^2/ε^2
  have hk : 0≤k := div_nonneg hLg hμ.le
  have hκ0 : 0≤κ := by linarith
  have hI0 : 0≤I := CachedOracleCost.initializationLog_nonneg hμ hLg
  have hA : 1≤A := le_max_left _ _
  have hA0 : 0≤A := by linarith
  have hV : 0≤V := by dsimp [V]; positivity
  have hW : 0≤W := by dsimp [W]; positivity
  have hN0 : 0≤N := by dsimp [N]; positivity
  have hB0 : 0≤B := by dsimp [B]; positivity
  have hnoise := lower_noise_normalized (σ := σg) (ε := ε) hk hκ0 hLgκ hE hL hθ hEb
  have hfirst : 1+Real.sqrt k*I+k^2*σg^2/(ε^2*(CachedParameterChoice.tilt E ε)^2) ≤
      4096*A*V := first_bracket hκ hLgκ (le_max_right _ _) hA
        (by positivity) (by positivity) hnoise
  have hsecond : 1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2) ≤ 4*W := by
    have hh := second_bracket (ε := ε) (σf := σf) (σg := σg)
      hk (div_nonneg hLf hμ.le) hκ hLgκ hLfκ
    convert hh using 1
    dsimp [W]
    ring
  have hN : 1+Λ*Δ/ε^2≤4*N := by
    have hΛb' : Λ≤4*((1+θ)*(L*κ^2)) := by nlinarith
    have hh := factor_bound (ε := ε) hΔ hΛb'
    convert hh using 1
    dsimp [N]
    ring
  have hB : 1+La*Δ/ε^2≤4*B := by
    have hLab' : La≤4*(L*κ^2) := by nlinarith
    have hh := factor_bound (ε := ε) hΔ hLab'
    exact hh
  have hterm1 := mul_le_mul hN hfirst (by positivity :
      0≤1+Real.sqrt k*I+k^2*σg^2/(ε^2*(CachedParameterChoice.tilt E ε)^2))
    (mul_nonneg (by norm_num) hN0)
  have hterm2 := mul_le_mul hB hsecond (by positivity :
      0≤1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2))
    (mul_nonneg (by norm_num) hB0)
  have hscale := mul_le_mul_of_nonneg_right (show (16:ℝ)≤16384*A by linarith)
    (mul_nonneg hB0 hW)
  change (1+Λ*Δ/ε^2)*(1+Real.sqrt k*I+k^2*σg^2/(ε^2*(CachedParameterChoice.tilt E ε)^2))+
    (1+La*Δ/ε^2)*(1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2)) ≤
    16384*A*(N*V+B*W)
  calc
    _ ≤ (4*N)*(4096*A*V)+(4*B)*(4*W) := add_le_add hterm1 hterm2
    _ = 16384*A*(N*V)+16*(B*W) := by ring
    _ ≤ 16384*A*(N*V)+16384*A*(B*W) := add_le_add_left hscale _
    _ = _ := by ring

theorem core_le_three_rates {μ L Lf Lg E Λ La θ κ Δ ε D σf σg : ℝ}
    (hμ : 0<μ) (hL : 0<L) (hLf : 0≤Lf) (hLg : 0≤Lg)
    (hE : 0≤E) (hθ : 1≤θ) (hκ : 1≤κ) (hΔ : 0<Δ)
    (hε : 0<ε) (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hLgκ : Lg/μ≤κ) (hLfκ : Lf/μ≤κ)
    (hEb : E≤L*θ*κ^2) (hΛb : Λ≤4*L*(1+θ)*κ^2) (hLab : La≤4*L*κ^2) :
    let I := CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg (Lg/μ) E ε)
    CachedCostRate.core μ Lf Lg E Λ La Δ ε D σf σg ≤ 98304*max 1 I*
      (ChiRefinementRates.deterministic L θ κ Δ ε+
        ChiRefinementRates.upperNoise L κ σf Δ ε+ChiRefinementRates.lowerNoise L θ κ σg Δ ε) := by
  have hθ0 : 0≤θ := by linarith
  have hc := core_le_normalizedExpansion (ε := ε) (D := D) (σf := σf) (σg := σg)
    hμ hL.le hLf hLg hE hθ0 hκ hΔ.le hLgκ hLfκ hEb hΛb hLab
  have he := ChiRefinementRates.normalizedExpansion_le_six_rates_of_accuracy
    (σf := σf) (σg := σg) hL hΔ hθ hκ hε haccuracy
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0≤16384*max 1
    (CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg (Lg/μ) E ε)))
  exact hc.trans (by convert hh using 1; ring)

/-- The comparison with the source's actual choices of bias, curvature, and
anchor smoothness; their normalized bounds are conclusions, not premises. -/
theorem source_core_le_normalizedExpansion {μ L Lf Lg Cf θ Δ ε D σf σg : ℝ}
    (hμ : 0<μ) (hL : 0<L) (hLf : 0≤Lf) (hLg : 0≤Lg) (hCf : 0≤Cf)
    (hLfL : Lf≤L) (hLgL : Lg≤L) (hCfL : Cf≤L) (hθ : 0≤θ) (hκ : 1≤L/μ)
    (hΔ : 0≤Δ) :
    let k := Lg/μ
    let E := (1+k)*(θ*μ)*Cf^2/(2*μ^2)
    let Λ := max L ((1+k)^2*(Lf+(θ*μ)*Cf/μ))
    let La := Lf*(1+k)^2
    let I := CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg k E ε)
    CachedCostRate.core μ Lf Lg E Λ La Δ ε D σf σg ≤
      16384*max 1 I*ChiRefinementRates.normalizedExpansion L θ (L/μ) σf σg Δ ε := by
  have hb := normalized_parameters hμ hL hLf hLg hCf hLfL hLgL hCfL hθ hκ
  dsimp only
  exact core_le_normalizedExpansion hμ hL.le hLf hLg (by positivity) hθ hκ hΔ
    (div_le_div_of_nonneg_right hLgL hμ.le) (div_le_div_of_nonneg_right hLfL hμ.le)
    hb.2.2 hb.1 hb.2.1

end Bilevel.CachedNormalizedRate
