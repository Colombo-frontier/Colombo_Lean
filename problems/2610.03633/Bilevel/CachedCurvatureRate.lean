import Bilevel.CachedNormalizedRate

/-! The upper-rate specialization in `cor:curvature-controlled`. A separately
certified curvature budget removes chi from the outer iteration factor.
This file proves only the upper comparison; it asserts no matching lower bound. -/
noncomputable section
namespace Bilevel.CachedCurvatureRate

def deterministic (L κ Δ ε : ℝ) : ℝ := L*κ^2*Real.sqrt κ*Δ/ε^2

def lowerNoise (L θ κ σg Δ ε : ℝ) : ℝ := L^3*θ^2*κ^8*σg^2*Δ/ε^6

def normalizedExpansion (L θ κ σf σg Δ ε : ℝ) : ℝ :=
  (1+L*κ^2*Δ/ε^2)*(Real.sqrt κ+κ^2*σg^2/ε^2+L^2*θ^2*κ^6*σg^2/ε^4)+
  (1+L*κ^2*Δ/ε^2)*(1+κ^2*σf^2/ε^2+κ^4*σg^2/ε^2)

private theorem first_bracket {k κ I a b c A : ℝ}
    (hκ : 1≤κ) (hkκ : k≤κ) (hI : I≤A) (hA : 1≤A)
    (hb : 0≤b) (hc : 0≤c) (hnoise : a≤b+4096*c) :
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

private theorem factor_bound {a b c Δ ε : ℝ} (hΔ : 0≤Δ) (hc : 1≤c) (ha : a≤c*b) :
    1+a*Δ/ε^2≤c*(1+b*Δ/ε^2) := by
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha hΔ) (sq_nonneg ε)
  convert add_le_add hc hh using 1
  ring

set_option maxHeartbeats 800000 in
/-- Floor-retaining comparison for a supplied certified upper-curvature
budget. Theta may be zero, and neither noise budget needs to be positive. -/
theorem core_le_normalizedExpansion {μ L Lf Lg E Λ La C_F θ κ Δ ε D σf σg : ℝ}
    (hμ : 0<μ) (hL : 0≤L) (hLf : 0≤Lf) (hLg : 0≤Lg)
    (hE : 0≤E) (hθ : 0≤θ) (hκ : 1≤κ) (hΔ : 0≤Δ)
    (hLgκ : Lg/μ≤κ) (hLfκ : Lf/μ≤κ)
    (hEb : E≤L*θ*κ^2) (hΛb : Λ≤C_F*L*κ^2) (hLab : La≤4*L*κ^2) :
    let I := CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg (Lg/μ) E ε)
    CachedCostRate.core μ Lf Lg E Λ La Δ ε D σf σg ≤
      16384*max 1 C_F*max 1 I*normalizedExpansion L θ κ σf σg Δ ε := by
  let k := Lg/μ
  let I := CachedOracleCost.initializationLog μ Lg D
    (CachedParameterChoice.anchorRadius Lf Lg k E ε)
  let A := max 1 I
  let C := max 1 C_F
  let N := 1+L*κ^2*Δ/ε^2
  let V := Real.sqrt κ+κ^2*σg^2/ε^2+L^2*θ^2*κ^6*σg^2/ε^4
  let W := 1+κ^2*σf^2/ε^2+κ^4*σg^2/ε^2
  have hk : 0≤k := div_nonneg hLg hμ.le
  have hκ0 : 0≤κ := by linarith
  have hI0 : 0≤I := CachedOracleCost.initializationLog_nonneg hμ hLg
  have hA : 1≤A := le_max_left _ _
  have hC : 1≤C := le_max_left _ _
  have hC0 : 0≤C := by linarith
  have hW : 0≤W := by dsimp [W]; positivity
  have hN0 : 0≤N := by dsimp [N]; positivity
  have hnoise := CachedNormalizedRate.lower_noise_normalized (σ := σg) (ε := ε)
    hk hκ0 hLgκ hE hL hθ hEb
  have hfirst : 1+Real.sqrt k*I+k^2*σg^2/(ε^2*(CachedParameterChoice.tilt E ε)^2) ≤
      4096*A*V := first_bracket hκ hLgκ (le_max_right _ _) hA
        (by positivity) (by positivity) hnoise
  have hsecond : 1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2) ≤ 4*W := by
    have hh := second_bracket (ε := ε) (σf := σf) (σg := σg)
      hk (div_nonneg hLf hμ.le) hκ hLgκ hLfκ
    convert hh using 1
    dsimp [W]
    ring
  have hΛb' : Λ≤(4*C)*(L*κ^2) := by
    have hh := mul_le_mul_of_nonneg_right (show C_F≤C from le_max_right _ _) (by positivity : 0≤L*κ^2)
    have hn : 0≤C*(L*κ^2) := by positivity
    nlinarith
  have hLab' : La≤(4*C)*(L*κ^2) := by
    have hh := mul_le_mul_of_nonneg_right hC (by positivity : 0≤4*L*κ^2)
    nlinarith
  have hN : 1+Λ*Δ/ε^2≤(4*C)*N :=
    factor_bound hΔ (by linarith) hΛb'
  have hB : 1+La*Δ/ε^2≤(4*C)*N :=
    factor_bound hΔ (by linarith) hLab'
  have hterm1 := mul_le_mul hN hfirst (by positivity :
      0≤1+Real.sqrt k*I+k^2*σg^2/(ε^2*(CachedParameterChoice.tilt E ε)^2))
    (by positivity : 0≤(4*C)*N)
  have hterm2 := mul_le_mul hB hsecond (by positivity :
      0≤1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2))
    (by positivity : 0≤(4*C)*N)
  have hscale := mul_le_mul_of_nonneg_right (show (16:ℝ)≤16384*A by linarith)
    (mul_nonneg hC0 (mul_nonneg hN0 hW))
  change (1+Λ*Δ/ε^2)*(1+Real.sqrt k*I+k^2*σg^2/(ε^2*(CachedParameterChoice.tilt E ε)^2))+
    (1+La*Δ/ε^2)*(1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2)) ≤
    16384*C*A*(N*V+N*W)
  calc
    _ ≤ ((4*C)*N)*(4096*A*V)+((4*C)*N)*(4*W) := add_le_add hterm1 hterm2
    _ = 16384*C*A*(N*V)+16*(C*(N*W)) := by ring
    _ ≤ 16384*C*A*(N*V)+16384*A*(C*(N*W)) := add_le_add_left hscale _
    _ = _ := by ring

private theorem abstract_absorption {X s a b c u : ℝ}
    (hX : 1≤X) (hs : 1≤s) (ha0 : 0≤a) (hb0 : 0≤b) (hc0 : 0≤c) (hu0 : 0≤u)
    (ha : a≤c) (hb : b≤c) :
    (1+X)*(s+a+c)+(1+X)*(1+u+b) ≤ 6*(X*s+X*u+X*c) := by
  have hX0 : 0≤X := by linarith
  have h1 := mul_le_mul_of_nonneg_right (show 1+X≤2*X by linarith)
    (show 0≤s+a+c by linarith)
  have h2 := mul_le_mul_of_nonneg_right (show 1+X≤2*X by linarith)
    (show 0≤1+u+b by linarith)
  have h3 := mul_le_mul_of_nonneg_left ha hX0
  have h4 := mul_le_mul_of_nonneg_left hb hX0
  have h5 := mul_le_mul_of_nonneg_left hs hX0
  have h6 : 0≤X*u := mul_nonneg hX0 hu0
  nlinarith

private theorem noise_absorption {L θ κ σ ε : ℝ}
    (hθ : 1≤θ) (hκ : 1≤κ) (hε : 0<ε) (hεL : ε^2≤L^2) :
    κ^2*σ^2/ε^2≤L^2*θ^2*κ^6*σ^2/ε^4 ∧
      κ^4*σ^2/ε^2≤L^2*θ^2*κ^6*σ^2/ε^4 := by
  have ht : 1≤θ^2 := one_le_pow₀ hθ
  have hk2 : 1≤κ^2 := one_le_pow₀ hκ
  have hcoef : ε^2≤L^2*θ^2*κ^2 := by
    have hh := mul_le_mul_of_nonneg_left hk2 (by positivity : 0≤L^2*θ^2)
    nlinarith [sq_nonneg L]
  have hb : κ^4*σ^2/ε^2≤L^2*θ^2*κ^6*σ^2/ε^4 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hε) (pow_pos hε 4)).mpr
    have hh := mul_le_mul_of_nonneg_right hcoef (by positivity : 0≤κ^4*σ^2*ε^2)
    nlinarith
  have hk24 : κ^2≤κ^4 := by nlinarith
  have ha := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hk24 (sq_nonneg σ)) (sq_nonneg ε)
  exact ⟨ha.trans hb,hb⟩

theorem normalizedExpansion_le_six_rates {L θ κ σf σg Δ ε : ℝ}
    (hL : 0<L) (hΔ : 0<Δ) (hθ : 1≤θ) (hκ : 1≤κ)
    (hε : 0<ε) (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    normalizedExpansion L θ κ σf σg Δ ε ≤
      6*(deterministic L κ Δ ε+ChiRefinementRates.upperNoise L κ σf Δ ε+
        lowerNoise L θ κ σg Δ ε) := by
  have hκ0 : 0≤κ := by linarith
  have heL := haccuracy.trans (min_le_left _ _)
  have heΔ := haccuracy.trans (min_le_right _ _)
  have hsqrt := Real.sq_sqrt (le_of_lt (mul_pos hL hΔ))
  have hroot := Real.sqrt_nonneg (L*Δ)
  have hεL : ε^2≤L^2 := by nlinarith
  have hεΔ : ε^2≤L*Δ := by nlinarith
  have hk2 : 1≤κ^2 := one_le_pow₀ hκ
  have hX : 1≤L*κ^2*Δ/ε^2 := by
    apply (one_le_div (sq_pos_of_pos hε)).mpr
    have hh := mul_le_mul_of_nonneg_left hk2 (le_of_lt (mul_pos hL hΔ))
    nlinarith
  obtain ⟨ha,hb⟩ := noise_absorption (σ := σg) hθ hκ hε hεL
  have hh := abstract_absorption (X := L*κ^2*Δ/ε^2) (s := Real.sqrt κ)
    (a := κ^2*σg^2/ε^2) (b := κ^4*σg^2/ε^2)
    (c := L^2*θ^2*κ^6*σg^2/ε^4) (u := κ^2*σf^2/ε^2)
    hX (Real.one_le_sqrt.mpr hκ) (by positivity) (by positivity) (by positivity) (by positivity) ha hb
  unfold normalizedExpansion deterministic ChiRefinementRates.upperNoise lowerNoise
  convert hh using 1
  ring

theorem core_le_three_rates {μ L Lf Lg E Λ La C_F θ κ Δ ε D σf σg : ℝ}
    (hμ : 0<μ) (hL : 0<L) (hLf : 0≤Lf) (hLg : 0≤Lg)
    (hE : 0≤E) (hθ : 1≤θ) (hκ : 1≤κ) (hΔ : 0<Δ)
    (hε : 0<ε) (haccuracy : ε≤min L (Real.sqrt (L*Δ)))
    (hLgκ : Lg/μ≤κ) (hLfκ : Lf/μ≤κ)
    (hEb : E≤L*θ*κ^2) (hΛb : Λ≤C_F*L*κ^2) (hLab : La≤4*L*κ^2) :
    let I := CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg (Lg/μ) E ε)
    CachedCostRate.core μ Lf Lg E Λ La Δ ε D σf σg ≤ 98304*max 1 C_F*max 1 I*
      (deterministic L κ Δ ε+ChiRefinementRates.upperNoise L κ σf Δ ε+
        lowerNoise L θ κ σg Δ ε) := by
  have hθ0 : 0≤θ := by linarith
  have hc := core_le_normalizedExpansion (ε := ε) (D := D) (σf := σf) (σg := σg)
    hμ hL.le hLf hLg hE hθ0 hκ hΔ.le hLgκ hLfκ hEb hΛb hLab
  have he := normalizedExpansion_le_six_rates (σf := σf) (σg := σg) hL hΔ hθ hκ hε haccuracy
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0≤16384*max 1 C_F*max 1
    (CachedOracleCost.initializationLog μ Lg D
      (CachedParameterChoice.anchorRadius Lf Lg (Lg/μ) E ε)))
  exact hc.trans (by convert hh using 1; ring)

end Bilevel.CachedCurvatureRate
