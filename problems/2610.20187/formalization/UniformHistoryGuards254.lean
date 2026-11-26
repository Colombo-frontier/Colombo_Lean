import TiltCovarianceBounds254

namespace Paper254

def uniformHistoryParameters (a b r p : ℕ) (lo hi : ℚ) : RationalHistoryParameters :=
  let n := 3*a+b+r+6
  { dimensionLog := a
    spectralLog := n+b+2
    accuracy := n
    storagePrecision := n
    projectionPrecision := p
    smoothing := ((2:ℚ)^n)⁻¹
    lowerThreshold := lo+((2:ℚ)^(r+2))⁻¹
    upperThreshold := hi-((2:ℚ)^(r+2))⁻¹ }

theorem uniform_history_scalar_guards (d a b r : ℕ) (hd : 0<d)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (H : ℝ) (hH : 0<H) (hHbound : H≤(2:ℝ)^b) :
    let n := 3*a+b+r+6
    (d:ℝ)*(((2:ℝ)^n)⁻¹+(d:ℝ)^2*((2:ℝ)^n)⁻¹+((2:ℝ)^n)⁻¹)≤
      ((2:ℝ)^(r+2))⁻¹ ∧
    (d:ℝ)*((2:ℝ)^n)⁻¹≤1/(2*H) := by
  dsimp
  have hA : (1:ℝ)≤2^a := one_le_pow₀ (by norm_num)
  have hB : (1:ℝ)≤2^b := one_le_pow₀ (by norm_num)
  have hR : (1:ℝ)≤2^r := one_le_pow₀ (by norm_num)
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg _
  have hcube : (d:ℝ)^3≤((2:ℝ)^a)^3 := pow_le_pow_left₀ hd0 hdim 3
  have hAcube : (2:ℝ)^a≤((2:ℝ)^a)^3 := by nlinarith [sq_nonneg ((2:ℝ)^a-1)]
  have hp : (2:ℝ)^(3*a+b+r+6)=64*((2:ℝ)^a)^3*(2:ℝ)^b*(2:ℝ)^r := by
    simp only [pow_add,pow_mul']
    ring
  have hmargin : (d:ℝ)^3+2*d≤16*((2:ℝ)^a)^3*(2:ℝ)^b := by
    have hh := mul_le_mul_of_nonneg_left hB (show 0≤((2:ℝ)^a)^3 by positivity)
    nlinarith
  have hmetric : 2*H*(d:ℝ)≤64*((2:ℝ)^a)^3*(2:ℝ)^b*(2:ℝ)^r := by
    have hh := mul_le_mul hdim hHbound hH.le (by positivity : 0≤(2:ℝ)^a)
    have hc := mul_le_mul_of_nonneg_right hAcube (show 0≤(2:ℝ)^b by positivity)
    have hr := mul_le_mul_of_nonneg_left hR (show 0≤((2:ℝ)^a)^3*(2:ℝ)^b by positivity)
    nlinarith
  constructor
  · rw [hp,show (2:ℝ)^(r+2)=4*(2:ℝ)^r by rw [pow_add]; ring]
    rw [show (d:ℝ)*((64*(2^a)^3*2^b*2^r)⁻¹+(d:ℝ)^2*(64*(2^a)^3*2^b*2^r)⁻¹+
      (64*(2^a)^3*2^b*2^r)⁻¹)=((d:ℝ)^3+2*d)/(64*(2^a)^3*2^b*2^r) by ring,
      inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hmargin (show 0≤4*(2:ℝ)^r by positivity)
    nlinarith
  · rw [hp]
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [hmetric]

theorem uniform_history_spectral_guard (n b : ℕ) (H : ℝ) (hH : H≤(2:ℝ)^b) :
    ((2:ℝ)^(n+b+2))⁻¹≤((2:ℝ)^n)⁻¹ ∧
    ∀ x l : ℝ,0≤x → x≤H → 0≤l → l≤H →
      |x-l|+((2:ℝ)^n)⁻¹≤(2:ℝ)^(n+b+2) := by
  have hn : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  have hb : (1:ℝ)≤2^b := one_le_pow₀ (by norm_num)
  have hp : (2:ℝ)^(n+b+2)=4*(2:ℝ)^n*(2:ℝ)^b := by rw [pow_add,pow_add]; ring
  have hi : ((2:ℝ)^n)⁻¹≤1 := inv_le_one_of_one_le₀ hn
  have hnb := mul_le_mul hn hb (by norm_num : (0:ℝ)≤1) (by positivity : (0:ℝ)≤2^n)
  constructor
  · apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    rw [hp]
    have hh := mul_le_mul_of_nonneg_left hb (show 0≤(2:ℝ)^n by positivity)
    nlinarith
  · intro x l hx hxH hl hlH
    have ha : |x-l|≤H := abs_le.mpr ⟨by linarith,by linarith⟩
    rw [hp]
    have hh := mul_le_mul_of_nonneg_right hn (show 0≤(2:ℝ)^b by positivity)
    nlinarith

structure UniformHistoryGuards (d : ℕ) (cfg : RationalHistoryParameters) (lo hi : ℝ) : Prop where
  dimension : (d:ℝ)≤(2:ℝ)^cfg.dimensionLog
  smoothing_pos : 0<(cfg.smoothing:ℝ)
  smoothing_lower : ((2:ℝ)^cfg.spectralLog)⁻¹≤(cfg.smoothing:ℝ)
  lower_spectral : ∀ x : ℝ,0≤x → x≤hi →
    |x-(cfg.lowerThreshold:ℝ)|+(cfg.smoothing:ℝ)≤(2:ℝ)^cfg.spectralLog
  upper_spectral : ∀ x : ℝ,0≤x → x≤hi →
    |x-(cfg.upperThreshold:ℝ)|+(cfg.smoothing:ℝ)≤(2:ℝ)^cfg.spectralLog
  thresholds : (cfg.lowerThreshold:ℝ)≤(cfg.upperThreshold:ℝ)
  lower_margin : lo+d*(((2:ℝ)^cfg.accuracy)⁻¹+(d:ℝ)^2*(cfg.smoothing:ℝ)+
    ((2:ℝ)^cfg.storagePrecision)⁻¹)≤(cfg.lowerThreshold:ℝ)
  upper_margin : (cfg.upperThreshold:ℝ)≤hi-d*(((2:ℝ)^cfg.accuracy)⁻¹+
    (d:ℝ)^2*(cfg.smoothing:ℝ)+((2:ℝ)^cfg.storagePrecision)⁻¹)
  metric : (d:ℝ)*((2:ℝ)^cfg.storagePrecision)⁻¹≤1/(2*hi)

/-- One explicit set of precision parameters works at every round. -/
theorem uniformHistoryParameters_guards (d a b r p : ℕ) (hd : 0<d)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (lo hi : ℚ) (hlo : 0<(lo:ℝ))
    (hhi : (hi:ℝ)≤(2:ℝ)^b) (hgap : ((2:ℝ)^r)⁻¹≤(hi:ℝ)-(lo:ℝ)) :
    UniformHistoryGuards d (uniformHistoryParameters a b r p lo hi) (lo:ℝ) (hi:ℝ) := by
  let n := 3*a+b+r+6
  let h : ℝ := ((2:ℝ)^(r+2))⁻¹
  have hh : 0<h := by dsimp [h]; positivity
  have h4 : ((2:ℝ)^r)⁻¹=4*h := by dsimp [h]; rw [pow_add]; norm_num; field_simp
  have hsep : 4*h≤(hi:ℝ)-(lo:ℝ) := by rwa [h4] at hgap
  have hhi0 : 0<(hi:ℝ) := by linarith
  have hs := uniform_history_scalar_guards d a b r hd hdim (hi:ℝ) hhi0 hhi
  have hb := uniform_history_spectral_guard n b (hi:ℝ) hhi
  constructor
  · exact hdim
  · dsimp [uniformHistoryParameters]; push_cast; positivity
  · simpa only [uniformHistoryParameters,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hb.1
  · intro x hx hxhi
    have hv := hb.2 x ((lo:ℝ)+h) hx hxhi (by linarith) (by linarith)
    simpa only [uniformHistoryParameters,Rat.cast_add,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hv
  · intro x hx hxhi
    have hv := hb.2 x ((hi:ℝ)-h) hx hxhi (by linarith) (by linarith)
    simpa only [uniformHistoryParameters,Rat.cast_sub,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hv
  · dsimp [uniformHistoryParameters]; push_cast
    change (lo:ℝ)+h≤(hi:ℝ)-h
    linarith
  · dsimp [uniformHistoryParameters]; push_cast
    have hv := hs.1
    dsimp [n,h] at *
    linarith
  · dsimp [uniformHistoryParameters]; push_cast
    have hv := hs.1
    dsimp [n,h] at *
    linarith
  · exact hs.2

end Paper254
#print axioms Paper254.uniformHistoryParameters_guards
