import Bilevel.ChiBoundedChainReceivers

/-! Global boundedness of the actual receiver primitives, with explicit
scale dependence. No unproved receiver amplitude is supplied as a premise. -/
noncomputable section
open MeasureTheory Set
namespace Bilevel.ChiBoundedChain

theorem primitive_bound_of_support {f : ℝ → ℝ} (hf : Continuous f) (R C : ℝ)
    (hR : 0≤R) (hC : 0≤C) (hb : ∀ t,|f t|≤C)
    (hz : ∀ t,R≤|t| → f t=0) (t : ℝ) : |primitive f t|≤C*R := by
  have hinside (s : ℝ) (hs : |s|≤R) : |primitive f s|≤C*R := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=s)
      (fun x _ => show ‖f x‖≤C by simpa only [Real.norm_eq_abs] using hb x)
    simp only [Real.norm_eq_abs,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hs hC)
  by_cases ht : |t|≤R
  · exact hinside t ht
  · rcases le_total 0 t with hpos|hneg
    · have hRt : R≤t := by rw [abs_of_nonneg hpos] at ht;linarith
      have hzint : (∫ s in R..t,f s)=0 := by
        calc
          _ = ∫ _s in R..t,(0:ℝ) := intervalIntegral.integral_congr (fun s hs => by
            rw [uIcc_of_le hRt] at hs
            exact hz s (le_trans hs.1 (le_abs_self s)))
          _ = 0 := by simp
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
        (hf.intervalIntegrable 0 R) (hf.intervalIntegrable R t)
      rw [hzint,add_zero] at hadd
      unfold primitive
      rw [← hadd]
      exact hinside R (by rw [abs_of_nonneg hR])
    · have htR : t≤-R := by rw [abs_of_nonpos hneg] at ht;linarith
      have hzint : (∫ s in (-R)..t,f s)=0 := by
        calc
          _ = ∫ _s in (-R)..t,(0:ℝ) := intervalIntegral.integral_congr (fun s hs => by
            rw [uIcc_of_ge htR] at hs
            apply hz s
            linarith [neg_le_abs s,hs.2])
          _ = 0 := by simp
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
        (hf.intervalIntegrable 0 (-R)) (hf.intervalIntegrable (-R) t)
      rw [hzint,add_zero] at hadd
      unfold primitive
      rw [← hadd]
      exact hinside (-R) (by rw [abs_neg,abs_of_nonneg hR])

theorem positiveReceiverSlope_zero_left (A ν g h hp t : ℝ) (hh : 0<h) (ht : t≤0) :
    positiveReceiverSlope A ν g h hp t=0 := by
  have he : receiverGate (t/h)=0 := receiverGate_zero (by
    have := div_nonpos_of_nonpos_of_nonneg ht hh.le
    linarith)
  simp [positiveReceiverSlope,he]

theorem positiveReceiverSlope_zero_right (A ν g h hp t : ℝ) (hhp : 0<hp) (ht : 3*hp≤t) :
    positiveReceiverSlope A ν g h hp t=0 := by
  have he : positiveTail (t/hp)=0 := positiveTail_zero ((le_div_iff₀ hhp).mpr ht)
  simp [positiveReceiverSlope,he]

theorem negativeReceiverSlope_zero_right (A g h T t : ℝ) (hh : 0<h) (ht : 0≤t) :
    negativeReceiverSlope A g h T t=0 := by
  have he : receiverGate (-t/h)=0 := receiverGate_zero (by
    have := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hh.le
    linarith)
  simp [negativeReceiverSlope,he]

theorem negativeReceiverSlope_zero_left (A g h T t : ℝ) (hT : 0<T) (ht : t≤-(2*T)) :
    negativeReceiverSlope A g h T t=0 := by
  have he : negativeTail (-t/T)=0 := negativeTail_zero ((le_div_iff₀ hT).mpr (by linarith))
  simp [negativeReceiverSlope,he]

theorem positiveReceiverSlope_abs_bound (A ν g h hp t : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) :
    |positiveReceiverSlope A ν g h hp t|≤A*(3*ν*hp+g) := by
  by_cases ht : t≤0
  · rw [positiveReceiverSlope_zero_left A ν g h hp t hh ht,abs_zero]
    positivity
  by_cases htp : 3*hp≤t
  · rw [positiveReceiverSlope_zero_right A ν g h hp t hhp htp,abs_zero]
    positivity
  have htg : 0≤ν*t+g := add_nonneg (mul_nonneg hν (le_of_lt (lt_of_not_ge ht))) hg
  have hgate := mul_le_one₀ (receiverGate_range (t/h)).2 (positiveTail_range (t/hp)).1 (positiveTail_range (t/hp)).2
  have hh₁ := mul_le_mul_of_nonneg_left hgate (mul_nonneg hA htg)
  have hh₂ := mul_le_mul_of_nonneg_left
    (show ν*t+g≤3*ν*hp+g by nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge htp) hν]) hA
  rw [positiveReceiverSlope,abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg hA,
    abs_of_nonneg htg,abs_of_nonneg (receiverGate_range _).1,abs_of_nonneg (positiveTail_range _).1]
  nlinarith

theorem negativeReceiverSlope_abs_bound (A g h T t : ℝ) (hA : 0≤A) (hg : 0≤g) :
    |negativeReceiverSlope A g h T t|≤A*g := by
  have hgate := mul_le_one₀ (receiverGate_range (-t/h)).2 (negativeTail_range (-t/T)).1 (negativeTail_range (-t/T)).2
  have hh := mul_le_mul_of_nonneg_left hgate (mul_nonneg hA hg)
  rw [negativeReceiverSlope,abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg hA,
    abs_of_nonneg hg,abs_of_nonneg (receiverGate_range _).1,abs_of_nonneg (negativeTail_range _).1]
  nlinarith

theorem positiveReceiver_abs_bound (A ν g h hp t : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) :
    |positiveReceiver A ν g h hp t|≤(A*(3*ν*hp+g))*(3*hp) := by
  apply primitive_bound_of_support (positiveReceiverSlope_contDiff A ν g h hp (k:=0)).continuous
    (3*hp) (A*(3*ν*hp+g)) (by positivity) (by positivity)
    (fun s => positiveReceiverSlope_abs_bound A ν g h hp s hA hν hg hh hhp)
  intro s hs
  rcases le_total 0 s with hspos|hn
  · exact positiveReceiverSlope_zero_right A ν g h hp s hhp (by simpa only [abs_of_nonneg hspos] using hs)
  · exact positiveReceiverSlope_zero_left A ν g h hp s hh hn

theorem negativeReceiver_abs_bound (A g h T t : ℝ)
    (hA : 0≤A) (hg : 0≤g) (hh : 0<h) (hT : 0<T) :
    |negativeReceiver A g h T t|≤(A*g)*(2*T) := by
  apply primitive_bound_of_support (negativeReceiverSlope_contDiff A g h T (k:=0)).continuous
    (2*T) (A*g) (by positivity) (by positivity)
    (fun s => negativeReceiverSlope_abs_bound A g h T s hA hg)
  intro s hs
  rcases le_total 0 s with hp|hn
  · exact negativeReceiverSlope_zero_right A g h T s hh hp
  · apply negativeReceiverSlope_zero_left A g h T s hT
    rw [abs_of_nonpos hn] at hs
    linarith

end Bilevel.ChiBoundedChain
