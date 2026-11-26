import RandomizedFO2003.SmoothSaturation

namespace RandomizedFO2003.Cascade

open Primitives

/-- Eliminating the outgoing gate term gives a fixed saturation threshold.
The value 12416 is `2*64 + 2*4096 + 64^2`, using the proved spectral ranges. -/
theorem projected_saturation_bound (q v c s k r w δa δb K : ℝ)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 ≤ s) (hs64 : s ≤ 64)
    (hk : 1 ≤ k) (hk4096 : k ≤ 4096) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hda : |δa| ≤ 1) (hdb : |δb| ≤ 1)
    (ha : δa = v - c * s * saturationSlope K q - k * (w * deriv Primitives.gate v))
    (hb : δb = q - c * r * saturationSlope K q - s * (w * deriv Primitives.gate v)) :
    |q| ≤ 12416 := by
  have ht := saturationSlope_mem K hK q
  have ht1 : |saturationSlope K q| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  by_cases hgate : deriv Primitives.gate v = 0
  · rw [hgate, mul_zero, mul_zero, sub_zero] at hb
    have hcr0 : 0 ≤ c * r := mul_nonneg hc hr
    have hcr1 : c * r ≤ 1 := (mul_le_of_le_one_left hr hc1).trans hr1
    have hcrt0 : 0 ≤ c * r * saturationSlope K q := mul_nonneg hcr0 ht.1
    have hcrt1 : c * r * saturationSlope K q ≤ 1 := (mul_le_of_le_one_left ht.1 hcr1).trans ht.2
    have hdb' := abs_le.mp hdb
    apply abs_le.mpr
    constructor <;> linarith [hdb'.1, hdb'.2]
  · have hvI := gate_deriv_support (show v ∈ Function.support (deriv Primitives.gate) from hgate)
    have hv : |v| ≤ 1 := abs_le.mpr ⟨by linarith [hvI.1], by linarith [hvI.2]⟩
    have h := RandomizedFO2003.saturation_bound q v c s k r (saturationSlope K q)
      (w * deriv Primitives.gate v) δa δb 64 4096 ha hb hk hk4096 hs hs64 hc hc1 hr hr1 ht1 hv hda hdb
    norm_num at h
    exact h

theorem projected_activation_bound (q v c s k r w δa δb K : ℝ)
    (hK : 12416 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 1 ≤ s) (hs64 : s ≤ 64)
    (hk : 1 ≤ k) (hk4096 : k ≤ 4096) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hw : 0 ≤ w)
    (hda : |δa| ≤ 1 / 8) (hdb : |δb| ≤ 1)
    (ha : δa = v - c * s * saturationSlope K q - k * (w * deriv Primitives.gate v))
    (hb : δb = q - c * r * saturationSlope K q - s * (w * deriv Primitives.gate v)) :
    |q| ≤ K ∧ saturationSlope K q = 1 ∧ c * s - 1 / 8 ≤ v := by
  have hK0 : 0 ≤ K := by linarith
  have hq := (projected_saturation_bound q v c s k r w δa δb K hK0 hc hc1 (by linarith) hs64
    hk hk4096 hr hr1 (hda.trans (by norm_num)) hdb ha hb).trans hK
  have ht := saturationSlope_one hq
  refine ⟨hq, ht, ?_⟩
  rw [ht, mul_one] at ha
  have hout : 0 ≤ k * (w * deriv Primitives.gate v) :=
    mul_nonneg (by linarith) (mul_nonneg hw (gate_deriv_nonneg v))
  have hlow := (abs_le.mp hda).1
  linarith

end RandomizedFO2003.Cascade
