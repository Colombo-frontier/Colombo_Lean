import Mathlib
/-! Exact scale identities, for positive actual clipping parameters. -/
namespace Task006.UpperPublicScale

lemma rpow_combine {x : ℝ} (hx : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a+b) :=
  (Real.rpow_add hx a b).symm

lemma clip_scale_identities {d m t : ℝ} (hd : 0 ≤ d) (hm : 0 < m) (ht : 0 < t) :
    let b := (m*t) ^ (2/3:ℝ)
    let B := Real.sqrt d * m ^ (2/3:ℝ) * t ^ (-1/3:ℝ)
    Real.sqrt d * m * b ^ (-1/2:ℝ) = B ∧
      Real.sqrt d * b = t * B ∧
      d*m*b ^ (1/2:ℝ) = t*B^2 ∧
      d*b^2 = t^2*B^2 := by
  dsimp only
  have hm₁ : m * m ^ (-1/3:ℝ) = m ^ (2/3:ℝ) := by
    calc
      _ = m ^ (1:ℝ) * m ^ (-1/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [rpow_combine hm]; norm_num
  have ht₁ : t * t ^ (-1/3:ℝ) = t ^ (2/3:ℝ) := by
    calc
      _ = t ^ (1:ℝ) * t ^ (-1/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [rpow_combine ht]; norm_num
  have hbroot : ((m*t) ^ (2/3:ℝ)) ^ (-1/2:ℝ) =
      m ^ (-1/3:ℝ) * t ^ (-1/3:ℝ) := by
    rw [← Real.rpow_mul (mul_pos hm ht).le]
    norm_num
    rw [Real.mul_rpow hm.le ht.le]
  have hb : (m*t) ^ (2/3:ℝ) = m ^ (2/3:ℝ) * t ^ (2/3:ℝ) := Real.mul_rpow hm.le ht.le
  have hbone : ((m*t) ^ (2/3:ℝ)) ^ (1/2:ℝ) =
      m ^ (1/3:ℝ) * t ^ (1/3:ℝ) := by
    rw [← Real.rpow_mul (mul_pos hm ht).le]
    norm_num
    rw [Real.mul_rpow hm.le ht.le]
  have hm₂ : (m ^ (2/3:ℝ)) ^ 2 = m ^ (4/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    norm_num
  have ht₂ : (t ^ (-1/3:ℝ)) ^ 2 = t ^ (-2/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hm₃ : m * m ^ (1/3:ℝ) = m ^ (4/3:ℝ) := by
    calc
      _ = m ^ (1:ℝ) * m ^ (1/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [rpow_combine hm]; norm_num
  have ht₃ : t * t ^ (-2/3:ℝ) = t ^ (1/3:ℝ) := by
    calc
      _ = t ^ (1:ℝ) * t ^ (-2/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [rpow_combine ht]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbroot]
    calc
      _ = Real.sqrt d * (m*m ^ (-1/3:ℝ)) * t ^ (-1/3:ℝ) := by ring
      _ = _ := by rw [hm₁]
  · rw [hb]
    calc
      _ = Real.sqrt d * m ^ (2/3:ℝ) * (t*t ^ (-1/3:ℝ)) := by rw [ht₁]; ring
      _ = _ := by ring
  · rw [hbone, mul_pow, mul_pow, Real.sq_sqrt hd, hm₂, ht₂]
    calc
      _ = d * (m*m ^ (1/3:ℝ)) * t ^ (1/3:ℝ) := by ring
      _ = d * m ^ (4/3:ℝ) * (t*t ^ (-2/3:ℝ)) := by rw [hm₃, ht₃]
      _ = _ := by ring
  · have hsecond : Real.sqrt d * ((m*t) ^ (2/3:ℝ)) =
        t * (Real.sqrt d * m ^ (2/3:ℝ) * t ^ (-1/3:ℝ)) := by
      rw [hb]
      calc
        _ = Real.sqrt d * m ^ (2/3:ℝ) * (t*t ^ (-1/3:ℝ)) := by rw [ht₁]; ring
        _ = _ := by ring
    have hh := congrArg (fun z : ℝ => z^2) hsecond
    simpa only [mul_pow, Real.sq_sqrt hd] using hh

/-- The public cubic round lower bound gives the precise clipping allowance. -/
lemma bias_scale_accuracy {C L A s t : ℝ} (hC : 0 < C) (hL : 0 < L) (hA : 0 < A)
    (hs : 0 < s) (ht : 0 < t)
    (hlower : 1728*C^2*A^3*s^(3/2:ℝ) ≤ t) :
    A * (C^(2/3:ℝ)*L*Real.sqrt s*t^(-1/3:ℝ)) ≤ L/12 := by
  have hCpow : (C^(2/3:ℝ))^3 = C^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC.le]
    norm_num
  have hspow : (Real.sqrt s)^3 = s^(3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  have htpow : (t^(-1/3:ℝ))^3 = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num [Real.rpow_neg_one]
  have heq : (12*A*(C^(2/3:ℝ)*L*Real.sqrt s*t^(-1/3:ℝ)))^3 =
      (1728*C^2*A^3*s^(3/2:ℝ))/t*L^3 := by
    simp only [mul_pow, hCpow, hspow, htpow]
    ring
  have hle : (12*A*(C^(2/3:ℝ)*L*Real.sqrt s*t^(-1/3:ℝ)))^3 ≤ L^3 := by
    rw [heq]
    have hh : (1728*C^2*A^3*s^(3/2:ℝ))/t ≤ 1 := (div_le_one ht).2 hlower
    exact (mul_le_mul_of_nonneg_right hh (pow_nonneg hL.le 3)).trans_eq (one_mul _)
  have hroot := le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) hL.le hle
  linarith

end Task006.UpperPublicScale

