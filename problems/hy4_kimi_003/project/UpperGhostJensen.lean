import Mathlib

open MeasureTheory Metric

namespace Task006.UpperGhostJensen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_convex_step {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f)
    (u x : E) (hu : u ∈ K) (hx : x ∈ K) (n : ℝ) (hn : 0 ≤ n) :
    (n+1)*f ((n/(n+1)) • u + (1/(n+1)) • x) ≤ n*f u+f x := by
  have hd : 0 < n+1 := by linarith
  have hw : n/(n+1)+1/(n+1)=1 := by field_simp
  have hc := hf.2 hu hx (div_nonneg hn hd.le) (div_nonneg (by norm_num) hd.le) hw
  have hm := mul_le_mul_of_nonneg_left hc hd.le
  have he : (n+1)*(n/(n+1)*f u+1/(n+1)*f x) = n*f u+f x := by
    field_simp
  simpa only [smul_eq_mul,he] using hm

theorem running_average_step {f : E → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ConvexOn ℝ (closedBall (0 : E) r) f)
    (x sum z : E) (n : ℕ) (hx : ‖x‖ ≤ r) (hsum : ‖sum‖ ≤ (n : ℝ)*r) :
    ((n+1 : ℕ) : ℝ)*(f (((n+1 : ℕ) : ℝ)⁻¹ • (sum+x))-f z) ≤
      (n : ℝ)*(f ((n : ℝ)⁻¹ • sum)-f z)+(f x-f z) := by
  by_cases hn : n = 0
  · subst n
    have hs : sum = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hsum) (norm_nonneg sum))
    simp [hs]
  · have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hden : (n : ℝ)+1 ≠ 0 := by positivity
    have hu : ‖(n : ℝ)⁻¹ • sum‖ ≤ r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hnp.le)]
      calc
        _ ≤ (n : ℝ)⁻¹*((n : ℝ)*r) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnp.le)
        _ = r := by field_simp
    have hK : (n : ℝ)⁻¹ • sum ∈ closedBall (0 : E) r := by simpa using hu
    have hxK : x ∈ closedBall (0 : E) r := by simpa using hx
    have hc := weighted_convex_step hf ((n : ℝ)⁻¹ • sum) x hK hxK n hnp.le
    have he : ((n : ℝ)/((n : ℝ)+1)) • ((n : ℝ)⁻¹ • sum) +
        (1/((n : ℝ)+1)) • x = ((n : ℝ)+1)⁻¹ • (sum+x) := by
      rw [smul_smul,smul_add]
      have hcoef : ((n : ℝ)/((n : ℝ)+1))*(n : ℝ)⁻¹ = ((n : ℝ)+1)⁻¹ := by field_simp
      rw [hcoef,one_div]
    rw [he] at hc
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith

theorem average_sequence_telescope (avg Δ : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ n < T, ((n+1 : ℕ) : ℝ)*avg (n+1) ≤ (n : ℝ)*avg n+Δ n) :
    (T : ℝ)*avg T ≤ ∑ n ∈ Finset.range T, Δ n := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hp := ih (fun n hn => hstep n (by omega))
    have hs := hstep T (by omega)
    rw [Finset.sum_range_succ]
    linarith

end Task006.UpperGhostJensen
