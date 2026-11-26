import RationalOneStep254
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology
namespace Paper254

theorem dyadic_inverse_tends_zero : Tendsto (fun r : ℕ=>((2:ℝ)^r)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  simpa only [div_pow,one_pow,one_div,inv_pow] using h

theorem uniform_history_errors_tend_zero (d a b : ℕ) (D lo hi G lam : ℝ)
    (loQ hiQ : ℚ) :
    Tendsto (fun r=>actualHistoryLocalError d D lo hi G lam
      (uniformHistoryParameters a b r r loQ hiQ) (((2:ℝ)^(r+2))⁻¹)) atTop (𝓝 0) := by
  let cfg := fun r=>uniformHistoryParameters a b r r loQ hiQ
  let margin := fun r : ℕ=>((2:ℝ)^(r+2))⁻¹
  let c : ℝ := ((2:ℝ)^(3*a+b+6))⁻¹
  have hbase := dyadic_inverse_tends_zero
  have hn : Tendsto (fun r=>((2:ℝ)^(3*a+b+r+6))⁻¹) atTop (𝓝 0) := by
    have hh := hbase.const_mul c
    simp only [mul_zero] at hh
    convert hh using 1
    ext r
    dsimp [c]
    rw [show 3*a+b+r+6=(3*a+b+6)+r by omega,pow_add,mul_inv]
  have hm : Tendsto margin atTop (𝓝 0) := by
    have hh := hbase.div_const 4
    simp only [zero_div] at hh
    convert hh using 1
    ext r
    dsimp [margin]
    rw [pow_add,mul_inv]
    norm_num
    ring
  have hc : Tendsto (fun r=>historyCovError d (cfg r) (margin r)) atTop (𝓝 0) := by
    have hh := ((hn.add hn).add (hn.const_mul ((d:ℝ)^2))).add (hm.const_mul ((d:ℝ)^2))
    simp only [add_zero,mul_zero] at hh
    convert hh using 1
    ext r
    simp only [historyCovError,cfg,uniformHistoryParameters,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat]
    ring
  have he : Tendsto (fun r=>historyPrecisionError d lo (cfg r) (margin r)) atTop (𝓝 0) := by
    simpa only [historyPrecisionError,mul_zero] using hc.const_mul (((d:ℝ)^3/lo)^2*d)
  let R := uniformHistoryRadius d D hi G lam
  have hmean : Tendsto (fun r=>historyMeanError d lo hi R (cfg r) (margin r)) atTop (𝓝 0) := by
    have hleft := (he.add hn).mul_const (R^2)
    have hright := (((hn.const_add ((d:ℝ)^2/lo)).const_mul (2*R)).mul hn)
    have hsum := (hbase.add ((hleft.add hright).const_mul (2*(d:ℝ)^2))).div_const (1/hi)
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    simp only [add_zero,mul_zero,zero_mul,zero_div,Real.sqrt_zero] at hh
    convert hh using 1
    ext r
    simp only [historyMeanError,cfg,uniformHistoryParameters]
    congr 1
    ring
  have hsum := (((he.const_mul (lo*d)).add
    (he.const_mul ((Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*(max 1 ((d:ℝ)^2/lo))^d/((1/hi)^d)))).add
      (((he.mul_const (D^2)).add (hmean.const_mul (2*(max 1 ((d:ℝ)^2/lo))*D))).const_mul ((d:ℝ)^2))).div_const 2
  simp only [mul_zero,zero_mul,zero_div,add_zero] at hsum
  convert hsum using 1
  ext r
  dsimp [actualHistoryLocalError,numericalKLError,R,cfg,margin]
  ring

/-- A single precision works uniformly in time and over all states obeying
the same covariance/gradient bounds. This is an existence theorem, not a
polynomial bit-cost claim. -/
theorem exists_uniform_history_budget (d a b : ℕ) (D G lam : ℝ) (lo hi : ℚ)
    (hgap : (lo:ℝ)<(hi:ℝ)) (eps : ℝ) (heps : 0<eps) :
    ∃ r : ℕ,((2:ℝ)^r)⁻¹≤(hi:ℝ)-(lo:ℝ) ∧
      actualHistoryLocalError d D (lo:ℝ) (hi:ℝ) G lam
        (uniformHistoryParameters a b r r lo hi) (((2:ℝ)^(r+2))⁻¹)≤eps := by
  have hsmall := (dyadic_inverse_tends_zero.eventually (gt_mem_nhds (sub_pos.mpr hgap)))
  have he := (uniform_history_errors_tend_zero d a b D (lo:ℝ) (hi:ℝ) G lam lo hi).eventually
    (gt_mem_nhds heps)
  obtain ⟨r,hr,her⟩ := (hsmall.and he).exists
  exact ⟨r,hr.le,her.le⟩

end Paper254
#print axioms Paper254.exists_uniform_history_budget
