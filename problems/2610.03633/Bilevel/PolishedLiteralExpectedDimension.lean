import Bilevel.PolishedLiteralObserverActivation

/-! A single source dimension choice at the floor horizon suffices for
every cap used by the expected-query reduction. -/
namespace Bilevel.PolishedProjectionDimension
set_option autoImplicit false

theorem sourceDimension_mono {m n K : ℕ} (hm : 0<m) (hK : 0<K) (hmn : m≤n)
    (R τ δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    sourceDimension m K R τ δ≤sourceDimension n K R τ δ := by
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hK1 : (1:ℝ)≤K := by exact_mod_cast hK
  have hmn' : (m:ℝ)≤n := by exact_mod_cast hmn
  have hC : 0≤(K:ℝ)+R^2/τ^2 := by positivity
  have harg : 1≤16*(m:ℝ)*K/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hlog : 0≤Real.log (16*(m:ℝ)*K/δ) := Real.log_nonneg harg
  have hargs : 16*(m:ℝ)*K/δ≤16*(n:ℝ)*K/δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    nlinarith
  have hlogs := Real.log_le_log (by positivity : (0:ℝ)<16*(m:ℝ)*K/δ) hargs
  have hcoeff := mul_le_mul_of_nonneg_right hmn' hC
  have hs := mul_le_mul hcoeff hlogs hlog (mul_nonneg (Nat.cast_nonneg n) hC)
  unfold sourceDimension
  nlinarith

theorem horizon_le_ceil (n T : ℕ) (p : ℝ) (hn : (n:ℝ)≤(T:ℝ)/(16*p)) :
    n≤⌈(T:ℝ)/(16*p)⌉₊ := by
  have hh := hn.trans (Nat.le_ceil ((T:ℝ)/(16*p)))
  exact_mod_cast hh


theorem horizon_le_floor (n T : ℕ) (p : ℝ) (hp : 0<p)
    (hn : (n:ℝ)≤(T:ℝ)/(16*p)) : n≤⌊(T:ℝ)/(16*p)⌋₊ := by
  exact (Nat.le_floor_iff (by positivity : (0:ℝ)≤(T:ℝ)/(16*p))).mpr hn

end Bilevel.PolishedProjectionDimension
