import InverseStability254

noncomputable section
namespace Paper254

/-- Finite-precision Newton iterates remain invertible without a common
eigenbasis. The rounding error is charged at every intermediate state. -/
theorem rounded_newton_trajectory {R : Type*} [NormedRing R] [Nontrivial R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
    (A : R) (x : ℕ → Rˣ) (y : ℕ → R) (N : ℕ) (M K h : ℝ)
    (hM : 0<M) (hK : 1≤K) (hh : 0≤h)
    (hstart : y 0=(x 0:R))
    (hnext : ∀ k<N,(x (k+1):R)=algebraNewtonStep A (x k:R))
    (hinv : ∀ k≤N,‖(↑(x k)⁻¹:R)‖≤M)
    (hlip : (1+2*M^2*‖A‖)/2≤K)
    (hround : ∀ k<N,‖y (k+1)-algebraNewtonStep A (y k)‖≤h)
    (hguard : h*(2*K)^N*M≤1/2) :
    ∀ k≤N, ‖y k-(x k:R)‖≤h*(2*K)^k ∧ IsUnit (y k) := by
  have hbase : 1≤2*K := by linarith
  have hK0 : 0≤K := by linarith
  have small : ∀ k≤N,h*(2*K)^k*M≤1/2 := by
    intro k hk
    have hp := pow_le_pow_right₀ hbase hk
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hh) hM.le).trans hguard
  intro k
  induction k with
  | zero =>
    intro _
    rw [hstart,sub_self,norm_zero]
    exact ⟨by positivity,(x 0).isUnit⟩
  | succ k ih =>
    intro hk
    have hkN : k<N := by omega
    have hkN' : k≤N := by omega
    obtain ⟨he,_⟩ := ih hkN'
    have hnear : ‖y k-(x k:R)‖*M≤1/2 :=
      (mul_le_mul_of_nonneg_right he hM.le).trans (small k hkN')
    have hs := (algebraNewtonStep_stability A (x k) (y k) M hM (hinv k hkN') hnear).2
    have htri := norm_sub_le_norm_sub_add_norm_sub (y (k+1)) (algebraNewtonStep A (y k)) (x (k+1):R)
    rw [hnext k hkN] at htri
    have hm := mul_le_mul_of_nonneg_right hlip (norm_nonneg (y k-(x k:R)))
    have hm2 := mul_le_mul_of_nonneg_left he hK0
    have hp : 1≤(2*K)^k := one_le_pow₀ hbase
    have hprod : h≤K*(h*(2*K)^k) := by
      have hpk : 1≤K*(2*K)^k := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hpk hh]
    have herr : ‖y (k+1)-(x (k+1):R)‖≤h*(2*K)^(k+1) := by
      rw [hnext k hkN, pow_succ]
      nlinarith [hround k hkN]
    refine ⟨herr,?_⟩
    exact (inverse_perturbation (x (k+1)) (y (k+1)) M hM (hinv (k+1) hk)
      ((mul_le_mul_of_nonneg_right herr hM.le).trans (small (k+1) hk))).1

/-- The precision budget grows linearly in the iteration count and in
the logarithms of the inverse and Lipschitz bounds. -/
theorem newton_guard_power_identity (a b m s N : ℕ) :
    (2:ℝ)^a*((2:ℝ)^(a+(b+1)*N+m+s+2))⁻¹ *
      (2*(2:ℝ)^b)^N*(2:ℝ)^m = ((2:ℝ)^(s+2))⁻¹ := by
  rw [show 2*(2:ℝ)^b=(2:ℝ)^(b+1) by rw [pow_succ]; ring]
  rw [← pow_mul]
  simp only [pow_add]
  field_simp

theorem dyadic_newton_guard (a b m s N : ℕ) (d M K : ℝ)
    (hd : 0≤d) (hM : 0≤M) (hK : 0≤K)
    (hdB : d≤(2:ℝ)^a) (hMB : M≤(2:ℝ)^m) (hKB : K≤(2:ℝ)^b) :
    d*((2:ℝ)^(a+(b+1)*N+m+s+2))⁻¹*(2*K)^N*M≤((2:ℝ)^(s+2))⁻¹ := by
  rw [← newton_guard_power_identity a b m s N]
  gcongr

theorem dyadic_newton_error (a b m s N : ℕ) (d K : ℝ)
    (hd : 0≤d) (hK : 0≤K) (hdB : d≤(2:ℝ)^a) (hKB : K≤(2:ℝ)^b) :
    d*((2:ℝ)^(a+(b+1)*N+m+s+2))⁻¹*(2*K)^N≤((2:ℝ)^(s+2))⁻¹ := by
  have hg := dyadic_newton_guard a b m s N d ((2:ℝ)^m) K hd (by positivity) hK
    hdB le_rfl hKB
  have hm : 1≤(2:ℝ)^m := one_le_pow₀ (by norm_num)
  have hn : 0≤d*((2:ℝ)^(a+(b+1)*N+m+s+2))⁻¹*(2*K)^N := by positivity
  nlinarith

end Paper254
#print axioms Paper254.rounded_newton_trajectory
#print axioms Paper254.newton_guard_power_identity
