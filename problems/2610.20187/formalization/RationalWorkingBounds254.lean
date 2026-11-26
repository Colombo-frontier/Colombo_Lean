import RationalMagnitude254
import RationalScaleGrid254
import StandardRationalPrefix254

noncomputable section
namespace Paper254

def workingMagnitude (d T b : ℕ) : ℕ :=
  b+d+2*(scaleCount T+1)+(Nat.log 2 (T+1)+1)+4

theorem workingMagnitude_basic (d T b : ℕ) :
    1≤workingMagnitude d T b ∧ b≤workingMagnitude d T b ∧
    (d:ℝ)≤(2:ℝ)^workingMagnitude d T b ∧
    (standardLiveCap T (scaleCount T):ℝ)≤(2:ℝ)^workingMagnitude d T b := by
  have hdb : (d:ℝ)≤(2:ℝ)^d := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n:=d))
  let J := Nat.log 2 (T+1)+1
  let K := scaleCount T+1
  have hJ : (J:ℝ)≤(2:ℝ)^J := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n:=J))
  have hK : (K:ℝ)≤(2:ℝ)^K := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n:=K))
  refine ⟨by dsimp [workingMagnitude]; omega,by dsimp [workingMagnitude]; omega,
    hdb.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [workingMagnitude]; omega)),?_⟩
  have hh : (standardLiveCap T (scaleCount T):ℝ)≤(2:ℝ)^(3+J+K) := by
    change ((5*J*K:ℕ):ℝ)≤_
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ 8*((2:ℝ)^J)*((2:ℝ)^K) := by gcongr; norm_num
      _ = _ := by simp only [pow_add]; norm_num
  exact hh.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [workingMagnitude,J,K]; omega))

theorem capped_variance_magnitude (d T b : ℕ) (H : ℚ) (hH : 0<(H:ℝ))
    (hheight : RationalHeight H b) (k : Fin (scaleCount T+1)) :
    (rationalCappedVariance H k.val:ℝ)⁻¹≤(2:ℝ)^workingMagnitude d T b ∧
    ((H:ℝ)-(rationalCappedVariance H k.val:ℝ))⁻¹≤(2:ℝ)^workingMagnitude d T b := by
  let K := scaleCount T+1
  let q : ℝ := (rationalCappedVariance H k.val:ℝ)
  have hk : k.val≤K := by dsimp [K]; omega
  have hK : 1≤K := by dsimp [K]; omega
  have hform : q=min ((H:ℝ)/((2:ℝ)^k.val)^2) ((H:ℝ)/4) := by
    dsimp [q,rationalCappedVariance]
    push_cast
    rfl
  have hq : 0<q := by rw [hform]; apply lt_min <;> positivity
  have hden : ((2:ℝ)^k.val)^2≤(2:ℝ)^(2*K) := by
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hfour : (4:ℝ)≤2^(2*K) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 2≤2*K)
    norm_num at hh ⊢
    exact hh
  have hlower : (H:ℝ)/(2:ℝ)^(2*K)≤q := by
    rw [hform]
    exact le_min (div_le_div_of_nonneg_left hH.le (by positivity) hden)
      (div_le_div_of_nonneg_left hH.le (by norm_num) hfour)
  have hquarter : q≤(H:ℝ)/4 := by rw [hform]; exact min_le_right _ _
  have hinv : (H:ℝ)⁻¹≤(2:ℝ)^b := by
    simpa only [abs_of_pos (inv_pos.mpr hH)] using hheight.inverse_real_abs
  have hscale : q⁻¹≤(2:ℝ)^(b+2*K) := by
    have hh := (inv_le_inv₀ hq (div_pos hH (by positivity))).mpr hlower
    rw [inv_div,div_eq_mul_inv] at hh
    calc
      q⁻¹≤(2:ℝ)^(2*K)*(H:ℝ)⁻¹ := hh
      _ ≤ (2:ℝ)^(2*K)*2^b := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hgap : 0<(H:ℝ)-q := by linarith
  have hgapb : ((H:ℝ)-q)⁻¹≤(2:ℝ)^(b+1) := by
    have hh := (inv_le_inv₀ hgap (div_pos hH (by norm_num : (0:ℝ)<2))).mpr
      (show (H:ℝ)/2≤(H:ℝ)-q by linarith)
    rw [inv_div,div_eq_mul_inv] at hh
    calc
      _ ≤ 2*(H:ℝ)⁻¹ := hh
      _ ≤ 2*(2:ℝ)^b := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = _ := by rw [pow_succ]; ring
  exact ⟨hscale.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [workingMagnitude,K]; omega)),
    hgapb.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [workingMagnitude]; omega))⟩

theorem working_error_budget (T ell z : ℕ) (lam delta : ℝ) (hT : 0<T)
    (hlam : ((2:ℝ)^ell)⁻¹≤lam) (hdelta : ((2:ℝ)^z)⁻¹≤delta) :
    ((2:ℝ)^(ell+z+Nat.log 2 T+2))⁻¹≤lam*delta/(2*T) := by
  have hTpow : (T:ℝ)≤(2:ℝ)^(Nat.log 2 T+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1<2) T).le
  have hprod := mul_le_mul hlam hdelta (by positivity : 0≤((2:ℝ)^z)⁻¹)
    (lt_of_lt_of_le (by positivity) hlam).le
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*T)).mpr
  have hh := mul_le_mul_of_nonneg_left hTpow (show 0≤2*((2:ℝ)^(ell+z+Nat.log 2 T+2))⁻¹ by positivity)
  have he : 2*((2:ℝ)^(ell+z+Nat.log 2 T+2))⁻¹*((2:ℝ)^(Nat.log 2 T+1))=
      ((2:ℝ)^ell)⁻¹*((2:ℝ)^z)⁻¹ := by
    simp only [pow_add,pow_succ]
    field_simp
  rw [he] at hh
  exact (by nlinarith : ((2:ℝ)^(ell+z+Nat.log 2 T+2))⁻¹*(2*T)≤
    ((2:ℝ)^ell)⁻¹*((2:ℝ)^z)⁻¹).trans hprod

end Paper254
#print axioms Paper254.capped_variance_magnitude
#print axioms Paper254.working_error_budget
