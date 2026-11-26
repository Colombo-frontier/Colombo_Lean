import GradientHessian.ForkChronologicalProbability

/-! Absolute constants for the marked-task lifetime. The arithmetic uses
the literal synthesized-readout degree and the proved sphere-column tail. -/

namespace GradientHessian.ForkLifetime
open Matrix MeasureTheory LowRank
noncomputable section

def gamma : ℝ := 1/3072
def overlapScale : ℝ := 2048/gamma^2
def lifetimeFraction : ℝ := 1/(8192*overlapScale)
def rankRatio : ℝ := 8192*overlapScale*(ReadoutFilter.degreeConstant+3)+12288
def depthThreshold : ℕ := ⌈32768*overlapScale⌉₊
def lifetime (J : ℕ) : ℕ := ⌊lifetimeFraction*(J:ℝ)⌋₊
def preBudget (J q₀ S : ℕ) : ℕ := q₀+S*ReadoutFilter.degree (ReadoutFilter.matrixUpper J) ReadoutFilter.delta

theorem gamma_pos : 0 < gamma := by norm_num [gamma]
theorem overlapScale_ge_one : 1 ≤ overlapScale := by norm_num [overlapScale,gamma]
theorem overlapScale_pos : 0 < overlapScale := lt_of_lt_of_le zero_lt_one overlapScale_ge_one
theorem lifetimeFraction_pos : 0 < lifetimeFraction := by
  have hA := overlapScale_pos
  unfold lifetimeFraction
  positivity
theorem lifetimeFraction_le : lifetimeFraction ≤ 1/8 := by norm_num [lifetimeFraction,overlapScale,gamma]
theorem rankRatio_ge : 12288 ≤ rankRatio := by
  unfold rankRatio
  have hc := ReadoutFilter.degreeConstant_pos
  have hA := overlapScale_pos
  have h : 0 ≤ 8192*overlapScale*(ReadoutFilter.degreeConstant+3) := by positivity
  linarith
theorem rankRatio_pos : 0 < rankRatio := lt_of_lt_of_le (by norm_num) rankRatio_ge
theorem depthThreshold_pos : 0 < depthThreshold := by
  have h := Nat.le_ceil (32768*overlapScale)
  have ha := overlapScale_ge_one
  by_contra hn
  have hz : depthThreshold = 0 := by omega
  change 32768*overlapScale ≤ (depthThreshold:ℝ) at h
  rw [hz] at h
  norm_num at h
  linarith

theorem depth_lower {J : ℕ} (hJ : depthThreshold ≤ J) : 32768*overlapScale ≤ (J:ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast hJ)

theorem lifetime_bounds {J : ℕ} (hJ : depthThreshold ≤ J) :
    (lifetimeFraction/2)*(J:ℝ) ≤ lifetime J ∧
      1 ≤ (lifetimeFraction/2)*(J:ℝ) ∧
      (lifetime J:ℝ) ≤ lifetimeFraction*(J:ℝ) := by
  have hA := overlapScale_pos
  have hd := depth_lower hJ
  have hmul : 2 ≤ lifetimeFraction*(J:ℝ) := by
    unfold lifetimeFraction
    calc
      2 ≤ (J:ℝ)/(8192*overlapScale) :=
        (le_div_iff₀ (by positivity)).mpr (by linarith)
      _ = _ := by ring
  have hu : (lifetime J:ℝ) ≤ lifetimeFraction*(J:ℝ) :=
    Nat.floor_le (mul_nonneg lifetimeFraction_pos.le (Nat.cast_nonneg J))
  have hl : lifetimeFraction*(J:ℝ) < (lifetime J:ℝ)+1 := Nat.lt_floor_add_one _
  exact ⟨by linarith,by linarith,hu⟩

theorem preBudget_le {M J q₀ S : ℕ} (hM : 1 ≤ M) (hJ : 1 ≤ J)
    (hS : S ≤ M) (hq : q₀ ≤ M*lifetime J+1) :
    (preBudget J q₀ S:ℝ) ≤ (M:ℝ)*(ReadoutFilter.degreeConstant+lifetimeFraction+2)*J := by
  have hqR : (q₀:ℝ) ≤ (M:ℝ)*lifetime J+1 := by exact_mod_cast hq
  have hl := Nat.floor_le (mul_nonneg lifetimeFraction_pos.le (Nat.cast_nonneg J))
  change (lifetime J:ℝ) ≤ lifetimeFraction*(J:ℝ) at hl
  have hml := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg M)
  have hd := ReadoutFilter.degree_linear_bound hJ
  have hsm := mul_le_mul_of_nonneg_right (show (S:ℝ)≤M by exact_mod_cast hS)
    (Nat.cast_nonneg (ReadoutFilter.degree (ReadoutFilter.matrixUpper J) ReadoutFilter.delta))
  have hmd := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg M)
  have hMR : (1:ℝ)≤M := by exact_mod_cast hM
  have hJR : (1:ℝ)≤J := by exact_mod_cast hJ
  simp only [preBudget,Nat.cast_add,Nat.cast_mul]
  nlinarith [mul_le_mul hMR hJR (by norm_num : (0:ℝ)≤1) (Nat.cast_nonneg M)]

theorem rank_ratio_control {M r : ℕ} (hM : 1 ≤ M)
    (hr : rankRatio*(M:ℝ) ≤ r) :
    12288 ≤ (r:ℝ) ∧
      (M:ℝ)*(ReadoutFilter.degreeConstant+lifetimeFraction+2) ≤
        (r:ℝ)/(8192*overlapScale) := by
  have hMR : (1:ℝ)≤M := by exact_mod_cast hM
  have hA := overlapScale_pos
  have hC := ReadoutFilter.degreeConstant_pos
  have hratio : rankRatio ≤ rankRatio*(M:ℝ) := le_mul_of_one_le_right rankRatio_pos.le hMR
  refine ⟨rankRatio_ge.trans (hratio.trans hr),?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 8192*overlapScale)).mpr
  have hc : lifetimeFraction ≤ 1 := lifetimeFraction_le.trans (by norm_num)
  have hp := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (M:ℝ)*(8192*overlapScale))
  unfold rankRatio at hr
  nlinarith

theorem budget_normalized {M r J q₀ q₁ S : ℕ}
    (hM : 1 ≤ M) (hJ : depthThreshold ≤ J) (hr : rankRatio*(M:ℝ) ≤ r)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*lifetime J+1) (hq₁ : q₁ ≤ lifetime J+1) :
    (preBudget J q₀ S:ℝ)/((r:ℝ)*J) ≤ 1/(8192*overlapScale) ∧
      (q₁:ℝ)/(J:ℝ) ≤ lifetimeFraction+1/(J:ℝ) ∧ 12288 ≤ (r:ℝ) ∧ 8 ≤ (J:ℝ) := by
  have hd := depth_lower hJ
  have hA := overlapScale_ge_one
  have hJR : (8:ℝ)≤J := by linarith
  have hJ0 : (0:ℝ)<J := by linarith
  have hJn : 1≤J := by exact_mod_cast (show (1:ℝ)≤J by linarith)
  have hratio := rank_ratio_control hM hr
  have hr0 : (0:ℝ)<r := by linarith [hratio.1]
  have hb := preBudget_le hM hJn hS hq₀
  have hrb := mul_le_mul_of_nonneg_right hratio.2 (Nat.cast_nonneg J)
  refine ⟨?_,?_,hratio.1,hJR⟩
  · apply (div_le_iff₀ (mul_pos hr0 hJ0)).mpr
    calc
      _ ≤ ((r:ℝ)/(8192*overlapScale))*(J:ℝ) := hb.trans hrb
      _ = _ := by ring
  · have hf := (lifetime_bounds hJ).2.2
    have hq : (q₁:ℝ)≤(lifetime J:ℝ)+1 := by exact_mod_cast hq₁
    apply (div_le_iff₀ hJ0).mpr
    have he : (lifetimeFraction+1/(J:ℝ))*(J:ℝ)=lifetimeFraction*(J:ℝ)+1 := by
      field_simp
    rw [he]
    linarith

def probabilityBound (k D r q₀ q₁ : ℝ) (pE : ℝ) : ℝ :=
  (512*k/(gamma^2*r*pE))*((q₀+2*r*q₁+2*r)/(D-q₀-r*q₁))+
    Real.exp (-Real.log (3/2:ℝ)*r)/pE

theorem mainTerm_reduction {k D r q₀ q₁ J pE : ℝ}
    (hk : 0 < k) (hr : 0 < r) (hJ : 0 < J) (hD : D=k*J)
    (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁) (hcap : q₀+r*q₁ ≤ D/2) (hpE : 1/2 ≤ pE) :
    (512*k/(gamma^2*r*pE))*((q₀+2*r*q₁+2*r)/(D-q₀-r*q₁)) ≤
      overlapScale*(q₀/(r*J)+2*q₁/J+2/J) := by
  have hDP : 0 < D := by rw [hD]; positivity
  have hden : 0 < D-q₀-r*q₁ := by linarith
  have hPE : 0 < pE := by linarith
  have hinv : 1/pE ≤ 2 := (div_le_iff₀ hPE).mpr (by linarith)
  have hdInv : 1/(D-q₀-r*q₁) ≤ 2/D := by
    apply (div_le_div_iff₀ hden hDP).mpr
    linarith
  have hN : 0 ≤ q₀+2*r*q₁+2*r := by positivity
  have hc : 0 ≤ 512*k/(gamma^2*r) := by positivity
  calc
    _ = (512*k/(gamma^2*r))*(1/pE)*(q₀+2*r*q₁+2*r)*(1/(D-q₀-r*q₁)) := by ring
    _ ≤ (512*k/(gamma^2*r))*2*(q₀+2*r*q₁+2*r)*(2/D) := by gcongr
    _ = _ := by
      rw [hD]
      unfold overlapScale
      field_simp [gamma_pos.ne',hr.ne',hJ.ne',hk.ne']
      ring

theorem exceptionalTerm_bound {r pE : ℝ} (hr : 12288 ≤ r) (hpE : 1/2 ≤ pE) :
    Real.exp (-Real.log (3/2:ℝ)*r)/pE ≤ 1/2048 := by
  have hr0 : 0 ≤ r := by linarith
  have hp : 0 < pE := by linarith
  have hlog : (1/3:ℝ)≤Real.log (3/2:ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2)
    norm_num at h
    linarith
  have he := Real.add_one_le_exp (Real.log (3/2:ℝ)*r)
  have hm := mul_le_mul_of_nonneg_right hlog hr0
  have hl : (4097:ℝ)≤Real.exp (Real.log (3/2:ℝ)*r) := by linarith
  have ht : Real.exp (-Real.log (3/2:ℝ)*r) ≤ 1/4097 := by
    rw [neg_mul,Real.exp_neg,inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hl
  calc
    _ ≤ (1/4097)/(1/2) := div_le_div₀ (by positivity) ht (by norm_num) hpE
    _ ≤ _ := by norm_num

theorem normalized_small {M r J q₀ q₁ S : ℕ}
    (hM : 1 ≤ M) (hJ : depthThreshold ≤ J) (hr : rankRatio*(M:ℝ) ≤ r)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*lifetime J+1) (hq₁ : q₁ ≤ lifetime J+1) :
    overlapScale*((preBudget J q₀ S:ℝ)/((r:ℝ)*J)+2*(q₁:ℝ)/J+2/J) ≤ 1/2048 := by
  obtain ⟨hb,hq,hrR,hJR⟩ := budget_normalized hM hJ hr hS hq₀ hq₁
  have hA := overlapScale_pos
  have hJpos : (0:ℝ)<J := by linarith
  have hi : 1/(J:ℝ) ≤ 1/(32768*overlapScale) :=
    one_div_le_one_div_of_le (by positivity) (depth_lower hJ)
  have hs : (preBudget J q₀ S:ℝ)/((r:ℝ)*J)+2*(q₁:ℝ)/J+2/J ≤
      1/(8192*overlapScale)+2*lifetimeFraction+4/(32768*overlapScale) := by
    calc
      _ ≤ 1/(8192*overlapScale)+2*lifetimeFraction+4/(J:ℝ) := by
        convert add_le_add_right (add_le_add hb
          (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤2))) (2/(J:ℝ)) using 1 <;> ring
      _ ≤ _ := by
        convert add_le_add_left (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤4))
          (1/(8192*overlapScale)+2*lifetimeFraction) using 1 <;> ring
  calc
    _ ≤ overlapScale*(1/(8192*overlapScale)+2*lifetimeFraction+4/(32768*overlapScale)) :=
      mul_le_mul_of_nonneg_left hs hA.le
    _ = _ := by unfold lifetimeFraction; field_simp; ring

theorem fork_budget_half {M r J κ q₀ q₁ S : ℕ}
    (hM : 1 ≤ M) (hJ : depthThreshold ≤ J) (hr : rankRatio*(M:ℝ) ≤ r) (hκ : 1 ≤ κ)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*lifetime J+1) (hq₁ : q₁ ≤ lifetime J+1) :
    (preBudget J q₀ S:ℝ)+(r:ℝ)*q₁ ≤ ((κ:ℝ)*r*J)/2 := by
  obtain ⟨hb,hq,hrR,hJR⟩ := budget_normalized hM hJ hr hS hq₀ hq₁
  have hrpos : (0:ℝ)<r := by linarith
  have hJpos : (0:ℝ)<J := by linarith
  have hc := lifetimeFraction_le
  have hb' : (preBudget J q₀ S:ℝ) ≤ ((r:ℝ)*J)/8 := by
    have hb0 : (preBudget J q₀ S:ℝ)/((r:ℝ)*J) ≤ 1/8 :=
      hb.trans hc
    have h := (div_le_iff₀ (mul_pos hrpos hJpos)).mp hb0
    linarith
  have hi : 1/(J:ℝ) ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) hJR
  have hq' : (q₁:ℝ)≤(J:ℝ)/4 := by
    have hq0 : (q₁:ℝ)/(J:ℝ) ≤ 1/4 := by linarith
    have h := (div_le_iff₀ hJpos).mp hq0
    linarith
  have hqr := mul_le_mul_of_nonneg_left hq' hrpos.le
  have hkR : (1:ℝ)≤κ := by exact_mod_cast hκ
  have hkJ := mul_le_mul_of_nonneg_right hkR (show 0≤(r:ℝ)*J by positivity)
  nlinarith

/-- Arithmetic form of the lifetime corollary, ready to compose with the
actual machine fork theorem. The source query cap is itself a conclusion. -/
theorem numerical_lifetime_bound {M r J κ q₀ q₁ S : ℕ} {pE : ℝ}
    (hM : 1 ≤ M) (hJ : depthThreshold ≤ J) (hr : rankRatio*(M:ℝ) ≤ r) (hκ : 1 ≤ κ)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*lifetime J+1) (hq₁ : q₁ ≤ lifetime J+1)
    (hpE : 99/100 ≤ pE) :
    preBudget J q₀ S+r*q₁ ≤ κ*r*J-κ*r ∧
      probabilityBound ((κ:ℝ)*r) ((κ:ℝ)*r*J) r (preBudget J q₀ S) q₁ pE ≤ 1/256 ∧
      (lifetimeFraction/2)*(J:ℝ) ≤ lifetime J ∧ 1 ≤ (lifetimeFraction/2)*(J:ℝ) := by
  have hn := budget_normalized hM hJ hr hS hq₀ hq₁
  have hrpos : (0:ℝ)<r := by linarith [hn.2.2.1]
  have hJpos : (0:ℝ)<J := by linarith [hn.2.2.2]
  have hkpos : (0:ℝ)<κ := by exact_mod_cast (show 0<κ by omega)
  have hhalf := fork_budget_half hM hJ hr hκ hS hq₀ hq₁
  have hcap : preBudget J q₀ S+r*q₁ ≤ κ*r*J-κ*r := by
    have hQ : 2*(preBudget J q₀ S+r*q₁) ≤ κ*r*J := by
      exact_mod_cast (show 2*((preBudget J q₀ S:ℝ)+(r:ℝ)*q₁) ≤ (κ:ℝ)*r*J by linarith)
    have hJ2 : 2≤J := by exact_mod_cast (show (2:ℝ)≤J by linarith [hn.2.2.2])
    have hk2 := Nat.mul_le_mul_left (κ*r) hJ2
    omega
  refine ⟨hcap,?_,(lifetime_bounds hJ).1,(lifetime_bounds hJ).2.1⟩
  have hm := mainTerm_reduction (mul_pos hkpos hrpos) hrpos hJpos rfl
    (Nat.cast_nonneg (preBudget J q₀ S)) (Nat.cast_nonneg q₁) hhalf (by linarith : 1/2≤pE)
  have hs := normalized_small hM hJ hr hS hq₀ hq₁
  have ht := exceptionalTerm_bound hn.2.2.1 (by linarith : 1/2≤pE)
  unfold probabilityBound
  linarith

theorem source_parameters {M r J : ℕ}
    (_hM : 1 ≤ M) (hJ : depthThreshold ≤ J) (hr : rankRatio*(M:ℝ) ≤ r) :
    4 ≤ J ∧ M ≤ r ∧ 1 ≤ lifetime J := by
  have hd := depth_lower hJ
  have hA := overlapScale_ge_one
  have hMR : (0:ℝ)≤M := Nat.cast_nonneg M
  have hrM : (M:ℝ)≤r := by
    have hc : (1:ℝ)≤rankRatio := le_trans (by norm_num) rankRatio_ge
    have h := mul_le_mul_of_nonneg_right hc hMR
    nlinarith
  have hf := lifetime_bounds hJ
  exact ⟨by exact_mod_cast (show (4:ℝ)≤J by linarith),by exact_mod_cast hrM,
    by exact_mod_cast (show (1:ℝ)≤lifetime J from hf.2.1.trans hf.1)⟩

/-- The exact numerator and residual denominator used by the chronological
machine theorem, rather than a separate asymptotic estimate. -/
theorem source_lifetime_bound {M r J κ q₀ q₁ S a b : ℕ} {pE : ℝ}
    (hM : 1 ≤ M) (hJ : depthThreshold ≤ J) (hr : rankRatio*(M:ℝ) ≤ r) (hκ : 1 ≤ κ)
    (hS : S ≤ M) (hq₀ : q₀ ≤ M*lifetime J+1) (hq₁ : q₁ ≤ lifetime J+1)
    (hpE : 99/100 ≤ pE)
    (hab : κ*r+b=a) (hD : a+(preBudget J q₀ S+r*q₁)=κ*r*J) :
    (512*((a:ℝ)-b)/(gamma^2*(r:ℝ)*pE))*
        ((preBudget J q₀ S:ℝ)+2*(r:ℝ)*q₁+2*r)/a+
      Real.exp (-Real.log (3/2:ℝ)*(r:ℝ))/pE ≤ 1/256 := by
  have h := (numerical_lifetime_bound hM hJ hr hκ hS hq₀ hq₁ hpE).2.1
  have habR : (κ:ℝ)*r+b=a := by exact_mod_cast hab
  have hDR : (a:ℝ)+((preBudget J q₀ S:ℝ)+(r:ℝ)*q₁)=(κ:ℝ)*r*J := by exact_mod_cast hD
  have hk : (a:ℝ)-b=(κ:ℝ)*r := by linarith
  have ha : (κ:ℝ)*r*J-(preBudget J q₀ S:ℝ)-(r:ℝ)*q₁=a := by linarith
  unfold probabilityBound at h
  rw [hk]
  rw [ha] at h
  convert h using 1
  ring

end
end GradientHessian.ForkLifetime
