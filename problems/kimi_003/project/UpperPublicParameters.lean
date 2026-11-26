import HaarRebalancingUpperMoments
import UpperPublicScale
import UpperLogBudget

/-! Public numerical choices for the actual fixed-budget upper algorithm.
All constants are functions of the proved absolute U3 coefficient. -/
set_option maxHeartbeats 1000000
open Task006.HaarRebalancing Task006.Full Task006.Full.SampleInstance
open scoped NNReal
namespace Task006.UpperPublicParameters
noncomputable section

def publicRho (R A : ℝ) : ℝ := R / (48 * A)
def publicDelta (d : ℕ) (R A : ℝ) : ℝ := publicRho R A / (48 * (d : ℝ) ^ (3 / 2 : ℝ) * A)
def publicMoment (d : ℕ) (L s : ℝ) : ℝ := rebalancingThreshold L d s
def publicRounds (A s : ℝ) : ℕ := Nat.ceil (1728 * rebalancingC2 ^ 2 * A ^ 3 * s ^ (3 / 2 : ℝ))
def publicClip (d : ℕ) (L A s : ℝ) : ℝ :=
  (publicMoment d L s * (publicRounds A s : ℝ)) ^ (2 / 3 : ℝ)
def publicBiasScale (L A s : ℝ) : ℝ :=
  rebalancingC2 ^ (2 / 3 : ℝ) * L * Real.sqrt s * (publicRounds A s : ℝ) ^ (-1 / 3 : ℝ)
def publicStep (R L A s : ℝ) : ℝ := R / ((publicRounds A s : ℝ) * publicBiasScale L A s)

theorem rebalancingC2_pos : 0 < rebalancingC2 := by
  have hC0 : 0 ≤ Task006.SphereConcentration.thirdHalfMomentConstant :=
    le_trans (by norm_num) Task006.SphereConcentration.thirdHalfMomentConstant_ge_one
  have hK : 0 ≤ rebalancingK0 := Real.rpow_nonneg (by positivity) _
  have hB : 0 < rebalancingB := by unfold rebalancingB; positivity
  exact Real.rpow_pos_of_pos hB _

theorem publicRho_pos {R A : ℝ} (hR : 0 < R) (hA : 0 < A) : 0 < publicRho R A :=
  div_pos hR (mul_pos (by norm_num) hA)

theorem publicDelta_pos {d : ℕ} {R A : ℝ} (hd : 0 < d) (hR : 0 < R) (hA : 0 < A) :
    0 < publicDelta d R A := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  exact div_pos (publicRho_pos hR hA)
    (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hdr _)) hA)

theorem publicMoment_pos {d : ℕ} {L s : ℝ} (hd : 0 < d) (hL : 0 < L) (hs : 0 < s) :
    0 < publicMoment d L s := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  exact mul_pos (mul_pos rebalancingC2_pos (Real.rpow_pos_of_pos hL _))
    (Real.rpow_pos_of_pos (div_pos hs hdr) _)

theorem publicRounds_lower {A s : ℝ} :
    1728 * rebalancingC2 ^ 2 * A ^ 3 * s ^ (3 / 2 : ℝ) ≤ (publicRounds A s : ℝ) :=
  Nat.le_ceil _

theorem publicRounds_pos {A s : ℝ} (hA : 0 < A) (hs : 0 < s) : 0 < publicRounds A s := by
  have ht : 0 < 1728 * rebalancingC2 ^ 2 * A ^ 3 * s ^ (3 / 2 : ℝ) := by
    have hC := rebalancingC2_pos
    positivity
  have htr : 0 < (publicRounds A s : ℝ) := ht.trans_le publicRounds_lower
  exact_mod_cast htr

theorem publicRounds_upper {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    (publicRounds A s : ℝ) < 1728 * rebalancingC2 ^ 2 * A ^ 3 * s ^ (3 / 2 : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (by
    have hC := rebalancingC2_pos
    positivity)

theorem publicClip_pos {d : ℕ} {L A s : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hA : 0 < A) (hs : 0 < s) : 0 < publicClip d L A s := by
  have hT : 0 < (publicRounds A s : ℝ) := by exact_mod_cast publicRounds_pos hA hs
  exact Real.rpow_pos_of_pos (mul_pos (publicMoment_pos hd hL hs) hT) _

theorem publicBiasScale_pos {L A s : ℝ} (hL : 0 < L) (hA : 0 < A) (hs : 0 < s) :
    0 < publicBiasScale L A s := by
  have hT : 0 < (publicRounds A s : ℝ) := by exact_mod_cast publicRounds_pos hA hs
  exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos rebalancingC2_pos _) hL)
    (Real.sqrt_pos.2 hs)) (Real.rpow_pos_of_pos hT _)

theorem publicStep_pos {R L A s : ℝ} (hR : 0 < R) (hL : 0 < L) (hA : 0 < A) (hs : 0 < s) :
    0 < publicStep R L A s := by
  have hT : 0 < (publicRounds A s : ℝ) := by exact_mod_cast publicRounds_pos hA hs
  exact div_pos hR (mul_pos hT (publicBiasScale_pos hL hA hs))

/-- The explicit U3 coefficient is at least one. -/
theorem rebalancingC2_ge_one : 1 ≤ rebalancingC2 := by
  have hC0 : 0 ≤ Task006.SphereConcentration.thirdHalfMomentConstant :=
    le_trans (by norm_num) Task006.SphereConcentration.thirdHalfMomentConstant_ge_one
  have hK : 0 ≤ rebalancingK0 := Real.rpow_nonneg (by positivity) _
  have hB : 1 ≤ rebalancingB := by unfold rebalancingB; nlinarith
  exact Real.one_le_rpow hB (by norm_num)

theorem rebalancingC2_twoThirds : rebalancingC2 ^ (2 / 3 : ℝ) = rebalancingB := by
  have hC0 : 0 ≤ Task006.SphereConcentration.thirdHalfMomentConstant :=
    le_trans (by norm_num) Task006.SphereConcentration.thirdHalfMomentConstant_ge_one
  have hK : 0 ≤ rebalancingK0 := Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ rebalancingB := by unfold rebalancingB; positivity
  unfold rebalancingC2
  rw [← Real.rpow_mul hB]
  norm_num

/-- The exact cancellation of dimension in the public clipping scale. -/
theorem publicMoment_root_scale {d : ℕ} {L s : ℝ} (hd : 0 < d) (hL : 0 < L) (hs : 0 < s) :
    Real.sqrt d * publicMoment d L s ^ (2 / 3 : ℝ) =
      rebalancingC2 ^ (2 / 3 : ℝ) * L * Real.sqrt s := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdr
  have hC0 : 0 ≤ Task006.SphereConcentration.thirdHalfMomentConstant :=
    le_trans (by norm_num) Task006.SphereConcentration.thirdHalfMomentConstant_ge_one
  have hK : 0 ≤ rebalancingK0 := Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ rebalancingB := by unfold rebalancingB; positivity
  have hroot : publicMoment d L s ^ (2 / 3 : ℝ) =
      rebalancingB * L * Real.sqrt (s / (d : ℝ)) :=
    Task006.RebalancingArithmetic.rpow_identity hB hL.le (div_pos hs hdr).le
  rw [hroot, rebalancingC2_twoThirds, Real.sqrt_div hs.le]
  field_simp [hsd.ne']

theorem public_scale_identities {d : ℕ} {L A s : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hA : 0 < A) (hs : 0 < s) :
    Real.sqrt d * publicMoment d L s * publicClip d L A s ^ (-1/2:ℝ) = publicBiasScale L A s ∧
      Real.sqrt d * publicClip d L A s = (publicRounds A s:ℝ)*publicBiasScale L A s ∧
      (d:ℝ)*publicMoment d L s*publicClip d L A s ^ (1/2:ℝ) =
        (publicRounds A s:ℝ)*publicBiasScale L A s^2 ∧
      (d:ℝ)*publicClip d L A s^2 = (publicRounds A s:ℝ)^2*publicBiasScale L A s^2 := by
  have hm := publicMoment_pos hd hL hs
  have ht : 0 < (publicRounds A s : ℝ) := by exact_mod_cast publicRounds_pos hA hs
  have hid := Task006.UpperPublicScale.clip_scale_identities (Nat.cast_nonneg d) hm ht
  dsimp only at hid
  have hscale : Real.sqrt d * publicMoment d L s ^ (2/3:ℝ) *
      (publicRounds A s:ℝ)^(-1/3:ℝ) = publicBiasScale L A s := by
    rw [publicMoment_root_scale hd hL hs]
    rfl
  simpa only [hscale, publicClip] using hid

/-- The public radii leave a nonnegative inner decision ball. -/
theorem public_inner_nonneg {d : ℕ} {R A : ℝ} (hd : 1 ≤ d) (hR : 0 ≤ R) (hA : 1 ≤ A) :
    0 ≤ R - (publicRho R A + publicDelta d R A) := by
  have hApos : 0 < A := by linarith
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdrpow : 1 ≤ (d:ℝ)^(3/2:ℝ) := Real.one_le_rpow hdr (by norm_num)
  have hrho : 0 ≤ publicRho R A := div_nonneg hR (by positivity)
  have hrhole : publicRho R A ≤ R/48 := by
    unfold publicRho
    apply div_le_div_of_nonneg_left hR (by norm_num)
    nlinarith
  have hδle : publicDelta d R A ≤ publicRho R A/48 := by
    unfold publicDelta
    apply div_le_div_of_nonneg_left hrho (by norm_num)
    have hh : 1 ≤ (d:ℝ)^(3/2:ℝ)*A := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdrpow) (sub_nonneg.mpr hA)]
    nlinarith
  linarith

/-- The implemented (conservative 2d) smoothing derivative bound gives this
exact finite-difference vector bias under the original public delta. -/
theorem public_finite_difference_scale {d : ℕ} {L R A : ℝ} (hd : 0 < d)
    (hR : 0 < R) (hA : 0 < A) :
    Real.sqrt d * ((d:ℝ)*L*publicDelta d R A/publicRho R A) = L/(48*A) := by
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have hrho := publicRho_pos hR hA
  have hpow : (d:ℝ)^(3/2:ℝ) = (d:ℝ)*Real.sqrt d := by
    calc
      _ = (d:ℝ)^((1:ℝ)+(1/2:ℝ)) := by norm_num
      _ = (d:ℝ)^(1:ℝ)*(d:ℝ)^(1/2:ℝ) := Real.rpow_add hdr _ _
      _ = _ := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold publicDelta
  rw [hpow]
  have hsd := (Real.sqrt_pos.2 hdr).ne'
  field_simp [hrho.ne', hA.ne', hdr.ne', hsd]
  <;> ring

/-- Explicit logarithmic tuning, with the tail budget proved independently. -/
def publicLogCoefficient : ℝ := 16 + 4*Real.log (32*(1728*rebalancingC2^2)+1)
def publicLogScale (d : ℕ) (A : ℝ) : ℝ := publicLogCoefficient * Real.log (Real.exp 1 * (d:ℝ) * A)

theorem public_log_budget {d : ℕ} {A : ℝ} (hd : 2 ≤ d) (hA : 2 ≤ A) (hdA : (d:ℝ) ≤ A) :
    let s := publicLogScale d A
    1 ≤ s ∧ 1 ≤ publicRounds A s ∧
      (publicRounds A s:ℝ)*(d:ℝ)*Real.exp (-s) ≤ (A⁻¹)^2 := by
  have hC := rebalancingC2_ge_one
  have hK : 1 ≤ 1728*rebalancingC2^2 := by nlinarith [sq_nonneg rebalancingC2]
  exact Task006.UpperLogBudget.log_budget (1728*rebalancingC2^2) (d:ℝ) A hK
    (by exact_mod_cast hd) hA hdA

theorem publicDelta_le_rho {d : ℕ} {R A : ℝ} (hd : 1 ≤ d) (hR : 0 ≤ R) (hA : 1 ≤ A) :
    publicDelta d R A ≤ publicRho R A := by
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hp : 1 ≤ (d:ℝ)^(3/2:ℝ) := Real.one_le_rpow hdr (by norm_num)
  have hden : 1 ≤ 48*(d:ℝ)^(3/2:ℝ)*A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hA)]
  have hrho : 0 ≤ publicRho R A := div_nonneg hR (by positivity)
  exact div_le_self hrho hden

/-- The exact requested optimization allowance, from the cubic public round
count and A=LR/eps. This is derived, not a terminal accuracy hypothesis. -/
theorem public_optimization_allowance {L R eps A s : ℝ} (hL : 0 < L) (hR : 0 < R)
    (heps : 0 < eps) (hA : 0 < A) (hs : 0 < s) (hAeq : A = L*R/eps) :
    R * publicBiasScale L A s ≤ eps/12 := by
  have ht : 0 < (publicRounds A s:ℝ) := by exact_mod_cast publicRounds_pos hA hs
  have hh := Task006.UpperPublicScale.bias_scale_accuracy rebalancingC2_pos hL hA hs ht
    (publicRounds_lower (A := A) (s := s))
  change A * publicBiasScale L A s ≤ L/12 at hh
  have hALR : A*eps = L*R := (eq_div_iff heps.ne').mp hAeq
  apply (mul_le_mul_iff_of_pos_left hA).mp
  calc
    A*(R*publicBiasScale L A s) = R*(A*publicBiasScale L A s) := by ring
    _ ≤ R*(L/12) := mul_le_mul_of_nonneg_left hh hR.le
    _ = A*(eps/12) := by nlinarith [hALR]

theorem publicLogCoefficient_pos : 0 < publicLogCoefficient := by
  have hC := rebalancingC2_ge_one
  have harg : 1 ≤ 32*(1728*rebalancingC2^2)+1 := by nlinarith [sq_nonneg rebalancingC2]
  have hlog : 0 ≤ Real.log (32*(1728*rebalancingC2^2)+1) := Real.log_nonneg harg
  unfold publicLogCoefficient
  linarith

theorem publicLogarithm_ge_one {d : ℕ} {A : ℝ} (hd : 2 ≤ d) (hA : 2 ≤ A) :
    1 ≤ Real.log (Real.exp 1*(d:ℝ)*A) := by
  have hdr : (2:ℝ) ≤ d := by exact_mod_cast hd
  have he := Real.exp_pos (1:ℝ)
  have hmul : (1:ℝ) ≤ (d:ℝ)*A := by
    nlinarith [mul_nonneg (show 0 ≤ (d:ℝ)-1 by linarith) (show 0 ≤ A-1 by linarith)]
  have harg : Real.exp 1 ≤ Real.exp 1*(d:ℝ)*A := by nlinarith
  simpa only [Real.log_exp] using Real.log_le_log he harg

/-- Explicit absolute complexity coefficient, independent of d,L,R,eps. -/
def publicComplexityCoefficient : ℝ :=
  1728*rebalancingC2^2*publicLogCoefficient^(3/2:ℝ)+1

/-- Concrete big-O certificate for the public integer round budget. -/
theorem publicRounds_complexity {d : ℕ} {A : ℝ} (hd : 2 ≤ d) (hA : 2 ≤ A) :
    (publicRounds A (publicLogScale d A):ℝ) ≤
      publicComplexityCoefficient * A^3 * Real.log (Real.exp 1*(d:ℝ)*A)^(3/2:ℝ) := by
  let ell := Real.log (Real.exp 1*(d:ℝ)*A)
  have hell : 1 ≤ ell := publicLogarithm_ge_one hd hA
  have hCs := publicLogCoefficient_pos
  have hs : 0 < publicLogScale d A := mul_pos hCs (by dsimp [ell] at hell; linarith)
  have hbase : 1 ≤ A^3*ell^(3/2:ℝ) := by
    have hAp : 1 ≤ A^3 := one_le_pow₀ (by linarith : (1:ℝ) ≤ A)
    have hep : 1 ≤ ell^(3/2:ℝ) := Real.one_le_rpow hell (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hAp) (sub_nonneg.mpr hep)]
  have hr := publicRounds_upper (show 0 ≤ A by linarith) hs.le
  have hsp : publicLogScale d A^(3/2:ℝ) = publicLogCoefficient^(3/2:ℝ)*ell^(3/2:ℝ) :=
    Real.mul_rpow hCs.le (by linarith : 0 ≤ ell)
  rw [hsp] at hr
  unfold publicComplexityCoefficient
  dsimp only [ell] at hbase hr
  nlinarith

end
end Task006.UpperPublicParameters
