import LeanArticleAudit.Pilot.Gate

/-!
# The fixed-diameter hidden-frame operator

This module formalizes the construction surrounding `lem:operator`.  Indices
are zero-based in Lean: a budget `N` uses `m = N + 1` frame vectors, and the
summand indexed by `i : Fin N` sends the gate on `v_i` into `v_(i+1)`.
-/

open Set
open scoped ContDiff RealInnerProductSpace

namespace LeanArticleAudit.Pilot

section Parameters

/-- `m=N+1`. -/
def hiddenM (N : ℕ) : ℕ := N + 1

/-- `q=1-1/(2m)`. -/
noncomputable def hiddenQ (N : ℕ) : ℝ :=
  1 - 1 / (2 * (hiddenM N : ℝ))

/-- `c=R/(2√m)`. -/
noncomputable def hiddenC (R : ℝ) (N : ℕ) : ℝ :=
  R / (2 * Real.sqrt (hiddenM N : ℝ))

/-- `τ=c/(8m)=R/(16m^(3/2))`, using the first expression as the definition. -/
noncomputable def hiddenTau (R : ℝ) (N : ℕ) : ℝ :=
  hiddenC R N / (8 * (hiddenM N : ℝ))

/-- `λ=L_p τ^(p-1)/B_p`. -/
noncomputable def hiddenLambda (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) : ℝ :=
  Lp * hiddenTau R N ^ (p - 1) / gateBp p profile

theorem hiddenM_pos (N : ℕ) : 0 < hiddenM N := by
  simp [hiddenM]

theorem hiddenQ_pos {N : ℕ} (hN : 1 ≤ N) : 0 < hiddenQ N := by
  rw [hiddenQ, sub_pos]
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  apply (div_lt_one (mul_pos (by norm_num) hm0)).2
  have hm : (2 : ℝ) ≤ hiddenM N := by
    norm_cast
    simp [hiddenM, hN]
  nlinarith

theorem hiddenQ_lt_one (N : ℕ) : hiddenQ N < 1 := by
  rw [hiddenQ, hiddenM]
  exact sub_lt_self _ (by positivity)

theorem hiddenQ_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ hiddenQ N :=
  (hiddenQ_pos hN).le

theorem hiddenC_pos {R : ℝ} (hR : 0 < R) (N : ℕ) : 0 < hiddenC R N := by
  rw [hiddenC]
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  exact div_pos hR (mul_pos (by norm_num) (Real.sqrt_pos.2 hm0))

theorem hiddenTau_pos {R : ℝ} (hR : 0 < R) (N : ℕ) :
    0 < hiddenTau R N := by
  rw [hiddenTau]
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  exact div_pos (hiddenC_pos hR N) (mul_pos (by norm_num) hm0)

theorem gateBp_pos (p : ℕ) (profile : GateProfile) : 0 < gateBp p profile := by
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem hiddenLambda_pos {p N : ℕ} (profile : GateProfile)
    {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R) :
    0 < hiddenLambda p profile Lp R N := by
  rw [hiddenLambda]
  exact div_pos (mul_pos hLp (pow_pos (hiddenTau_pos hR N) _))
    (gateBp_pos p profile)

theorem hidden_scaling_identity {p N : ℕ} (hp : 1 ≤ p) (profile : GateProfile)
    (Lp : ℝ) {R : ℝ} (hR : 0 < R) :
    hiddenLambda p profile Lp R N *
        (gateBp p profile * hiddenTau R N ^ (1 - (p : ℤ))) = Lp := by
  have htau0 : hiddenTau R N ≠ 0 := (hiddenTau_pos hR N).ne'
  have hBp0 : gateBp p profile ≠ 0 := (gateBp_pos p profile).ne'
  have hexp : ((p - 1 : ℕ) : ℤ) + (1 - (p : ℤ)) = 0 := by
    omega
  have hpow : hiddenTau R N ^ (p - 1) *
      hiddenTau R N ^ (1 - (p : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ htau0, hexp, zpow_zero]
  rw [hiddenLambda]
  field_simp [hBp0]
  calc
    Lp * hiddenTau R N ^ (p - 1) * hiddenTau R N ^ (1 - (p : ℤ)) =
        Lp * (hiddenTau R N ^ (p - 1) *
          hiddenTau R N ^ (1 - (p : ℤ))) := by ring
    _ = Lp := by rw [hpow, mul_one]

theorem hidden_ball_scalar_bound {R : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    hiddenC R N ^ 2 + hiddenQ N ^ 2 * R ^ 2 ≤ R ^ 2 := by
  let m : ℝ := hiddenM N
  have hm0 : 0 < m := by
    dsimp [m]
    exact_mod_cast hiddenM_pos N
  have hm2 : 2 ≤ m := by
    dsimp [m]
    norm_cast
    simp [hiddenM, hN]
  have hsqrt : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0.le
  have hc : hiddenC R N ^ 2 = R ^ 2 / (4 * m) := by
    rw [hiddenC, div_pow]
    change R ^ 2 / ((2 * Real.sqrt m) ^ 2) = R ^ 2 / (4 * m)
    rw [mul_pow, hsqrt]
    norm_num
  have hgap : 1 / (4 * m) ≤ 1 - hiddenQ N ^ 2 := by
    change 1 / (4 * m) ≤ 1 - (1 - 1 / (2 * m)) ^ 2
    field_simp [ne_of_gt hm0]
    nlinarith
  rw [hc]
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  calc
    R ^ 2 / (4 * m) + hiddenQ N ^ 2 * R ^ 2 =
        R ^ 2 * (1 / (4 * m) + hiddenQ N ^ 2) := by ring
    _ ≤ R ^ 2 * 1 := by
      apply mul_le_mul_of_nonneg_left _ hR2
      linarith
    _ = R ^ 2 := by ring

theorem hidden_loss_identity (R : ℝ) (N : ℕ) :
    (1 - hiddenQ N) * hiddenC R N = 4 * hiddenTau R N := by
  rw [hiddenQ, hiddenTau]
  have hm0 : (hiddenM N : ℝ) ≠ 0 := by
    exact_mod_cast (hiddenM_pos N).ne'
  field_simp [hm0]
  ring

theorem hidden_mass_identity (R : ℝ) (N : ℕ) :
    (hiddenM N : ℝ) * hiddenTau R N = hiddenC R N / 8 := by
  rw [hiddenTau]
  have hm0 : (hiddenM N : ℝ) ≠ 0 := by
    exact_mod_cast (hiddenM_pos N).ne'
  field_simp [hm0]

theorem hidden_c_sq_mass (R : ℝ) (N : ℕ) :
    (hiddenM N : ℝ) * hiddenC R N ^ 2 = R ^ 2 / 4 := by
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  have hsqrt : Real.sqrt (hiddenM N : ℝ) ^ 2 = hiddenM N :=
    Real.sq_sqrt hm0.le
  rw [hiddenC, div_pow]
  field_simp [hm0.ne', Real.sqrt_ne_zero'.mpr hm0]
  nlinarith

end Parameters

section BallData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Public VI data for the fixed ball `B₂(0,R)`, whose supplied diameter bound
is `D=2R` and whose public initial point is the origin. -/
noncomputable def ballVIData (p : ℕ) (hp : 2 ≤ p) (Lp : ℝ) (hLp : 0 < Lp)
    (R : ℝ) (hR : 0 < R) : VIPublicData E where
  dimension_pos := Module.finrank_pos
  p := p
  p_ge_two := hp
  Lp := Lp
  Lp_pos := hLp
  D := 2 * R
  D_pos := by positivity
  X := Metric.closedBall 0 R
  X_nonempty := ⟨0, by simp [Metric.mem_closedBall, hR.le]⟩
  X_compact := ProperSpace.isCompact_closedBall 0 R
  X_convex := convex_closedBall 0 R
  x0 := 0
  x0_mem := by simp [Metric.mem_closedBall, hR.le]
  diameter_le := by
    intro x hx y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hx hy
    calc
      dist x y ≤ dist x 0 + dist 0 y := dist_triangle _ _ _
      _ = ‖x‖ + ‖y‖ := by rw [dist_zero_right, dist_zero_left]
      _ ≤ 2 * R := by linarith

end BallData

section Construction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hidden-frame contraction
`c v₁ + q ∑ hτ(⟪vᵢ,x⟫) vᵢ₊₁`. -/
noncomputable def hiddenMap (profile : GateProfile) (R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) (x : E) : E :=
  hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩ +
    hiddenQ N • ∑ i : Fin N,
      gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ

/-- `F_V(x)=λ(x-T_V(x))`. -/
noncomputable def hiddenOperator (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) (v : Fin (N + 1) → E) (x : E) : E :=
  hiddenLambda p profile Lp R N • (x - hiddenMap profile R N v x)

/-- One scalar gate pulled back along an inner-product coordinate and placed
in a (possibly different) output direction. -/
noncomputable def gateRidge (profile : GateProfile) (tau : ℝ)
    (a w : E) (x : E) : E := gate profile tau (inner ℝ a x) • w

/-- Scalar coordinates of the explicit fixed point. -/
noncomputable def hiddenCoeffNat (profile : GateProfile) (R : ℝ) (N : ℕ) : ℕ → ℝ
  | 0 => hiddenC R N
  | k + 1 => hiddenQ N * gate profile (hiddenTau R N) (hiddenCoeffNat profile R N k)

noncomputable def hiddenCoeff (profile : GateProfile) (R : ℝ) (N : ℕ) :
    Fin (N + 1) → ℝ := fun i => hiddenCoeffNat profile R N i.1

/-- Explicit hidden-chain fixed point `∑ sᵢvᵢ`. -/
noncomputable def hiddenZero (profile : GateProfile) (R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) : E :=
  ∑ i : Fin (N + 1), hiddenCoeff profile R N i • v i

theorem gate_nonneg_of_nonneg (profile : GateProfile) {tau : ℝ} (htau : 0 < tau)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gate profile tau s := by
  rw [gate]
  have hend : 0 ≤ s / tau := div_nonneg hs htau.le
  have hint : 0 ≤ ∫ u in 0..s / tau, profile.rho u :=
    intervalIntegral.integral_nonneg hend fun u _ => (profile.range u).1
  exact mul_nonneg htau.le hint

theorem gateRidge_iteratedFDeriv_apply (n : ℕ) (profile : GateProfile)
    {tau : ℝ} (htau : tau ≠ 0) (a w x : E) (u : Fin n → E) :
    iteratedFDeriv ℝ n (gateRidge profile tau a w) x u =
      ((∏ j : Fin n, inner ℝ a (u j)) *
        iteratedDeriv n (gate profile tau) (inner ℝ a x)) • w := by
  have hgate : ContDiff ℝ n (gate profile tau) :=
    contDiff_infty.mp (gate_contDiff profile htau) n
  have hcomp : ContDiff ℝ n
      ((gate profile tau) ∘ (innerSL ℝ a : E →L[ℝ] ℝ)) :=
    hgate.comp (innerSL ℝ a).contDiff
  change iteratedFDeriv ℝ n
      (fun y : E => ((gate profile tau) ∘ (innerSL ℝ a : E →L[ℝ] ℝ)) y • w) x u = _
  rw [iteratedFDeriv_smul_const_apply hcomp.contDiffAt]
  change (iteratedFDeriv ℝ n
      ((gate profile tau) ∘ (innerSL ℝ a : E →L[ℝ] ℝ)) x u) • w = _
  rw [
    ContinuousLinearMap.iteratedFDeriv_comp_right (innerSL ℝ a) hgate x le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp only [innerSL_apply_apply]
  simp [mul_comm]

theorem orthonormal_norm_sum_sq {ι : Type*} [Fintype ι]
    {w : ι → E} (hw : Orthonormal ℝ w) (a : ι → ℝ) :
    ‖∑ i, a i • w i‖ ^ 2 = ∑ i, a i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa [pow_two] using hw.inner_sum a a Finset.univ

theorem hiddenZero_coordinate (profile : GateProfile) (R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) (i : Fin (N + 1)) :
    inner ℝ (v i) (hiddenZero profile R N v) = hiddenCoeff profile R N i := by
  exact hv.inner_right_fintype (hiddenCoeff profile R N) i

theorem hiddenZero_fixed (profile : GateProfile) (R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) :
    hiddenMap profile R N v (hiddenZero profile R N v) =
      hiddenZero profile R N v := by
  have hgateSum :
      (∑ i : Fin N, gate profile (hiddenTau R N)
          (inner ℝ (v i.castSucc) (hiddenZero profile R N v)) • v i.succ) =
        ∑ i : Fin N, gate profile (hiddenTau R N)
          (hiddenCoeff profile R N i.castSucc) • v i.succ := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hiddenZero_coordinate profile R N v hv i.castSucc]
  rw [hiddenMap, hgateSum, hiddenZero, Fin.sum_univ_succ]
  simp only [hiddenCoeff, hiddenCoeffNat, Fin.val_zero, Fin.val_succ,
    Fin.val_castSucc]
  rw [Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_smul]

theorem hiddenCoeffNat_nonneg_le (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    0 ≤ hiddenCoeffNat profile R N k ∧
      hiddenCoeffNat profile R N k ≤ hiddenC R N := by
  induction k with
  | zero =>
      simp only [hiddenCoeffNat]
      exact ⟨(hiddenC_pos hR N).le, le_rfl⟩
  | succ k ih =>
      have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
      rcases ih hk' with ⟨hs0, hsc⟩
      have hgate0 := gate_nonneg_of_nonneg profile (hiddenTau_pos hR N) hs0
      have hgateAbs := (gate_basic_bounds profile (hiddenTau_pos hR N)
        (hiddenCoeffNat profile R N k)).2.2.1
      have hgateLe : gate profile (hiddenTau R N)
          (hiddenCoeffNat profile R N k) ≤ hiddenCoeffNat profile R N k := by
        have habs : |hiddenCoeffNat profile R N k| =
            hiddenCoeffNat profile R N k := abs_of_nonneg hs0
        exact (le_abs_self _).trans (hgateAbs.trans_eq habs)
      have hq0 := hiddenQ_nonneg hN
      have hq1 := (hiddenQ_lt_one N).le
      simp only [hiddenCoeffNat]
      constructor
      · exact mul_nonneg hq0 hgate0
      · calc
          hiddenQ N * gate profile (hiddenTau R N)
              (hiddenCoeffNat profile R N k) ≤
              hiddenQ N * hiddenCoeffNat profile R N k :=
            mul_le_mul_of_nonneg_left hgateLe hq0
          _ ≤ 1 * hiddenCoeffNat profile R N k :=
            mul_le_mul_of_nonneg_right hq1 hs0
          _ ≤ hiddenC R N := by simpa using hsc

theorem hiddenCoeffNat_lower (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    hiddenC R N - 5 * (k : ℝ) * hiddenTau R N ≤
      hiddenCoeffNat profile R N k := by
  induction k with
  | zero => simp [hiddenCoeffNat]
  | succ k ih =>
      have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
      have ih' := ih hk'
      rcases hiddenCoeffNat_nonneg_le profile hR hN hk' with ⟨hs0, hsc⟩
      have hgate := (gate_basic_bounds profile (hiddenTau_pos hR N)
        (hiddenCoeffNat profile R N k)).2.2.2.2
      have hq0 := hiddenQ_nonneg hN
      have hq1 := (hiddenQ_lt_one N).le
      have hloss := hidden_loss_identity R N
      have htau0 := (hiddenTau_pos hR N).le
      have honeq0 : 0 ≤ 1 - hiddenQ N := sub_nonneg.mpr hq1
      have hstep : hiddenCoeffNat profile R N k - 5 * hiddenTau R N ≤
          hiddenQ N * gate profile (hiddenTau R N)
            (hiddenCoeffNat profile R N k) := by
        have hmul := mul_le_mul_of_nonneg_left hgate hq0
        have hlossLe : (1 - hiddenQ N) *
            hiddenCoeffNat profile R N k ≤ 4 * hiddenTau R N := by
          calc
            (1 - hiddenQ N) * hiddenCoeffNat profile R N k ≤
                (1 - hiddenQ N) * hiddenC R N :=
              mul_le_mul_of_nonneg_left hsc honeq0
            _ = 4 * hiddenTau R N := hloss
        nlinarith
      simp only [hiddenCoeffNat, Nat.cast_succ]
      nlinarith

theorem hiddenCoeff_bounds (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    3 * hiddenC R N / 8 ≤ hiddenCoeff profile R N i ∧
      hiddenCoeff profile R N i ≤ hiddenC R N := by
  have hiN : i.1 ≤ N := by omega
  rcases hiddenCoeffNat_nonneg_le profile hR hN hiN with ⟨_hs0, hupper⟩
  have hlower := hiddenCoeffNat_lower profile hR hN hiN
  have hik : (i.1 : ℝ) ≤ hiddenM N := by
    exact_mod_cast (Nat.le_trans hiN (Nat.le_succ N))
  have htau0 := (hiddenTau_pos hR N).le
  have hmass := hidden_mass_identity R N
  have hmul : (i.1 : ℝ) * hiddenTau R N ≤
      (hiddenM N : ℝ) * hiddenTau R N :=
    mul_le_mul_of_nonneg_right hik htau0
  constructor
  · change 3 * hiddenC R N / 8 ≤ hiddenCoeffNat profile R N i.1
    nlinarith
  · exact hupper

theorem hiddenZero_norm_bounds (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) :
    3 * R / 16 ≤ ‖hiddenZero profile R N v‖ ∧
      ‖hiddenZero profile R N v‖ ≤ R / Real.sqrt 3 := by
  have hc0 := (hiddenC_pos hR N).le
  have hbase0 : 0 ≤ 3 * hiddenC R N / 8 := by positivity
  have hnormsq : ‖hiddenZero profile R N v‖ ^ 2 =
      ∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2 := by
    exact orthonormal_norm_sum_sq hv (hiddenCoeff profile R N)
  have hlowerSum :
      (hiddenM N : ℝ) * (3 * hiddenC R N / 8) ^ 2 ≤
        ∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2 := by
    calc
      (hiddenM N : ℝ) * (3 * hiddenC R N / 8) ^ 2 =
          ∑ _i : Fin (N + 1), (3 * hiddenC R N / 8) ^ 2 := by
        simp [hiddenM]
      _ ≤ ∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hi := (hiddenCoeff_bounds profile hR hN i).1
        have hci0 : 0 ≤ hiddenCoeff profile R N i := hbase0.trans hi
        exact (sq_le_sq₀ hbase0 hci0).2 hi
  have hupperSum :
      (∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2) ≤
        (hiddenM N : ℝ) * hiddenC R N ^ 2 := by
    calc
      (∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2) ≤
          ∑ _i : Fin (N + 1), hiddenC R N ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hi := hiddenCoeff_bounds profile hR hN i
        have hci0 : 0 ≤ hiddenCoeff profile R N i := hbase0.trans hi.1
        exact (sq_le_sq₀ hci0 hc0).2 hi.2
      _ = (hiddenM N : ℝ) * hiddenC R N ^ 2 := by simp [hiddenM]
  have hmass := hidden_c_sq_mass R N
  have hlowerSq : (3 * R / 16) ^ 2 ≤ ‖hiddenZero profile R N v‖ ^ 2 := by
    rw [hnormsq]
    calc
      (3 * R / 16) ^ 2 =
          (hiddenM N : ℝ) * (3 * hiddenC R N / 8) ^ 2 := by
        nlinarith
      _ ≤ ∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2 := hlowerSum
  have hupperSq : ‖hiddenZero profile R N v‖ ^ 2 ≤ (R / Real.sqrt 3) ^ 2 := by
    rw [hnormsq]
    have hsqrt3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    calc
      (∑ i : Fin (N + 1), hiddenCoeff profile R N i ^ 2) ≤
          (hiddenM N : ℝ) * hiddenC R N ^ 2 := hupperSum
      _ = R ^ 2 / 4 := hmass
      _ ≤ R ^ 2 / 3 := by nlinarith [sq_nonneg R]
      _ = (R / Real.sqrt 3) ^ 2 := by
        rw [div_pow, hsqrt3]
  constructor
  · exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 hlowerSq
  · exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hR.le (Real.sqrt_nonneg _))).1 hupperSq

theorem hiddenZero_mem_openBall (profile : GateProfile) {R : ℝ} (hR : 0 < R)
    {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) :
    hiddenZero profile R N v ∈ Metric.ball (0 : E) R := by
  rw [Metric.mem_ball, dist_zero_right]
  have hu := (hiddenZero_norm_bounds profile hR hN v hv).2
  have hsqrt : 1 < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hs0 := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hsqrt0 : 0 < Real.sqrt 3 := lt_trans (by norm_num) hsqrt
  apply hu.trans_lt
  apply (div_lt_iff₀ hsqrt0).2
  nlinarith

theorem hiddenZero_isZero (p : ℕ) (profile : GateProfile) (Lp R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) :
    hiddenOperator p profile Lp R N v (hiddenZero profile R N v) = 0 := by
  rw [hiddenOperator, hiddenZero_fixed profile R N v hv, sub_self, smul_zero]

/-- A dimension-free coordinate-product estimate.  One factor is summed by
Bessel's inequality; all remaining factors are bounded coordinatewise. -/
theorem orthonormal_coordinate_product_sum_sq_le {ι : Type*} [Fintype ι]
    {w : ι → E} (hw : Orthonormal ℝ w) (z : E) {n : ℕ} (u : Fin n → E) :
    (∑ i : ι, (inner ℝ (w i) z * ∏ j : Fin n, inner ℝ (w i) (u j)) ^ 2) ≤
      ‖z‖ ^ 2 * ∏ j : Fin n, ‖u j‖ ^ 2 := by
  let K : ℝ := ∏ j : Fin n, ‖u j‖ ^ 2
  have hK0 : 0 ≤ K := Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hprod (i : ι) :
      (∏ j : Fin n, inner ℝ (w i) (u j)) ^ 2 ≤ K := by
    calc
      (∏ j : Fin n, inner ℝ (w i) (u j)) ^ 2 =
          ∏ j : Fin n, (inner ℝ (w i) (u j)) ^ 2 := by
        exact (Finset.prod_pow Finset.univ 2 _).symm
      _ ≤ K := by
        apply Finset.prod_le_prod
        · intro j _hj
          exact sq_nonneg _
        · intro j _hj
          have hij : |inner ℝ (w i) (u j)| ≤ ‖u j‖ := by
            calc
              |inner ℝ (w i) (u j)| = ‖inner ℝ (w i) (u j)‖ := by
                rw [Real.norm_eq_abs]
              _ ≤ ‖w i‖ * ‖u j‖ := norm_inner_le_norm _ _
              _ = ‖u j‖ := by rw [hw.1 i, one_mul]
          have hij' : |inner ℝ (w i) (u j)| ≤ |‖u j‖| := by
            simpa [abs_of_nonneg (norm_nonneg _)] using hij
          exact sq_le_sq.mpr hij'
  calc
    (∑ i : ι, (inner ℝ (w i) z * ∏ j : Fin n,
        inner ℝ (w i) (u j)) ^ 2) =
        ∑ i : ι, (inner ℝ (w i) z) ^ 2 *
          (∏ j : Fin n, inner ℝ (w i) (u j)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ i : ι, ‖inner ℝ (w i) z‖ ^ 2 * K := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [Real.norm_eq_abs]
      have hi0 : 0 ≤ inner ℝ (w i) z ^ 2 := sq_nonneg _
      have heq : |inner ℝ (w i) z| ^ 2 = inner ℝ (w i) z ^ 2 := by
        rw [sq_abs]
      rw [heq]
      exact mul_le_mul_of_nonneg_left (hprod i) hi0
    _ = (∑ i : ι, ‖inner ℝ (w i) z‖ ^ 2) * K := by
      rw [Finset.sum_mul]
    _ ≤ ‖z‖ ^ 2 * K :=
      mul_le_mul_of_nonneg_right (hw.sum_inner_products_le z) hK0

theorem hiddenMap_contraction (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E)
    (hv : Orthonormal ℝ v) (x y : E) :
    ‖hiddenMap profile R N v x - hiddenMap profile R N v y‖ ≤
      hiddenQ N * ‖x - y‖ := by
  have htau := hiddenTau_pos hR N
  have hq0 := hiddenQ_nonneg hN
  let a : Fin N → ℝ := fun i =>
    gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) -
      gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) y)
  have htail : Orthonormal ℝ (fun i : Fin N => v i.succ) :=
    hv.comp Fin.succ (Fin.succ_injective N)
  have hhead : Orthonormal ℝ (fun i : Fin N => v i.castSucc) :=
    hv.comp Fin.castSucc (Fin.castSucc_injective N)
  have hsum_sq : ‖∑ i : Fin N, a i • v i.succ‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [orthonormal_norm_sum_sq htail]
    calc
      (∑ i : Fin N, a i ^ 2) ≤
          ∑ i : Fin N, ‖inner ℝ (v i.castSucc) (x - y)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hg := gate_norm_sub_le profile htau.ne'
          (inner ℝ (v i.castSucc) y) (inner ℝ (v i.castSucc) x)
        have hinner :
            inner ℝ (v i.castSucc) x - inner ℝ (v i.castSucc) y =
              inner ℝ (v i.castSucc) (x - y) := by
          rw [inner_sub_right]
        rw [← hinner, Real.norm_eq_abs]
        exact sq_le_sq.mpr (by simpa [a] using hg)
      _ ≤ ‖x - y‖ ^ 2 := hhead.sum_inner_products_le (x - y)
  have hsum : ‖∑ i : Fin N, a i • v i.succ‖ ≤ ‖x - y‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsum_sq
  have hrewrite :
      hiddenMap profile R N v x - hiddenMap profile R N v y =
        hiddenQ N • ∑ i : Fin N, a i • v i.succ := by
    have hsums :
        (∑ i : Fin N,
            gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ) -
          (∑ i : Fin N,
            gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) y) • v i.succ) =
          ∑ i : Fin N, a i • v i.succ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [a, sub_smul]
    simp only [hiddenMap, add_sub_add_left_eq_sub, ← smul_sub]
    rw [hsums]
  rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
  exact mul_le_mul_of_nonneg_left hsum hq0

theorem hiddenZero_unique (p : ℕ) (profile : GateProfile) {Lp R : ℝ}
    (hLp : 0 < Lp) (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) (z : E)
    (hz : hiddenOperator p profile Lp R N v z = 0) :
    z = hiddenZero profile R N v := by
  have hlambda0 : hiddenLambda p profile Lp R N ≠ 0 :=
    (hiddenLambda_pos (p := p) (N := N) profile hLp hR).ne'
  have hzfix : z = hiddenMap profile R N v z := by
    rw [hiddenOperator, smul_eq_zero] at hz
    rcases hz with hz | hz
    · contradiction
    · exact sub_eq_zero.mp hz
  have hstarfix := (hiddenZero_fixed profile R N v hv).symm
  have hcontract := hiddenMap_contraction profile hR hN v hv z
    (hiddenZero profile R N v)
  rw [← hzfix, ← hstarfix] at hcontract
  have hq1 := hiddenQ_lt_one N
  have hnorm0 : ‖z - hiddenZero profile R N v‖ = 0 := by
    have hn := norm_nonneg (z - hiddenZero profile R N v)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

theorem hiddenMap_mapsTo_ball (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E)
    (hv : Orthonormal ℝ v) :
    MapsTo (hiddenMap profile R N v) (Metric.closedBall 0 R)
      (Metric.closedBall 0 R) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  let a : Fin N → ℝ := fun i =>
    gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x)
  have htail : Orthonormal ℝ (fun i : Fin N => v i.succ) :=
    hv.comp Fin.succ (Fin.succ_injective N)
  have hhead : Orthonormal ℝ (fun i : Fin N => v i.castSucc) :=
    hv.comp Fin.castSucc (Fin.castSucc_injective N)
  have hsum_sq : ‖∑ i : Fin N, a i • v i.succ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [orthonormal_norm_sum_sq htail]
    calc
      (∑ i : Fin N, a i ^ 2) ≤
          ∑ i : Fin N, ‖inner ℝ (v i.castSucc) x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hg := (gate_basic_bounds profile (hiddenTau_pos hR N)
          (inner ℝ (v i.castSucc) x)).2.2.1
        rw [Real.norm_eq_abs]
        exact sq_le_sq.mpr (by simpa [a] using hg)
      _ ≤ ‖x‖ ^ 2 := hhead.sum_inner_products_le x
  have horth : inner ℝ
      (hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩)
      (hiddenQ N • ∑ i : Fin N, a i • v i.succ) = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sum]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hv.inner_eq_zero]
    · simp
    · intro heq
      have := congrArg Fin.val heq
      simp at this
  have hnorm_sq : ‖hiddenMap profile R N v x‖ ^ 2 =
      hiddenC R N ^ 2 + hiddenQ N ^ 2 * ‖∑ i : Fin N, a i • v i.succ‖ ^ 2 := by
    change ‖hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩ +
        hiddenQ N • ∑ i : Fin N, a i • v i.succ‖ ^ 2 = _
    rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real horth,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hiddenQ_nonneg hN)]
    have hc0 : 0 ≤ hiddenC R N := (hiddenC_pos hR N).le
    rw [abs_of_nonneg hc0, hv.1]
    ring
  have hsq : ‖hiddenMap profile R N v x‖ ^ 2 ≤ R ^ 2 := by
    rw [hnorm_sq]
    calc
      hiddenC R N ^ 2 + hiddenQ N ^ 2 *
          ‖∑ i : Fin N, a i • v i.succ‖ ^ 2 ≤
          hiddenC R N ^ 2 + hiddenQ N ^ 2 * ‖x‖ ^ 2 := by
        gcongr
      _ ≤ hiddenC R N ^ 2 + hiddenQ N ^ 2 * R ^ 2 := by
        gcongr
      _ ≤ R ^ 2 := hidden_ball_scalar_bound hN
  exact (sq_le_sq₀ (norm_nonneg _) hR.le).1 hsq

theorem hiddenMap_contDiff (profile : GateProfile) {R : ℝ} (hR : 0 < R) {N : ℕ}
    (v : Fin (N + 1) → E) : ContDiff ℝ ∞ (hiddenMap profile R N v) := by
  have htau : hiddenTau R N ≠ 0 := (hiddenTau_pos hR N).ne'
  apply ContDiff.add
  · fun_prop
  · apply ContDiff.const_smul
    apply ContDiff.sum
    intro i _hi
    apply ContDiff.smul_const
    exact (gate_contDiff profile htau).comp ((innerSL ℝ (v i.castSucc)).contDiff)

theorem hiddenMap_iteratedFDeriv_sub_apply (n : ℕ) (profile : GateProfile)
    {R : ℝ} (hR : 0 < R) {N : ℕ} (v : Fin (N + 1) → E)
    (x y : E) (u : Fin n → E) :
    (iteratedFDeriv ℝ n (hiddenMap profile R N v) x -
        iteratedFDeriv ℝ n (hiddenMap profile R N v) y) u =
      hiddenQ N • ∑ i : Fin N,
        (((∏ j : Fin n, inner ℝ (v i.castSucc) (u j)) *
            (iteratedDeriv n (gate profile (hiddenTau R N))
                (inner ℝ (v i.castSucc) x) -
              iteratedDeriv n (gate profile (hiddenTau R N))
                (inner ℝ (v i.castSucc) y))) • v i.succ) := by
  let G : E → E := fun z => ∑ i : Fin N,
    gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ) z
  have hridge (i : Fin N) : ContDiff ℝ n
      (gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ)) := by
    exact ((contDiff_infty.mp
      (gate_contDiff profile (hiddenTau_pos hR N).ne') n).comp
        (innerSL ℝ (v i.castSucc)).contDiff).smul_const _
  have hG : ContDiff ℝ n G := by
    apply ContDiff.sum
    intro i _hi
    exact hridge i
  have hqG : ContDiff ℝ n (fun z => hiddenQ N • G z) :=
    hG.const_smul (hiddenQ N)
  have hmap : hiddenMap profile R N v = fun z =>
      hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩ + hiddenQ N • G z := by
    funext z
    simp only [hiddenMap, G, gateRidge]
  rw [hmap]
  change (iteratedFDeriv ℝ n
      ((fun _ : E => hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) +
        fun z => hiddenQ N • G z) x -
      iteratedFDeriv ℝ n
      ((fun _ : E => hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) +
        fun z => hiddenQ N • G z) y) u = _
  rw [iteratedFDeriv_add_apply contDiffAt_const hqG.contDiffAt,
    iteratedFDeriv_add_apply contDiffAt_const hqG.contDiffAt]
  have hsmul (z : E) :
      iteratedFDeriv ℝ n (fun z => hiddenQ N • G z) z =
        hiddenQ N • iteratedFDeriv ℝ n G z := by
    exact iteratedFDeriv_const_smul_apply' hG.contDiffAt
  rw [hsmul x, hsmul y]
  change (_ + hiddenQ N • iteratedFDeriv ℝ n G x -
      (_ + hiddenQ N • iteratedFDeriv ℝ n G y)) u = _
  have hconst :
      iteratedFDeriv ℝ n (fun _ : E =>
        hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) x =
      iteratedFDeriv ℝ n (fun _ : E =>
        hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩) y := by
    by_cases hn : n = 0
    · subst n
      rfl
    · simp [iteratedFDeriv_const_of_ne hn]
  rw [hconst]
  simp only [add_sub_add_left_eq_sub, ← smul_sub,
    smul_apply]
  congr 1
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hridge i).contDiffAt),
    iteratedFDeriv_fun_sum_apply (fun i _ => (hridge i).contDiffAt)]
  rw [sub_apply]
  rw [sum_apply, sum_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [gateRidge_iteratedFDeriv_apply n profile (hiddenTau_pos hR N).ne',
    gateRidge_iteratedFDeriv_apply n profile (hiddenTau_pos hR N).ne']
  module

theorem hiddenMap_top_derivative_lipschitz (p : ℕ) (profile : GateProfile)
    (hp : 2 ≤ p) {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) (x y : E) :
    ‖iteratedFDeriv ℝ (p - 1) (hiddenMap profile R N v) x -
        iteratedFDeriv ℝ (p - 1) (hiddenMap profile R N v) y‖ ≤
      hiddenQ N * (gateBp p profile *
        hiddenTau R N ^ (1 - (p : ℤ))) * ‖x - y‖ := by
  let n := p - 1
  let A := gateBp p profile * hiddenTau R N ^ (1 - (p : ℤ))
  have hA0 : 0 ≤ A := mul_nonneg (gateBp_pos p profile).le
    (zpow_nonneg (hiddenTau_pos hR N).le _)
  have hq0 := hiddenQ_nonneg hN
  have htail : Orthonormal ℝ (fun i : Fin N => v i.succ) :=
    hv.comp Fin.succ (Fin.succ_injective N)
  have hhead : Orthonormal ℝ (fun i : Fin N => v i.castSucc) :=
    hv.comp Fin.castSucc (Fin.castSucc_injective N)
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (mul_nonneg hq0 hA0) (norm_nonneg _))
  intro u
  let b : Fin N → ℝ := fun i =>
    (∏ j : Fin n, inner ℝ (v i.castSucc) (u j)) *
      (iteratedDeriv n (gate profile (hiddenTau R N))
          (inner ℝ (v i.castSucc) x) -
        iteratedDeriv n (gate profile (hiddenTau R N))
          (inner ℝ (v i.castSucc) y))
  have hb (i : Fin N) :
      |b i| ≤ A *
        |inner ℝ (v i.castSucc) (x - y) *
          ∏ j : Fin n, inner ℝ (v i.castSucc) (u j)| := by
    have hg := gate_high_derivative_lipschitz p profile hp
      (hiddenTau_pos hR N)
      (inner ℝ (v i.castSucc) x) (inner ℝ (v i.castSucc) y)
    have hinner :
        inner ℝ (v i.castSucc) x - inner ℝ (v i.castSucc) y =
          inner ℝ (v i.castSucc) (x - y) := by rw [inner_sub_right]
    rw [hinner] at hg
    calc
      |b i| =
          |iteratedDeriv n (gate profile (hiddenTau R N))
              (inner ℝ (v i.castSucc) x) -
            iteratedDeriv n (gate profile (hiddenTau R N))
              (inner ℝ (v i.castSucc) y)| *
            |∏ j : Fin n, inner ℝ (v i.castSucc) (u j)| := by
        simp only [b, abs_mul]
        ring
      _ ≤ (A * |inner ℝ (v i.castSucc) (x - y)|) *
            |∏ j : Fin n, inner ℝ (v i.castSucc) (u j)| := by
        apply mul_le_mul_of_nonneg_right
        · simpa [A, n] using hg
        · positivity
      _ = A * |inner ℝ (v i.castSucc) (x - y) *
            ∏ j : Fin n, inner ℝ (v i.castSucc) (u j)| := by
        rw [abs_mul]
        ring
  have hb_sq (i : Fin N) :
      (b i) ^ 2 ≤ A ^ 2 *
        (inner ℝ (v i.castSucc) (x - y) *
          ∏ j : Fin n, inner ℝ (v i.castSucc) (u j)) ^ 2 := by
    have hrhs0 : 0 ≤ A *
        |inner ℝ (v i.castSucc) (x - y) *
          ∏ j : Fin n, inner ℝ (v i.castSucc) (u j)| := mul_nonneg hA0 (abs_nonneg _)
    have hb' : |b i| ≤ abs (A *
        abs (inner ℝ (v i.castSucc) (x - y) *
          ∏ j : Fin n, inner ℝ (v i.castSucc) (u j))) := by
      rw [abs_of_nonneg hrhs0]
      exact hb i
    have hs := sq_le_sq.mpr hb'
    simpa [sq_abs, mul_pow] using hs
  have hcoord := orthonormal_coordinate_product_sum_sq_le hhead (x - y) u
  have hsum_sq : (∑ i : Fin N, b i ^ 2) ≤
      A ^ 2 * (‖x - y‖ ^ 2 * ∏ j : Fin n, ‖u j‖ ^ 2) := by
    calc
      (∑ i : Fin N, b i ^ 2) ≤
          ∑ i : Fin N, A ^ 2 *
            (inner ℝ (v i.castSucc) (x - y) *
              ∏ j : Fin n, inner ℝ (v i.castSucc) (u j)) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => hb_sq i
      _ = A ^ 2 * ∑ i : Fin N,
            (inner ℝ (v i.castSucc) (x - y) *
              ∏ j : Fin n, inner ℝ (v i.castSucc) (u j)) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ A ^ 2 * (‖x - y‖ ^ 2 * ∏ j : Fin n, ‖u j‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hcoord (sq_nonneg A)
  have hsum_norm : ‖∑ i : Fin N, b i • v i.succ‖ ≤
      A * ‖x - y‖ * ∏ j : Fin n, ‖u j‖ := by
    have hP0 : 0 ≤ ∏ j : Fin n, ‖u j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hright0 : 0 ≤ A * ‖x - y‖ * ∏ j : Fin n, ‖u j‖ := by positivity
    apply (sq_le_sq₀ (norm_nonneg _) hright0).1
    rw [orthonormal_norm_sum_sq htail]
    calc
      (∑ i : Fin N, b i ^ 2) ≤
          A ^ 2 * (‖x - y‖ ^ 2 * ∏ j : Fin n, ‖u j‖ ^ 2) := hsum_sq
      _ = (A * ‖x - y‖ * ∏ j : Fin n, ‖u j‖) ^ 2 := by
        rw [Finset.prod_pow]
        ring
  have hformula := hiddenMap_iteratedFDeriv_sub_apply n profile hR v x y u
  change ‖(iteratedFDeriv ℝ n (hiddenMap profile R N v) x -
      iteratedFDeriv ℝ n (hiddenMap profile R N v) y) u‖ ≤ _
  rw [hformula, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
  calc
    hiddenQ N * ‖∑ i : Fin N, b i • v i.succ‖ ≤
        hiddenQ N * (A * ‖x - y‖ * ∏ j : Fin n, ‖u j‖) :=
      mul_le_mul_of_nonneg_left hsum_norm hq0
    _ = (hiddenQ N * A * ‖x - y‖) * ∏ j : Fin n, ‖u j‖ := by ring

theorem hiddenOperator_contDiff (p : ℕ) (profile : GateProfile) (Lp : ℝ)
    {R : ℝ} (hR : 0 < R) {N : ℕ} (v : Fin (N + 1) → E) :
    ContDiff ℝ ∞ (hiddenOperator p profile Lp R N v) := by
  apply ContDiff.const_smul
  exact contDiff_id.sub (hiddenMap_contDiff profile hR v)

theorem iteratedFDeriv_id_eq_of_pos {n : ℕ} (hn : 0 < n) (x y : E) :
    iteratedFDeriv ℝ n (id : E → E) x = iteratedFDeriv ℝ n id y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction k generalizing x y with
  | zero =>
      ext u
      rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
        fderiv_id, fderiv_id]
  | succ k ih =>
      have hfun : iteratedFDeriv ℝ (k + 1) (id : E → E) =
          fun _ => iteratedFDeriv ℝ (k + 1) id x := by
        funext z
        exact ih z x (by omega)
      ext u
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left,
        hfun]
      simp

theorem hiddenOperator_top_derivative_lipschitz (p : ℕ) (profile : GateProfile)
    (hp : 2 ≤ p) {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R)
    {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v)
    (x y : E) :
    ‖iteratedFDeriv ℝ (p - 1) (hiddenOperator p profile Lp R N v) x -
        iteratedFDeriv ℝ (p - 1) (hiddenOperator p profile Lp R N v) y‖ ≤
      Lp * ‖x - y‖ := by
  let n := p - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hT := hiddenMap_top_derivative_lipschitz p profile hp hR hN v hv x y
  have hId := iteratedFDeriv_id_eq_of_pos hn x y
  have hF (z : E) :
      iteratedFDeriv ℝ n (hiddenOperator p profile Lp R N v) z =
        hiddenLambda p profile Lp R N •
          (iteratedFDeriv ℝ n id z -
            iteratedFDeriv ℝ n (hiddenMap profile R N v) z) := by
    have hsub : ContDiffAt ℝ n
        (fun w : E => id w - hiddenMap profile R N v w) z :=
      contDiffAt_id.sub
        ((contDiff_infty.mp (hiddenMap_contDiff profile hR v) n).contDiffAt)
    have hmap : hiddenOperator p profile Lp R N v = fun w =>
        hiddenLambda p profile Lp R N •
          (id w - hiddenMap profile R N v w) := by
      funext w
      rfl
    rw [hmap, iteratedFDeriv_const_smul_apply' hsub,
      ]
    congr 1
    change iteratedFDeriv ℝ n
        ((id : E → E) - hiddenMap profile R N v) z = _
    exact iteratedFDeriv_sub_apply contDiffAt_id
      ((contDiff_infty.mp (hiddenMap_contDiff profile hR v) n).contDiffAt)
  rw [show p - 1 = n by rfl, hF x, hF y]
  rw [← smul_sub]
  have hrearrange :
      (iteratedFDeriv ℝ n id x - iteratedFDeriv ℝ n
          (hiddenMap profile R N v) x) -
        (iteratedFDeriv ℝ n id y - iteratedFDeriv ℝ n
          (hiddenMap profile R N v) y) =
        -(iteratedFDeriv ℝ n (hiddenMap profile R N v) x -
          iteratedFDeriv ℝ n (hiddenMap profile R N v) y) := by
    rw [hId]
    abel
  rw [hrearrange, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_pos (hiddenLambda_pos (p := p) (N := N) profile hLp hR)]
  calc
    hiddenLambda p profile Lp R N *
        ‖iteratedFDeriv ℝ n (hiddenMap profile R N v) x -
          iteratedFDeriv ℝ n (hiddenMap profile R N v) y‖ ≤
      hiddenLambda p profile Lp R N *
        (hiddenQ N * (gateBp p profile *
          hiddenTau R N ^ (1 - (p : ℤ))) * ‖x - y‖) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [n] using hT
      · exact (hiddenLambda_pos (p := p) (N := N) profile hLp hR).le
    _ ≤ hiddenLambda p profile Lp R N *
        (gateBp p profile * hiddenTau R N ^ (1 - (p : ℤ))) *
          ‖x - y‖ := by
      have hq1 : hiddenQ N ≤ 1 := (hiddenQ_lt_one N).le
      have hscale0 : 0 ≤ gateBp p profile *
          hiddenTau R N ^ (1 - (p : ℤ)) :=
        mul_nonneg (gateBp_pos p profile).le
          (zpow_nonneg (hiddenTau_pos hR N).le _)
      have hl0 := (hiddenLambda_pos (p := p) (N := N) profile hLp hR).le
      calc
        hiddenLambda p profile Lp R N *
            (hiddenQ N * (gateBp p profile *
              hiddenTau R N ^ (1 - (p : ℤ))) * ‖x - y‖) =
          (hiddenLambda p profile Lp R N *
            (gateBp p profile * hiddenTau R N ^ (1 - (p : ℤ))) *
              ‖x - y‖) * hiddenQ N := by ring
        _ ≤ (hiddenLambda p profile Lp R N *
            (gateBp p profile * hiddenTau R N ^ (1 - (p : ℤ))) *
              ‖x - y‖) * 1 := by
          apply mul_le_mul_of_nonneg_left hq1
          positivity
        _ = hiddenLambda p profile Lp R N *
            (gateBp p profile * hiddenTau R N ^ (1 - (p : ℤ))) *
              ‖x - y‖ := by ring
    _ = Lp * ‖x - y‖ := by
      rw [hidden_scaling_identity (by omega) profile Lp hR]

theorem hiddenOperator_strongMonotone (p : ℕ) (profile : GateProfile)
    {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) (x y : E) :
    hiddenLambda p profile Lp R N * (1 - hiddenQ N) * ‖x - y‖ ^ 2 ≤
      inner ℝ
        (hiddenOperator p profile Lp R N v x -
          hiddenOperator p profile Lp R N v y) (x - y) := by
  let d := x - y
  let e := hiddenMap profile R N v x - hiddenMap profile R N v y
  have hlambda0 : 0 ≤ hiddenLambda p profile Lp R N :=
    (hiddenLambda_pos (p := p) (N := N) profile hLp hR).le
  have hq0 := hiddenQ_nonneg hN
  have he : ‖e‖ ≤ hiddenQ N * ‖d‖ := by
    exact hiddenMap_contraction profile hR hN v hv x y
  have hip : inner ℝ e d ≤ hiddenQ N * ‖d‖ ^ 2 := by
    calc
      inner ℝ e d ≤ ‖e‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ (hiddenQ N * ‖d‖) * ‖d‖ := by gcongr
      _ = hiddenQ N * ‖d‖ ^ 2 := by ring
  have hrewrite :
      hiddenOperator p profile Lp R N v x -
          hiddenOperator p profile Lp R N v y =
        hiddenLambda p profile Lp R N • (d - e) := by
    simp only [hiddenOperator, d, e]
    module
  rw [hrewrite, real_inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq]
  nlinarith

theorem hiddenOperator_admissible [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) :
    IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
      (hiddenOperator p profile Lp R N v) := by
  let data := ballVIData (E := E) p hp Lp hLp R hR
  refine
    { regularity := ?_
      monotone_on := ?_
      top_derivative_lipschitz := ?_ }
  · refine ⟨Set.univ, isOpen_univ, subset_univ _, ?_⟩
    exact (contDiff_infty.mp
      (hiddenOperator_contDiff p profile Lp hR v) (p - 1)).contDiffOn
  · intro x _hx y _hy
    have hstrong := hiddenOperator_strongMonotone p profile hLp hR hN v hv x y
    have hcoef0 : 0 ≤ hiddenLambda p profile Lp R N * (1 - hiddenQ N) := by
      exact mul_nonneg
        (hiddenLambda_pos (p := p) (N := N) profile hLp hR).le
        (sub_nonneg.mpr (hiddenQ_lt_one N).le)
    exact (mul_nonneg hcoef0 (sq_nonneg ‖x - y‖)).trans hstrong
  · intro x _hx y _hy
    exact hiddenOperator_top_derivative_lipschitz p profile hp hLp hR hN v hv x y

theorem hiddenOperator_inner_normal_nonneg (p : ℕ) (profile : GateProfile)
    {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v)
    {x n : E} (hx : x ∈ Metric.closedBall (0 : E) R)
    (hn : n ∈ normalCone (Metric.closedBall (0 : E) R) x) :
    0 ≤ inner ℝ (hiddenOperator p profile Lp R N v x) n := by
  have hTx := hiddenMap_mapsTo_ball profile hR hN v hv hx
  have hnormal := hn (hiddenMap profile R N v x) hTx
  have hlambda0 := (hiddenLambda_pos (p := p) (N := N) profile hLp hR).le
  rw [hiddenOperator, real_inner_smul_left]
  have hinner : 0 ≤ inner ℝ (x - hiddenMap profile R N v x) n := by
    rw [← real_inner_comm]
    rw [show x - hiddenMap profile R N v x =
      -(hiddenMap profile R N v x - x) by abel, inner_neg_right]
    linarith
  exact mul_nonneg hlambda0 hinner

theorem hiddenOperator_tangentResidual [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (hp : 2 ≤ p)
    (profile : GateProfile) {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R)
    {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v)
    (x : E) (hx : x ∈ Metric.closedBall (0 : E) R) :
    tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
        (hiddenOperator p profile Lp R N v) x =
      ‖hiddenOperator p profile Lp R N v x‖ := by
  let F := hiddenOperator p profile Lp R N v
  let S := (fun n => F x + n) '' normalCone (Metric.closedBall (0 : E) R) x
  have hzero : (0 : E) ∈ normalCone (Metric.closedBall (0 : E) R) x := by
    intro z _hz
    simp
  have hFx : F x ∈ S := ⟨0, hzero, by simp⟩
  have hS : S.Nonempty := ⟨F x, hFx⟩
  change Metric.infDist 0 S = ‖F x‖
  apply le_antisymm
  · have hu := Metric.infDist_le_dist_of_mem (x := (0 : E)) hFx
    simpa [dist_zero_left] using hu
  · apply (Metric.le_infDist hS).2
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    rw [dist_zero_left]
    have hip : 0 ≤ inner ℝ (F x) n := by
      exact hiddenOperator_inner_normal_nonneg p profile hLp hR hN v hv hx hn
    have hip' : 0 ≤ inner ℝ n (F x) := by
      rw [real_inner_comm]
      exact hip
    have hsq : ‖F x‖ ^ 2 ≤ ‖F x + n‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right]
      rw [real_inner_comm n (F x), real_inner_self_eq_norm_sq]
      nlinarith [hip', real_inner_self_nonneg (x := n)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Source-faithful conclusion bundle for `lem:operator`. -/
def HiddenOperatorConclusion [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile) (Lp R : ℝ)
    (hLp : 0 < Lp) (hR : 0 < R) (N : ℕ) (v : Fin (N + 1) → E) : Prop :=
  let q := hiddenQ N
  let lambda := hiddenLambda p profile Lp R N
  let T := hiddenMap profile R N v
  let F := hiddenOperator p profile Lp R N v
  let data := ballVIData (E := E) p hp Lp hLp R hR
  (∀ x y, ‖T x - T y‖ ≤ q * ‖x - y‖) ∧
  MapsTo T (Metric.closedBall 0 R) (Metric.closedBall 0 R) ∧
  (∀ x y, lambda * (1 - q) * ‖x - y‖ ^ 2 ≤
    inner ℝ (F x - F y) (x - y)) ∧
  IsAdmissibleOperator data F ∧
  (∃ xStar : E,
    F xStar = 0 ∧ xStar ∈ Metric.ball 0 R ∧
    xStar ∈ Metric.closedBall 0 R ∧
    3 * R / 16 ≤ ‖xStar‖ ∧ ‖xStar‖ ≤ R / Real.sqrt 3 ∧
    (∀ z : E, F z = 0 → z = xStar)) ∧
  ∀ x ∈ Metric.closedBall 0 R,
    tangentResidual data F x = ‖F x‖

/-- Proposition corresponding exactly to `lem:operator`. -/
def HiddenOperatorClaim [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (profile : GateProfile) (Lp R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) : Prop :=
  ∀ hp : 2 ≤ p, ∀ hLp : 0 < Lp, ∀ hR : 0 < R,
    1 ≤ N → Orthonormal ℝ v →
      HiddenOperatorConclusion p hp profile Lp R hLp hR N v

/-- Kernel-checked headline theorem for `lem:operator`. -/
theorem hiddenOperatorClaim_proof [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (profile : GateProfile) (Lp R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) :
    HiddenOperatorClaim p profile Lp R N v := by
  intro hp hLp hR hN hv
  dsimp [HiddenOperatorConclusion]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y => hiddenMap_contraction profile hR hN v hv x y
  · exact hiddenMap_mapsTo_ball profile hR hN v hv
  · exact fun x y => hiddenOperator_strongMonotone p profile hLp hR hN v hv x y
  · exact hiddenOperator_admissible p hp profile hLp hR hN v hv
  · refine ⟨hiddenZero profile R N v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hiddenZero_isZero p profile Lp R N v hv
    · exact hiddenZero_mem_openBall profile hR hN v hv
    · exact Metric.ball_subset_closedBall
        (hiddenZero_mem_openBall profile hR hN v hv)
    · exact (hiddenZero_norm_bounds profile hR hN v hv).1
    · exact (hiddenZero_norm_bounds profile hR hN v hv).2
    · intro z hz
      exact hiddenZero_unique p profile hLp hR hN v hv z hz
  · intro x hx
    exact hiddenOperator_tangentResidual p hp profile hLp hR hN v hv x hx

end Construction

end LeanArticleAudit.Pilot
