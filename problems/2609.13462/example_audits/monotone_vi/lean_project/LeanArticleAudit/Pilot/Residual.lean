import LeanArticleAudit.Pilot.Operator

/-!
# Residual lower bound on the hidden final-coordinate slab

This module formalizes `lem:residual`.  Indices are zero-based, so the
article's final vector `v_m` is `v (Fin.last N)` when `m=N+1`.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

section ScalarTelescope

/-- Backward-geometric weighted error expression used in the hidden-chain
telescoping argument. -/
noncomputable def weightedChainError (q c tau : ℝ) (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => s 0 - c
  | n + 1 => q * weightedChainError q c tau s n +
      (s (n + 1) - q * s n + q * tau)

noncomputable def reverseGeom (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => q * reverseGeom q n + 1

/-- Exact telescoping formula for the recursively weighted chain. -/
theorem weightedChainError_eq (q c tau : ℝ) (s : ℕ → ℝ) (N : ℕ) :
    weightedChainError q c tau s N =
      s N - c * q ^ N + q * tau * reverseGeom q N := by
  induction N with
  | zero => simp [weightedChainError, reverseGeom]
  | succ N ih =>
      rw [weightedChainError, ih, reverseGeom, pow_succ]
      ring

theorem reverseGeom_nonneg_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    0 ≤ reverseGeom q N ∧ reverseGeom q N ≤ N := by
  induction N with
  | zero => simp [reverseGeom]
  | succ N ih =>
      simp only [reverseGeom, Nat.cast_succ]
      constructor
      · exact add_nonneg (mul_nonneg hq0 ih.1) zero_le_one
      · nlinarith [mul_le_mul_of_nonneg_right hq1 ih.1,
          mul_le_mul_of_nonneg_left ih.2 hq0]

/-- Recursive form of the backward-geometric witness. -/
noncomputable def chainWitness {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (q : ℝ) (v : ℕ → E) : ℕ → E
  | 0 => v 0
  | n + 1 => q • chainWitness q v n + v (n + 1)

end ScalarTelescope

section Residual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The backward-geometric witness vector
`w=∑ᵢ q^(m-1-i) vᵢ`. -/
noncomputable def hiddenResidualWitness (N : ℕ) (v : Fin (N + 1) → E) : E :=
  ∑ i : Fin (N + 1), hiddenQ N ^ (N - i.1) • v i

/-- Total natural-number view of a finite frame; values beyond the frame are
irrelevant and set to zero. -/
noncomputable def finFrameNat (N : ℕ) (v : Fin (N + 1) → E) (k : ℕ) : E :=
  if hk : k < N + 1 then v ⟨k, hk⟩ else 0

theorem finFrameNat_eq {N k : ℕ} (v : Fin (N + 1) → E) (hk : k ≤ N) :
    finFrameNat N v k = v ⟨k, by omega⟩ := by
  simp [finFrameNat, show k < N + 1 by omega]

theorem chainWitness_orthogonal_later {q : ℝ} {v : ℕ → E} {N j : ℕ}
    (horth : ∀ a ≤ N, ∀ b ≤ N, a ≠ b → inner ℝ (v a) (v b) = 0)
    (hjN : j ≤ N) : ∀ k < j, inner ℝ (v j) (chainWitness q v k) = 0 := by
  intro k hkj
  induction k with
  | zero =>
      simp only [chainWitness]
      exact horth j hjN 0 (Nat.zero_le _) (by omega)
  | succ k ih =>
      simp only [chainWitness, inner_add_right, real_inner_smul_right]
      rw [ih (by omega), horth j hjN (k + 1) (by omega) (by omega)]
      ring

theorem chainWitness_norm_sq_le {q : ℝ} {v : ℕ → E} {N : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hnorm : ∀ k ≤ N, ‖v k‖ = 1)
    (horth : ∀ a ≤ N, ∀ b ≤ N, a ≠ b → inner ℝ (v a) (v b) = 0) :
    ∀ k ≤ N, ‖chainWitness q v k‖ ^ 2 ≤ k + 1 := by
  intro k hkN
  induction k with
  | zero => simp [chainWitness, hnorm 0 (Nat.zero_le _)]
  | succ k ih =>
      have hkN' : k ≤ N := by omega
      have hperp : inner ℝ (q • chainWitness q v k) (v (k + 1)) = 0 := by
        rw [real_inner_smul_left, real_inner_comm]
        rw [chainWitness_orthogonal_later horth hkN (k := k) (by omega), mul_zero]
      have hsqeq : ‖chainWitness q v (k + 1)‖ ^ 2 =
          q ^ 2 * ‖chainWitness q v k‖ ^ 2 + 1 := by
        rw [chainWitness, pow_two,
          norm_add_sq_eq_norm_sq_add_norm_sq_real hperp,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0,
          hnorm (k + 1) hkN]
        ring
      rw [hsqeq]
      have hq2 : q ^ 2 ≤ 1 := by nlinarith
      have hi := ih hkN'
      have hmul : q ^ 2 * ‖chainWitness q v k‖ ^ 2 ≤ k + 1 := calc
        q ^ 2 * ‖chainWitness q v k‖ ^ 2
            ≤ 1 * ‖chainWitness q v k‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
        _ ≤ 1 * (k + 1) := mul_le_mul_of_nonneg_left hi zero_le_one
        _ = k + 1 := by ring
      norm_num at hmul ⊢
      linarith

theorem chainWitness_norm_le_sqrt {q : ℝ} {v : ℕ → E} {N : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hnorm : ∀ k ≤ N, ‖v k‖ = 1)
    (horth : ∀ a ≤ N, ∀ b ≤ N, a ≠ b → inner ℝ (v a) (v b) = 0) :
    ‖chainWitness q v N‖ ≤ Real.sqrt (N + 1) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (by positivity)]
  exact chainWitness_norm_sq_le hq0 hq1 hnorm horth N le_rfl

theorem hiddenMap_coordinate_zero (profile : GateProfile) (R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) (x : E) :
    inner ℝ (v ⟨0, Nat.zero_lt_succ N⟩) (hiddenMap profile R N v x) =
      hiddenC R N := by
  simp only [hiddenMap, inner_add_right, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, hv.1]
  norm_num
  have htail : inner ℝ (v ⟨0, Nat.zero_lt_succ N⟩)
      (∑ i : Fin N,
        gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ) = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [inner_smul_right, hv.inner_eq_zero]
    · simp
    · intro heq
      have := congrArg Fin.val heq
      simp at this
  exact Or.inr htail

theorem hiddenMap_coordinate_succ (profile : GateProfile) (R : ℝ) (N : ℕ)
    (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v) (x : E) (i : Fin N) :
    inner ℝ (v i.succ) (hiddenMap profile R N v x) =
      hiddenQ N * gate profile (hiddenTau R N)
        (inner ℝ (v i.castSucc) x) := by
  simp only [hiddenMap, inner_add_right, real_inner_smul_right]
  have hhead : inner ℝ (v i.succ) (v ⟨0, Nat.zero_lt_succ N⟩) = 0 := by
    rw [hv.inner_eq_zero]
    intro heq
    have := congrArg Fin.val heq
    simp at this
  rw [hhead, mul_zero, zero_add]
  congr 1
  have htail : Orthonormal ℝ (fun j : Fin N => v j.succ) :=
    hv.comp Fin.succ (Fin.succ_injective N)
  exact htail.inner_right_fintype
    (fun j : Fin N => gate profile (hiddenTau R N)
      (inner ℝ (v j.castSucc) x)) i

theorem finFrameNat_norm {N k : ℕ} (v : Fin (N + 1) → E)
    (hv : Orthonormal ℝ v) (hk : k ≤ N) : ‖finFrameNat N v k‖ = 1 := by
  rw [finFrameNat_eq v hk]
  exact hv.1 _

theorem finFrameNat_inner_eq_zero {N a b : ℕ} (v : Fin (N + 1) → E)
    (hv : Orthonormal ℝ v) (ha : a ≤ N) (hb : b ≤ N) (hab : a ≠ b) :
    inner ℝ (finFrameNat N v a) (finFrameNat N v b) = 0 := by
  rw [finFrameNat_eq v ha, finFrameNat_eq v hb]
  apply hv.inner_eq_zero
  intro h
  apply hab
  exact congrArg Fin.val h

/-- The backward-geometric witness applied to the actual chain error is
bounded by the scalar telescope from the article. -/
theorem chainWitness_inner_error_le (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E)
    (hv : Orthonormal ℝ v) (x : E) : ∀ k ≤ N,
    inner ℝ (chainWitness (hiddenQ N) (finFrameNat N v) k)
        (x - hiddenMap profile R N v x) ≤
      weightedChainError (hiddenQ N) (hiddenC R N) (hiddenTau R N)
        (fun j => inner ℝ (finFrameNat N v j) x) k := by
  intro k hkN
  induction k with
  | zero =>
      simp only [chainWitness, weightedChainError, inner_sub_right]
      rw [finFrameNat_eq v (Nat.zero_le _), hiddenMap_coordinate_zero profile R N v hv x]
  | succ k ih =>
      have hkN' : k ≤ N := by omega
      have hklt : k < N := by omega
      let i : Fin N := ⟨k, hklt⟩
      have hframeSucc : finFrameNat N v (k + 1) = v i.succ := by
        rw [finFrameNat_eq v hkN]
        rfl
      have hframePrev : finFrameNat N v k = v i.castSucc := by
        rw [finFrameNat_eq v hkN']
        rfl
      simp only [chainWitness, weightedChainError, inner_add_left,
        real_inner_smul_left]
      have hcoord : inner ℝ (finFrameNat N v (k + 1))
          (x - hiddenMap profile R N v x) =
          inner ℝ (finFrameNat N v (k + 1)) x -
            hiddenQ N * gate profile (hiddenTau R N)
              (inner ℝ (finFrameNat N v k) x) := by
        rw [inner_sub_right, hframeSucc, hframePrev,
          hiddenMap_coordinate_succ profile R N v hv x i]
      rw [hcoord]
      have hq0 := hiddenQ_nonneg hN
      have hgate := (gate_basic_bounds profile (hiddenTau_pos hR N)
        (inner ℝ (finFrameNat N v k) x)).2.2.2.2
      have hih := ih hkN'
      nlinarith [mul_le_mul_of_nonneg_left hih hq0,
        mul_le_mul_of_nonneg_left hgate hq0]

theorem hiddenQ_pow_ge_half (N : ℕ) :
    (1 / 2 : ℝ) ≤ hiddenQ N ^ N := by
  let m : ℝ := hiddenM N
  have hm1 : 1 ≤ m := by
    dsimp [m, hiddenM]
    norm_cast
    omega
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have ha : (-2 : ℝ) ≤ -(1 / (2 * m)) := by
    have : 1 / (2 * m) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    linarith
  have hbern := one_add_mul_le_pow ha N
  change 1 + (N : ℝ) * (-(1 / (2 * m))) ≤
      (1 + -(1 / (2 * m))) ^ N at hbern
  have hNm : (N : ℝ) ≤ m := by
    dsimp [m, hiddenM]
    norm_num
  have hratio : (N : ℝ) / (2 * m) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  rw [hiddenQ]
  change (1 / 2 : ℝ) ≤ (1 - 1 / (2 * m)) ^ N
  have hleft : (1 / 2 : ℝ) ≤ 1 + (N : ℝ) * (-(1 / (2 * m))) := by
    have heq : (N : ℝ) * (1 / (2 * m)) = (N : ℝ) / (2 * m) := by ring
    rw [mul_neg, heq]
    linarith
  exact hleft.trans (by simpa [sub_eq_add_neg] using hbern)

theorem weightedChainError_final_le (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) (s : ℕ → ℝ)
    (hslab : |s N| ≤ hiddenTau R N / 2) :
    weightedChainError (hiddenQ N) (hiddenC R N) (hiddenTau R N) s N ≤
      -hiddenC R N / 4 := by
  have hc := hiddenC_pos hR N
  have ht := hiddenTau_pos hR N
  have hq0 := hiddenQ_nonneg hN
  have hq1 := (hiddenQ_lt_one N).le
  have hgeom := reverseGeom_nonneg_le (hiddenQ N) hq0 hq1 N
  have hqgeom : hiddenQ N * reverseGeom (hiddenQ N) N ≤ N := calc
    hiddenQ N * reverseGeom (hiddenQ N) N
        ≤ 1 * reverseGeom (hiddenQ N) N :=
          mul_le_mul_of_nonneg_right hq1 hgeom.1
    _ ≤ N := by simpa using hgeom.2
  have htail : hiddenQ N * hiddenTau R N * reverseGeom (hiddenQ N) N ≤
      (N : ℝ) * hiddenTau R N := by
    calc
      hiddenQ N * hiddenTau R N * reverseGeom (hiddenQ N) N =
          hiddenTau R N * (hiddenQ N * reverseGeom (hiddenQ N) N) := by ring
      _ ≤ hiddenTau R N * N := mul_le_mul_of_nonneg_left hqgeom ht.le
      _ = (N : ℝ) * hiddenTau R N := by ring
  have hNm : (N : ℝ) ≤ hiddenM N := by
    simp [hiddenM]
  have hNmass : (N : ℝ) * hiddenTau R N ≤ hiddenC R N / 8 := by
    calc
      (N : ℝ) * hiddenTau R N ≤ (hiddenM N : ℝ) * hiddenTau R N :=
        mul_le_mul_of_nonneg_right hNm ht.le
      _ = hiddenC R N / 8 := hidden_mass_identity R N
  have ht_le_mass : hiddenTau R N ≤ hiddenC R N / 8 := by
    calc
      hiddenTau R N = 1 * hiddenTau R N := by ring
      _ ≤ (hiddenM N : ℝ) * hiddenTau R N := by
        gcongr
        simp [hiddenM]
      _ = hiddenC R N / 8 := hidden_mass_identity R N
  have hs : s N ≤ hiddenTau R N / 2 := (le_abs_self _).trans hslab
  rw [weightedChainError_eq]
  have hpow := hiddenQ_pow_ge_half N
  have hcpow : hiddenC R N / 2 ≤ hiddenC R N * hiddenQ N ^ N := by
    nlinarith [mul_le_mul_of_nonneg_left hpow hc.le]
  linarith

/-- Euclidean chain error lower bound on the last-coordinate slab. -/
theorem hidden_error_norm_lower (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E)
    (hv : Orthonormal ℝ v) (x : E)
    (hslab : |inner ℝ (v (Fin.last N)) x| ≤ hiddenTau R N / 2) :
    R / (8 * hiddenM N) ≤ ‖x - hiddenMap profile R N v x‖ := by
  let w := chainWitness (hiddenQ N) (finFrameNat N v) N
  let e := x - hiddenMap profile R N v x
  let s : ℕ → ℝ := fun j => inner ℝ (finFrameNat N v j) x
  have hsN : s N = inner ℝ (v (Fin.last N)) x := by
    dsimp [s]
    rw [finFrameNat_eq v le_rfl]
    rfl
  have htel := chainWitness_inner_error_le profile hR hN v hv x N le_rfl
  have hscalar := weightedChainError_final_le profile hR hN s (by simpa [hsN] using hslab)
  have hinner : inner ℝ w e ≤ -hiddenC R N / 4 := htel.trans hscalar
  have habs : hiddenC R N / 4 ≤ |inner ℝ w e| := by
    exact (by linarith : hiddenC R N / 4 ≤ -inner ℝ w e) |>.trans (neg_le_abs _)
  have hw : ‖w‖ ≤ Real.sqrt (hiddenM N) := by
    dsimp [w]
    simpa [hiddenM] using chainWitness_norm_le_sqrt
      (hiddenQ_nonneg hN) (hiddenQ_lt_one N).le
      (fun k hk => finFrameNat_norm v hv hk)
      (fun a ha b hb hab => finFrameNat_inner_eq_zero v hv ha hb hab)
  have hprod : hiddenC R N / 4 ≤ Real.sqrt (hiddenM N) * ‖e‖ := calc
    hiddenC R N / 4 ≤ |inner ℝ w e| := habs
    _ ≤ ‖w‖ * ‖e‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (hiddenM N) * ‖e‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  have hsqrt0 : 0 < Real.sqrt (hiddenM N) := Real.sqrt_pos.2 hm0
  have hscale :
      (R / (8 * hiddenM N)) * Real.sqrt (hiddenM N) = hiddenC R N / 4 := by
    rw [hiddenC]
    have hsquare : Real.sqrt (hiddenM N : ℝ) ^ 2 = hiddenM N :=
      Real.sq_sqrt hm0.le
    field_simp [hsqrt0.ne', hm0.ne']
    nlinarith
  rw [← hscale] at hprod
  exact le_of_mul_le_mul_right (by simpa [mul_comm] using hprod) hsqrt0

theorem hidden_tangentResidual_lower (p : ℕ) (hp : 2 ≤ p)
    (profile : GateProfile) {Lp R : ℝ} (hLp : 0 < Lp) (hR : 0 < R)
    {N : ℕ} (hN : 1 ≤ N) (v : Fin (N + 1) → E) (hv : Orthonormal ℝ v)
    (x : E) (hx : x ∈ Metric.closedBall (0 : E) R)
    (hslab : |inner ℝ (v (Fin.last N)) x| ≤ hiddenTau R N / 2) :
    hiddenLambda p profile Lp R N * R / (8 * hiddenM N) ≤
      tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
        (hiddenOperator p profile Lp R N v) x := by
  rw [hiddenOperator_tangentResidual p hp profile hLp hR hN v hv x hx,
    hiddenOperator, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (hiddenLambda_pos profile hLp hR).le]
  have herr := hidden_error_norm_lower profile hR hN v hv x hslab
  have hlambda := (hiddenLambda_pos (p := p) (N := N) profile hLp hR).le
  calc
    hiddenLambda p profile Lp R N * R / (8 * hiddenM N) =
        hiddenLambda p profile Lp R N * (R / (8 * hiddenM N)) := by ring
    _ ≤ hiddenLambda p profile Lp R N *
        ‖x - hiddenMap profile R N v x‖ :=
      mul_le_mul_of_nonneg_left herr hlambda

/-- Algebraic form of the article's
`L_p R^p /(8 B_p 16^(p-1) m^((3p-1)/2))`.  For integer `p`, the final two
factors represent `m^p * m^((p-1)/2)`. -/
noncomputable def hiddenResidualClosedForm (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) : ℝ :=
  Lp * R ^ p /
    (8 * gateBp p profile * 16 ^ (p - 1) *
      (hiddenM N : ℝ) ^ p * Real.sqrt (hiddenM N : ℝ) ^ (p - 1))

theorem hidden_residual_scale_eq (p : ℕ) (hp : 1 ≤ p)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ) :
    hiddenLambda p profile Lp R N * R / (8 * hiddenM N) =
      hiddenResidualClosedForm p profile Lp R N := by
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  have hs0 : 0 < Real.sqrt (hiddenM N : ℝ) := Real.sqrt_pos.2 hm0
  have hBp0 := (gateBp_pos p profile).ne'
  have hpowR : R ^ (p - 1) * R = R ^ p := by
    rw [← pow_succ]
    congr
    omega
  rw [hiddenLambda, hiddenTau, hiddenC, hiddenResidualClosedForm]
  simp only [div_pow, mul_pow]
  field_simp [hm0.ne', hs0.ne', hBp0]
  have hmPow : (hiddenM N : ℝ) ^ p =
      (hiddenM N : ℝ) * (hiddenM N : ℝ) ^ (p - 1) := by
    calc
      (hiddenM N : ℝ) ^ p = (hiddenM N : ℝ) ^ ((p - 1) + 1) := by
        congr 1
        omega
      _ = (hiddenM N : ℝ) * (hiddenM N : ℝ) ^ (p - 1) := by
        rw [pow_succ]
        ring
  have h16 : (16 : ℝ) ^ (p - 1) =
      (2 : ℝ) ^ (p - 1) * (8 : ℝ) ^ (p - 1) := by
    rw [← mul_pow]
    norm_num
  rw [hmPow, h16]
  rw [← hpowR]
  ring

/-- Source-faithful proposition corresponding to `lem:residual`. -/
def HiddenResidualClaim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E],
    ∀ (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
      (Lp R : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
      (N : ℕ) (hN : 1 ≤ N) (v : Fin (N + 1) → E),
      Orthonormal ℝ v → ∀ x ∈ Metric.closedBall (0 : E) R,
      |inner ℝ (v (Fin.last N)) x| ≤ hiddenTau R N / 2 →
      (hiddenLambda p profile Lp R N * R / (8 * hiddenM N) ≤
          tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N v) x) ∧
        hiddenLambda p profile Lp R N * R / (8 * hiddenM N) =
          hiddenResidualClosedForm p profile Lp R N

/-- Kernel-checked headline theorem for `lem:residual`. -/
theorem hiddenResidualClaim_proof : HiddenResidualClaim := by
  intro E _ _ _ _ p hp profile Lp R hLp hR N hN v hv x hx hslab
  exact ⟨hidden_tangentResidual_lower p hp profile hLp hR hN v hv x hx hslab,
    hidden_residual_scale_eq p (by omega) profile Lp hR N⟩

end Residual

end LeanArticleAudit.Pilot
