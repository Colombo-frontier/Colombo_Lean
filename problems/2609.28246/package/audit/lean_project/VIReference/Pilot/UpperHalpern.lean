import VIReference.Pilot.Halpern

/-!
# Stability and certification for the inexact Halpern layer

This module formalizes the shadow-orbit estimates used by `lem:warm-energy`
and `lem:final-cert`.  The model solver itself is developed separately; here
its only analytic input is the checked proximal error bound.
-/

open Set
open scoped RealInnerProductSpace

namespace VIReference.Pilot

section Shadow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite inexact Halpern orbit with pointwise proximal error at most `e`.
The recurrence is required only through the requested horizon. -/
def IsInexactHalpernOrbit (P : E → E) (x0 : E) (e : ℝ) (K : ℕ)
    (x yHat : ℕ → E) : Prop :=
  x 0 = x0 ∧
  (∀ t, t ≤ K → ‖yHat t - P (x t)‖ ≤ e) ∧
  (∀ t, t < K → x (t + 1) =
    (1 / (t + 2 : ℝ)) • x0 +
      ((t + 1 : ℝ) / (t + 2 : ℝ)) • yHat t)

/-- Stability of the actual orbit against the exact orbit. -/
theorem inexactHalpern_shadow
    {P : E → E} {x0 : E} {e : ℝ} {K : ℕ}
    {x yHat xBar yBar : ℕ → E}
    (hP : FirmlyNonexpansive P)
    (he : 0 ≤ e)
    (hactual : IsInexactHalpernOrbit P x0 e K x yHat)
    (hexact : IsHalpernOrbit P x0 xBar yBar) :
    (∀ t, t ≤ K → ‖x t - xBar t‖ ≤ (t : ℝ) * e / 2) ∧
    (∀ t, t ≤ K → ‖yHat t - yBar t‖ ≤ (t + 2 : ℝ) * e / 2) := by
  have hnonexp : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖ :=
    firmlyNonexpansive_norm_le hP
  have hx : ∀ t, t ≤ K → ‖x t - xBar t‖ ≤ (t : ℝ) * e / 2 := by
    intro t ht
    induction t with
    | zero =>
        rw [hactual.1, hexact.1]
        simp
    | succ t ih =>
        have htK : t < K := Nat.lt_of_succ_le ht
        rw [hactual.2.2 t htK, hexact.2.2 t]
        have hyerr : ‖yHat t - yBar t‖ ≤ (t + 2 : ℝ) * e / 2 := by
          rw [hexact.2.1 t]
          calc
            ‖yHat t - P (xBar t)‖ ≤
                ‖yHat t - P (x t)‖ + ‖P (x t) - P (xBar t)‖ := by
              rw [show yHat t - P (xBar t) =
                (yHat t - P (x t)) + (P (x t) - P (xBar t)) by abel]
              exact norm_add_le _ _
            _ ≤ e + ‖x t - xBar t‖ := by
              gcongr
              · exact hactual.2.1 t (Nat.le_of_lt htK)
              · exact hnonexp _ _
            _ ≤ e + (t : ℝ) * e / 2 := by
              gcongr
              exact ih (Nat.le_of_lt htK)
            _ = (t + 2 : ℝ) * e / 2 := by ring
        have hcoef : 0 ≤ ((t + 1 : ℝ) / (t + 2 : ℝ)) := by positivity
        have hdiff :
            (1 / (t + 2 : ℝ)) • x0 +
                ((t + 1 : ℝ) / (t + 2 : ℝ)) • yHat t -
              ((1 / (t + 2 : ℝ)) • x0 +
                ((t + 1 : ℝ) / (t + 2 : ℝ)) • yBar t) =
            ((t + 1 : ℝ) / (t + 2 : ℝ)) • (yHat t - yBar t) := by
          module
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
        have hbound :
            ((t + 1 : ℝ) / (t + 2 : ℝ)) * ‖yHat t - yBar t‖ ≤
              (t + 1 : ℝ) * e / 2 := by
          calc
          ((t + 1 : ℝ) / (t + 2 : ℝ)) * ‖yHat t - yBar t‖ ≤
              ((t + 1 : ℝ) / (t + 2 : ℝ)) * ((t + 2 : ℝ) * e / 2) := by
            gcongr
          _ = (t + 1 : ℝ) * e / 2 := by
            have : (t + 2 : ℝ) ≠ 0 := by positivity
            field_simp
        simpa only [Nat.cast_add, Nat.cast_one] using hbound
  refine ⟨hx, ?_⟩
  intro t ht
  rw [hexact.2.1 t]
  calc
    ‖yHat t - P (xBar t)‖ ≤
        ‖yHat t - P (x t)‖ + ‖P (x t) - P (xBar t)‖ :=
      by
        rw [show yHat t - P (xBar t) =
          (yHat t - P (x t)) + (P (x t) - P (xBar t)) by abel]
        exact norm_add_le _ _
    _ ≤ e + ‖x t - xBar t‖ := by
      gcongr
      · exact hactual.2.1 t ht
      · exact hnonexp _ _
    _ ≤ e + (t : ℝ) * e / 2 := by gcongr; exact hx t ht
    _ = (t + 2 : ℝ) * e / 2 := by ring

/-- The projection predictor is used only through its distance-minimizing
property against the feasible exact resolvent point. -/
def IsProjectedLinearPredictor (P : E → E) (x0 : E)
    (x yHat w : ℕ → E) (K : ℕ) : Prop :=
  w 0 = x0 ∧ w 1 = yHat 0 ∧
    ∀ t, 2 ≤ t → t ≤ K →
      ‖w t - P (x t)‖ ≤
        ‖(2 : ℝ) • yHat (t - 1) - yHat (t - 2) - P (x t)‖

/-- Pointwise comparison between the true warm-start distance and the second
difference of the exact shadow orbit. -/
theorem warmStart_comparison
    {P : E → E} {x0 : E} {e R : ℝ} {K : ℕ}
    {x yHat w xBar yBar : ℕ → E}
    (hP : FirmlyNonexpansive P) (he : 0 ≤ e)
    (hactual : IsInexactHalpernOrbit P x0 e K x yHat)
    (hexact : IsHalpernOrbit P x0 xBar yBar)
    (hpredict : IsProjectedLinearPredictor P x0 x yHat w K) :
    ∀ t, 2 ≤ t → t ≤ K →
      ‖w t - P (x t)‖ ≤
        ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖ +
          (2 * (t : ℝ) + 1) * e := by
  obtain ⟨hxshadow, hyshadow⟩ :=
    inexactHalpern_shadow hP he hactual hexact
  intro t ht2 htK
  have ht1K : t - 1 ≤ K := (Nat.sub_le t 1).trans htK
  have ht2K : t - 2 ≤ K := (Nat.sub_le t 2).trans htK
  have hyt := hyshadow (t - 1) ht1K
  have hytt := hyshadow (t - 2) ht2K
  have hxt := hxshadow t htK
  have hbar : yBar t = P (xBar t) := hexact.2.1 t
  have hraw := hpredict.2.2 t ht2 htK
  calc
    ‖w t - P (x t)‖ ≤
        ‖(2 : ℝ) • yHat (t - 1) - yHat (t - 2) - P (x t)‖ := hraw
    _ ≤ ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖ +
        (2 * (t : ℝ) + 1) * e := by
      have hid :
          (2 : ℝ) • yHat (t - 1) - yHat (t - 2) - P (x t) =
            -(yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)) +
              (2 : ℝ) • (yHat (t - 1) - yBar (t - 1)) -
              (yHat (t - 2) - yBar (t - 2)) -
              (P (x t) - yBar t) := by
        rw [hbar]
        module
      rw [hid]
      calc
        ‖-(yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)) +
            (2 : ℝ) • (yHat (t - 1) - yBar (t - 1)) -
            (yHat (t - 2) - yBar (t - 2)) -
            (P (x t) - yBar t)‖ ≤
            ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖ +
              2 * ‖yHat (t - 1) - yBar (t - 1)‖ +
              ‖yHat (t - 2) - yBar (t - 2)‖ +
              ‖P (x t) - P (xBar t)‖ := by
          rw [hbar]
          let A := P (xBar t) - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)
          let B := (2 : ℝ) • (yHat (t - 1) - yBar (t - 1))
          let C := yHat (t - 2) - yBar (t - 2)
          let D := P (x t) - P (xBar t)
          have htri : ‖(-A) + B + (-C) + (-D)‖ ≤
              ‖-A‖ + ‖B‖ + ‖-C‖ + ‖-D‖ := by
            calc
              ‖(-A) + B + (-C) + (-D)‖ ≤ ‖(-A) + B + (-C)‖ + ‖-D‖ :=
                norm_add_le _ _
              _ ≤ (‖(-A) + B‖ + ‖-C‖) + ‖-D‖ := by
                gcongr
                exact norm_add_le _ _
              _ ≤ ((‖-A‖ + ‖B‖) + ‖-C‖) + ‖-D‖ := by
                gcongr
                exact norm_add_le _ _
          have htri' : ‖(-A) + B + (-C) + (-D)‖ ≤
              ‖A‖ + 2 * ‖yHat (t - 1) - yBar (t - 1)‖ + ‖C‖ + ‖D‖ := by
            calc
              _ ≤ ‖-A‖ + ‖B‖ + ‖-C‖ + ‖-D‖ := htri
              _ = _ := by simp [B, norm_smul]
          simpa [A, B, C, D, sub_eq_add_neg] using htri'
        _ ≤ _ := by
          have hnonexp := firmlyNonexpansive_norm_le hP (x t) (xBar t)
          rw [Nat.cast_sub (by omega : 1 ≤ t)] at hyt
          rw [Nat.cast_sub (by omega : 2 ≤ t)] at hytt
          have hyt' : ‖yHat (t - 1) - yBar (t - 1)‖ ≤
              ((t + 1 : ℕ) : ℝ) * e / 2 := by
            have hyt0 : ‖yHat (t - 1) - yBar (t - 1)‖ ≤
                ((t : ℝ) - 1 + 2) * e / 2 := by
              simpa only [Nat.cast_one] using hyt
            calc
              _ ≤ ((t : ℝ) - 1 + 2) * e / 2 := hyt0
              _ = ((t + 1 : ℕ) : ℝ) * e / 2 := by push_cast; ring
          have hytt' : ‖yHat (t - 2) - yBar (t - 2)‖ ≤
              (t : ℝ) * e / 2 := by
            calc
              _ ≤ ((t : ℝ) - 2 + 2) * e / 2 := hytt
              _ = (t : ℝ) * e / 2 := by ring
          have hnonexp' : ‖P (x t) - P (xBar t)‖ ≤ (t : ℝ) * e / 2 :=
            hnonexp.trans hxt
          calc
            _ ≤ ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖ +
                2 * (((t + 1 : ℕ) : ℝ) * e / 2) +
                ((t : ℕ) : ℝ) * e / 2 +
                ((t : ℕ) : ℝ) * e / 2 := by
              gcongr
            _ = _ := by push_cast; ring

/-- Elementary square estimate used when the exact second-difference energy
is perturbed by the inexact-orbit error. -/
theorem sq_le_two_sq_add_two_sq {u a b : ℝ}
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : u ≤ a + b) :
    u ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have husq : u ^ 2 ≤ (a + b) ^ 2 := (sq_le_sq₀ hu hab).2 h
  nlinarith [sq_nonneg (a - b)]

/-- On a dyadic block, the accumulated deterministic shadow-error term has
the explicit coefficient `50` used in the article. -/
theorem dyadic_shadow_error_sum
    {e : ℝ} {k ell : ℕ} (he : 0 ≤ e)
    (hk : 2 ≤ k) (hkle : k ≤ ell) (hell : ell ≤ 2 * k - 1) :
    2 * (∑ t ∈ Finset.Icc k ell, ((2 * (t : ℝ) + 1) * e) ^ 2) ≤
      50 * (k : ℝ) ^ 3 * e ^ 2 := by
  have hpoint : ∀ t ∈ Finset.Icc k ell,
      ((2 * (t : ℝ) + 1) * e) ^ 2 ≤
        25 * (k : ℝ) ^ 2 * e ^ 2 := by
    intro t ht
    have htk : t ≤ 2 * k - 1 := (Finset.mem_Icc.mp ht).2.trans hell
    have htk' : t + 1 ≤ 2 * k := by omega
    have htR' : (t : ℝ) + 1 ≤ 2 * (k : ℝ) := by
      exact_mod_cast htk'
    have hkR : 0 ≤ (k : ℝ) := by positivity
    have hcoef0 : 0 ≤ 2 * (t : ℝ) + 1 := by positivity
    have hcoef : 2 * (t : ℝ) + 1 ≤ 5 * (k : ℝ) := by linarith
    have hmul : (2 * (t : ℝ) + 1) * e ≤ 5 * (k : ℝ) * e := by
      exact mul_le_mul_of_nonneg_right hcoef he
    have hsq := (sq_le_sq₀ (mul_nonneg hcoef0 he)
      (mul_nonneg (mul_nonneg (by norm_num) hkR) he)).2 hmul
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  have hcard : (Finset.Icc k ell).card ≤ k := by
    rw [Nat.card_Icc]
    omega
  have hconst0 : 0 ≤ 25 * (k : ℝ) ^ 2 * e ^ 2 := by positivity
  calc
    2 * (∑ t ∈ Finset.Icc k ell, ((2 * (t : ℝ) + 1) * e) ^ 2)
        ≤ 2 * (∑ _t ∈ Finset.Icc k ell,
          (25 * (k : ℝ) ^ 2 * e ^ 2)) := by gcongr
    _ = 2 * ((Finset.Icc k ell).card : ℝ) *
          (25 * (k : ℝ) ^ 2 * e ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (k : ℝ) * (25 * (k : ℝ) ^ 2 * e ^ 2) := by
      have hcardR : ((Finset.Icc k ell).card : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hcard
      nlinarith
    _ = 50 * (k : ℝ) ^ 3 * e ^ 2 := by ring

/-- The prescribed fourth-power inner accuracy makes the whole dyadic
shadow error smaller than the main `R²/k²` scale. -/
theorem dyadic_shadow_error_absorbed
    {R e : ℝ} {k K : ℕ} (hR : 0 ≤ R) (hk : 2 ≤ k) (hkK : k ≤ K)
    (heq : e = R / (K + 2 : ℝ) ^ 4) :
    50 * (k : ℝ) ^ 3 * e ^ 2 ≤ 50 * R ^ 2 / (k : ℝ) ^ 2 := by
  have hk0 : 0 < (k : ℝ) := by positivity
  have hK0 : 0 < (K + 2 : ℝ) := by positivity
  have hkK' : (k : ℝ) ≤ (K + 2 : ℝ) := by
    exact_mod_cast (show k ≤ K + 2 by omega)
  have hpow4 : (k : ℝ) ^ 4 ≤ (K + 2 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (le_of_lt hk0) hkK' 4
  have he0 : 0 ≤ e := by rw [heq]; positivity
  have heK : e * (K + 2 : ℝ) ^ 4 = R := by
    rw [heq]
    field_simp
  have hek4 : e * (k : ℝ) ^ 4 ≤ R := by
    calc
      e * (k : ℝ) ^ 4 ≤ e * (K + 2 : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow4 he0
      _ = R := heK
  have hsq : (e * (k : ℝ) ^ 4) ^ 2 ≤ R ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg he0 (by positivity)) hR).2 hek4
  have hkpow : (k : ℝ) ^ 5 ≤ (k : ℝ) ^ 8 := by
    have hk1 : 1 ≤ (k : ℝ) := by
      exact_mod_cast (show 1 ≤ k by omega)
    exact pow_le_pow_right₀ hk1 (by omega)
  apply (le_div_iff₀ (sq_pos_of_pos hk0)).2
  have hcore : e ^ 2 * (k : ℝ) ^ 5 ≤ R ^ 2 := by
    calc
      e ^ 2 * (k : ℝ) ^ 5 ≤ e ^ 2 * (k : ℝ) ^ 8 := by
        gcongr
      _ = (e * (k : ℝ) ^ 4) ^ 2 := by ring
      _ ≤ R ^ 2 := hsq
  nlinarith

/-- The article's `C = 256` block estimate for the true projected
warm-start distances. -/
theorem warmStart_energy
    {P : E → E} {zStar x0 : E} {R e : ℝ} {K : ℕ}
    {x yHat w xBar yBar : ℕ → E}
    (hP : FirmlyNonexpansive P) (hfix : P zStar = zStar)
    (hR : ‖x0 - zStar‖ ≤ R)
    (hactual : IsInexactHalpernOrbit P x0 e K x yHat)
    (hexact : IsHalpernOrbit P x0 xBar yBar)
    (hpredict : IsProjectedLinearPredictor P x0 x yHat w K)
    (heq : e = R / (K + 2 : ℝ) ^ 4) :
    ∀ k ell, 2 ≤ k → k ≤ ell → ell ≤ 2 * k - 1 → ell ≤ K →
      (∑ t ∈ Finset.Icc k ell, ‖w t - P (x t)‖ ^ 2) ≤
        256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg (x0 - zStar)).trans hR
  have he0 : 0 ≤ e := by rw [heq]; positivity
  have hcomparison := warmStart_comparison (R := R) hP he0 hactual hexact hpredict
  have henergy := secondEnergy hP hfix hexact hR
  intro k ell hk hkle hell hellK
  let A : ℕ → ℝ := fun t =>
    ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖
  let B : ℕ → ℝ := fun t => (2 * (t : ℝ) + 1) * e
  have hpoint : ∀ t ∈ Finset.Icc k ell,
      ‖w t - P (x t)‖ ^ 2 ≤ 2 * (A t) ^ 2 + 2 * (B t) ^ 2 := by
    intro t ht
    have hmem := Finset.mem_Icc.mp ht
    have ht2 : 2 ≤ t := hk.trans hmem.1
    have htK : t ≤ K := hmem.2.trans hellK
    apply sq_le_two_sq_add_two_sq (norm_nonneg _) (norm_nonneg _)
      (mul_nonneg (by positivity) he0)
    simpa [A, B] using hcomparison t ht2 htK
  have hsum := Finset.sum_le_sum hpoint
  have hexactBlock := henergy k ell hk hkle hell
  have herr := dyadic_shadow_error_sum he0 hk hkle hell
  have habsorb := dyadic_shadow_error_absorbed hR0 hk (hkle.trans hellK) heq
  have hsplit :
      (∑ t ∈ Finset.Icc k ell, (2 * (A t) ^ 2 + 2 * (B t) ^ 2)) =
        2 * (∑ t ∈ Finset.Icc k ell, (A t) ^ 2) +
        2 * (∑ t ∈ Finset.Icc k ell, (B t) ^ 2) := by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit] at hsum
  have hexactBlock' :
      (∑ t ∈ Finset.Icc k ell, (A t) ^ 2) ≤
        64 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2 := by
    simpa [A] using hexactBlock
  have herr' : 2 * (∑ t ∈ Finset.Icc k ell, (B t) ^ 2) ≤
      50 * (k : ℝ) ^ 3 * e ^ 2 := by
    simpa [B] using herr
  let S : ℝ := R ^ 2 / (k : ℝ) ^ 2
  let H : ℝ := (1 + harmonicR (2 * k)) ^ 2
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hH1 : 1 ≤ H := by
    dsimp [H]
    have hh := harmonicR_nonneg (2 * k)
    nlinarith [sq_nonneg (harmonicR (2 * k))]
  have habsorb' : 50 * (k : ℝ) ^ 3 * e ^ 2 ≤ 50 * S := by
    calc
      _ ≤ 50 * R ^ 2 / (k : ℝ) ^ 2 := habsorb
      _ = 50 * S := by simp [S]; ring
  have hmainRewrite :
      64 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2 =
        64 * (S * H) := by simp [S, H]; ring
  rw [hmainRewrite] at hexactBlock'
  have htargetRewrite :
      256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2 =
        256 * (S * H) := by simp [S, H]; ring
  rw [htargetRewrite]
  calc
    (∑ t ∈ Finset.Icc k ell, ‖w t - P (x t)‖ ^ 2)
        ≤ 2 * (∑ t ∈ Finset.Icc k ell, (A t) ^ 2) +
          2 * (∑ t ∈ Finset.Icc k ell, (B t) ^ 2) := hsum
    _ ≤ 2 * (64 * (S * H)) + 50 * S := by
      exact add_le_add (mul_le_mul_of_nonneg_left hexactBlock' (by norm_num))
        (herr'.trans habsorb')
    _ ≤ 256 * (S * H) := by nlinarith

/-- The two startup solves satisfy the same explicit `3R` bound used before
the dyadic decomposition. -/
theorem warmStart_startup
    {P : E → E} {zStar x0 : E} {R e : ℝ} {K : ℕ}
    {x yHat w : ℕ → E}
    (hP : FirmlyNonexpansive P) (hfix : P zStar = zStar)
    (hR : ‖x0 - zStar‖ ≤ R) (he : 0 ≤ e) (heR : e ≤ R)
    (hK : 1 ≤ K)
    (hactual : IsInexactHalpernOrbit P x0 e K x yHat)
    (hpredict : IsProjectedLinearPredictor P x0 x yHat w K) :
    ‖w 0 - P (x 0)‖ ≤ 3 * R ∧ ‖w 1 - P (x 1)‖ ≤ 3 * R := by
  have hR0 : 0 ≤ R := he.trans heR
  have hnonexp := firmlyNonexpansive_norm_le hP
  have hPx0 : ‖P x0 - zStar‖ ≤ R := by
    rw [← hfix]
    exact (hnonexp x0 zStar).trans hR
  have hr0 : ‖w 0 - P (x 0)‖ ≤ 3 * R := by
    rw [hpredict.1, hactual.1]
    calc
      ‖x0 - P x0‖ ≤ ‖x0 - zStar‖ + ‖zStar - P x0‖ := by
        rw [show x0 - P x0 = (x0 - zStar) + (zStar - P x0) by abel]
        exact norm_add_le _ _
      _ = ‖x0 - zStar‖ + ‖P x0 - zStar‖ := by rw [norm_sub_rev zStar (P x0)]
      _ ≤ R + R := add_le_add hR hPx0
      _ ≤ 3 * R := by linarith
  have hyerr : ‖yHat 0 - P (x 0)‖ ≤ e := hactual.2.1 0 (by omega)
  have hyerr' : ‖yHat 0 - P x0‖ ≤ e := by simpa [hactual.1] using hyerr
  have hyx0 : ‖yHat 0 - x0‖ ≤ e + 2 * R := by
    calc
      ‖yHat 0 - x0‖ ≤ ‖yHat 0 - P x0‖ + ‖P x0 - zStar‖ + ‖zStar - x0‖ := by
        rw [show yHat 0 - x0 = (yHat 0 - P x0) + (P x0 - zStar) +
          (zStar - x0) by abel]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ e + R + R := by
        gcongr
        simpa [norm_sub_rev] using hR
      _ = e + 2 * R := by ring
  have hx10 : ‖x 1 - x0‖ ≤ R + e / 2 := by
    have hup := hactual.2.2 0 (by omega)
    norm_num at hup
    have hid : x 1 - x0 = (1 / 2 : ℝ) • (yHat 0 - x0) := by
      rw [hup]
      module
    rw [hid, norm_smul]
    norm_num [Real.norm_eq_abs]
    nlinarith
  have hr1 : ‖w 1 - P (x 1)‖ ≤ 3 * R := by
    rw [hpredict.2.1]
    calc
      ‖yHat 0 - P (x 1)‖ ≤
          ‖yHat 0 - P x0‖ + ‖P x0 - P (x 1)‖ := by
        rw [show yHat 0 - P (x 1) = (yHat 0 - P x0) + (P x0 - P (x 1)) by abel]
        exact norm_add_le _ _
      _ ≤ e + ‖x0 - x 1‖ := add_le_add hyerr' (hnonexp x0 (x 1))
      _ = e + ‖x 1 - x0‖ := by rw [norm_sub_rev x0 (x 1)]
      _ ≤ e + (R + e / 2) := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hx10 e
      _ ≤ 3 * R := by linarith
  exact ⟨hr0, hr1⟩

/-- Source-facing contract for `lem:warm-energy`. -/
def WarmEnergyClaim
    (P : E → E) (zStar x0 : E) (R e : ℝ) (K : ℕ)
    (x yHat w xBar yBar : ℕ → E) : Prop :=
  FirmlyNonexpansive P → P zStar = zStar → ‖x0 - zStar‖ ≤ R →
  1 ≤ K → IsInexactHalpernOrbit P x0 e K x yHat →
  IsHalpernOrbit P x0 xBar yBar →
  IsProjectedLinearPredictor P x0 x yHat w K →
  e = R / (K + 2 : ℝ) ^ 4 →
  (‖w 0 - P (x 0)‖ ≤ 3 * R ∧ ‖w 1 - P (x 1)‖ ≤ 3 * R) ∧
  (∀ t, 2 ≤ t → t ≤ K →
    ‖w t - P (x t)‖ ≤
      ‖yBar t - (2 : ℝ) • yBar (t - 1) + yBar (t - 2)‖ +
        (2 * (t : ℝ) + 1) * e) ∧
  (∀ k ell, 2 ≤ k → k ≤ ell → ell ≤ 2 * k - 1 → ell ≤ K →
    (∑ t ∈ Finset.Icc k ell, ‖w t - P (x t)‖ ^ 2) ≤
      256 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2)

/-- Kernel proof of the full warm-energy claim. -/
theorem warmEnergyClaim_proof
    (P : E → E) (zStar x0 : E) (R e : ℝ) (K : ℕ)
    (x yHat w xBar yBar : ℕ → E) :
    WarmEnergyClaim P zStar x0 R e K x yHat w xBar yBar := by
  intro hP hfix hR hK hactual hexact hpredict heq
  have hR0 : 0 ≤ R := (norm_nonneg (x0 - zStar)).trans hR
  have he0 : 0 ≤ e := by rw [heq]; positivity
  have heR : e ≤ R := by
    rw [heq]
    have hden : 1 ≤ (K + 2 : ℝ) ^ 4 := by
      have : 1 ≤ (K + 2 : ℝ) := by
        exact_mod_cast (show 1 ≤ K + 2 by omega)
      exact one_le_pow₀ this
    exact div_le_self hR0 hden
  refine ⟨warmStart_startup hP hfix hR he0 heR hK hactual hpredict, ?_, ?_⟩
  · exact warmStart_comparison (R := R) hP he0 hactual hexact hpredict
  · exact warmStart_energy hP hfix hR hactual hexact hpredict heq

section FinalCertificate

/-- Analytic output estimate before substituting the outer parameters.  It
also accounts for the final inner certificate `‖v‖ ≤ e/η`; no exact
proximal recovery is assumed. -/
theorem finalCertificate_output_bound
    {F P : E → E} {zStar x0 n v : E} {R e eta : ℝ} {K : ℕ}
    {x yHat xBar yBar : ℕ → E}
    (hP : FirmlyNonexpansive P) (hfix : P zStar = zStar)
    (hR : ‖x0 - zStar‖ ≤ R) (he : 0 ≤ e) (heta : 0 < eta)
    (hK : 2 ≤ K)
    (hactual : IsInexactHalpernOrbit P x0 e K x yHat)
    (hexact : IsHalpernOrbit P x0 xBar yBar)
    (hv : F (yHat K) + n = v - (1 / eta) • (yHat K - x K))
    (hvcert : ‖v‖ ≤ e / eta) :
    ‖F (yHat K) + n‖ ≤
      (1 / eta) *
        (2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ) +
          (K + 2 : ℝ) * e) := by
  obtain ⟨hxshadow, hyshadow⟩ := inexactHalpern_shadow hP he hactual hexact
  have hres := (firstDifference hP hfix hexact hR).1 K (by omega)
  have hshadowY := hyshadow K le_rfl
  have hshadowX := hxshadow K le_rfl
  have hyx : ‖yHat K - x K‖ ≤
      2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ) +
        (K + 1 : ℝ) * e := by
    calc
      ‖yHat K - x K‖ ≤
          ‖yHat K - yBar K‖ + ‖yBar K - xBar K‖ + ‖xBar K - x K‖ := by
        rw [show yHat K - x K = (yHat K - yBar K) +
          (yBar K - xBar K) + (xBar K - x K) by abel]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((K + 2 : ℝ) * e / 2) +
          (2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ)) +
          ((K : ℝ) * e / 2) := by
        exact add_le_add
          (add_le_add hshadowY (by simpa [norm_sub_rev] using hres.2.2))
          (by simpa [norm_sub_rev] using hshadowX)
      _ = 2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ) +
          (K + 1 : ℝ) * e := by ring
  rw [hv]
  have hetaInv : 0 ≤ 1 / eta := by positivity
  calc
    ‖v - (1 / eta) • (yHat K - x K)‖ ≤
        ‖v‖ + ‖(1 / eta) • (yHat K - x K)‖ := norm_sub_le _ _
    _ = ‖v‖ + (1 / eta) * ‖yHat K - x K‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hetaInv]
    _ ≤ e / eta + (1 / eta) *
        (2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ) +
          (K + 1 : ℝ) * e) := by gcongr
    _ = (1 / eta) *
        (2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ) +
          (K + 2 : ℝ) * e) := by
      have : eta ≠ 0 := ne_of_gt heta
      field_simp [this]
      ring

/-- Substitution of the article's explicit outer parameters gives the checked
final tolerance, with slack (`ε/2` would already suffice). -/
theorem outer_parameters_output_le
    {R epsilon e eta : ℝ} {K : ℕ}
    (hR : 0 < R) (heps : 0 < epsilon) (hK : 2 ≤ K)
    (heq : e = R / (K + 2 : ℝ) ^ 4)
    (heta : eta = 8 * R * (1 + harmonicR (K + 1)) /
      (epsilon * (K + 1 : ℝ))) :
    (1 / eta) *
        (2 * R * (1 + harmonicR (K + 1)) / (K + 1 : ℝ) +
          (K + 2 : ℝ) * e) ≤ epsilon := by
  have hH : 1 ≤ 1 + harmonicR (K + 1) := by
    linarith [harmonicR_nonneg (K + 1)]
  have hK1 : 0 < (K + 1 : ℝ) := by positivity
  have hK2 : 2 ≤ (K + 2 : ℝ) := by
    exact_mod_cast (show 2 ≤ K + 2 by omega)
  have heta0 : 0 < eta := by rw [heta]; positivity
  rw [heq, heta]
  have hR0 : R ≠ 0 := ne_of_gt hR
  have he0 : epsilon ≠ 0 := ne_of_gt heps
  have hH0 : 1 + harmonicR (K + 1) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hH)
  have hK10 : (K + 1 : ℝ) ≠ 0 := ne_of_gt hK1
  have hK20 : (K + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hR0, he0, hH0, hK10, hK20]
  have hKcube : (K + 1 : ℝ) ≤
      6 * (1 + harmonicR (K + 1)) * (K + 2 : ℝ) ^ 3 := by
    have hbase : 1 ≤ (K + 2 : ℝ) := by linarith
    have hpow : (K + 2 : ℝ) ≤ (K + 2 : ℝ) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤ 3)
    have hlin : (K + 1 : ℝ) ≤ (K + 2 : ℝ) := by linarith
    have hfactor : 1 ≤ 6 * (1 + harmonicR (K + 1)) := by nlinarith
    calc
      (K + 1 : ℝ) ≤ (K + 2 : ℝ) := hlin
      _ ≤ (K + 2 : ℝ) ^ 3 := hpow
      _ = 1 * (K + 2 : ℝ) ^ 3 := by ring
      _ ≤ 6 * (1 + harmonicR (K + 1)) * (K + 2 : ℝ) ^ 3 := by gcongr
  nlinarith

/-- Source-facing contract for `lem:final-cert`. -/
def FinalCertificateClaim
    (X : Set E) (F P : E → E) (zStar x0 n v : E) (R epsilon e eta : ℝ) (K : ℕ)
    (x yHat xBar yBar : ℕ → E) : Prop :=
  FirmlyNonexpansive P → P zStar = zStar → ‖x0 - zStar‖ ≤ R →
  0 < R → 0 < epsilon → 2 ≤ K →
  IsInexactHalpernOrbit P x0 e K x yHat →
  IsHalpernOrbit P x0 xBar yBar →
  n ∈ normalCone X (yHat K) →
  F (yHat K) + n = v - (1 / eta) • (yHat K - x K) →
  ‖v‖ ≤ e / eta →
  e = R / (K + 2 : ℝ) ^ 4 →
  eta = 8 * R * (1 + harmonicR (K + 1)) /
    (epsilon * (K + 1 : ℝ)) →
  n ∈ normalCone X (yHat K) ∧ ‖F (yHat K) + n‖ ≤ epsilon

/-- Kernel proof of the final-certificate contract. -/
theorem finalCertificateClaim_proof
    (X : Set E) (F P : E → E) (zStar x0 n v : E)
    (R epsilon e eta : ℝ) (K : ℕ)
    (x yHat xBar yBar : ℕ → E) :
    FinalCertificateClaim X F P zStar x0 n v R epsilon e eta K
      x yHat xBar yBar := by
  intro hP hfix hR hRpos heps hK hactual hexact hn hv hvcert heq heta
  have he0 : 0 ≤ e := by rw [heq]; positivity
  have hHpos : 0 < 1 + harmonicR (K + 1) := by
    linarith [harmonicR_nonneg (K + 1)]
  have heta0 : 0 < eta := by rw [heta]; positivity
  exact ⟨hn, (finalCertificate_output_bound hP hfix hR he0 heta0 hK hactual hexact hv hvcert).trans
    (outer_parameters_output_le hRpos heps hK heq heta)⟩

end FinalCertificate

end Shadow

end VIReference.Pilot
