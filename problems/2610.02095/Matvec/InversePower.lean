import Matvec.Refinement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Factor-two inverse-norm estimation and logarithmic parameter choices

These theorems extract roots of the actual inexact power sequence. A good
eigenvector component and successful approximate applications are explicit
events; the final norm bounds are proved, not taken as assumptions.
-/

namespace Matvec

noncomputable section

def powerRoot (x : ℝ) (q : ℕ) : ℝ := x ^ (1 / (q : ℝ))

theorem powerRoot_pow (x : ℝ) (hx : 0 ≤ x) (q : ℕ) (hq : 0 < q) :
    powerRoot x q ^ q = x := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [powerRoot, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  rw [one_div_mul_cancel hq', Real.rpow_one]

theorem powerRoot_factor_two_of_powers (x L : ℝ) (hx : 0 ≤ x) (hL : 0 ≤ L)
    (q : ℕ) (hq : 0 < q) (hlo : (L / 2) ^ q ≤ x) (hhi : x ≤ (2 * L) ^ q) :
    L / 2 ≤ powerRoot x q ∧ powerRoot x q ≤ 2 * L := by
  have hroot : 0 ≤ powerRoot x q := Real.rpow_nonneg hx _
  have heq := powerRoot_pow x hx q hq
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) hroot (Nat.ne_of_gt hq)).mp
    rwa [heq]
  · apply (pow_le_pow_iff_left₀ hroot (by positivity) (Nat.ne_of_gt hq)).mp
    rwa [heq]

section Estimator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Analysis-only exact continuation after the q applications actually used.
It removes any requirement on unexecuted approximate applications. -/
def completeApplications (M : E →L[ℝ] E) (z : ℕ → E) (q : ℕ) : ℕ → E
  | 0 => z 0
  | n + 1 => if n < q then z (n + 1) else M (completeApplications M z q n)

theorem completeApplications_eq (M : E →L[ℝ] E) (z : ℕ → E) (q n : ℕ)
    (hn : n ≤ q) : completeApplications M z q n = z n := by
  cases n with
  | zero => rfl
  | succ n => simp [completeApplications, show n < q by omega]

theorem completeApplications_success (M : E →L[ℝ] E) (z : ℕ → E) (q : ℕ)
    (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (happly : ∀ n < q, ‖z (n + 1) - M (z n)‖ ≤ η * L * ‖z n‖) :
    ∀ n, ‖completeApplications M z q (n + 1) - M (completeApplications M z q n)‖ ≤
      η * L * ‖completeApplications M z q n‖ := by
  intro n
  by_cases hn : n < q
  · rw [completeApplications_eq M z q (n + 1) (by omega),
      completeApplications_eq M z q n (by omega)]
    exact happly n hn
  · simp only [completeApplications, if_neg hn, sub_self, norm_zero]
    positivity

/-- Every successful start has an upper factor-two estimate, independently
of its eigenvector component. -/
theorem inexactPower_root_upper (M : E →L[ℝ] E) (g : E) (z : ℕ → E)
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hM : ‖M‖ ≤ L)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n, ‖z (n + 1) - M (z n)‖ ≤ η * L * ‖z n‖)
    (q : ℕ) (hq : 0 < q) (hsmall : (q : ℝ) * η ≤ 1 / 2) :
    powerRoot ‖z q‖ q ≤ 2 * L := by
  have hu := inexactPower_norm_upper M g z L η hL hη hM hg hz0 happly q
  have he := power_error_growth_le η hη q hsmall
  have hgrowth : (1 + η) ^ q ≤ 2 := by linarith
  have htwo : (2 : ℝ) ≤ 2 ^ q := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq
  have hnorm : ‖z q‖ ≤ (2 * L) ^ q := by
    calc
      _ ≤ 2 * L ^ q := hu.trans (mul_le_mul_of_nonneg_right hgrowth (pow_nonneg hL q))
      _ ≤ 2 ^ q * L ^ q := mul_le_mul_of_nonneg_right htwo (pow_nonneg hL q)
      _ = _ := (mul_pow _ _ _).symm
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (norm_nonneg _) _)
    (by positivity) (Nat.ne_of_gt hq)).mp
  change powerRoot ‖z q‖ q ^ q ≤ (2 * L) ^ q
  rwa [powerRoot_pow _ (norm_nonneg _) q hq]

/-- A good eigenvector component gives the complete factor-two estimate.
`a` is the normalized component threshold, later instantiated as ν/sqrt d. -/
theorem inexactPower_factor_two (M : E →L[ℝ] E) (g v : E) (z : ℕ → E)
    (μ η a : ℝ) (_ha : 0 < a)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|)
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n, ‖z (n + 1) - M (z n)‖ ≤ η * |μ| * ‖z n‖)
    (hstart : a ≤ |@inner ℝ E _ v g|) (q : ℕ) (hq : 0 < q)
    (hsmall : (q : ℝ) * η ≤ 1 / 2) (haccuracy : 2 * (q : ℝ) * η ≤ a / 4)
    (hthreshold : 1 ≤ (3 * a / 4) * 2 ^ q) :
    |μ| / 2 ≤ powerRoot ‖z q‖ q ∧ powerRoot ‖z q‖ q ≤ 2 * |μ| := by
  have hgrowth : (1 + η) ^ q - 1 ≤ a / 4 :=
    (power_error_growth_le η hη q hsmall).trans haccuracy
  have hlower := inexactPower_good_start_lower M g v z μ η a hsymm heigen hv hM
    hη hg hz0 happly hstart q hgrowth
  have hpowtwo : (0 : ℝ) < 2 ^ q := by positivity
  have hscale : (|μ| / 2) ^ q ≤ (3 * a / 4) * |μ| ^ q := by
    rw [div_pow]
    apply (div_le_iff₀ hpowtwo).mpr
    have hmul := mul_le_mul_of_nonneg_right hthreshold (pow_nonneg (abs_nonneg μ) q)
    nlinarith
  refine ⟨?_, inexactPower_root_upper M g z |μ| η (abs_nonneg μ) hη hM hg hz0 happly q hq hsmall⟩
  apply (pow_le_pow_iff_left₀ (by positivity)
    (Real.rpow_nonneg (norm_nonneg _) _) (Nat.ne_of_gt hq)).mp
  change (|μ| / 2) ^ q ≤ powerRoot ‖z q‖ q ^ q
  rw [powerRoot_pow _ (norm_nonneg _) q hq]
  exact hscale.trans hlower

/-- Manuscript parameters ν, d, q and η imply the component-scale conditions
used in the deterministic estimator theorem. -/
theorem inversePower_parameter_conditions (ν η : ℝ) (d q : ℕ)
    (hν : 0 < ν) (hd : 0 < d) (hq : 0 < q)
    (hη : η ≤ ν / (8 * (q : ℝ) * Real.sqrt d))
    (hpow : 4 * Real.sqrt d / (3 * ν) ≤ (2 : ℝ) ^ q) :
    0 < ν / Real.sqrt d ∧
    2 * (q : ℝ) * η ≤ (ν / Real.sqrt d) / 4 ∧
    1 ≤ (3 * (ν / Real.sqrt d) / 4) * 2 ^ q := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd'
  refine ⟨div_pos hν hs, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hη (show 0 ≤ 2 * (q : ℝ) by positivity)
    have heq : 2 * (q : ℝ) * (ν / (8 * (q : ℝ) * Real.sqrt d)) =
        (ν / Real.sqrt d) / 4 := by field_simp; ring
    rwa [heq] at h
  · have h := (div_le_iff₀ (show 0 < 3 * ν by positivity)).mp hpow
    have heq : 3 * (ν / Real.sqrt d) / 4 * 2 ^ q =
        (2 ^ q * (3 * ν)) / (4 * Real.sqrt d) := by ring
    rw [heq]
    apply (le_div_iff₀ (show 0 < 4 * Real.sqrt (d : ℝ) by positivity)).mpr
    simpa only [one_mul] using h

/-- Complete deterministic `lem:inverse-power` for one good start, with only
the q actually executed approximate applications required to succeed. -/
theorem inversePower_good_start_estimate (M : E →L[ℝ] E) (g v : E) (z : ℕ → E)
    (μ ν η : ℝ) (d q : ℕ) (hν : 0 < ν) (hd : 0 < d) (hq : 0 < q)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|)
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n < q, ‖z (n + 1) - M (z n)‖ ≤ η * |μ| * ‖z n‖)
    (hstart : ν / Real.sqrt d ≤ |@inner ℝ E _ v g|)
    (hsmall : (q : ℝ) * η ≤ 1 / 2)
    (haccuracy : η ≤ ν / (8 * (q : ℝ) * Real.sqrt d))
    (hthreshold : 4 * Real.sqrt d / (3 * ν) ≤ (2 : ℝ) ^ q) :
    |μ| / 2 ≤ powerRoot ‖z q‖ q ∧ powerRoot ‖z q‖ q ≤ 2 * |μ| := by
  obtain ⟨ha, hacc, hth⟩ := inversePower_parameter_conditions ν η d q hν hd hq haccuracy hthreshold
  have h := inexactPower_factor_two M g v (completeApplications M z q) μ η
    (ν / Real.sqrt d) ha hsymm heigen hv hM hη hg hz0
    (completeApplications_success M z q η |μ| hη (abs_nonneg μ) happly)
    hstart q hq hsmall hacc hth
  rwa [completeApplications_eq M z q q le_rfl] at h

theorem inversePower_all_start_upper (M : E →L[ℝ] E) (g : E) (z : ℕ → E)
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hM : ‖M‖ ≤ L)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g) (q : ℕ) (hq : 0 < q)
    (happly : ∀ n < q, ‖z (n + 1) - M (z n)‖ ≤ η * L * ‖z n‖)
    (hsmall : (q : ℝ) * η ≤ 1 / 2) : powerRoot ‖z q‖ q ≤ 2 * L := by
  have h := inexactPower_root_upper M g (completeApplications M z q) L η hL hη hM hg hz0
    (completeApplications_success M z q η L hη hL happly) q hq hsmall
  rwa [completeApplications_eq M z q q le_rfl] at h

/-- The actual maximum over multiple starts from the manuscript. One good
start suffices; every start is controlled from above. -/
theorem inversePower_multiple_starts {S : Type*} [Fintype S] [Nonempty S]
    (M : E →L[ℝ] E) (g : S → E) (v : E) (z : S → ℕ → E)
    (μ ν η : ℝ) (d q : ℕ) (hν : 0 < ν) (hd : 0 < d) (hq : 0 < q)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|)
    (hη : 0 ≤ η) (hg : ∀ s, ‖g s‖ ≤ 1) (hz0 : ∀ s, z s 0 = g s)
    (happly : ∀ s n, n < q → ‖z s (n + 1) - M (z s n)‖ ≤ η * |μ| * ‖z s n‖)
    (hstart : ∃ s, ν / Real.sqrt d ≤ |@inner ℝ E _ v (g s)|)
    (hsmall : (q : ℝ) * η ≤ 1 / 2)
    (haccuracy : η ≤ ν / (8 * (q : ℝ) * Real.sqrt d))
    (hthreshold : 4 * Real.sqrt d / (3 * ν) ≤ (2 : ℝ) ^ q) :
    |μ| / 2 ≤ Finset.univ.sup' Finset.univ_nonempty (fun s => powerRoot ‖z s q‖ q) ∧
    Finset.univ.sup' Finset.univ_nonempty (fun s => powerRoot ‖z s q‖ q) ≤ 2 * |μ| := by
  constructor
  · obtain ⟨s, hs⟩ := hstart
    have h := inversePower_good_start_estimate M (g s) v (z s) μ ν η d q hν hd hq
      hsymm heigen hv hM hη (hg s) (hz0 s) (happly s) hs hsmall haccuracy hthreshold
    exact h.1.trans (Finset.le_sup' (fun s : S => powerRoot ‖z s q‖ q) (Finset.mem_univ s))
  · apply Finset.sup'_le
    intro s hs
    exact inversePower_all_start_upper M (g s) (z s) |μ| η (abs_nonneg μ) hη hM
      (hg s) (hz0 s) q hq (happly s) hsmall

end Estimator

/-- An explicit logarithmic power length for the universal start constant
ν = 1/2. -/
def inversePowerLength (d : ℕ) : ℕ := ⌈4 * Real.log ((d : ℝ) + 2)⌉₊

theorem inversePowerLength_bounds (d : ℕ) (hd : 2 ≤ d) :
    0 < inversePowerLength d ∧
    (inversePowerLength d : ℝ) < 4 * Real.log ((d : ℝ) + 2) + 1 ∧
    4 * Real.sqrt (d : ℝ) / (3 * (1 / 2)) ≤ (2 : ℝ) ^ inversePowerLength d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 < Real.log ((d : ℝ) + 2) := Real.log_pos (by linarith)
  have hceil := Nat.le_ceil (4 * Real.log ((d : ℝ) + 2))
  have hq : 0 < inversePowerLength d := by
    unfold inversePowerLength
    by_contra h
    have hz : ⌈4 * Real.log ((d : ℝ) + 2)⌉₊ = 0 := Nat.eq_zero_of_not_pos h
    rw [hz] at hceil
    norm_num at hceil
    linarith
  refine ⟨hq, Nat.ceil_lt_add_one (by positivity), ?_⟩
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hmul := mul_le_mul_of_nonneg_right hceil (show 0 ≤ Real.log 2 by linarith)
  have hexp : 2 * Real.log ((d : ℝ) + 2) ≤
      (inversePowerLength d : ℝ) * Real.log 2 := by
    change 4 * Real.log ((d : ℝ) + 2) * Real.log 2 ≤
      (inversePowerLength d : ℝ) * Real.log 2 at hmul
    nlinarith
  have hpow : ((d : ℝ) + 2) ^ 2 ≤ (2 : ℝ) ^ inversePowerLength d := by
    calc
      _ = Real.exp ((2 : ℝ) * Real.log ((d : ℝ) + 2)) := by
        rw [two_mul, Real.exp_add, Real.exp_log (by linarith)]
        ring
      _ ≤ Real.exp ((inversePowerLength d : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hsnonneg := Real.sqrt_nonneg (d : ℝ)
  have hsle : Real.sqrt (d : ℝ) ≤ d := by nlinarith
  apply le_trans _ hpow
  calc
    _ = (8 / 3 : ℝ) * Real.sqrt (d : ℝ) := by ring
    _ ≤ (8 / 3 : ℝ) * d := mul_le_mul_of_nonneg_left hsle (by norm_num)
    _ ≤ ((d : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg (d : ℝ)]

def inversePowerAccuracy (d : ℕ) : ℝ :=
  1 / (16 * (inversePowerLength d : ℝ) * Real.sqrt d)

theorem inversePowerAccuracy_bounds (d : ℕ) (hd : 2 ≤ d) :
    0 < inversePowerAccuracy d ∧
    (inversePowerLength d : ℝ) * inversePowerAccuracy d ≤ 1 / 2 ∧
    inversePowerAccuracy d ≤ (1 / 2) /
      (8 * (inversePowerLength d : ℝ) * Real.sqrt d) := by
  have hq := (inversePowerLength_bounds d hd).1
  have hq' : (0 : ℝ) < inversePowerLength d := by exact_mod_cast hq
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hsone : 1 ≤ Real.sqrt (d : ℝ) := by nlinarith
  refine ⟨by unfold inversePowerAccuracy; positivity, ?_, ?_⟩
  · have heq : (inversePowerLength d : ℝ) * inversePowerAccuracy d =
        1 / (16 * Real.sqrt d) := by unfold inversePowerAccuracy; field_simp; ring
    rw [heq]
    apply (div_le_iff₀ (show 0 < 16 * Real.sqrt (d : ℝ) by positivity)).mpr
    nlinarith
  · unfold inversePowerAccuracy
    apply le_of_eq
    field_simp
    ring

/-- Explicit logarithmic power length and explicit application accuracy close
the deterministic estimator theorem with ν=1/2. -/
theorem inversePower_logarithmic_estimate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (g v : E) (z : ℕ → E) (μ : ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n < inversePowerLength d,
      ‖z (n + 1) - M (z n)‖ ≤ inversePowerAccuracy d * |μ| * ‖z n‖)
    (hstart : (1 / 2) / Real.sqrt d ≤ |@inner ℝ E _ v g|) :
    |μ| / 2 ≤ powerRoot ‖z (inversePowerLength d)‖ (inversePowerLength d) ∧
    powerRoot ‖z (inversePowerLength d)‖ (inversePowerLength d) ≤ 2 * |μ| := by
  obtain ⟨hq, _, hthreshold⟩ := inversePowerLength_bounds d hd
  obtain ⟨hη, hsmall, haccuracy⟩ := inversePowerAccuracy_bounds d hd
  exact inversePower_good_start_estimate M g v z μ (1 / 2) (inversePowerAccuracy d)
    d (inversePowerLength d) (by norm_num) (by omega) hq hsymm heigen hv hM hη.le
    hg hz0 happly hstart hsmall haccuracy hthreshold

theorem top_eigenvalue_eq_opNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (v : E) (μ : ℝ)
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|) : |μ| = ‖M‖ := by
  have h := M.le_opNorm v
  rw [heigen, norm_smul, Real.norm_eq_abs, hv, mul_one, mul_one] at h
  exact le_antisymm h hM

/-- The estimate is explicitly for the inverse operator norm L=‖M‖. -/
theorem inverseNorm_logarithmic_estimate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (g v : E) (z : ℕ → E) (μ : ℝ) (d : ℕ) (hd : 2 ≤ d)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n < inversePowerLength d,
      ‖z (n + 1) - M (z n)‖ ≤ inversePowerAccuracy d * ‖M‖ * ‖z n‖)
    (hstart : (1 / 2) / Real.sqrt d ≤ |@inner ℝ E _ v g|) :
    ‖M‖ / 2 ≤ powerRoot ‖z (inversePowerLength d)‖ (inversePowerLength d) ∧
    powerRoot ‖z (inversePowerLength d)‖ (inversePowerLength d) ≤ 2 * ‖M‖ := by
  have heq := top_eigenvalue_eq_opNorm M v μ heigen hv hM
  rw [← heq] at happly ⊢
  exact inversePower_logarithmic_estimate M g v z μ d hd hsymm heigen hv hM hg hz0 happly hstart

end
end Matvec
