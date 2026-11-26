import Bilevel.SmallGapProfiles
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Uniform derivative bounds and exact scaling for the actual small-gap profiles.
The constants are obtained from compactness, rather than postulated as hypotheses.
-/

noncomputable section

open Set

namespace Bilevel.SmallGapProfileBounds

open SmallGapProfiles

theorem compactSupport_of_tail {f : ℝ → ℝ} (R : ℝ)
    (h : ∀ x, R ≤ |x| → f x = 0) : HasCompactSupport f := by
  apply HasCompactSupport.intro (K := Icc (-R) R) isCompact_Icc
  intro x hx
  apply h
  by_contra! hn
  exact hx (abs_le.mp hn.le)

theorem psi_compactSupport : HasCompactSupport psi :=
  compactSupport_of_tail 34 psi_support

theorem normal_compactSupport (a : ℝ) (ha : 0 < a) : HasCompactSupport (normal a) :=
  compactSupport_of_tail a (fun s hs => normal_support a s ha hs)

theorem phi_deriv_compactSupport : HasCompactSupport (deriv phi) := by
  apply compactSupport_of_tail 2
  intro t ht
  rw [phi_deriv, step_one (by linarith : 1 ≤ |t| - 1)]
  ring

theorem compactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem bound_of_compactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f)
    (hc : Continuous f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.exists_bound_of_continuous hc
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact (show |f x| ≤ C by simpa only [Real.norm_eq_abs] using hC x).trans
    (le_max_left _ _)

theorem compact_c3_bound {f : ℝ → ℝ} (hf : HasCompactSupport f)
    (hc : ContDiff ℝ 3 f) (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j f x| ≤ C := by
  apply bound_of_compactSupport (compactSupport_iteratedDeriv hf j)
  exact (contDiff_nat_iff_iteratedDeriv.mp hc).1 j hj

theorem phi_iteratedDeriv_bound (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j phi x| ≤ C := by
  cases j with
  | zero =>
    refine ⟨2, by norm_num, fun x => ?_⟩
    simpa only [iteratedDeriv_zero, abs_of_nonneg (phi_nonneg x)] using phi_bounded x
  | succ j =>
    apply bound_of_compactSupport
    · rw [iteratedDeriv_succ']
      exact compactSupport_iteratedDeriv phi_deriv_compactSupport j
    · exact (contDiff_nat_iff_iteratedDeriv.mp phi_contDiff).1 (j + 1) hj

theorem psi_iteratedDeriv_bound (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j psi x| ≤ C :=
  compact_c3_bound psi_compactSupport psi_contDiff j hj

theorem normal_one_iteratedDeriv_bound (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv j (normal 1) x| ≤ C :=
  compact_c3_bound (normal_compactSupport 1 (by norm_num))
    (normal_contDiff 1 (by norm_num)) j hj

/-- One fixed bound for each derivative order, common to all three unscaled profiles. -/
theorem common_profile_bounds : ∃ C : Fin 4 → ℝ,
    (∀ j, 0 ≤ C j) ∧ ∀ j x,
      |iteratedDeriv j.val phi x| ≤ C j ∧
      |iteratedDeriv j.val psi x| ≤ C j ∧
      |iteratedDeriv j.val (normal 1) x| ≤ C j := by
  have he (j : Fin 4) : ∃ c : ℝ, 0 ≤ c ∧ ∀ x,
      |iteratedDeriv j.val phi x| ≤ c ∧
      |iteratedDeriv j.val psi x| ≤ c ∧
      |iteratedDeriv j.val (normal 1) x| ≤ c := by
    have hj : j.val ≤ 3 := by omega
    obtain ⟨c₀, h₀, hb₀⟩ := phi_iteratedDeriv_bound j.val hj
    obtain ⟨c₁, h₁, hb₁⟩ := psi_iteratedDeriv_bound j.val hj
    obtain ⟨c₂, h₂, hb₂⟩ := normal_one_iteratedDeriv_bound j.val hj
    refine ⟨c₀ + c₁ + c₂, by positivity, fun x => ?_⟩
    have := hb₀ x
    have := hb₁ x
    have := hb₂ x
    constructor
    · linarith
    constructor <;> linarith
  choose C hC hb using he
  exact ⟨C, hC, hb⟩

/-- Fixed universal constants; they depend only on the three displayed base profiles. -/
def profileBound : Fin 4 → ℝ := Classical.choose common_profile_bounds

theorem profileBound_nonneg (j : Fin 4) : 0 ≤ profileBound j :=
  (Classical.choose_spec common_profile_bounds).1 j

theorem phi_bound (j : Fin 4) (x : ℝ) :
    |iteratedDeriv j.val phi x| ≤ profileBound j :=
  ((Classical.choose_spec common_profile_bounds).2 j x).1

theorem psi_bound (j : Fin 4) (x : ℝ) :
    |iteratedDeriv j.val psi x| ≤ profileBound j :=
  ((Classical.choose_spec common_profile_bounds).2 j x).2.1

theorem normal_one_bound (j : Fin 4) (x : ℝ) :
    |iteratedDeriv j.val (normal 1) x| ≤ profileBound j :=
  ((Classical.choose_spec common_profile_bounds).2 j x).2.2

/-- The chain rule with its exact scale factor, including order zero. -/
theorem iteratedDeriv_scaled {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f)
    (A a x : ℝ) :
    iteratedDeriv n (fun u => A * f (u / a)) x =
      A / a ^ n * iteratedDeriv n f (x / a) := by
  have hc : ContDiff ℝ n (fun u : ℝ => f (u / a)) :=
    hf.comp (contDiff_id.div_const a)
  rw [iteratedDeriv_const_mul hc.contDiffAt]
  have he := congrFun (iteratedDeriv_comp_const_mul hf a⁻¹) x
  simp only [← div_eq_inv_mul] at he
  rw [he, inv_pow]
  ring

def r0 (S R u : ℝ) : ℝ := S * R ^ 2 * phi (u / R)

def r1 (S δ u : ℝ) : ℝ := S * δ ^ 2 * psi (u / δ)

theorem r0_contDiff (S R : ℝ) : ContDiff ℝ 3 (r0 S R) :=
  contDiff_const.mul (phi_contDiff.comp (contDiff_id.div_const R))

theorem r1_contDiff (S δ : ℝ) : ContDiff ℝ 3 (r1 S δ) :=
  contDiff_const.mul (psi_contDiff.comp (contDiff_id.div_const δ))

theorem r0_iteratedDeriv (S R x : ℝ) (j : ℕ) (hj : j ≤ 3) :
    iteratedDeriv j (r0 S R) x =
      S * R ^ 2 / R ^ j * iteratedDeriv j phi (x / R) := by
  exact iteratedDeriv_scaled (phi_contDiff.of_le (by exact_mod_cast hj)) (S * R ^ 2) R x

theorem r1_iteratedDeriv (S δ x : ℝ) (j : ℕ) (hj : j ≤ 3) :
    iteratedDeriv j (r1 S δ) x =
      S * δ ^ 2 / δ ^ j * iteratedDeriv j psi (x / δ) := by
  exact iteratedDeriv_scaled (psi_contDiff.of_le (by exact_mod_cast hj)) (S * δ ^ 2) δ x

theorem normal_scaling (a : ℝ) (ha : 0 < a) :
    normal a = fun s => a * normal 1 (s / a) := by
  funext s
  simp only [normal, div_one, abs_div, abs_of_pos ha]
  field_simp

theorem normal_iteratedDeriv (a x : ℝ) (ha : 0 < a) (j : ℕ) (hj : j ≤ 3) :
    iteratedDeriv j (normal a) x =
      a / a ^ j * iteratedDeriv j (normal 1) (x / a) := by
  rw [normal_scaling a ha]
  exact iteratedDeriv_scaled
    ((normal_contDiff 1 (by norm_num)).of_le (by exact_mod_cast hj)) a a x

theorem r0_bound (S R x : ℝ) (hR : 0 < R) (j : Fin 4) :
    |iteratedDeriv j.val (r0 S R) x| ≤
      |S| * R ^ 2 / R ^ j.val * profileBound j := by
  rw [r0_iteratedDeriv S R x j.val (by omega), abs_mul]
  calc
    _ ≤ |S * R ^ 2 / R ^ j.val| * profileBound j :=
      mul_le_mul_of_nonneg_left (phi_bound j (x / R)) (abs_nonneg _)
    _ = _ := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg R),
        abs_of_pos (pow_pos hR _)]

theorem r1_bound (S δ x : ℝ) (hδ : 0 < δ) (j : Fin 4) :
    |iteratedDeriv j.val (r1 S δ) x| ≤
      |S| * δ ^ 2 / δ ^ j.val * profileBound j := by
  rw [r1_iteratedDeriv S δ x j.val (by omega), abs_mul]
  calc
    _ ≤ |S * δ ^ 2 / δ ^ j.val| * profileBound j :=
      mul_le_mul_of_nonneg_left (psi_bound j (x / δ)) (abs_nonneg _)
    _ = _ := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg δ),
        abs_of_pos (pow_pos hδ _)]

theorem normal_bound (a x : ℝ) (ha : 0 < a) (j : Fin 4) :
    |iteratedDeriv j.val (normal a) x| ≤
      a / a ^ j.val * profileBound j := by
  rw [normal_iteratedDeriv a x ha j.val (by omega), abs_mul]
  calc
    _ ≤ |a / a ^ j.val| * profileBound j :=
      mul_le_mul_of_nonneg_left (normal_one_bound j (x / a)) (abs_nonneg _)
    _ = _ := by rw [abs_div, abs_of_pos ha, abs_of_pos (pow_pos ha _)]

end Bilevel.SmallGapProfileBounds
