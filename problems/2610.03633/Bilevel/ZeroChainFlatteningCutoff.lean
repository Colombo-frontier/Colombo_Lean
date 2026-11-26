import Bilevel.ZeroChainResidualScaled
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A concrete even flat cutoff and the paper's coordinate flattening map. -/

noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainFlatteningCutoff
open ZeroChain ZeroChainResidualCutoffs

def omega (t : ℝ) : ℝ := Real.smoothTransition ((t^2-1)/3)
def core (t : ℝ) : ℝ := t*omega t
def flatten (δ t : ℝ) : ℝ := t*omega (t/δ)

theorem omega_contDiff_all {k : ℕ∞} : ContDiff ℝ k omega :=
  Real.smoothTransition.contDiff.comp (((contDiff_id.pow 2).sub contDiff_const).div_const 3)

theorem omega_contDiff : ContDiff ℝ 3 omega := omega_contDiff_all

theorem core_contDiff : ContDiff ℝ 3 core := contDiff_id.mul omega_contDiff

theorem flatten_contDiff (δ : ℝ) : ContDiff ℝ 3 (flatten δ) :=
  contDiff_id.mul (omega_contDiff.comp (contDiff_id.div_const δ))

theorem omega_even (t : ℝ) : omega (-t) = omega t := by simp only [omega,neg_sq]

theorem omega_range (t : ℝ) : 0 ≤ omega t ∧ omega t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem omega_zero {t : ℝ} (ht : |t| ≤ 1) : omega t = 0 := by
  have hsq := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at hsq
  exact Real.smoothTransition.zero_of_nonpos (by nlinarith)

theorem omega_one {t : ℝ} (ht : 2 ≤ |t|) : omega t = 1 := by
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) ht 2
  rw [sq_abs] at hsq
  exact Real.smoothTransition.one_of_one_le (by nlinarith)

theorem core_zero {t : ℝ} (ht : |t| ≤ 1) : core t = 0 := by rw [core, omega_zero ht, mul_zero]
theorem core_identity {t : ℝ} (ht : 2 ≤ |t|) : core t = t := by rw [core, omega_one ht, mul_one]

theorem flatten_zero {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ) : flatten δ t = 0 := by
  rw [flatten, omega_zero (by rw [abs_div, abs_of_pos hδ]; exact (div_le_one hδ).mpr ht), mul_zero]

theorem flatten_identity {δ t : ℝ} (hδ : 0 < δ) (ht : 2*δ ≤ |t|) : flatten δ t = t := by
  rw [flatten, omega_one (by rw [abs_div, abs_of_pos hδ]; exact (le_div_iff₀ hδ).mpr ht), mul_one]

theorem flatten_abs_le (δ t : ℝ) : |flatten δ t| ≤ |t| := by
  rw [flatten, abs_mul, abs_of_nonneg (omega_range _).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (omega_range _).2

theorem flatten_error_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : |t-flatten δ t| ≤ 2*δ := by
  by_cases ht : 2*δ ≤ |t|
  · rw [flatten_identity hδ ht, sub_self, abs_zero]
    positivity
  · rw [flatten, show t-t*omega (t/δ) = t*(1-omega (t/δ)) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (omega_range _).2)]
    exact (mul_le_of_le_one_right (abs_nonneg t) (by linarith [(omega_range (t/δ)).1])).trans (le_of_not_ge ht)

theorem flatten_eq_scaled_core (δ : ℝ) (hδ : δ ≠ 0) : flatten δ = fun t => δ*core (t/δ) := by
  ext t
  dsimp [flatten, core]
  field_simp

theorem iteratedDeriv_eq_on {f g : ℝ → ℝ} {s : Set ℝ} (hf : ContDiff ℝ 3 f)
    (hg : ContDiff ℝ 3 g) (hs : UniqueDiffOn ℝ s) (he : EqOn f g s)
    (k : ℕ) (hk : k ≤ 3) : EqOn (iteratedDeriv k f) (iteratedDeriv k g) s := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using he
  | succ k ih =>
    intro t ht
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfk := hf.differentiable_iteratedDeriv k (by exact_mod_cast (show k < 3 by omega))
    have hgk := hg.differentiable_iteratedDeriv k (by exact_mod_cast (show k < 3 by omega))
    exact (hs t ht).eq_deriv s (hfk t).hasDerivAt.hasDerivWithinAt
      (((hgk t).hasDerivAt.hasDerivWithinAt).congr_of_mem (ih (by omega)) ht)

theorem flatten_flat_inner {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (hk : k ≤ 3)
    (t : ℝ) (ht : |t| ≤ δ) : iteratedDeriv k (flatten δ) t = 0 := by
  by_cases hk0 : k = 0
  · subst k
    simpa only [iteratedDeriv_zero] using flatten_zero hδ ht
  · exact iteratedDeriv_zero_of_constant_on (flatten_contDiff δ)
      (uniqueDiffOn_Icc (show -δ < δ by linarith))
      (fun _ hu => flatten_zero hδ (abs_le.mpr hu)) k (by omega) hk t (abs_le.mp ht)

theorem flatten_identity_jets {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (hk : k ≤ 3)
    (t : ℝ) (ht : 2*δ ≤ |t|) : iteratedDeriv k (flatten δ) t = iteratedDeriv k id t := by
  rcases le_total 0 t with hp | hn
  · apply iteratedDeriv_eq_on (flatten_contDiff δ) contDiff_id (uniqueDiffOn_Ici (2*δ))
      (fun x hx => flatten_identity hδ (by
        change 2*δ ≤ x at hx
        simpa only [abs_of_nonneg (by linarith : 0 ≤ x)] using hx)) k hk
    simpa only [abs_of_nonneg hp] using ht
  · apply iteratedDeriv_eq_on (flatten_contDiff δ) contDiff_id (uniqueDiffOn_Iic (-(2*δ)))
      (fun x hx => flatten_identity hδ (by
        change x ≤ -(2*δ) at hx
        rw [abs_of_nonpos (by linarith : x ≤ 0)]
        linarith)) k hk
    change t ≤ -(2*δ)
    rw [abs_of_nonpos hn] at ht
    linarith

theorem core_identity_jets (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : 2 ≤ |t|) :
    iteratedDeriv k core t = iteratedDeriv k id t := by
  have he : flatten 1 = core := by ext u; simp [flatten, core]
  rw [← he]
  exact flatten_identity_jets (by norm_num) k hk t (by simpa using ht)

theorem id_jet_abs_le (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) (t : ℝ) :
    |iteratedDeriv k (id : ℝ → ℝ) t| ≤ 1 := by
  interval_cases k <;> norm_num [iteratedDeriv_succ, iteratedDeriv_zero]

theorem core_jet_bound (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t, |iteratedDeriv k core t| ≤ B := by
  have hc : Continuous (iteratedDeriv k core) :=
    (contDiff_nat_iff_iteratedDeriv.mp core_contDiff).1 k hk
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 1, le_max_right _ _, fun t => ?_⟩
  by_cases ht : |t| ≤ 2
  · exact (show |iteratedDeriv k core t| ≤ B by simpa only [Real.norm_eq_abs] using hB t (abs_le.mp ht)).trans (le_max_left _ _)
  · rw [core_identity_jets k hk t (le_of_not_ge ht)]
    exact (id_jet_abs_le k hk0 hk t).trans (le_max_right _ _)

theorem core_common_jet_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ t,
    |iteratedDeriv k core t| ≤ B := by
  obtain ⟨B1,h1,hb1⟩ := core_jet_bound 1 (by norm_num) (by norm_num)
  obtain ⟨B2,h2,hb2⟩ := core_jet_bound 2 (by norm_num) (by norm_num)
  obtain ⟨B3,h3,hb3⟩ := core_jet_bound 3 (by norm_num) (by norm_num)
  refine ⟨B1+B2+B3, by linarith, fun k hk0 hk t => ?_⟩
  interval_cases k
  · exact (hb1 t).trans (by linarith)
  · exact (hb2 t).trans (by linarith)
  · exact (hb3 t).trans (by linarith)

theorem flatten_jet_bound {B : ℝ} (hb : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ t, |iteratedDeriv k core t| ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) (t : ℝ) :
    |iteratedDeriv k (flatten δ) t| ≤ B*δ/δ^k := by
  rw [flatten_eq_scaled_core δ hδ.ne', SmallGapProfileBounds.iteratedDeriv_scaled
    (core_contDiff.of_le (by exact_mod_cast hk)), abs_mul,
    abs_of_pos (div_pos hδ (pow_pos hδ _))]
  exact (mul_le_mul_of_nonneg_left (hb k hk0 hk _) (by positivity)).trans_eq (by ring)

end Bilevel.ZeroChainFlatteningCutoff
