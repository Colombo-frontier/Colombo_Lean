import Bilevel.ZeroChainCertificate
import Bilevel.SmallGapProfileBounds

/-!
# Concrete flat C³ cutoffs for the paper's tail-mask residual

The paper permits any flat C³ cutoffs with the stated plateaux. These are
polynomial compositions of the verified septic step, including the endpoints.
-/

noncomputable section
open Set

namespace Bilevel.ZeroChainResidualCutoffs

def coordinateCutoff (t : ℝ) : ℝ := SmallGap.septicStep ((16*t^2-1)/3)
def energyCutoff (s : ℝ) : ℝ := 1-SmallGap.septicStep ((4*s-1)/3)

theorem coordinateCutoff_contDiff : ContDiff ℝ 3 coordinateCutoff :=
  SepticRegularity.septicStep_contDiff.comp
    (((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const).div_const 3)

theorem energyCutoff_contDiff : ContDiff ℝ 3 energyCutoff := by
  exact contDiff_const.sub (SepticRegularity.septicStep_contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 3))

theorem coordinateCutoff_range (t : ℝ) : 0 ≤ coordinateCutoff t ∧ coordinateCutoff t ≤ 1 :=
  SmallGap.septicStep_range _

theorem energyCutoff_range (s : ℝ) : 0 ≤ energyCutoff s ∧ energyCutoff s ≤ 1 := by
  have h := SmallGap.septicStep_range ((4*s-1)/3)
  dsimp [energyCutoff]
  constructor <;> linarith

theorem coordinateCutoff_zero {t : ℝ} (ht : |t| ≤ 1/4) : coordinateCutoff t = 0 := by
  apply SmallGapProfiles.step_zero
  have hsq := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at hsq
  nlinarith

theorem coordinateCutoff_one {t : ℝ} (ht : 1/2 ≤ |t|) : coordinateCutoff t = 1 := by
  apply SmallGapProfiles.step_one
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ht 2
  rw [sq_abs] at hsq
  nlinarith

theorem energyCutoff_one {s : ℝ} (hs : s ≤ 1/4) : energyCutoff s = 1 := by
  rw [energyCutoff, SmallGapProfiles.step_zero (by linarith : (4*s-1)/3 ≤ 0)]
  ring

theorem energyCutoff_zero {s : ℝ} (hs : 1 ≤ s) : energyCutoff s = 0 := by
  rw [energyCutoff, SmallGapProfiles.step_one (by linarith : 1 ≤ (4*s-1)/3)]
  ring

theorem deriv_zero_of_constant_on {f : ℝ → ℝ} {s : Set ℝ} {c x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hs : UniqueDiffOn ℝ s)
    (he : EqOn f (fun _ => c) s) (hx : x ∈ s) : deriv f x = 0 := by
  exact (hs x hx).eq_deriv s hf.hasDerivAt.hasDerivWithinAt
    ((hasDerivWithinAt_const x s c).congr_of_mem he hx)

/-- Global C³ regularity makes all one-sided plateau jets flat at their
boundary, as well as in their interior. -/
theorem iteratedDeriv_zero_of_constant_on {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hf : ContDiff ℝ 3 f) (hs : UniqueDiffOn ℝ s) (he : EqOn f (fun _ => c) s)
    (j : ℕ) (hj0 : 1 ≤ j) (hj3 : j ≤ 3) :
    ∀ x ∈ s, iteratedDeriv j f x = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hd := hf.differentiable_iteratedDeriv j (by exact_mod_cast (show j < 3 by omega))
    cases j with
    | zero =>
      simpa only [iteratedDeriv_zero] using deriv_zero_of_constant_on
        (hf.differentiable (by norm_num) x) hs he hx
    | succ j =>
      exact deriv_zero_of_constant_on (hd x) hs (ih (by omega) (by omega)) hx

theorem coordinateCutoff_flat_inner (j : ℕ) (hj : j ≤ 3) (t : ℝ) (ht : |t| ≤ 1/4) :
    iteratedDeriv j coordinateCutoff t = 0 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [iteratedDeriv_zero] using coordinateCutoff_zero ht
  · exact iteratedDeriv_zero_of_constant_on coordinateCutoff_contDiff
      (uniqueDiffOn_Icc (by norm_num : -(1/4:ℝ) < 1/4))
      (fun x hx => coordinateCutoff_zero (abs_le.mpr hx)) j (by omega) hj t (abs_le.mp ht)

theorem coordinateCutoff_flat_outer (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ 3)
    (t : ℝ) (ht : 1/2 ≤ |t|) : iteratedDeriv j coordinateCutoff t = 0 := by
  rcases le_total 0 t with hpos | hneg
  · apply iteratedDeriv_zero_of_constant_on coordinateCutoff_contDiff
      (uniqueDiffOn_Ici (1/2)) (c:=1)
      (fun x hx => coordinateCutoff_one (by
        change (1/2:ℝ) ≤ x at hx
        simpa only [abs_of_nonneg (by linarith : 0 ≤ x)] using hx))
      j hj0 hj t
    simpa only [abs_of_nonneg hpos] using ht
  · apply iteratedDeriv_zero_of_constant_on coordinateCutoff_contDiff
      (uniqueDiffOn_Iic (-(1/2))) (c:=1)
      (fun x hx => coordinateCutoff_one (by
        change x ≤ -(1/2:ℝ) at hx
        rw [abs_of_nonpos (by linarith : x ≤ 0)]; linarith))
      j hj0 hj t
    rw [abs_of_nonpos hneg] at ht
    change t ≤ -(1/2:ℝ)
    linarith

theorem energyCutoff_flat_right (j : ℕ) (hj : j ≤ 3) (s : ℝ) (hs : 1 ≤ s) :
    iteratedDeriv j energyCutoff s = 0 := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [iteratedDeriv_zero] using energyCutoff_zero hs
  · exact iteratedDeriv_zero_of_constant_on energyCutoff_contDiff (uniqueDiffOn_Ici 1)
      (fun _ ht => energyCutoff_zero ht) j (by omega) hj s hs

theorem energyCutoff_flat_left (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ 3)
    (s : ℝ) (hs : s ≤ 1/4) : iteratedDeriv j energyCutoff s = 0 :=
  iteratedDeriv_zero_of_constant_on energyCutoff_contDiff (uniqueDiffOn_Iic (1/4))
    (fun _ ht => energyCutoff_one ht) j hj0 hj s hs

theorem coordinateCutoff_deriv_compactSupport : HasCompactSupport (deriv coordinateCutoff) := by
  apply SmallGapProfileBounds.compactSupport_of_tail (1/2)
  intro t ht
  simpa only [iteratedDeriv_one] using coordinateCutoff_flat_outer 1 (by norm_num) (by norm_num) t ht

theorem energyCutoff_deriv_compactSupport : HasCompactSupport (deriv energyCutoff) := by
  apply SmallGapProfileBounds.compactSupport_of_tail 1
  intro t ht
  rcases le_total 0 t with hp | hn
  · simpa only [iteratedDeriv_one] using energyCutoff_flat_right 1 (by norm_num) t
      (by simpa only [abs_of_nonneg hp] using ht)
  · simpa only [iteratedDeriv_one] using energyCutoff_flat_left 1 (by norm_num) (by norm_num) t
      (by rw [abs_of_nonpos hn] at ht; linarith)

theorem plateau_profile_bound (f : ℝ → ℝ) (hc : ContDiff ℝ 3 f)
    (hr : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (hs : HasCompactSupport (deriv f))
    (j : ℕ) (hj : j ≤ 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv j f t| ≤ C := by
  cases j with
  | zero =>
    refine ⟨1, by norm_num, fun t => ?_⟩
    simpa only [iteratedDeriv_zero, abs_of_nonneg (hr t).1] using (hr t).2
  | succ j =>
    apply SmallGapProfileBounds.bound_of_compactSupport
    · rw [iteratedDeriv_succ']
      exact SmallGapProfileBounds.compactSupport_iteratedDeriv hs j
    · exact (contDiff_nat_iff_iteratedDeriv.mp hc).1 (j+1) hj

theorem cutoff_common_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Fin 4, ∀ t,
    |iteratedDeriv j.val coordinateCutoff t| ≤ C ∧ |iteratedDeriv j.val energyCutoff t| ≤ C := by
  have he (j : Fin 4) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      |iteratedDeriv j.val coordinateCutoff t| ≤ C ∧ |iteratedDeriv j.val energyCutoff t| ≤ C := by
    obtain ⟨A,hA,ha⟩ := plateau_profile_bound coordinateCutoff coordinateCutoff_contDiff
      coordinateCutoff_range coordinateCutoff_deriv_compactSupport j.val (by omega)
    obtain ⟨B,hB,hb⟩ := plateau_profile_bound energyCutoff energyCutoff_contDiff
      energyCutoff_range energyCutoff_deriv_compactSupport j.val (by omega)
    refine ⟨A+B, by positivity, fun t => ⟨?_, ?_⟩⟩
    · exact (ha t).trans (le_add_of_nonneg_right hB)
    · exact (hb t).trans (le_add_of_nonneg_left hA)
  choose C hC hb using he
  refine ⟨1+∑ j, C j, le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hC j)), fun j t => ⟨?_, ?_⟩⟩
  all_goals have hj : C j ≤ ∑ k, C k := Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
  · exact (hb j t).1.trans (by linarith)
  · exact (hb j t).2.trans (by linarith)

end Bilevel.ZeroChainResidualCutoffs
