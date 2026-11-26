import Bilevel.SmallGap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.FunProp

/-! # Global C³ regularity of the article's septic step

The endpoint gluing is proved from matching derivatives on the closed
half-lines. No smoothness of the piecewise function is assumed.
-/

noncomputable section
namespace Bilevel.SepticRegularity
open scoped Topology
open Filter

def join (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ c then f x else g x

theorem join_continuous (c : ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (heq : f c = g c) :
    Continuous (join c f g) := by
  apply Continuous.if _ hf hg
  intro x hx
  change x ∈ frontier (Set.Iic c) at hx
  have hx' : x = c := by simpa only [frontier_Iic, Set.mem_singleton_iff] using hx
  simpa only [hx'] using heq

theorem join_hasDerivAt (c : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (heq : f c = g c) (hdeq : df c = dg c) (x : ℝ) :
    HasDerivAt (join c f g) (join c df dg x) x := by
  rcases lt_trichotomy x c with h | h | h
  · rw [join, if_pos h.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h] with z hz
    simp only [join, if_pos hz.le]
  · subst x
    rw [join, if_pos le_rfl]
    have hl : HasDerivWithinAt (join c f g) (df c) (Set.Iic c) c := by
      apply ((hf c).hasDerivWithinAt (s := Set.Iic c)).congr_of_mem
      · intro z hz
        exact if_pos hz
      · exact Set.mem_Iic.mpr le_rfl
    have hr : HasDerivWithinAt (join c f g) (df c) (Set.Ici c) c := by
      rw [hdeq]
      apply ((hg c).hasDerivWithinAt (s := Set.Ici c)).congr_of_mem
      · intro z hz
        dsimp [join]
        split_ifs with hz'
        · have he : z = c := le_antisymm hz' hz
          simpa only [he] using heq
        · rfl
      · exact Set.mem_Ici.mpr le_rfl
    simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · rw [join, if_neg (not_le.mpr h)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with z hz
    simp only [join, if_neg (not_le.mpr hz)]

def clip (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  join 0 (fun _ => a) (join 1 f (fun _ => b))

theorem clip_continuous (f : ℝ → ℝ) (a b : ℝ) (hf : Continuous f)
    (hzero : f 0 = a) (hone : f 1 = b) : Continuous (clip f a b) := by
  apply join_continuous 0 _ _ continuous_const
    (join_continuous 1 _ _ hf continuous_const hone)
  simpa only [join, if_pos (by norm_num : (0 : ℝ) ≤ 1)] using hzero.symm

theorem clip_hasDerivAt (f df : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hzero : f 0 = a) (hone : f 1 = b) (hdzero : df 0 = 0) (hdone : df 1 = 0)
    (x : ℝ) : HasDerivAt (clip f a b) (clip df 0 0 x) x := by
  apply join_hasDerivAt 0 _ _ _ _ (fun x => hasDerivAt_const x a)
    (fun x => join_hasDerivAt 1 f (fun _ => b) df (fun _ => 0)
      hf (fun x => hasDerivAt_const x b) hone hdone x)
  · simpa only [join, if_pos (by norm_num : (0 : ℝ) ≤ 1)] using hzero.symm
  · simpa only [join, if_pos (by norm_num : (0 : ℝ) ≤ 1)] using hdzero.symm

def d1 (t : ℝ) : ℝ := 140 * t ^ 3 - 420 * t ^ 4 + 420 * t ^ 5 - 140 * t ^ 6
def d2 (t : ℝ) : ℝ := 420 * t ^ 2 - 1680 * t ^ 3 + 2100 * t ^ 4 - 840 * t ^ 5
def d3 (t : ℝ) : ℝ := 840 * t - 5040 * t ^ 2 + 8400 * t ^ 3 - 4200 * t ^ 4

theorem core_derivative (t : ℝ) : HasDerivAt SmallGap.septicCore (d1 t) t := by
  convert SmallGap.septicCore_hasDerivAt t using 1
  unfold d1
  ring

theorem d1_derivative (t : ℝ) : HasDerivAt d1 (d2 t) t := by
  unfold d1 d2
  convert (((((hasDerivAt_id t).pow 3).const_mul 140).sub
    (((hasDerivAt_id t).pow 4).const_mul 420)).add
    (((hasDerivAt_id t).pow 5).const_mul 420)).sub
    (((hasDerivAt_id t).pow 6).const_mul 140) using 1
  dsimp
  ring

theorem d2_derivative (t : ℝ) : HasDerivAt d2 (d3 t) t := by
  unfold d2 d3
  convert (((((hasDerivAt_id t).pow 2).const_mul 420).sub
    (((hasDerivAt_id t).pow 3).const_mul 1680)).add
    (((hasDerivAt_id t).pow 4).const_mul 2100)).sub
    (((hasDerivAt_id t).pow 5).const_mul 840) using 1
  dsimp
  ring

theorem clipped_core_derivative (t : ℝ) :
    HasDerivAt (clip SmallGap.septicCore 0 1) (clip d1 0 0 t) t := by
  apply clip_hasDerivAt _ _ _ _ core_derivative <;> norm_num [SmallGap.septicCore, d1]

theorem clipped_d1_derivative (t : ℝ) :
    HasDerivAt (clip d1 0 0) (clip d2 0 0 t) t := by
  apply clip_hasDerivAt _ _ _ _ d1_derivative <;> norm_num [d1, d2]

theorem clipped_d2_derivative (t : ℝ) :
    HasDerivAt (clip d2 0 0) (clip d3 0 0 t) t := by
  apply clip_hasDerivAt _ _ _ _ d2_derivative <;> norm_num [d2, d3]

theorem clipped_d3_continuous : Continuous (clip d3 0 0) := by
  apply clip_continuous
  · unfold d3
    fun_prop
  · norm_num [d3]
  · norm_num [d3]

theorem septicStep_eq_clip : SmallGap.septicStep = clip SmallGap.septicCore 0 1 := by
  funext t
  unfold SmallGap.septicStep clip join
  split_ifs with ht0 ht1 ht2 ht3
  all_goals try rfl
  all_goals try { exfalso; linarith }
  all_goals have heq : t = 1 := by linarith
  all_goals norm_num [heq, SmallGap.septicCore]

/-- The actual globally defined article cutoff is C³, including both joins. -/
theorem septicStep_contDiff : ContDiff ℝ 3 SmallGap.septicStep := by
  have hd0 : deriv (clip SmallGap.septicCore 0 1) = clip d1 0 0 :=
    funext (fun t => (clipped_core_derivative t).deriv)
  have hd1 : deriv (clip d1 0 0) = clip d2 0 0 :=
    funext (fun t => (clipped_d1_derivative t).deriv)
  have hd2 : deriv (clip d2 0 0) = clip d3 0 0 :=
    funext (fun t => (clipped_d2_derivative t).deriv)
  have hc1 : ContDiff ℝ 1 (clip d2 0 0) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t => (clipped_d2_derivative t).differentiableAt, ?_⟩
    rw [hd2]
    exact clipped_d3_continuous
  have hc2 : ContDiff ℝ 2 (clip d1 0 0) := by
    change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (clip d1 0 0)
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun t => (clipped_d1_derivative t).differentiableAt, ?_, ?_⟩
    · norm_num
    · rw [hd1]
      exact hc1
  rw [septicStep_eq_clip]
  change ContDiff ℝ ((2 : WithTop ℕ∞) + 1) (clip SmallGap.septicCore 0 1)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (clipped_core_derivative t).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [hd0]
    exact hc2

theorem septicStep_deriv (t : ℝ) : deriv SmallGap.septicStep t = clip d1 0 0 t := by
  rw [septicStep_eq_clip]
  exact (clipped_core_derivative t).deriv

/-- The sharp derivative bound is global, including both glued endpoints. -/
theorem septicStep_deriv_bounds (t : ℝ) :
    0 ≤ deriv SmallGap.septicStep t ∧ deriv SmallGap.septicStep t ≤ 35 / 16 := by
  rw [septicStep_deriv]
  unfold clip join
  split_ifs with hzero hone
  · norm_num
  · have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_ge hzero, hone⟩
    rw [← (core_derivative t).deriv]
    exact SmallGap.septicCore_deriv_bounds t ht
  · norm_num

theorem septicStep_deriv_midpoint : deriv SmallGap.septicStep (1 / 2) = 35 / 16 := by
  rw [septicStep_deriv]
  norm_num [clip, join, d1]

theorem septicStep_monotone : Monotone SmallGap.septicStep := by
  apply monotone_of_deriv_nonneg (septicStep_contDiff.differentiable (by norm_num))
  exact fun t => (septicStep_deriv_bounds t).1

theorem septicStep_lipschitz : LipschitzWith (35 / 16) SmallGap.septicStep := by
  apply lipschitzWith_of_nnnorm_deriv_le (septicStep_contDiff.differentiable (by norm_num))
  intro t
  have h := septicStep_deriv_bounds t
  change ‖deriv SmallGap.septicStep t‖₊ ≤ (35 / 16 : NNReal)
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg h.1, NNReal.coe_div,
    NNReal.coe_ofNat] using h.2

theorem septicStep_second_deriv (t : ℝ) :
    deriv (deriv SmallGap.septicStep) t = clip d2 0 0 t := by
  have hfun : deriv SmallGap.septicStep = clip d1 0 0 := funext septicStep_deriv
  rw [hfun]
  exact (clipped_d1_derivative t).deriv

theorem septicStep_third_deriv (t : ℝ) :
    deriv (deriv (deriv SmallGap.septicStep)) t = clip d3 0 0 t := by
  have hfun : deriv (deriv SmallGap.septicStep) = clip d2 0 0 := funext septicStep_second_deriv
  rw [hfun]
  exact (clipped_d2_derivative t).deriv

end Bilevel.SepticRegularity
