import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

open Filter Set
open scoped Topology

namespace SecondOrder
noncomputable section

def joinAt (a : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ a then f x else g x

/-- Matching values and first derivatives glue the two one-sided derivatives. -/
theorem joinAt_hasDerivAt (a : ℝ) (f g f' g' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hv : f a = g a) (hd : f' a = g' a) (x : ℝ) :
    HasDerivAt (joinAt a f g) (joinAt a f' g' x) x := by
  rcases lt_trichotomy x a with hx | rfl | hx
  · rw [joinAt, if_pos hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [joinAt, (mem_Iio.mp hy).le]
  · rw [joinAt, if_pos le_rfl]
    have hl : HasDerivWithinAt (joinAt x f g) (f' x) (Iic x) x :=
      (hf x).hasDerivWithinAt.congr (by intro y hy; simp [joinAt, mem_Iic.mp hy]) (by simp [joinAt])
    have hr : HasDerivWithinAt (joinAt x f g) (f' x) (Ici x) x := by
      rw [hd]
      apply (hg x).hasDerivWithinAt.congr
      · intro y hy
        by_cases he : y = x
        · subst y; simp [joinAt, hv]
        · simp [joinAt, not_le.mpr (lt_of_le_of_ne hy (Ne.symm he))]
      · simp [joinAt, hv]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · rw [joinAt, if_neg (not_le.mpr hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [joinAt, not_le.mpr (mem_Ioi.mp hy)]

/-- Constant extension from the unit interval, without changing endpoint values. -/
def unitClipped (f : ℝ → ℝ) : ℝ → ℝ :=
  joinAt 0 (fun _ => f 0) (joinAt 1 f (fun _ => f 1))

def unitClip (x : ℝ) : ℝ := max 0 (min 1 x)

theorem unitClip_mem (x : ℝ) : unitClip x ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem unitClipped_eq_comp (f : ℝ → ℝ) : unitClipped f = f ∘ unitClip := by
  funext x
  by_cases h0 : x ≤ 0
  · simp [unitClipped, joinAt, unitClip, h0, min_eq_right (h0.trans (by norm_num : (0:ℝ) ≤ 1)), max_eq_left h0]
  · by_cases h1 : x ≤ 1
    · simp [unitClipped, joinAt, unitClip, h0, h1, min_eq_right h1, max_eq_right (le_of_not_ge h0)]
    · simp [unitClipped, joinAt, unitClip, h0, h1, min_eq_left (le_of_not_ge h1)]

theorem unitClip_lipschitz : LipschitzWith 1 unitClip :=
  (LipschitzWith.id.const_min 1).const_max 0

theorem unitClipped_continuous (f : ℝ → ℝ) (hf : Continuous f) : Continuous (unitClipped f) := by
  rw [unitClipped_eq_comp]
  exact hf.comp unitClip_lipschitz.continuous

theorem unitClipped_hasDerivAt (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f' 0 = 0) (h1 : f' 1 = 0) (x : ℝ) :
    HasDerivAt (unitClipped f) (unitClipped f' x) x := by
  have hi := joinAt_hasDerivAt 1 f (fun _ => f 1) f' (fun _ => 0)
    hf (fun y => hasDerivAt_const y (f 1)) rfl h1
  have ho := joinAt_hasDerivAt 0 (fun _ => f 0) (joinAt 1 f (fun _ => f 1))
    (fun _ => 0) (joinAt 1 f' (fun _ => 0)) (fun y => hasDerivAt_const y (f 0)) hi
    (by simp [joinAt]) (by simp [joinAt, h0]) x
  simpa only [unitClipped, h0, h1] using ho

theorem unitClipped_deriv (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f' 0 = 0) (h1 : f' 1 = 0) :
    deriv (unitClipped f) = unitClipped f' :=
  funext (fun x => (unitClipped_hasDerivAt f f' hf h0 h1 x).deriv)

theorem unitClipped_eq_of_mem (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    unitClipped f x = f x := by
  rw [unitClipped_eq_comp]
  simp [Function.comp_def, unitClip, min_eq_right hx.2, max_eq_right hx.1]

theorem unitClipped_lipschitz_bound (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x ∈ Icc (0:ℝ) 1, ‖f' x‖ ≤ M) (x y : ℝ) :
    ‖unitClipped f y-unitClipped f x‖ ≤ M*‖y-x‖ := by
  rw [unitClipped_eq_comp]
  have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hf z).hasDerivWithinAt) hb (convex_Icc (0:ℝ) 1)
    (unitClip_mem x) (unitClip_mem y)
  have hc : ‖unitClip y-unitClip x‖ ≤ ‖y-x‖ := by
    simpa only [Real.dist_eq, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
      unitClip_lipschitz.dist_le_mul y x
  exact hl.trans (mul_le_mul_of_nonneg_left hc hM)

end
end SecondOrder
