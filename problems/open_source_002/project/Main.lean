import Mathlib


/- BEGIN gde_invariants -/
section SnapshotModule_000

/-!
Local proof audit of genuine algebraic steps in the signed-ratio GDE proof
(paper source/main.tex, Lemma `lem:gde`). These declarations do not define the
comparison oracle, derive the smoothness remainder, formalize the coordinate
tournament as a complete algorithm, or prove the full GDE theorem.
-/

namespace Task004GDE

noncomputable section

theorem positive_reply_direction
    {change dot tau : ℝ} (ht : 0 < tau)
    (hremainder : |change - 2 * tau * dot| ≤ 2 * tau ^ 2)
    (hreply : 0 ≤ change) : -tau ≤ dot := by
  have hr := (abs_le.mp hremainder).2
  nlinarith

theorem negative_reply_direction
    {change dot tau : ℝ} (ht : 0 < tau)
    (hremainder : |change - 2 * tau * dot| ≤ 2 * tau ^ 2)
    (hreply : change < 0) : dot ≤ tau := by
  have hr := (abs_le.mp hremainder).1
  nlinarith

theorem positive_ratio_reply
    {a alpha ratio denom tau zeta : ℝ}
    (ha : 0 < a) (hd : 0 < denom)
    (htol : tau * denom ≤ a * zeta)
    (hreply : -tau ≤ a * (alpha - ratio) / denom) :
    ratio - zeta ≤ alpha := by
  have h := (le_div_iff₀ hd).mp hreply
  nlinarith

theorem negative_ratio_reply
    {a alpha ratio denom tau zeta : ℝ}
    (ha : 0 < a) (hd : 0 < denom)
    (htol : tau * denom ≤ a * zeta)
    (hreply : a * (alpha - ratio) / denom ≤ tau) :
    alpha ≤ ratio + zeta := by
  have h := (div_le_iff₀ hd).mp hreply
  nlinarith

structure Interval where
  lo : ℝ
  hi : ℝ

def midpoint (I : Interval) : ℝ := (I.lo + I.hi) / 2

def width (I : Interval) : ℝ := I.hi - I.lo

def step (positive : Bool) (I : Interval) : Interval :=
  if positive then ⟨I.lo, midpoint I⟩ else ⟨midpoint I, I.hi⟩

def invariant (I : Interval) (ratio zeta : ℝ) : Prop :=
  I.lo ≤ I.hi ∧ I.lo ≤ ratio + zeta ∧ ratio - zeta ≤ I.hi

def replySound (positive : Bool) (I : Interval) (ratio zeta : ℝ) : Prop :=
  if positive then ratio - zeta ≤ midpoint I
  else midpoint I ≤ ratio + zeta

theorem step_preserves_invariant
    {positive : Bool} {I : Interval} {ratio zeta : ℝ}
    (hI : invariant I ratio zeta)
    (hreply : replySound positive I ratio zeta) :
    invariant (step positive I) ratio zeta := by
  rcases hI with ⟨horder, hlo, hhi⟩
  cases positive <;> simp_all [invariant, replySound, step, midpoint] <;> linarith

theorem step_halves_width (positive : Bool) (I : Interval) :
    width (step positive I) = width I / 2 := by
  cases positive <;> simp [step, width, midpoint] <;> ring

def bisection (answers : ℕ → Bool) : ℕ → Interval
  | 0 => ⟨-2, 2⟩
  | k + 1 => step (answers k) (bisection answers k)

theorem bisection_width (answers : ℕ → Bool) (k : ℕ) :
    width (bisection answers k) = 4 * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num [bisection, width]
  | succ k ih =>
    rw [bisection, step_halves_width, ih, pow_succ]
    ring

theorem bisection_invariant
    (answers : ℕ → Bool) {ratio zeta : ℝ}
    (hzeta : 0 ≤ zeta) (hratio : -2 ≤ ratio ∧ ratio ≤ 2)
    (k : ℕ)
    (hsound : ∀ j < k, replySound (answers j) (bisection answers j) ratio zeta) :
    invariant (bisection answers k) ratio zeta := by
  revert hsound
  induction k with
  | zero =>
    intro _
    simp only [bisection, invariant]
    rcases hratio with ⟨hl, hu⟩
    constructor
    · norm_num
    constructor <;> linarith
  | succ k ih =>
    intro hsound
    have hi := ih (fun j hj => hsound j (by omega))
    exact step_preserves_invariant hi (hsound k (by omega))

theorem midpoint_error
    {I : Interval} {ratio zeta : ℝ}
    (hI : invariant I ratio zeta) (hwidth : width I ≤ 2 * zeta) :
    |midpoint I - ratio| ≤ 2 * zeta := by
  rcases hI with ⟨_, hlo, hhi⟩
  apply abs_le.mpr
  dsimp [midpoint, width] at *
  constructor <;> linarith

theorem bisection_final_error
    (answers : ℕ → Bool) {ratio zeta : ℝ}
    (hzeta : 0 ≤ zeta) (hratio : -2 ≤ ratio ∧ ratio ≤ 2)
    (k : ℕ)
    (hsound : ∀ j < k, replySound (answers j) (bisection answers j) ratio zeta)
    (hrounds : 4 * (1 / 2 : ℝ) ^ k ≤ 2 * zeta) :
    |midpoint (bisection answers k) - ratio| ≤ 2 * zeta := by
  apply midpoint_error (bisection_invariant answers hzeta hratio k hsound)
  simpa only [bisection_width] using hrounds

theorem tournament_error_step
    {champion challenger winner oldMax noise count : ℝ}
    (hnoise : 0 ≤ noise) (hcount : 0 ≤ count)
    (hold : oldMax - count * noise ≤ champion)
    (hw1 : champion - noise ≤ winner)
    (hw2 : challenger - noise ≤ winner) :
    max oldMax challenger - (count + 1) * noise ≤ winner := by
  rcases le_total oldMax challenger with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

theorem anchored_vector_nonzero
    {E : Type*} [AddMonoid E] {u : E} {coordinate : E → ℝ}
    (hzero : coordinate 0 = 0) (hanchor : coordinate u = 1) : u ≠ 0 := by
  intro hu
  rw [hu, hzero] at hanchor
  norm_num at hanchor

theorem normalized_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖NormedSpace.normalize u - NormedSpace.normalize v‖ ≤
      2 * ‖u - v‖ / ‖v‖ := by
  have hid :
      ‖v‖ • (NormedSpace.normalize u - NormedSpace.normalize v) =
      (‖v‖ - ‖u‖) • NormedSpace.normalize u + (u - v) := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  have hscaled :
      ‖v‖ * ‖NormedSpace.normalize u - NormedSpace.normalize v‖ ≤ 2 * ‖u - v‖ := by
    calc
      _ = ‖‖v‖ • (NormedSpace.normalize u - NormedSpace.normalize v)‖ :=
        (norm_smul_of_nonneg (norm_nonneg v) _).symm
      _ = ‖(‖v‖ - ‖u‖) • NormedSpace.normalize u + (u - v)‖ := congrArg norm hid
      _ ≤ ‖(‖v‖ - ‖u‖) • NormedSpace.normalize u‖ + ‖u - v‖ := norm_add_le _ _
      _ = |‖v‖ - ‖u‖| + ‖u - v‖ := by
        rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hu, mul_one]
      _ ≤ 2 * ‖u - v‖ := by
        have habs := abs_norm_sub_norm_le v u
        rw [norm_sub_rev] at habs
        linarith
  apply (le_div_iff₀ (norm_pos_iff.mpr hv)).mpr
  nlinarith

theorem normalized_error_of_norm_ge_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} {error : ℝ} (hu : u ≠ 0) (hv : 1 ≤ ‖v‖)
    (herror : ‖u - v‖ ≤ error) :
    ‖NormedSpace.normalize u - NormedSpace.normalize v‖ ≤ 2 * error := by
  have hvpos : 0 < ‖v‖ := by linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  have he0 : 0 ≤ error := (norm_nonneg _).trans herror
  apply (normalized_error hu hv0).trans
  apply (div_le_iff₀ hvpos).mpr
  nlinarith

theorem final_angular_constant (d delta : ℝ) (hd : 1 ≤ d) (hdelta : 0 ≤ delta) :
    2 * Real.sqrt 5 * delta / (15 * Real.sqrt d) ≤ delta := by
  have hs : 1 ≤ Real.sqrt d := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd
  have hs5 : Real.sqrt 5 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ)), Real.sqrt_nonneg (5 : ℝ)]
  apply (div_le_iff₀ (by positivity : 0 < 15 * Real.sqrt d)).mpr
  nlinarith

theorem exact_query_count (d k : ℕ) (hd : 1 ≤ d) :
    d + (d - 1) + (d - 1) * k = 2 * d - 1 + (d - 1) * k := by
  omega

end

end Task004GDE

end SnapshotModule_000
/- END gde_invariants -/

/- BEGIN PaperSmooth -/
section SnapshotModule_001

/- Calculus bridges from the original smooth convex objective assumptions. -/
namespace PaperSmooth

open Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma line_hasDeriv (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (x v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (grad (x + t • v)) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  have hc := (hg (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl
  simpa using! hc

lemma convex_first_order (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f) (x y : V) :
    inner ℝ (grad x) (y - x) ≤ f y - f x := by
  let l : ℝ →ᵃ[ℝ] V := AffineMap.lineMap x y
  have hline := hc.comp_affineMap l
  have hd : HasDerivAt (fun t : ℝ => f (l t)) (inner ℝ (grad x) (y - x)) 0 := by
    have hh := line_hasDeriv f grad hg x (y - x) 0
    simpa [l, AffineMap.lineMap_apply, add_comm] using! hh
  have hs := hline.le_slope_of_hasDerivAt (show (0 : ℝ) ∈ l ⁻¹' univ by trivial)
    (show (1 : ℝ) ∈ l ⁻¹' univ by trivial) (by norm_num : (0 : ℝ) < 1) hd
  simpa [slope, l] using hs

lemma taylor_remainder (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (beta : NNReal)
    (hLip : LipschitzWith beta grad) (x y : V) :
    |f y - f x - inner ℝ (grad x) (y - x)| ≤ (beta : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  let v := y - x
  let F : ℝ → ℝ := fun t => f (x + t • v) - f x - t * inner ℝ (grad x) v
  let F' : ℝ → ℝ := fun t => inner ℝ (grad (x + t • v) - grad x) v
  have hF : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have hh := ((line_hasDeriv f grad hg x v t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (grad x) v))
    simpa [F, F', inner_sub_left, Pi.sub_apply] using! hh
  let B : ℝ → ℝ := fun t => (beta : ℝ) / 2 * ‖v‖ ^ 2 * t ^ 2
  let B' : ℝ → ℝ := fun t => (beta : ℝ) * ‖v‖ ^ 2 * t
  have hB : ∀ t : ℝ, HasDerivAt B (B' t) t := by
    intro t
    convert! ((hasDerivAt_id t).pow 2).const_mul ((beta : ℝ) / 2 * ‖v‖ ^ 2) using 1 <;>
      simp only [B, B', id_eq] <;> ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖F' t‖ ≤ B' t := by
    intro t ht
    have hi := abs_real_inner_le_norm (grad (x + t • v) - grad x) v
    have hl := hLip.norm_sub_le (x + t • v) x
    have hs : ‖(x + t • v) - x‖ = t * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul_of_nonneg ht.1]
    rw [hs] at hl
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg v)
    simpa only [F', Real.norm_eq_abs, B', pow_two, mul_assoc, mul_left_comm, mul_comm]
      using hi.trans hm
  have hnorm := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (show ContinuousOn F (Icc (0 : ℝ) 1) from fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show ‖F 0‖ ≤ B 0 by simp [F, B]) hB hbound
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa [F, B, v, Real.norm_eq_abs] using hnorm

lemma gradient_at_global_min (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (a : V)
    (hmin : ∀ x, f a ≤ f x) : grad a = 0 := by
  have hl : IsLocalMin f a := Filter.Eventually.of_forall hmin
  have hd := hl.hasFDerivAt_eq_zero (hg a).hasFDerivAt
  apply (InnerProductSpace.toDual ℝ V).injective
  simpa using hd

lemma gap_at_min (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (beta : NNReal)
    (hLip : LipschitzWith beta grad) (a x : V) (hmin : ∀ y, f a ≤ f y) :
    f x - f a ≤ (beta : ℝ) / 2 * ‖x - a‖ ^ 2 := by
  have hr := taylor_remainder f grad hg beta hLip a x
  have hzero := gradient_at_global_min f grad hg a hmin
  simpa [hzero, abs_of_nonneg (sub_nonneg.mpr (hmin x))] using hr

lemma descent_upper (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (beta : NNReal)
    (hLip : LipschitzWith beta grad) (x y : V) :
    f y ≤ f x + inner ℝ (grad x) (y - x) + (beta : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  have hr := (abs_le.mp (taylor_remainder f grad hg beta hLip x y)).2
  linarith

lemma normalized_gradient_gap (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x)
    (hLip : LipschitzWith 1 grad) (a x : V) (hmin : ∀ y, f a ≤ f y) :
    ‖grad x‖ ^ 2 ≤ 2 * (f x - f a) := by
  have hd := descent_upper f grad hg 1 hLip x (x - grad x)
  have hval := hmin (x - grad x)
  have hs : (x - grad x) - x = -(grad x) := by abel
  rw [hs, inner_neg_right, real_inner_self_eq_norm_sq, norm_neg] at hd
  norm_num at hd
  nlinarith

lemma smooth_probe (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x)
    (hLip : LipschitzWith 1 grad) (x v : V) (tau : ℝ)
    (htau : 0 ≤ tau) (hv : ‖v‖ ≤ 1) :
    |f (x + (2 * tau) • v) - f x - 2 * tau * inner ℝ (grad x) v| ≤ 2 * tau ^ 2 := by
  have hr := taylor_remainder f grad hg 1 hLip x (x + (2 * tau) • v)
  rw [add_sub_cancel_left, real_inner_smul_right, norm_smul_of_nonneg (by positivity)] at hr
  norm_num at hr
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hvsq : ‖v‖ ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg tau) (sub_nonneg.mpr hvsq)]

end PaperSmooth

end SnapshotModule_001
/- END PaperSmooth -/

/- BEGIN gde_complete -/
section SnapshotModule_002

/- Phase 2: actual finite-dimensional coordinates and comparison-only GDE.
   This file is under development. Theorems state their remaining interfaces
   explicitly; it is not yet a whole-Lemma certificate. -/

namespace PaperGDE

noncomputable section

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))
abbrev Oracle (n : ℕ) := Vec n → Vec n → Bool

def OracleCorrect {n : ℕ} (C : Oracle n) (g : Vec n → ℝ) : Prop :=
  ∀ y x, C y x = true ↔ g x ≤ g y

def basis {n : ℕ} (i : Fin (n + 1)) : Vec n := EuclideanSpace.single i 1

def probe {n : ℕ} (x : Vec n) (tau : ℝ) (v : Vec n) : Vec n :=
  x + (2 * tau) • v

def sign {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ) (i : Fin (n + 1)) : ℝ :=
  if C (probe x tau (basis i)) x then 1 else -1

def signedBasis {n : ℕ} (s : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Vec n :=
  EuclideanSpace.single i (s i)

def signedCoord {n : ℕ} (h : Vec n) (s : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  s i * h i

def matchDirection {n : ℕ} (s : Fin (n + 1) → ℝ) (p i : Fin (n + 1)) : Vec n :=
  (Real.sqrt 2)⁻¹ • (signedBasis s p - signedBasis s i)

def winner {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (p i : Fin (n + 1)) : Fin (n + 1) :=
  if C (probe x tau (matchDirection s p i)) x then p else i

def challengers (n : ℕ) : List (Fin (n + 1)) :=
  (List.finRange n).map Fin.succ

def champion {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (challengers n).foldl (winner C x tau s) 0

def DirectionalSound {n : ℕ} (C : Oracle n) (x h : Vec n) (tau : ℝ) : Prop :=
  ∀ v, ‖v‖ ≤ 1 →
    (C (probe x tau v) x = true → -tau ≤ inner ℝ h v) ∧
    (C (probe x tau v) x = false → inner ℝ h v ≤ tau)

theorem sign_abs {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ) (i : Fin (n + 1)) :
    |sign C x tau i| = 1 := by
  unfold sign
  split <;> norm_num

theorem basis_norm {n : ℕ} (i : Fin (n + 1)) : ‖basis i‖ = 1 := by
  simp [basis]

theorem signedBasis_norm {n : ℕ} (s : Fin (n + 1) → ℝ)
    (hs : ∀ i, |s i| = 1) (i : Fin (n + 1)) : ‖signedBasis s i‖ = 1 := by
  simpa [signedBasis, Real.norm_eq_abs] using hs i

theorem matchDirection_inner {n : ℕ} (h : Vec n) (s : Fin (n + 1) → ℝ)
    (p i : Fin (n + 1)) :
    inner ℝ h (matchDirection s p i) =
      (signedCoord h s p - signedCoord h s i) / Real.sqrt 2 := by
  simp [matchDirection, signedBasis, signedCoord, inner_smul_right, inner_sub_right,
    EuclideanSpace.inner_single_right, div_eq_mul_inv]
  ring

theorem matchDirection_norm_le {n : ℕ} (s : Fin (n + 1) → ℝ)
    (hs : ∀ i, |s i| = 1) (p i : Fin (n + 1)) :
    ‖matchDirection s p i‖ ≤ 1 := by
  by_cases hpi : p = i
  · subst p
    simp [matchDirection]
  have hinner : inner ℝ (signedBasis s p) (signedBasis s i) = 0 := by
    simp [signedBasis, EuclideanSpace.inner_single_left, hpi]
  have hdiff : ‖signedBasis s p - signedBasis s i‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, signedBasis_norm s hs p, signedBasis_norm s hs i, hinner]
    norm_num
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hle : ‖signedBasis s p - signedBasis s i‖ ≤ Real.sqrt 2 := by
    nlinarith [norm_nonneg (signedBasis s p - signedBasis s i)]
  rw [matchDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt)]
  calc
    (Real.sqrt 2)⁻¹ * ‖signedBasis s p - signedBasis s i‖ ≤
        (Real.sqrt 2)⁻¹ * Real.sqrt 2 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hsqrt)

theorem coordinate_sign_lower {n : ℕ} {C : Oracle n} {x h : Vec n} {tau : ℝ}
    (hsound : DirectionalSound C x h tau) (i : Fin (n + 1)) :
    -tau ≤ signedCoord h (sign C x tau) i := by
  have hh := hsound (basis i) (le_of_eq (basis_norm i))
  simp [basis, EuclideanSpace.inner_single_right] at hh
  unfold signedCoord sign
  cases hb : C (probe x tau (basis i)) x
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
    have hc := hh.2 hb
    linarith
  · simp only [↓reduceIte, one_mul]
    exact hh.1 hb

theorem winner_approximation {n : ℕ} {C : Oracle n} {x h : Vec n} {tau : ℝ}
    (htau : 0 ≤ tau) (s : Fin (n + 1) → ℝ) (hs : ∀ i, |s i| = 1)
    (hsound : DirectionalSound C x h tau) (p i : Fin (n + 1)) :
    signedCoord h s p ≤ signedCoord h s (winner C x tau s p i) + Real.sqrt 2 * tau ∧
    signedCoord h s i ≤ signedCoord h s (winner C x tau s p i) + Real.sqrt 2 * tau := by
  have hh := hsound (matchDirection s p i) (matchDirection_norm_le s hs p i)
  rw [matchDirection_inner] at hh
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnoise : 0 ≤ Real.sqrt 2 * tau := mul_nonneg (le_of_lt hsqrt) htau
  unfold winner
  cases hb : C (probe x tau (matchDirection s p i)) x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hc := (div_le_iff₀ hsqrt).mp (hh.2 hb)
    constructor <;> linarith
  · simp only [↓reduceIte]
    have hc := (le_div_iff₀ hsqrt).mp (hh.1 hb)
    constructor <;> linarith

theorem foldl_approximation {I : Type*} (choose : I → I → I) (a : I → ℝ) (noise : ℝ)
    (hnoise : 0 ≤ noise)
    (hchoose : ∀ p i, a p ≤ a (choose p i) + noise ∧ a i ≤ a (choose p i) + noise)
    (l : List I) (p : I) :
    a p ≤ a (l.foldl choose p) + (l.length : ℝ) * noise ∧
    ∀ i ∈ l, a i ≤ a (l.foldl choose p) + (l.length : ℝ) * noise := by
  induction l generalizing p with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hp, hi⟩ := hchoose p i
    obtain ⟨hchamp, hrest⟩ := ih (choose p i)
    simp only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor
    · linarith
    · intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · linarith
      · have h := hrest j hj
        linarith

theorem all_indices_covered (n : ℕ) (i : Fin (n + 1)) :
    i = 0 ∨ i ∈ challengers n := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Or.inl rfl
  · right
    simp [challengers]

theorem champion_bound {n : ℕ} {C : Oracle n} {x h : Vec n} {tau : ℝ}
    (htau : 0 ≤ tau) (s : Fin (n + 1) → ℝ) (hs : ∀ i, |s i| = 1)
    (hsound : DirectionalSound C x h tau) (i : Fin (n + 1)) :
    signedCoord h s i ≤ signedCoord h s (champion C x tau s) + (n : ℝ) * (Real.sqrt 2 * tau) := by
  have h := foldl_approximation (winner C x tau s) (signedCoord h s) (Real.sqrt 2 * tau)
    (by positivity) (winner_approximation htau s hs hsound) (challengers n) 0
  have hlen : (challengers n).length = n := by simp [challengers]
  rw [hlen] at h
  rcases all_indices_covered n i with hi | hi
  · subst i
    exact h.1
  · exact h.2 i hi

theorem directionalSound_of_remainder {n : ℕ} {C : Oracle n}
    {g : Vec n → ℝ} {x h : Vec n} {tau : ℝ} (htau : 0 < tau)
    (horacle : OracleCorrect C g)
    (hremainder : ∀ v, ‖v‖ ≤ 1 →
      |g (probe x tau v) - g x - 2 * tau * inner ℝ h v| ≤ 2 * tau ^ 2) :
    DirectionalSound C x h tau := by
  intro v hv
  constructor
  · intro hb
    have hc : 0 ≤ g (probe x tau v) - g x := sub_nonneg.mpr ((horacle _ _).mp hb)
    exact Task004GDE.positive_reply_direction htau (hremainder v hv) hc
  · intro hb
    have hc : g (probe x tau v) - g x < 0 := by
      apply sub_neg.mpr
      apply lt_of_not_ge
      intro hle
      have htrue := (horacle _ _).mpr hle
      rw [hb] at htrue
      contradiction
    exact Task004GDE.negative_reply_direction htau (hremainder v hv) hc

theorem coordinate_sign_large {n : ℕ} {C : Oracle n} {x h : Vec n} {tau : ℝ}
    (hsound : DirectionalSound C x h tau) (i : Fin (n + 1))
    (hlarge : tau < |h i|) :
    signedCoord h (sign C x tau) i = |h i| := by
  have hh := hsound (basis i) (le_of_eq (basis_norm i))
  simp [basis, EuclideanSpace.inner_single_right] at hh
  unfold signedCoord sign
  cases hb : C (probe x tau (basis i)) x
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
    have hc := hh.2 hb
    by_cases hi : h i ≤ 0
    · rw [abs_of_nonpos hi]
    · have hp : 0 < h i := lt_of_not_ge hi
      rw [abs_of_pos hp] at hlarge
      linarith
  · simp only [↓reduceIte, one_mul]
    have hc := hh.1 hb
    by_cases hi : 0 ≤ h i
    · exact (abs_of_nonneg hi).symm
    · have hp : h i < 0 := lt_of_not_ge hi
      rw [abs_of_neg hp] at hlarge
      linarith

theorem signedCoord_abs {n : ℕ} (h : Vec n) (s : Fin (n + 1) → ℝ)
    (hs : ∀ i, |s i| = 1) (i : Fin (n + 1)) :
    |signedCoord h s i| = |h i| := by
  simp [signedCoord, abs_mul, hs]

theorem exists_max_coordinate (n : ℕ) (h : Vec n) :
    ∃ i : Fin (n + 1), (∀ j, |h j| ≤ |h i|) ∧
      ‖h‖ ≤ Real.sqrt (n + 1 : ℝ) * |h i| := by
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin (n + 1) => |h i|)
    Finset.univ_nonempty
  have hm : ∀ j, |h j| ≤ |h i| := fun j => hmax j (Finset.mem_univ j)
  refine ⟨i, hm, ?_⟩
  have hs : ‖h‖ ^ 2 ≤ (n + 1 : ℝ) * |h i| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j : Fin (n + 1), (h j) ^ 2) ≤ ∑ _j : Fin (n + 1), |h i| ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hh := sq_le_sq₀ (abs_nonneg (h j)) (abs_nonneg (h i)) |>.mpr (hm j)
        simpa only [sq_abs] using hh
      _ = (n + 1 : ℝ) * |h i| ^ 2 := by simp
  have hsqrt : (Real.sqrt (n + 1 : ℝ)) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ Real.sqrt (n + 1 : ℝ) * |h i| := by positivity
  nlinarith [norm_nonneg h]

def tauValue (n : ℕ) (delta gamma : ℝ) : ℝ :=
  delta * gamma / (32 * (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ))

def zetaValue (n : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt 5 * delta / (30 * (n + 1 : ℝ))

theorem tau_parameter_bound (n : ℕ) {delta gamma M : ℝ}
    (hd : 0 < delta) (hgamma : 0 < gamma)
    (hM : gamma ≤ Real.sqrt (n + 1 : ℝ) * M) :
    0 < tauValue n delta gamma ∧
      tauValue n delta gamma ≤ delta * M / (32 * (n + 1 : ℝ)) := by
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · unfold tauValue
    positivity
  · unfold tauValue
    apply (div_le_iff₀ (by positivity : 0 < 32 * (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_left hM (le_of_lt hd)
    have heq : delta * M / (32 * (n + 1 : ℝ)) *
        (32 * (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ)) =
        delta * (Real.sqrt (n + 1 : ℝ) * M) := by
      field_simp
    rw [heq]
    exact hmul

theorem champion_pivot {n : ℕ} {C : Oracle n} {x h : Vec n}
    {delta gamma : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hgamma : 0 < gamma) (hnorm : gamma ≤ ‖h‖)
    (hsound : DirectionalSound C x h (tauValue n delta gamma)) :
    ∃ M : ℝ, 0 < M ∧ (∀ i, |h i| ≤ M) ∧
      tauValue n delta gamma ≤ delta * M / (32 * (n + 1 : ℝ)) ∧
      (15 * M / 16 ≤ signedCoord h (sign C x (tauValue n delta gamma))
        (champion C x (tauValue n delta gamma) (sign C x (tauValue n delta gamma)))) ∧
      (∀ i, |signedCoord h (sign C x (tauValue n delta gamma)) i /
        signedCoord h (sign C x (tauValue n delta gamma))
          (champion C x (tauValue n delta gamma) (sign C x (tauValue n delta gamma)))| < 2) := by
  obtain ⟨imax, hmax, hnormM⟩ := exists_max_coordinate n h
  let M := |h imax|
  have hM : gamma ≤ Real.sqrt (n + 1 : ℝ) * M := hnorm.trans hnormM
  have hMpos : 0 < M := by
    have hs : 0 ≤ Real.sqrt (n + 1 : ℝ) := Real.sqrt_nonneg _
    have hm : 0 ≤ M := abs_nonneg _
    by_contra hn
    have hz : M = 0 := le_antisymm (le_of_not_gt hn) hm
    rw [hz, mul_zero] at hM
    linarith
  obtain ⟨htaupos, htaub⟩ := tau_parameter_bound n hdelta hgamma hM
  have htaub1 : tauValue n delta gamma ≤ M / (32 * (n + 1 : ℝ)) := by
    apply htaub.trans
    apply div_le_div_of_nonneg_right
    · nlinarith
    · positivity
  have htauM : tauValue n delta gamma < M := by
    apply htaub1.trans_lt
    exact div_lt_self hMpos (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have himax : signedCoord h (sign C x (tauValue n delta gamma)) imax = M :=
    coordinate_sign_large hsound imax htauM
  have hc := champion_bound (le_of_lt htaupos) (sign C x (tauValue n delta gamma))
    (sign_abs C x (tauValue n delta gamma)) hsound imax
  rw [himax] at hc
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), Real.sqrt_nonneg (2 : ℝ)]
  have hnoise : (n : ℝ) * (Real.sqrt 2 * tauValue n delta gamma) ≤ M / 16 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 32 * (n + 1 : ℝ))).mp htaub1
    have hm := mul_le_mul_of_nonneg_right hsqrt2 (le_of_lt htaupos)
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm2 := mul_le_mul_of_nonneg_left hm hnn
    nlinarith
  have hpivot : 15 * M / 16 ≤ signedCoord h (sign C x (tauValue n delta gamma))
      (champion C x (tauValue n delta gamma) (sign C x (tauValue n delta gamma))) := by
    linarith
  refine ⟨M, hMpos, hmax, htaub, hpivot, ?_⟩
  intro i
  have hp : 0 < signedCoord h (sign C x (tauValue n delta gamma))
      (champion C x (tauValue n delta gamma) (sign C x (tauValue n delta gamma))) := by
    linarith
  rw [abs_div, abs_of_pos hp]
  apply (div_lt_iff₀ hp).mpr
  rw [signedCoord_abs h _ (sign_abs C x _) i]
  have hi := hmax i
  linarith

theorem directionalSound_of_smooth {n : ℕ} {C : Oracle n}
    (g : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt g (grad x) x) (hLip : LipschitzWith 1 grad)
    (horacle : OracleCorrect C g) (x : Vec n) (tau : ℝ) (htau : 0 < tau) :
    DirectionalSound C x (grad x) tau := by
  apply directionalSound_of_remainder htau horacle
  intro v hv
  exact PaperSmooth.smooth_probe g grad hg hLip x v tau (le_of_lt htau) hv

def ratioDirection {n : ℕ} (s : Fin (n + 1) → ℝ) (j i : Fin (n + 1)) (alpha : ℝ) : Vec n :=
  (Real.sqrt (1 + alpha ^ 2))⁻¹ • (alpha • signedBasis s j - signedBasis s i)

theorem ratioDirection_inner {n : ℕ} (h : Vec n) (s : Fin (n + 1) → ℝ)
    (j i : Fin (n + 1)) (alpha : ℝ) :
    inner ℝ h (ratioDirection s j i alpha) =
      (alpha * signedCoord h s j - signedCoord h s i) / Real.sqrt (1 + alpha ^ 2) := by
  simp [ratioDirection, signedBasis, signedCoord, inner_smul_right, inner_sub_right,
    EuclideanSpace.inner_single_right, div_eq_mul_inv]
  ring

theorem ratioDirection_norm_le {n : ℕ} (s : Fin (n + 1) → ℝ)
    (hs : ∀ i, |s i| = 1) (j i : Fin (n + 1)) (hij : i ≠ j) (alpha : ℝ) :
    ‖ratioDirection s j i alpha‖ ≤ 1 := by
  have hinner : inner ℝ (alpha • signedBasis s j) (signedBasis s i) = 0 := by
    simp [signedBasis, EuclideanSpace.inner_single_left, inner_smul_left, Ne.symm hij]
  have hdiff : ‖alpha • signedBasis s j - signedBasis s i‖ ^ 2 = 1 + alpha ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, signedBasis_norm s hs j,
      signedBasis_norm s hs i, hinner, Real.norm_eq_abs]
    simp [sq_abs]
    ring
  have hsqrt : 0 < Real.sqrt (1 + alpha ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt2 : (Real.sqrt (1 + alpha ^ 2)) ^ 2 = 1 + alpha ^ 2 := Real.sq_sqrt (by positivity)
  have hle : ‖alpha • signedBasis s j - signedBasis s i‖ ≤ Real.sqrt (1 + alpha ^ 2) := by
    nlinarith [norm_nonneg (alpha • signedBasis s j - signedBasis s i)]
  rw [ratioDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt)]
  calc
    (Real.sqrt (1 + alpha ^ 2))⁻¹ * ‖alpha • signedBasis s j - signedBasis s i‖ ≤
        (Real.sqrt (1 + alpha ^ 2))⁻¹ * Real.sqrt (1 + alpha ^ 2) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hsqrt)

theorem ratio_noise_budget (n : ℕ) {delta M tau a alpha : ℝ}
    (hd : 0 < delta) (hM : 0 < M) (htau : 0 ≤ tau)
    (htaub : tau ≤ delta * M / (32 * (n + 1 : ℝ)))
    (ha : 15 * M / 16 ≤ a) (halpha : -2 ≤ alpha ∧ alpha ≤ 2) :
    tau * Real.sqrt (1 + alpha ^ 2) ≤ a * zetaValue n delta := by
  have hsqrt : Real.sqrt (1 + alpha ^ 2) ≤ Real.sqrt 5 := by
    apply Real.sqrt_le_sqrt
    nlinarith
  calc
    tau * Real.sqrt (1 + alpha ^ 2) ≤ tau * Real.sqrt 5 :=
      mul_le_mul_of_nonneg_left hsqrt htau
    _ ≤ (delta * M / (32 * (n + 1 : ℝ))) * Real.sqrt 5 :=
      mul_le_mul_of_nonneg_right htaub (Real.sqrt_nonneg _)
    _ = (15 * M / 16) * zetaValue n delta := by
      unfold zetaValue
      field_simp
      ring
    _ ≤ a * zetaValue n delta := mul_le_mul_of_nonneg_right ha (by unfold zetaValue; positivity)

open Task004GDE (Interval midpoint step width invariant replySound)

def ratioState {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j i : Fin (n + 1)) : ℕ → Interval
  | 0 => ⟨-2, 2⟩
  | k + 1 =>
      let I := ratioState C x tau s j i k
      step (C (probe x tau (ratioDirection s j i (midpoint I))) x) I

theorem interval_step_bounds (I : Interval) (b : Bool)
    (hI : -2 ≤ I.lo ∧ I.lo ≤ I.hi ∧ I.hi ≤ 2) :
    -2 ≤ (step b I).lo ∧ (step b I).lo ≤ (step b I).hi ∧ (step b I).hi ≤ 2 := by
  rcases hI with ⟨hl, ho, hu⟩
  cases b <;> simp [step, Task004GDE.midpoint] <;> (repeat' constructor) <;> linarith

theorem ratioState_bounds {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j i : Fin (n + 1)) (k : ℕ) :
    -2 ≤ (ratioState C x tau s j i k).lo ∧
      (ratioState C x tau s j i k).lo ≤ (ratioState C x tau s j i k).hi ∧
      (ratioState C x tau s j i k).hi ≤ 2 := by
  induction k with
  | zero => norm_num [ratioState]
  | succ k ih => exact interval_step_bounds _ _ ih

theorem ratioState_width {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j i : Fin (n + 1)) (k : ℕ) :
    width (ratioState C x tau s j i k) = 4 * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num [ratioState, width]
  | succ k ih =>
    rw [ratioState, Task004GDE.step_halves_width, ih, pow_succ]
    ring

theorem ratio_reply_sound {n : ℕ} {C : Oracle n} {x h : Vec n}
    {delta M tau : ℝ} (hd : 0 < delta) (hM : 0 < M) (htau : 0 ≤ tau)
    (htaub : tau ≤ delta * M / (32 * (n + 1 : ℝ)))
    (s : Fin (n + 1) → ℝ) (hs : ∀ i, |s i| = 1)
    (j i : Fin (n + 1)) (hij : i ≠ j)
    (ha : 15 * M / 16 ≤ signedCoord h s j)
    (hsound : DirectionalSound C x h tau) (alpha : ℝ)
    (halpha : -2 ≤ alpha ∧ alpha ≤ 2) :
    (C (probe x tau (ratioDirection s j i alpha)) x = true →
      signedCoord h s i / signedCoord h s j - zetaValue n delta ≤ alpha) ∧
    (C (probe x tau (ratioDirection s j i alpha)) x = false →
      alpha ≤ signedCoord h s i / signedCoord h s j + zetaValue n delta) := by
  have hap : 0 < signedCoord h s j := by linarith
  have hden : 0 < Real.sqrt (1 + alpha ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have htol := ratio_noise_budget n hd hM htau htaub ha halpha
  have hdir := hsound (ratioDirection s j i alpha) (ratioDirection_norm_le s hs j i hij alpha)
  have heq : inner ℝ h (ratioDirection s j i alpha) = signedCoord h s j *
      (alpha - signedCoord h s i / signedCoord h s j) / Real.sqrt (1 + alpha ^ 2) := by
    rw [ratioDirection_inner]
    field_simp
  rw [heq] at hdir
  constructor
  · intro hb
    exact Task004GDE.positive_ratio_reply hap hden htol (hdir.1 hb)
  · intro hb
    exact Task004GDE.negative_ratio_reply hap hden htol (hdir.2 hb)

theorem ratioState_invariant {n : ℕ} {C : Oracle n} {x h : Vec n}
    {delta M tau : ℝ} (hd : 0 < delta) (hM : 0 < M) (htau : 0 ≤ tau)
    (htaub : tau ≤ delta * M / (32 * (n + 1 : ℝ)))
    (s : Fin (n + 1) → ℝ) (hs : ∀ i, |s i| = 1)
    (j i : Fin (n + 1)) (hij : i ≠ j)
    (ha : 15 * M / 16 ≤ signedCoord h s j)
    (hsound : DirectionalSound C x h tau)
    (hratio : |signedCoord h s i / signedCoord h s j| < 2) (k : ℕ) :
    invariant (ratioState C x tau s j i k)
      (signedCoord h s i / signedCoord h s j) (zetaValue n delta) := by
  have hzeta : 0 ≤ zetaValue n delta := by unfold zetaValue; positivity
  induction k with
  | zero =>
    have hr := abs_lt.mp hratio
    simp only [ratioState, invariant]
    constructor
    · norm_num
    constructor <;> linarith
  | succ k ih =>
    apply Task004GDE.step_preserves_invariant ih
    have hb := ratioState_bounds C x tau s j i k
    have hm : -2 ≤ midpoint (ratioState C x tau s j i k) ∧
        midpoint (ratioState C x tau s j i k) ≤ 2 := by
      dsimp [Task004GDE.midpoint]
      constructor <;> linarith [hb.1, hb.2.1, hb.2.2]
    have hr := ratio_reply_sound hd hM htau htaub s hs j i hij ha hsound _ hm
    unfold replySound
    split <;> rename_i heq
    · exact hr.1 heq
    · have hf : C (probe x tau (ratioDirection s j i (midpoint (ratioState C x tau s j i k)))) x = false := by
        cases h : C (probe x tau (ratioDirection s j i (midpoint (ratioState C x tau s j i k)))) x <;> simp_all
      exact hr.2 hf

def rounds (n : ℕ) (delta : ℝ) : ℕ :=
  ⌈Real.logb 2 (60 * (n + 1 : ℝ) / (Real.sqrt 5 * delta))⌉₊

theorem rounds_width (n : ℕ) {delta : ℝ} (hd : 0 < delta) :
    4 * (1 / 2 : ℝ) ^ rounds n delta ≤ 2 * zetaValue n delta := by
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hzeta : 0 < zetaValue n delta := by unfold zetaValue; positivity
  have harg : 0 < 60 * (n + 1 : ℝ) / (Real.sqrt 5 * delta) := by positivity
  have hlog := Nat.le_ceil (Real.logb 2 (60 * (n + 1 : ℝ) / (Real.sqrt 5 * delta)))
  have hpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) harg).mp hlog
  rw [Real.rpow_natCast] at hpow
  change _ ≤ (2 : ℝ) ^ rounds n delta at hpow
  have heq : 60 * (n + 1 : ℝ) / (Real.sqrt 5 * delta) = 2 / zetaValue n delta := by
    unfold zetaValue
    field_simp
    norm_num
  rw [heq] at hpow
  have hp := (div_le_iff₀ hzeta).mp hpow
  rw [one_div_pow, mul_one_div]
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ rounds n delta)).mpr
  nlinarith

def estimate {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (k : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = j then 1 else midpoint (ratioState C x tau s j i k)

def rawVector {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (k : ℕ) : Vec n :=
  WithLp.toLp 2 (fun i => estimate C x tau s j k i * s i)

theorem rawVector_anchor {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (k : ℕ) :
    (rawVector C x tau s j k) j = s j := by
  simp [rawVector, estimate]

theorem rawVector_ne_zero {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (hs : ∀ i, |s i| = 1) (j : Fin (n + 1)) (k : ℕ) :
    rawVector C x tau s j k ≠ 0 := by
  intro hz
  have ha := rawVector_anchor C x tau s j k
  rw [hz] at ha
  have hs1 := hs j
  have hzero : s j = 0 := ha.symm
  rw [hzero] at hs1
  norm_num at hs1

theorem euclidean_coordinate_bound {n : ℕ} (u : Vec n) {b : ℝ}
    (hb : 0 ≤ b) (hu : ∀ i, |u i| ≤ b) :
    ‖u‖ ≤ Real.sqrt (n + 1 : ℝ) * b := by
  have hs : ‖u‖ ^ 2 ≤ (n + 1 : ℝ) * b ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Fin (n + 1), (u i) ^ 2) ≤ ∑ _i : Fin (n + 1), b ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh := sq_le_sq₀ (abs_nonneg (u i)) hb |>.mpr (hu i)
        simpa only [sq_abs] using hh
      _ = (n + 1 : ℝ) * b ^ 2 := by simp
  have hsqrt : (Real.sqrt (n + 1 : ℝ)) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ Real.sqrt (n + 1 : ℝ) * b := by positivity
  nlinarith [norm_nonneg u]

theorem reflected_ratio_identity {n : ℕ} (h : Vec n) (s : Fin (n + 1) → ℝ)
    (hs : ∀ i, |s i| = 1) (j i : Fin (n + 1)) :
    s i * (signedCoord h s i / signedCoord h s j) =
      (signedCoord h s j)⁻¹ * h i := by
  have hs2 : (s i) ^ 2 = 1 := by nlinarith [sq_abs (s i), hs i]
  calc
    s i * (signedCoord h s i / signedCoord h s j) =
        (s i) ^ 2 * h i / signedCoord h s j := by unfold signedCoord; ring
    _ = (signedCoord h s j)⁻¹ * h i := by rw [hs2]; ring

theorem normalized_raw_accuracy {n : ℕ} {C : Oracle n} {x h : Vec n}
    {delta M tau : ℝ} (hd : 0 < delta) (hM : 0 < M) (htau : 0 ≤ tau)
    (htaub : tau ≤ delta * M / (32 * (n + 1 : ℝ)))
    (s : Fin (n + 1) → ℝ) (hs : ∀ i, |s i| = 1)
    (j : Fin (n + 1)) (ha : 15 * M / 16 ≤ signedCoord h s j)
    (hsound : DirectionalSound C x h tau)
    (hratio : ∀ i, |signedCoord h s i / signedCoord h s j| < 2) :
    ‖NormedSpace.normalize (rawVector C x tau s j (rounds n delta)) -
      NormedSpace.normalize h‖ ≤ delta := by
  let v : Vec n := (signedCoord h s j)⁻¹ • h
  have hap : 0 < signedCoord h s j := by linarith
  have hzeta : 0 ≤ zetaValue n delta := by unfold zetaValue; positivity
  have herr : ∀ i, |estimate C x tau s j (rounds n delta) i -
      signedCoord h s i / signedCoord h s j| ≤ 2 * zetaValue n delta := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [estimate, ne_of_gt hap, hzeta]
    · have hi := ratioState_invariant hd hM htau htaub s hs j i hij ha hsound (hratio i) (rounds n delta)
      have hw : width (ratioState C x tau s j i (rounds n delta)) ≤ 2 * zetaValue n delta := by
        rw [ratioState_width]
        exact rounds_width n hd
      simpa [estimate, hij] using Task004GDE.midpoint_error hi hw
  have hvj : v j = s j := by
    have hh := reflected_ratio_identity h s hs j j
    simp only [div_self (ne_of_gt hap), mul_one] at hh
    simpa [v] using hh.symm
  have hvnorm : 1 ≤ ‖v‖ := by
    have hp := PiLp.norm_apply_le v j
    simpa only [Real.norm_eq_abs, hvj, hs j] using hp
  have hecoord : ∀ i, |(rawVector C x tau s j (rounds n delta) - v) i| ≤ 2 * zetaValue n delta := by
    intro i
    have hid : (rawVector C x tau s j (rounds n delta) - v) i =
        s i * (estimate C x tau s j (rounds n delta) i - signedCoord h s i / signedCoord h s j) := by
      have hh := reflected_ratio_identity h s hs j i
      change estimate C x tau s j (rounds n delta) i * s i - (signedCoord h s j)⁻¹ * h i = _
      rw [← hh]
      ring
    rw [hid, abs_mul, hs i, one_mul]
    exact herr i
  have hnormerr := euclidean_coordinate_bound
    (rawVector C x tau s j (rounds n delta) - v) (by positivity) hecoord
  have hnormalize := Task004GDE.normalized_error_of_norm_ge_one
    (rawVector_ne_zero C x tau s hs j (rounds n delta)) hvnorm hnormerr
  have hvnormalize : NormedSpace.normalize v = NormedSpace.normalize h :=
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr hap) h
  rw [hvnormalize] at hnormalize
  apply hnormalize.trans
  have hsd : (Real.sqrt (n + 1 : ℝ)) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have heq : 2 * (Real.sqrt (n + 1 : ℝ) * (2 * zetaValue n delta)) =
      2 * Real.sqrt 5 * delta / (15 * Real.sqrt (n + 1 : ℝ)) := by
    unfold zetaValue
    field_simp
    nlinarith [hsd]
  rw [heq]
  exact Task004GDE.final_angular_constant (n + 1 : ℝ) delta (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (le_of_lt hd)

def gde {n : ℕ} (C : Oracle n) (x : Vec n) (delta gamma : ℝ) : Vec n :=
  let tau := tauValue n delta gamma
  let s := sign C x tau
  let j := champion C x tau s
  NormedSpace.normalize (rawVector C x tau s j (rounds n delta))

theorem gde_unit {n : ℕ} (C : Oracle n) (x : Vec n) (delta gamma : ℝ) :
    ‖gde C x delta gamma‖ = 1 := by
  apply NormedSpace.norm_normalize
  exact rawVector_ne_zero C x _ _ (sign_abs C x _) _ _

theorem gde_accuracy {n : ℕ} {C : Oracle n}
    (g : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt g (grad x) x) (hLip : LipschitzWith 1 grad)
    (horacle : OracleCorrect C g) (x : Vec n) (delta gamma : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hgamma : 0 < gamma)
    (hnorm : gamma ≤ ‖grad x‖) :
    ‖gde C x delta gamma - NormedSpace.normalize (grad x)‖ ≤ delta := by
  have htau : 0 < tauValue n delta gamma := by unfold tauValue; positivity
  have hsound := directionalSound_of_smooth g grad hg hLip horacle x _ htau
  obtain ⟨M, hM, _hmax, htaub, hpivot, hratio⟩ := champion_pivot hd hd1 hgamma hnorm hsound
  exact normalized_raw_accuracy hd hM (le_of_lt htau) htaub _ (sign_abs C x _)
    _ hpivot hsound hratio

end
end PaperGDE

end SnapshotModule_002
/- END gde_complete -/

/- BEGIN gde_program -/
section SnapshotModule_003

/- A finite comparison-query syntax and an oracle-only implementation of GDE.
   Real arithmetic is mathematical/free, as in the paper's declared model. -/
namespace PaperGDE
noncomputable section

inductive Program (n : ℕ) (α : Type) where
  | pure : α → Program n α
  | query : Vec n → Vec n → (Bool → Program n α) → Program n α

namespace Program

def bind {n : ℕ} {α β : Type} (P : Program n α) (f : α → Program n β) : Program n β :=
  match P with
  | .pure a => f a
  | .query y x next => .query y x (fun b => bind (next b) f)

def eval {n : ℕ} {α : Type} (C : Oracle n) : Program n α → α
  | .pure a => a
  | .query y x next => eval C (next (C y x))

def count {n : ℕ} {α : Type} (C : Oracle n) : Program n α → ℕ
  | .pure _ => 0
  | .query y x next => 1 + count C (next (C y x))

theorem eval_bind {n : ℕ} {α β : Type} (C : Oracle n)
    (P : Program n α) (f : α → Program n β) :
    eval C (bind P f) = eval C (f (eval C P)) := by
  induction P with
  | pure a => rfl
  | query y x next ih => simp [bind, eval, ih]

theorem count_bind {n : ℕ} {α β : Type} (C : Oracle n)
    (P : Program n α) (f : α → Program n β) :
    count C (bind P f) = count C P + count C (f (eval C P)) := by
  induction P with
  | pure a => simp [bind, count, eval]
  | query y x next ih => simp [bind, count, eval, ih, Nat.add_assoc]

def collect {n : ℕ} {α : Type} : (m : ℕ) → (Fin m → Program n α) → Program n (Fin m → α)
  | 0, _ => .pure Fin.elim0
  | m + 1, f => bind (f 0) (fun first =>
      bind (collect m (fun i => f i.succ)) (fun rest => .pure (Fin.cons first rest)))

theorem eval_collect {n : ℕ} {α : Type} (C : Oracle n) (m : ℕ) (f : Fin m → Program n α) :
    eval C (collect m f) = fun i => eval C (f i) := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    simp only [collect, eval_bind, eval]
    rw [ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem count_collect {n : ℕ} {α : Type} (C : Oracle n) (m : ℕ) (f : Fin m → Program n α) :
    count C (collect m f) = ∑ i, count C (f i) := by
  induction m with
  | zero => simp [collect, count]
  | succ m ih => simp [collect, count_bind, count, ih, Fin.sum_univ_succ]

end Program

def signsProgram {n : ℕ} (x : Vec n) (tau : ℝ) : Program n (Fin (n + 1) → ℝ) :=
  Program.collect (n + 1) (fun i => .query (probe x tau (basis i)) x
    (fun b => .pure (if b then 1 else -1)))

theorem signsProgram_eval {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ) :
    Program.eval C (signsProgram x tau) = sign C x tau := by
  rw [signsProgram, Program.eval_collect]
  rfl

theorem signsProgram_count {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ) :
    Program.count C (signsProgram x tau) = n + 1 := by
  simp [signsProgram, Program.count_collect, Program.count]

def tournamentProgram {n : ℕ} (x : Vec n) (tau : ℝ) (s : Fin (n + 1) → ℝ) :
    Fin (n + 1) → List (Fin (n + 1)) → Program n (Fin (n + 1))
  | p, [] => .pure p
  | p, i :: rest => .query (probe x tau (matchDirection s p i)) x
      (fun b => tournamentProgram x tau s (if b then p else i) rest)

theorem tournamentProgram_eval {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (l : List (Fin (n + 1))) (p : Fin (n + 1)) :
    Program.eval C (tournamentProgram x tau s p l) = l.foldl (winner C x tau s) p := by
  induction l generalizing p with
  | nil => rfl
  | cons i rest ih => simp [tournamentProgram, Program.eval, List.foldl_cons, ih, winner]

theorem tournamentProgram_count {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (l : List (Fin (n + 1))) (p : Fin (n + 1)) :
    Program.count C (tournamentProgram x tau s p l) = l.length := by
  induction l generalizing p with
  | nil => rfl
  | cons i rest ih => simp [tournamentProgram, Program.count, ih, Nat.add_comm]

def ratioProgram {n : ℕ} (x : Vec n) (tau : ℝ) (s : Fin (n + 1) → ℝ)
    (j i : Fin (n + 1)) : ℕ → Program n Task004GDE.Interval
  | 0 => .pure ⟨-2, 2⟩
  | k + 1 => Program.bind (ratioProgram x tau s j i k) (fun I =>
      .query (probe x tau (ratioDirection s j i (Task004GDE.midpoint I))) x
        (fun b => .pure (Task004GDE.step b I)))

theorem ratioProgram_eval {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j i : Fin (n + 1)) (k : ℕ) :
    Program.eval C (ratioProgram x tau s j i k) = ratioState C x tau s j i k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ratioProgram, Program.eval_bind, Program.eval, ih, ratioState]

theorem ratioProgram_count {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j i : Fin (n + 1)) (k : ℕ) :
    Program.count C (ratioProgram x tau s j i k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ratioProgram, Program.count_bind, Program.count, ih]

def estimatesProgram {n : ℕ} (x : Vec n) (tau : ℝ) (s : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (k : ℕ) : Program n (Fin (n + 1) → ℝ) :=
  Program.collect (n + 1) (fun i => if i = j then .pure 1 else
    Program.bind (ratioProgram x tau s j i k) (fun I => .pure (Task004GDE.midpoint I)))

theorem estimatesProgram_eval {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (k : ℕ) :
    Program.eval C (estimatesProgram x tau s j k) = estimate C x tau s j k := by
  rw [estimatesProgram, Program.eval_collect]
  funext i
  by_cases hij : i = j <;> simp [hij, Program.eval, Program.eval_bind, ratioProgram_eval, estimate]

theorem sum_except_anchor (n k : ℕ) (j : Fin (n + 1)) :
    (∑ i : Fin (n + 1), if i = j then 0 else k) = n * k := by
  have hs : (∑ i : Fin (n + 1), if i = j then k else 0) +
      (∑ i : Fin (n + 1), if i = j then 0 else k) = (n + 1) * k := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i : Fin (n + 1), ((if i = j then k else 0) + (if i = j then 0 else k))) =
          ∑ _i : Fin (n + 1), k := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = (n + 1) * k := by simp
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hs
  rw [Nat.add_mul, one_mul] at hs
  omega

theorem estimatesProgram_count {n : ℕ} (C : Oracle n) (x : Vec n) (tau : ℝ)
    (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (k : ℕ) :
    Program.count C (estimatesProgram x tau s j k) = n * k := by
  rw [estimatesProgram, Program.count_collect]
  have heq : (fun i : Fin (n + 1) => Program.count C
      (if i = j then Program.pure 1 else Program.bind (ratioProgram x tau s j i k)
        (fun I => Program.pure (Task004GDE.midpoint I)))) =
      (fun i => if i = j then 0 else k) := by
    funext i
    by_cases hij : i = j <;> simp [hij, Program.count, Program.count_bind, ratioProgram_count]
  change (∑ i, (fun i : Fin (n + 1) => Program.count C
      (if i = j then Program.pure 1 else Program.bind (ratioProgram x tau s j i k)
        (fun I => Program.pure (Task004GDE.midpoint I)))) i) = _
  rw [heq]
  exact sum_except_anchor n k j

def gdeProgram {n : ℕ} (x : Vec n) (delta gamma : ℝ) : Program n (Vec n) :=
  let tau := tauValue n delta gamma
  Program.bind (signsProgram x tau) (fun s =>
    Program.bind (tournamentProgram x tau s 0 (challengers n)) (fun j =>
      Program.bind (estimatesProgram x tau s j (rounds n delta)) (fun alpha =>
        .pure (NormedSpace.normalize (WithLp.toLp 2 (fun i => alpha i * s i))))))

theorem gdeProgram_eval {n : ℕ} (C : Oracle n) (x : Vec n) (delta gamma : ℝ) :
    Program.eval C (gdeProgram x delta gamma) = gde C x delta gamma := by
  simp [gdeProgram, Program.eval_bind, Program.eval, signsProgram_eval,
    tournamentProgram_eval, estimatesProgram_eval, gde, rawVector, champion]

theorem gdeProgram_exact_count {n : ℕ} (C : Oracle n) (x : Vec n) (delta gamma : ℝ) :
    Program.count C (gdeProgram x delta gamma) =
      2 * (n + 1) - 1 + n * rounds n delta := by
  simp only [gdeProgram, Program.count_bind, signsProgram_count, estimatesProgram_count,
    tournamentProgram_count, Program.count, add_zero]
  have hlen : (challengers n).length = n := by simp [challengers]
  rw [hlen]
  omega

theorem full_gde_certificate {n : ℕ} {C : Oracle n}
    (g : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt g (grad x) x) (hLip : LipschitzWith 1 grad)
    (horacle : OracleCorrect C g) (x : Vec n) (delta gamma : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hgamma : 0 < gamma)
    (hnorm : gamma ≤ ‖grad x‖) :
    ‖Program.eval C (gdeProgram x delta gamma)‖ = 1 ∧
      ‖Program.eval C (gdeProgram x delta gamma) - NormedSpace.normalize (grad x)‖ ≤ delta ∧
      Program.count C (gdeProgram x delta gamma) =
        2 * (n + 1) - 1 + n * rounds n delta := by
  rw [gdeProgram_eval]
  exact ⟨gde_unit C x delta gamma, gde_accuracy g grad hg hLip horacle x delta gamma hd hd1 hgamma hnorm,
    gdeProgram_exact_count C x delta gamma⟩

theorem gdeProgram_total_unit {n : ℕ} (C : Oracle n) (x : Vec n) (delta gamma : ℝ) :
    ‖Program.eval C (gdeProgram x delta gamma)‖ = 1 := by
  rw [gdeProgram_eval]
  exact gde_unit C x delta gamma

def oracleOfOrdering {n : ℕ} (C : Vec n → Vec n → Ordering) : Oracle n :=
  fun y x => decide (C y x ≠ Ordering.lt)

theorem oracleOfOrdering_correct {n : ℕ} (C : Vec n → Vec n → Ordering)
    (g : Vec n → ℝ) (hnegative : ∀ y x, C y x = Ordering.lt ↔ g y < g x) :
    OracleCorrect (oracleOfOrdering C) g := by
  intro y x
  simp only [oracleOfOrdering, decide_eq_true_eq]
  exact (not_congr (hnegative y x)).trans not_lt

end
end PaperGDE

end SnapshotModule_003
/- END gde_program -/

/- BEGIN gde_rescaling -/
section SnapshotModule_004

namespace PaperGDE
noncomputable section

theorem scaled_hasGradient {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (L : ℝ) :
    ∀ x, HasGradientAt (fun y => f y / L) (L⁻¹ • grad x) x := by
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa [div_eq_mul_inv, mul_comm] using (hg x).hasFDerivAt.const_mul L⁻¹

theorem scaled_lipschitz {n : ℕ} (grad : Vec n → Vec n) (L : NNReal)
    (hL : 0 < L) (hLip : LipschitzWith L grad) :
    LipschitzWith 1 (fun x => (L : ℝ)⁻¹ • grad x) := by
  have hp : 0 < (L : ℝ) := hL
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  calc
    (L : ℝ)⁻¹ * ‖grad x - grad y‖ ≤ (L : ℝ)⁻¹ * ((L : ℝ) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (hLip.norm_sub_le x y) (by positivity)
    _ = ‖x - y‖ := by field_simp

theorem scaled_oracle {n : ℕ} {C : Oracle n} (f : Vec n → ℝ) (L : ℝ)
    (hL : 0 < L) (hC : OracleCorrect C f) :
    OracleCorrect C (fun x => f x / L) := by
  intro y x
  rw [hC y x, div_le_div_iff_of_pos_right hL]

theorem tau_rescaling (n : ℕ) (delta gamma L : ℝ) :
    tauValue n delta (gamma / L) = tauValue n delta gamma / L := by
  unfold tauValue
  ring

theorem gde_accuracy_L_smooth {n : ℕ} {C : Oracle n}
    (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (L : NNReal) (hL : 0 < L)
    (hLip : LipschitzWith L grad) (horacle : OracleCorrect C f)
    (x : Vec n) (delta gamma : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hgamma : 0 < gamma)
    (hnorm : gamma ≤ ‖grad x‖) :
    ‖Program.eval C (gdeProgram x delta (gamma / L)) - NormedSpace.normalize (grad x)‖ ≤ delta := by
  have hp : 0 < (L : ℝ) := hL
  have hgrad := scaled_hasGradient f grad hg (L : ℝ)
  have hscalednorm : gamma / (L : ℝ) ≤ ‖(L : ℝ)⁻¹ • grad x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.mpr hp))
  have hh := gde_accuracy (fun y => f y / (L : ℝ)) (fun y => (L : ℝ)⁻¹ • grad y)
    hgrad (scaled_lipschitz grad L hL hLip) (scaled_oracle f _ hp horacle)
    x delta (gamma / L) hd hd1 (div_pos hgamma hp) hscalednorm
  rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hp)] at hh
  simpa only [gdeProgram_eval] using hh

end
end PaperGDE

end SnapshotModule_004
/- END gde_rescaling -/

/- BEGIN comparison_simulation -/
section SnapshotModule_005

/- Exact two-value simulation on arbitrary adaptive oracle programs.
   The external lower-bound theorems themselves are not introduced as axioms. -/
namespace PaperOracle

inductive Program (Q R A : Type*) where
  | done : A → Program Q R A
  | ask : Q → (R → Program Q R A) → Program Q R A

namespace Program
variable {Q R A : Type*}

def run (oracle : Q → R) : Program Q R A → A
  | .done a => a
  | .ask q next => run oracle (next (oracle q))

def trace (oracle : Q → R) : Program Q R A → List Q
  | .done _ => []
  | .ask q next => q :: trace oracle (next (oracle q))

def Cap : ℕ → Program Q R A → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | n + 1, .ask _ next => ∀ r, Cap n (next r)

lemma trace_length_le {n : ℕ} (p : Program Q R A) (hcap : Cap n p) (oracle : Q → R) :
    (trace oracle p).length ≤ n := by
  induction n generalizing p with
  | zero => cases p <;> simp_all [Cap, trace]
  | succ n ih =>
    cases p with
    | done _ => simp [trace]
    | ask q next =>
      have hh := ih (next (oracle q)) (hcap (oracle q))
      simpa only [trace, List.length_cons, Nat.add_le_add_iff_right] using hh
end Program

noncomputable section
open Program

noncomputable def realOrder (a b : ℝ) : Ordering :=
  if a < b then .lt else if a = b then .eq else .gt

def comparisonOracle {P : Type*} (f : P → ℝ) (q : P × P) : Ordering := realOrder (f q.1) (f q.2)

noncomputable def simulate {P A : Type*} : Program (P × P) Ordering A → Program P ℝ A
  | .done a => .done a
  | .ask q next => .ask q.1 (fun a => .ask q.2 (fun b => simulate (next (realOrder a b))))

lemma simulate_output {P A : Type*} (f : P → ℝ) (p : Program (P × P) Ordering A) :
    Program.run f (simulate p) = Program.run (comparisonOracle f) p := by
  induction p with
  | done _ => rfl
  | ask q next ih => exact ih (realOrder (f q.1) (f q.2))

def flattenPairs {P : Type*} : List (P × P) → List P
  | [] => []
  | q :: qs => q.1 :: q.2 :: flattenPairs qs

lemma flattenPairs_length {P : Type*} (qs : List (P × P)) :
    (flattenPairs qs).length = 2 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [flattenPairs, ih]; omega

lemma simulate_trace {P A : Type*} (f : P → ℝ) (p : Program (P × P) Ordering A) :
    Program.trace f (simulate p) = flattenPairs (Program.trace (comparisonOracle f) p) := by
  induction p with
  | done _ => rfl
  | ask q next ih =>
    simp only [Program.trace, simulate, comparisonOracle, flattenPairs]
    rw [ih]

lemma simulate_query_count {P A : Type*} (f : P → ℝ) (p : Program (P × P) Ordering A) :
    (Program.trace f (simulate p)).length = 2 * (Program.trace (comparisonOracle f) p).length := by
  rw [simulate_trace, flattenPairs_length]

lemma simulate_cap {P A : Type*} {n : ℕ} (p : Program (P × P) Ordering A)
    (hc : Program.Cap n p) : Program.Cap (2 * n) (simulate p) := by
  induction n generalizing p with
  | zero => cases p <;> simp_all [Program.Cap, simulate]
  | succ n ih =>
    cases p with
    | done _ => trivial
    | ask q next =>
      have hh : ∀ a b : ℝ, Program.Cap (2 * n) (simulate (next (realOrder a b))) :=
        fun a b => ih (next _) (hc _)
      simpa only [simulate, show 2 * (n + 1) = 2*n + 1 + 1 by omega, Program.Cap] using hh

lemma seedwise_simulation {P A Seed : Type*} (f : P → ℝ)
    (alg : Seed → Program (P × P) Ordering A) (seed : Seed) :
    Program.run f (simulate (alg seed)) = Program.run (comparisonOracle f) (alg seed) ∧
    (Program.trace f (simulate (alg seed))).length =
      2 * (Program.trace (comparisonOracle f) (alg seed)).length :=
  ⟨simulate_output f _, simulate_query_count f _⟩

lemma success_event_preserved {P A Seed : Type*} (f : P → ℝ)
    (alg : Seed → Program (P × P) Ordering A) (success : A → Prop) :
    {s : Seed | success (Program.run f (simulate (alg s)))} =
      {s : Seed | success (Program.run (comparisonOracle f) (alg s))} := by
  ext s
  simp only [Set.mem_setOf_eq, simulate_output]

lemma success_probability_preserved {P A Seed : Type*} [MeasurableSpace Seed]
    (mu : MeasureTheory.Measure Seed) (f : P → ℝ)
    (alg : Seed → Program (P × P) Ordering A) (success : A → Prop) :
    mu {s : Seed | success (Program.run f (simulate (alg s)))} =
      mu {s : Seed | success (Program.run (comparisonOracle f) (alg s))} := by
  rw [success_event_preserved]

lemma measurable_output_preserved {P A Seed : Type*} [MeasurableSpace A] [MeasurableSpace Seed]
    (f : P → ℝ) (alg : Seed → Program (P × P) Ordering A)
    (hm : Measurable (fun s => Program.run (comparisonOracle f) (alg s))) :
    Measurable (fun s => Program.run f (simulate (alg s))) := by
  simpa only [simulate_output] using hm

lemma realOrder_eq_lt_iff (a b : ℝ) : realOrder a b = .lt ↔ a < b := by
  classical
  by_cases h : a < b <;> simp [realOrder, h]

lemma realOrder_eq_eq_iff (a b : ℝ) : realOrder a b = .eq ↔ a = b := by
  classical
  by_cases h : a < b
  · have hn : a ≠ b := ne_of_lt h
    simp [realOrder, h, hn]
  · simp [realOrder, h]

lemma realOrder_eq_gt_iff (a b : ℝ) : realOrder a b = .gt ↔ b < a := by
  classical
  by_cases h : a < b
  · have hn : ¬ b < a := not_lt_of_ge h.le
    simp [realOrder, h, hn]
  · by_cases heq : a = b
    · simp [realOrder, h, heq]
    · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm heq)
      simp [realOrder, h, heq, hgt]

lemma realOrder_positive_division (a b s : ℝ) (hs : 0 < s) :
    realOrder (a / s) (b / s) = realOrder a b := by
  classical
  simp only [realOrder, div_lt_div_iff_of_pos_right hs, div_left_inj' (ne_of_gt hs)]

lemma seedwise_public_cap {P A Seed : Type*} (n : ℕ)
    (alg : Seed → Program (P × P) Ordering A) (hc : ∀ s, Program.Cap n (alg s)) :
    ∀ s, Program.Cap (2 * n) (simulate (alg s)) := fun s => simulate_cap _ (hc s)

end
end PaperOracle

end SnapshotModule_005
/- END comparison_simulation -/

/- BEGIN borel_history_policy -/
section SnapshotModule_006

/- Total Borel seed/history policies, with arbitrary query locations, arbitrary
   unqueried outputs, early stopping, and a public cap. History is stored with
   the most recent response first; this is a finite-coordinate permutation of
   chronological history. This file supplies the semantics, not a lower bound. -/
namespace PaperBorelPolicy
noncomputable section
open MeasureTheory PaperOracle

structure Policy (Seed Q R A : Type) [MeasurableSpace Seed] [MeasurableSpace Q]
    [MeasurableSpace R] [MeasurableSpace A] where
  query : (t : ℕ) → Seed × (Fin t → R) → Q
  output : (t : ℕ) → Seed × (Fin t → R) → A
  stop : (t : ℕ) → Seed × (Fin t → R) → Bool
  query_measurable : ∀ t, Measurable (query t)
  output_measurable : ∀ t, Measurable (output t)
  stop_measurable : ∀ t, MeasurableSet {st | stop t st = true}

namespace Policy
variable {Seed Q R A : Type} [MeasurableSpace Seed] [MeasurableSpace Q]
  [MeasurableSpace R] [MeasurableSpace A]

def unroll (P : Policy Seed Q R A) :
    (budget t : ℕ) → Seed × (Fin t → R) → PaperOracle.Program Q R A
  | 0, t, st => .done (P.output t st)
  | budget + 1, t, st =>
      if P.stop t st then .done (P.output t st) else
      .ask (P.query t st) (fun r =>
        unroll P budget (t + 1) (st.1, Fin.cons r st.2))

def runFrom (P : Policy Seed Q R A) (oracle : Seed → Q → R) :
    (budget t : ℕ) → Seed × (Fin t → R) → A
  | 0, t, st => P.output t st
  | budget + 1, t, st =>
      if P.stop t st then P.output t st else
      runFrom P oracle budget (t + 1) (st.1, Fin.cons (oracle st.1 (P.query t st)) st.2)

def queriesFrom (P : Policy Seed Q R A) (oracle : Seed → Q → R) :
    (budget t : ℕ) → Seed × (Fin t → R) → List Q
  | 0, _, _ => []
  | budget + 1, t, st =>
      if P.stop t st then [] else P.query t st ::
      queriesFrom P oracle budget (t + 1) (st.1, Fin.cons (oracle st.1 (P.query t st)) st.2)

theorem unroll_cap (P : Policy Seed Q R A) (budget t : ℕ) (st : Seed × (Fin t → R)) :
    PaperOracle.Program.Cap budget (P.unroll budget t st) := by
  induction budget generalizing t with
  | zero => trivial
  | succ budget ih =>
    cases hs : P.stop t st
    · simp only [unroll, hs, Bool.false_eq_true, ↓reduceIte, PaperOracle.Program.Cap]
      exact fun r => ih (t + 1) (st.1, Fin.cons r st.2)
    · simp [unroll, hs, PaperOracle.Program.Cap]

theorem unroll_run (P : Policy Seed Q R A) (oracle : Seed → Q → R)
    (budget t : ℕ) (st : Seed × (Fin t → R)) :
    PaperOracle.Program.run (oracle st.1) (P.unroll budget t st) =
      P.runFrom oracle budget t st := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    cases hs : P.stop t st
    · simp only [unroll, runFrom, hs, Bool.false_eq_true, ↓reduceIte, PaperOracle.Program.run]
      exact ih (t + 1) (st.1, Fin.cons (oracle st.1 (P.query t st)) st.2)
    · simp [unroll, runFrom, hs, PaperOracle.Program.run]

theorem unroll_trace (P : Policy Seed Q R A) (oracle : Seed → Q → R)
    (budget t : ℕ) (st : Seed × (Fin t → R)) :
    PaperOracle.Program.trace (oracle st.1) (P.unroll budget t st) =
      P.queriesFrom oracle budget t st := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    cases hs : P.stop t st
    · simp only [unroll, queriesFrom, hs, Bool.false_eq_true, ↓reduceIte, PaperOracle.Program.trace]
      congr 1
      exact ih (t + 1) (st.1, Fin.cons (oracle st.1 (P.query t st)) st.2)
    · simp [unroll, queriesFrom, hs, PaperOracle.Program.trace]

theorem queries_length_le (P : Policy Seed Q R A) (oracle : Seed → Q → R)
    (budget t : ℕ) (st : Seed × (Fin t → R)) :
    (P.queriesFrom oracle budget t st).length ≤ budget := by
  rw [← unroll_trace]
  exact PaperOracle.Program.trace_length_le _ (P.unroll_cap budget t st) _

theorem next_state_measurable (P : Policy Seed Q R A) (oracle : Seed → Q → R)
    (hOracle : Measurable (fun x : Seed × Q => oracle x.1 x.2)) (t : ℕ) :
    Measurable (fun st : Seed × (Fin t → R) =>
      (st.1, (Fin.cons (oracle st.1 (P.query t st)) st.2 : Fin (t + 1) → R))) := by
  have hr : Measurable (fun st : Seed × (Fin t → R) => oracle st.1 (P.query t st)) :=
    hOracle.comp (measurable_fst.prodMk (P.query_measurable t))
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hr
  · exact (measurable_pi_apply j).comp measurable_snd

theorem runFrom_measurable (P : Policy Seed Q R A) (oracle : Seed → Q → R)
    (hOracle : Measurable (fun x : Seed × Q => oracle x.1 x.2)) (budget t : ℕ) :
    Measurable (P.runFrom oracle budget t) := by
  induction budget generalizing t with
  | zero => exact P.output_measurable t
  | succ budget ih =>
    have hn := (ih (t + 1)).comp (P.next_state_measurable oracle hOracle t)
    exact Measurable.ite (P.stop_measurable t) (P.output_measurable t) hn

def fromSeed (P : Policy Seed Q R A) (budget : ℕ) (seed : Seed) : PaperOracle.Program Q R A :=
  P.unroll budget 0 (seed, Fin.elim0)

theorem fromSeed_cap (P : Policy Seed Q R A) (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.Cap budget (P.fromSeed budget seed) := P.unroll_cap _ _ _

theorem seed_output_measurable (P : Policy Seed Q R A) (oracle : Seed → Q → R)
    (hOracle : Measurable (fun x : Seed × Q => oracle x.1 x.2)) (budget : ℕ) :
    Measurable (fun seed => PaperOracle.Program.run (oracle seed) (P.fromSeed budget seed)) := by
  have heq : (fun seed => PaperOracle.Program.run (oracle seed) (P.fromSeed budget seed)) =
      (fun seed => P.runFrom oracle budget 0 (seed, Fin.elim0)) := by
    funext seed
    exact P.unroll_run oracle budget 0 (seed, Fin.elim0)
  rw [heq]
  exact (P.runFrom_measurable oracle hOracle budget 0).comp
    (Measurable.prodMk measurable_id measurable_const)

theorem fixed_oracle_output_measurable (P : Policy Seed Q R A) (oracle : Q → R)
    (hOracle : Measurable oracle) (budget : ℕ) :
    Measurable (fun seed => PaperOracle.Program.run oracle (P.fromSeed budget seed)) :=
  P.seed_output_measurable (fun _ => oracle) (hOracle.comp measurable_snd) budget

def withParameter {Theta : Type} [MeasurableSpace Theta]
    (P : Policy Seed Q R A) : Policy (Theta × Seed) Q R A where
  query t st := P.query t (st.1.2, st.2)
  output t st := P.output t (st.1.2, st.2)
  stop t st := P.stop t (st.1.2, st.2)
  query_measurable t := (P.query_measurable t).comp (by fun_prop)
  output_measurable t := (P.output_measurable t).comp (by fun_prop)
  stop_measurable t := (P.stop_measurable t).preimage (by fun_prop)

theorem withParameter_unroll {Theta : Type} [MeasurableSpace Theta]
    (P : Policy Seed Q R A) (budget t : ℕ) (theta : Theta) (seed : Seed) (history : Fin t → R) :
    P.withParameter.unroll budget t ((theta, seed), history) =
      P.unroll budget t (seed, history) := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    cases hs : P.stop t (seed, history)
    · simp [unroll, withParameter, hs]
      funext r
      exact ih (t + 1) (Fin.cons r history)
    · simp [unroll, withParameter, hs]

theorem withParameter_fromSeed {Theta : Type} [MeasurableSpace Theta]
    (P : Policy Seed Q R A) (budget : ℕ) (theta : Theta) (seed : Seed) :
    P.withParameter.fromSeed budget (theta, seed) = P.fromSeed budget seed :=
  P.withParameter_unroll budget 0 theta seed Fin.elim0

theorem joint_output_measurable {Theta : Type} [MeasurableSpace Theta]
    (P : Policy Seed Q R A) (F : Theta → Q → R)
    (hF : Measurable (fun x : Theta × Q => F x.1 x.2)) (budget : ℕ) :
    Measurable (fun st : Theta × Seed =>
      PaperOracle.Program.run (F st.1) (P.fromSeed budget st.2)) := by
  have hOracle : Measurable (fun x : (Theta × Seed) × Q => F x.1.1 x.2) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hh := (P.withParameter (Theta := Theta)).seed_output_measurable
    (fun st => F st.1) hOracle budget
  have hp : ∀ st : Theta × Seed,
      P.withParameter.fromSeed budget st = P.fromSeed budget st.2 := by
    intro st
    rcases st with ⟨theta, seed⟩
    exact P.withParameter_fromSeed budget theta seed
  simpa only [hp] using hh

theorem joint_success_measurable {Theta : Type} [MeasurableSpace Theta]
    (P : Policy Seed Q R A) (F : Theta → Q → R)
    (hF : Measurable (fun x : Theta × Q => F x.1 x.2)) (budget : ℕ)
    (loss : Theta → A → ℝ) (hLoss : Measurable (fun x : Theta × A => loss x.1 x.2))
    (epsilon : ℝ) :
    MeasurableSet {st : Theta × Seed |
      loss st.1 (PaperOracle.Program.run (F st.1) (P.fromSeed budget st.2)) ≤ epsilon} := by
  exact measurableSet_le
    (hLoss.comp (measurable_fst.prodMk (P.joint_output_measurable F hF budget))) measurable_const

end Policy

theorem per_instance_success_to_joint {Theta Seed : Type}
    [MeasurableSpace Theta] [MeasurableSpace Seed]
    (prior : Measure Theta) (seedLaw : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seedLaw]
    (success : Set (Theta × Seed)) (hSuccess : MeasurableSet success)
    (hPointwise : ∀ᵐ theta ∂prior,
      (2 / 3 : ENNReal) ≤ seedLaw {seed | (theta, seed) ∈ success}) :
    (2 / 3 : ENNReal) ≤ prior.prod seedLaw success := by
  rw [Measure.prod_apply hSuccess]
  change (2 / 3 : ENNReal) ≤ ∫⁻ theta, seedLaw {seed | (theta, seed) ∈ success} ∂prior
  have hconst : (∫⁻ _theta, (2 / 3 : ENNReal) ∂prior) = 2 / 3 := by simp
  rw [← hconst]
  exact lintegral_mono_ae hPointwise

end
end PaperBorelPolicy

end SnapshotModule_006
/- END borel_history_policy -/

/- BEGIN program_borel_legality -/
section SnapshotModule_007

namespace PaperProgramBorel
open PaperOracle PaperBorelPolicy MeasureTheory
noncomputable section
variable {Q R A : Type} [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace A]
  [Countable R] [MeasurableSingletonClass R] [Inhabited Q] [Inhabited A]

def consume (p : Program Q R A) (r : R) : Program Q R A :=
  match p with
  | .done a => .done a
  | .ask _ next => next r

def afterReplies (p : Program Q R A) : (t : ℕ) → (Fin t → R) → Program Q R A
  | 0,_ => p
  | t+1,h => consume (afterReplies p t (fun i => h i.succ)) (h 0)

lemma afterReplies_cons (p : Program Q R A) (t : ℕ) (history : Fin t → R) (r : R) :
    afterReplies p (t+1) (Fin.cons r history)=consume (afterReplies p t history) r := by
  simp only [afterReplies,Fin.cons_zero,Fin.cons_succ]

def policy (p : Program Q R A) : Policy Unit Q R A where
  query t st := match afterReplies p t st.2 with
    | .done _ => default
    | .ask q _ => q
  output t st := match afterReplies p t st.2 with
    | .done a => a
    | .ask _ _ => default
  stop t st := match afterReplies p t st.2 with
    | .done _ => true
    | .ask _ _ => false
  query_measurable t := measurable_of_countable _
  output_measurable t := measurable_of_countable _
  stop_measurable t := Set.to_countable _ |>.measurableSet

def truncate : (budget : ℕ) → Program Q R A → Program Q R A
  | 0,.done a => .done a
  | 0,.ask _ _ => .done default
  | k+1,.done a => .done a
  | k+1,.ask q next => .ask q (fun r => truncate k (next r))

lemma truncate_eq (k : ℕ) (p : Program Q R A) (hp : Program.Cap k p) : truncate k p=p := by
  induction k generalizing p with
  | zero => cases p with
    | done a => rfl
    | ask q f => exact False.elim hp
  | succ k ih =>
    cases p with
    | done a => rfl
    | ask q f =>
      simp only [truncate]
      congr 1
      funext r
      exact ih (f r) (hp r)

lemma policy_unroll (p : Program Q R A) (k t : ℕ) (history : Fin t → R) :
    (policy p).unroll k t ((),history)=truncate k (afterReplies p t history) := by
  induction k generalizing t with
  | zero =>
    simp only [Policy.unroll,policy]
    cases afterReplies p t history <;> rfl
  | succ k ih =>
    simp only [Policy.unroll,policy]
    cases he : afterReplies p t history with
    | done a => simp [truncate]
    | ask q next =>
      simp only [Bool.false_eq_true,↓reduceIte,truncate]
      congr 1
      funext r
      change (policy p).unroll k (t+1) ((),Fin.cons r history)=truncate k (next r)
      rw [ih,afterReplies_cons,he]
      rfl

/-- Every finite comparison tree has a total Borel finite-history policy with
identical queries, stopping behavior, and outputs. The policy never reads f. -/
theorem finite_program_borel_realization (p : Program Q R A) (budget : ℕ)
    (hp : Program.Cap budget p) :
    (policy p).fromSeed budget ()=p := by
  rw [Policy.fromSeed,policy_unroll]
  exact truncate_eq budget p hp

lemma deterministic_probability_one {Seed : Type} [MeasurableSpace Seed]
    (mu : Measure Seed) [IsProbabilityMeasure mu] (a : A) (success : A → Prop) (ha : success a) :
    mu {seed : Seed | success a}=1 := by
  simp [ha]

end
end PaperProgramBorel

end SnapshotModule_007
/- END program_borel_legality -/

/- BEGIN uniform_budget_model -/
section SnapshotModule_008

namespace PaperUniformBudget
open Set MeasureTheory PaperOracle PaperBorelPolicy
open scoped ENNReal
noncomputable section

instance responseMeasurableSpace : MeasurableSpace Ordering := ⊤
instance responseMeasurableSingletons : MeasurableSingletonClass Ordering := ⟨fun _ => by trivial⟩

variable {V : Type} [MeasurableSpace V] [Inhabited V]

def DeterministicBudget (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop) (T : ℕ) : Prop :=
  ∃ p : Program (V×V) Ordering V, Program.Cap T p ∧
    ∀ f ∈ objectives, success f (Program.run (comparisonOracle f) p)

def RandomizedBudget (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop) (T : ℕ) : Prop :=
  ∃ Seed : Type, ∃ m : MeasurableSpace Seed, letI := m
    ∃ law : Measure Seed, IsProbabilityMeasure law ∧
      ∃ policy : Policy Seed (V×V) Ordering V,
        ∀ f ∈ objectives,
          MeasurableSet {s | success f (Program.run (comparisonOracle f) (policy.fromSeed T s))} ∧
          (2/3:ℝ≥0∞) ≤ law {s | success f (Program.run (comparisonOracle f) (policy.fromSeed T s))}

/-- Constant private randomness gives a total Borel policy and probability one,
while preserving the public cap of every finite deterministic comparison tree. -/
theorem deterministic_is_randomized (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop)
    (T : ℕ) (hT : DeterministicBudget objectives success T) :
    RandomizedBudget objectives success T := by
  obtain ⟨p,hcap,hsuccess⟩ := hT
  refine ⟨Unit,inferInstance,Measure.dirac (),inferInstance,PaperProgramBorel.policy p,?_⟩
  intro f hf
  have hp := PaperProgramBorel.finite_program_borel_realization p T hcap
  have hgood : ∀ seed : Unit, success f (Program.run (comparisonOracle f)
      ((PaperProgramBorel.policy p).fromSeed T seed)) := by
    intro seed
    cases seed
    rw [hp]
    exact hsuccess f hf
  have hevent : {seed : Unit | success f (Program.run (comparisonOracle f)
      ((PaperProgramBorel.policy p).fromSeed T seed))}=univ := Set.eq_univ_of_forall hgood
  rw [hevent]
  refine ⟨MeasurableSet.univ,?_⟩
  rw [Measure.dirac_apply_of_mem (Set.mem_univ ())]
  exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)

def deterministicComplexity (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop) : ℕ :=
  sInf {T | DeterministicBudget objectives success T}

def randomizedComplexity (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop) : ℕ :=
  sInf {T | RandomizedBudget objectives success T}

theorem deterministic_upper (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop)
    (T : ℕ) (hT : DeterministicBudget objectives success T) :
    deterministicComplexity objectives success ≤ T := Nat.sInf_le hT

theorem randomized_upper (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop)
    (T : ℕ) (hT : RandomizedBudget objectives success T) :
    randomizedComplexity objectives success ≤ T := Nat.sInf_le hT

/-- The nonempty condition is supplied by the actual deterministic upper bound;
this prevents the empty-budget-set convention for Nat.sInf from being misused. -/
theorem randomized_le_deterministic (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop)
    (hexists : ∃ T, DeterministicBudget objectives success T) :
    randomizedComplexity objectives success ≤ deterministicComplexity objectives success := by
  have hmem : DeterministicBudget objectives success (deterministicComplexity objectives success) :=
    Nat.sInf_mem hexists
  exact randomized_upper objectives success _ (deterministic_is_randomized objectives success _ hmem)

theorem select_smaller_public_cap (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop)
    (T U : ℕ) (hT : DeterministicBudget objectives success T) (hU : DeterministicBudget objectives success U) :
    DeterministicBudget objectives success (min T U) := by
  rcases le_total T U with h | h
  · simpa only [min_eq_left h] using hT
  · simpa only [min_eq_right h] using hU

end
end PaperUniformBudget

end SnapshotModule_008
/- END uniform_budget_model -/

/- BEGIN program_public_cap -/
section SnapshotModule_009

namespace PaperGDE.Program
noncomputable section

def height {n : ℕ} {α : Type} : Program n α → ℕ
  | .pure _ => 0
  | .query _ _ next => 1+max (height (next true)) (height (next false))

lemma count_le_height {n : ℕ} {α : Type} (C : Oracle n) (P : Program n α) :
    count C P ≤ height P := by
  induction P with
  | pure a => exact le_rfl
  | query y x next ih =>
    simp only [count,height]
    apply Nat.add_le_add_left
    cases hb : C y x
    · exact (ih false).trans (le_max_right _ _)
    · exact (ih true).trans (le_max_left _ _)

lemma height_bind_le {n : ℕ} {α β : Type} (P : Program n α) (f : α → Program n β)
    (a b : ℕ) (hP : height P ≤ a) (hf : ∀ x, height (f x) ≤ b) :
    height (bind P f) ≤ a+b := by
  have haux : height (bind P f) ≤ height P+b := by
    clear hP a
    induction P with
    | pure x => simpa [bind,height] using hf x
    | query y x next ih =>
      simp only [bind,height]
      have hl := ih true
      have hr := ih false
      omega
  omega

lemma height_collect_le {n m : ℕ} {α : Type} (f : Fin m → Program n α)
    (t : Fin m → ℕ) (hf : ∀ i, height (f i) ≤ t i) :
    height (collect m f) ≤ ∑ i, t i := by
  induction m with
  | zero => simp [collect,height]
  | succ m ih =>
    simp only [collect]
    have htail : ∀ first : α, height (bind (collect m (fun i => f i.succ))
        (fun rest => Program.pure (α := Fin (m+1) → α) (Fin.cons first rest))) ≤ ∑ i : Fin m, t i.succ := by
      intro first
      have h := height_bind_le (collect m (fun i => f i.succ))
        (fun rest => Program.pure (α := Fin (m+1) → α) (Fin.cons first rest))
        (∑ i : Fin m, t i.succ) 0 (ih _ _ (fun i => hf i.succ)) (by intro x; rfl)
      simpa using h
    exact (height_bind_le (f 0) _ (t 0) (∑ i : Fin m, t i.succ) (hf 0) htail).trans_eq
      (Fin.sum_univ_succ t).symm

end
end PaperGDE.Program

namespace PaperGDE
noncomputable section

lemma signsProgram_height {n : ℕ} (x : Vec n) (tau : ℝ) :
    Program.height (signsProgram x tau) ≤ n+1 := by
  have h := Program.height_collect_le
    (fun i : Fin (n+1) => Program.query (probe x tau (basis i)) x
      (fun b => Program.pure (if b then (1:ℝ) else -1)))
    (fun _ => 1) (by intro i; simp [Program.height])
  simpa [signsProgram] using h

lemma tournamentProgram_height {n : ℕ} (x : Vec n) (tau : ℝ)
    (s : Fin (n+1) → ℝ) (l : List (Fin (n+1))) (p : Fin (n+1)) :
    Program.height (tournamentProgram x tau s p l) ≤ l.length := by
  induction l generalizing p with
  | nil => simp [tournamentProgram,Program.height]
  | cons i rest ih =>
    simp only [tournamentProgram,Program.height,List.length_cons]
    have ht := ih p
    have hf := ih i
    simp only [Bool.true_eq, ↓reduceIte, Bool.false_eq_true] at *
    omega

lemma ratioProgram_height {n : ℕ} (x : Vec n) (tau : ℝ)
    (s : Fin (n+1) → ℝ) (j i : Fin (n+1)) (k : ℕ) :
    Program.height (ratioProgram x tau s j i k) ≤ k := by
  induction k with
  | zero => simp [ratioProgram,Program.height]
  | succ k ih =>
    exact Program.height_bind_le _ _ k 1 ih (by intro I; simp [Program.height])

lemma estimatesProgram_height {n : ℕ} (x : Vec n) (tau : ℝ)
    (s : Fin (n+1) → ℝ) (j : Fin (n+1)) (k : ℕ) :
    Program.height (estimatesProgram x tau s j k) ≤ n*k := by
  rw [estimatesProgram]
  apply (Program.height_collect_le _ (fun i => if i=j then 0 else k) ?_).trans_eq
    (sum_except_anchor n k j)
  intro i
  by_cases hi : i=j
  · simp [hi,Program.height]
  · simp only [hi, ↓reduceIte]
    have h := Program.height_bind_le (ratioProgram x tau s j i k)
      (fun I => Program.pure (Task004GDE.midpoint I)) k 0
      (ratioProgram_height x tau s j i k) (by intro I; rfl)
    simpa using h

/-- A fixed cap for every possible reply branch, including inconsistent replies. -/
theorem gdeProgram_public_height {n : ℕ} (x : Vec n) (delta gamma : ℝ) :
    Program.height (gdeProgram x delta gamma) ≤
      2*(n+1)-1+n*rounds n delta := by
  unfold gdeProgram
  apply (Program.height_bind_le _ _ (n+1) (n+n*rounds n delta)
    (signsProgram_height _ _) ?_).trans (by omega)
  intro s
  apply Program.height_bind_le _ _ n (n*rounds n delta)
  · simpa [challengers] using tournamentProgram_height x (tauValue n delta gamma) s (challengers n) 0
  · intro j
    have h := Program.height_bind_le _
      (fun alpha : Fin (n+1) → ℝ => Program.pure
        (NormedSpace.normalize (WithLp.toLp 2 (fun i => alpha i*s i)))) (n*rounds n delta) 0
      (estimatesProgram_height x (tauValue n delta gamma) s j (rounds n delta))
      (by intro a; rfl)
    simpa using h

end
end PaperGDE

end SnapshotModule_009
/- END program_public_cap -/

/- BEGIN line_search_complete -/
section SnapshotModule_010

/- Complete finite comparison-program proof of main.tex:274-279.
   Original smooth-optimization paper is not modified. No external model/API calls. -/

namespace PaperLineSearchComplete

open Set

variable {target : Set ℝ}

theorem left_comparison_retains_min
    {f : ℝ → ℝ} {a b p q : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f)
    (hp : p ∈ Icc a b) (_hq : q ∈ Icc a b) (hpq : p < q)
    (hcmp : f p ≤ f q)
    (hm : ∃ m ∈ Icc a b, ∀ x ∈ target, f m ≤ f x) :
    ∃ m ∈ Icc a q, ∀ x ∈ target, f m ≤ f x := by
  obtain ⟨m, hm, hmin⟩ := hm
  by_cases hmq : m ≤ q
  · exact ⟨m, ⟨hm.1, hmq⟩, hmin⟩
  · have hqm : q ≤ m := le_of_lt (lt_of_not_ge hmq)
    have hqmval : f q ≤ f m := hf.le_right_of_left_le'' hp hm hpq hqm hcmp
    refine ⟨p, ⟨hp.1, hpq.le⟩, ?_⟩
    intro x hx
    exact (hcmp.trans hqmval).trans (hmin x hx)

theorem right_comparison_retains_min
    {f : ℝ → ℝ} {a b p q : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f)
    (_hp : p ∈ Icc a b) (hq : q ∈ Icc a b) (hpq : p < q)
    (hcmp : f q ≤ f p)
    (hm : ∃ m ∈ Icc a b, ∀ x ∈ target, f m ≤ f x) :
    ∃ m ∈ Icc p b, ∀ x ∈ target, f m ≤ f x := by
  obtain ⟨m, hm, hmin⟩ := hm
  by_cases hpm : p ≤ m
  · exact ⟨m, ⟨hpm, hm.2⟩, hmin⟩
  · have hmp : m ≤ p := le_of_lt (lt_of_not_ge hpm)
    have hpmval : f p ≤ f m := hf.le_left_of_right_le'' hm hq hmp hpq hcmp
    refine ⟨q, ⟨hpq.le, hq.2⟩, ?_⟩
    intro x hx
    exact (hcmp.trans hpmval).trans (hmin x hx)

/-- The equality branch is justified by convexity, without assuming the endpoints are minimizers. -/
theorem tie_retains_middle_min
    {f : ℝ → ℝ} {a b p q : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f)
    (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) (hpq : p < q)
    (hcmp : f p = f q)
    (hm : ∃ m ∈ Icc a b, ∀ x ∈ target, f m ≤ f x) :
    ∃ m ∈ Icc p q, ∀ x ∈ target, f m ≤ f x := by
  obtain ⟨m, hm, hmin⟩ := hm
  by_cases hpm : p ≤ m
  · by_cases hmq : m ≤ q
    · exact ⟨m, ⟨hpm, hmq⟩, hmin⟩
    · have hqm : q ≤ m := le_of_lt (lt_of_not_ge hmq)
      have hqmval : f q ≤ f m := hf.le_right_of_left_le'' hp hm hpq hqm hcmp.le
      refine ⟨q, ⟨hpq.le, le_rfl⟩, ?_⟩
      intro x hx
      exact hqmval.trans (hmin x hx)
  · have hmp : m ≤ p := le_of_lt (lt_of_not_ge hpm)
    have hpmval : f p ≤ f m := hf.le_left_of_right_le'' hm hq hmp hpq hcmp.ge
    refine ⟨p, ⟨le_rfl, hpq.le⟩, ?_⟩
    intro x hx
    exact hpmval.trans (hmin x hx)

theorem trisection_geometry {a b : ℝ} (hab : a < b) :
    let p := a + (b-a)/3
    let q := a + 2*(b-a)/3
    p ∈ Icc a b ∧ q ∈ Icc a b ∧ p < q ∧
      q-a = (2/3 : ℝ)*(b-a) ∧ b-p = (2/3 : ℝ)*(b-a) ∧
      q-p = (1/3 : ℝ)*(b-a) := by
  dsimp
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor
  · ring
  constructor <;> ring

/-- The branch computation consumes a trinary reply, not objective values. -/
noncomputable def trisectionReplyStep (reply : Ordering) (a b : ℝ) : ℝ × ℝ :=
  let p := a + (b-a)/3
  let q := a + 2*(b-a)/3
  match reply with
  | .lt => (a,q)
  | .gt => (p,b)
  | .eq => (p,q)

theorem one_reply_step_preserves_min
    {f : ℝ → ℝ} {a b : ℝ} (reply : Ordering)
    (hab : a < b) (hf : ConvexOn ℝ (Icc a b) f)
    (hreply : match reply with
      | .lt => f (a+(b-a)/3) < f (a+2*(b-a)/3)
      | .gt => f (a+2*(b-a)/3) < f (a+(b-a)/3)
      | .eq => f (a+(b-a)/3) = f (a+2*(b-a)/3))
    (hm : ∃ m ∈ Icc a b, ∀ x ∈ target, f m ≤ f x) :
    let next := trisectionReplyStep reply a b
    a ≤ next.1 ∧ next.1 < next.2 ∧ next.2 ≤ b ∧
      next.2-next.1 ≤ (2/3 : ℝ)*(b-a) ∧
      ∃ m ∈ Icc next.1 next.2, ∀ x ∈ target, f m ≤ f x := by
  have hg := trisection_geometry hab
  dsimp at hg
  obtain ⟨hp,hq,hpq,hwidthL,hwidthR,hwidthM⟩ := hg
  cases reply with
  | lt =>
    dsimp [trisectionReplyStep] at hreply ⊢
    refine ⟨le_rfl, ?_, hq.2, hwidthL.le, ?_⟩
    · linarith [hp.1]
    · exact left_comparison_retains_min hf hp hq hpq hreply.le hm
  | gt =>
    dsimp [trisectionReplyStep] at hreply ⊢
    refine ⟨hp.1, ?_, le_rfl, hwidthR.le, ?_⟩
    · linarith [hq.2]
    · exact right_comparison_retains_min hf hp hq hpq hreply.le hm
  | eq =>
    dsimp [trisectionReplyStep] at hreply ⊢
    refine ⟨hp.1, hpq, hq.2, ?_, ?_⟩
    · linarith
    · exact tie_retains_middle_min hf hp hq hpq hreply hm

theorem minimum_exists_of_lipschitz
    {f : ℝ → ℝ} {a b : ℝ} {C : NNReal} (hab : a ≤ b)
    (hLip : LipschitzOnWith C f (Icc a b)) :
    ∃ m ∈ Icc a b, ∀ x ∈ Icc a b, f m ≤ f x := by
  exact isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hLip.continuousOn

theorem endpoint_error_of_lipschitz
    {f : ℝ → ℝ} {a b x m xi : ℝ} {C : NNReal}
    (hLip : LipschitzOnWith C f (Icc a b))
    (hx : x ∈ Icc a b) (hm : m ∈ Icc a b)
    (hbudget : (C : ℝ)*(b-a) ≤ xi) :
    f x-f m ≤ xi := by
  have hd := hLip.dist_le_mul x hx m hm
  simp only [Real.dist_eq] at hd
  have hdist : |x-m| ≤ b-a := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hm.1,hm.2]
  calc
    f x-f m ≤ |f x-f m| := le_abs_self _
    _ ≤ (C : ℝ)*|x-m| := hd
    _ ≤ (C : ℝ)*(b-a) := mul_le_mul_of_nonneg_left hdist C.coe_nonneg
    _ ≤ xi := hbudget

/-- The geometric shrinkage consequence for a finite-width recurrence. -/
theorem width_decay {w : ℕ → ℝ}
    (hstep : ∀ k, w (k+1) ≤ (2/3 : ℝ)*w k) :
    ∀ n, w n ≤ (2/3 : ℝ)^n*w 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      w (n+1) ≤ (2/3 : ℝ)*w n := hstep n
      _ ≤ (2/3 : ℝ)*((2/3 : ℝ)^n*w 0) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2/3 : ℝ)^(n+1)*w 0 := by ring


/-- A finite comparison-only program. Objective-dependent information enters only
through the one trinary reply at a query node. -/
inductive QueryProgram (α : Type)
  | done (value : α)
  | query (x y : ℝ) (next : Ordering → QueryProgram α)

abbrev Oracle := ℝ → ℝ → Ordering

def CorrectOracle (f : ℝ → ℝ) (oracle : Oracle) : Prop :=
  ∀ x y, match oracle x y with
    | .lt => f x < f y
    | .eq => f x = f y
    | .gt => f y < f x

/-- The evaluator records one pair per query node; the length is the query counter. -/
def evaluate {α : Type} (oracle : Oracle) : QueryProgram α → α × List (ℝ × ℝ)
  | .done value => (value, [])
  | .query x y next =>
    let result := evaluate oracle (next (oracle x y))
    (result.1, (x,y)::result.2)

noncomputable def searchProgram : ℕ → ℝ → ℝ → QueryProgram (ℝ × ℝ)
  | 0, a, b => .done (a,b)
  | n+1, a, b =>
    let p := a+(b-a)/3
    let q := a+2*(b-a)/3
    .query p q fun reply =>
      let next := trisectionReplyStep reply a b
      searchProgram n next.1 next.2

theorem search_query_count (oracle : Oracle) (n : ℕ) (a b : ℝ) :
    (evaluate oracle (searchProgram n a b)).2.length = n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [searchProgram, evaluate, ih]

theorem search_value_invariants {f : ℝ → ℝ} (oracle : Oracle)
    (hcorrect : CorrectOracle f oracle) (n : ℕ) {a b : ℝ}
    (hab : a < b) (hf : ConvexOn ℝ (Icc a b) f)
    (hm : ∃ m ∈ Icc a b, ∀ x ∈ target, f m ≤ f x) :
    let out := (evaluate oracle (searchProgram n a b)).1
    a ≤ out.1 ∧ out.1 < out.2 ∧ out.2 ≤ b ∧
      out.2-out.1 ≤ (2/3 : ℝ)^n*(b-a) ∧
      ∃ m ∈ Icc out.1 out.2, ∀ x ∈ target, f m ≤ f x := by
  induction n generalizing a b with
  | zero =>
    simp only [searchProgram, evaluate, pow_zero, one_mul]
    exact ⟨le_rfl, hab, le_rfl, le_rfl, hm⟩
  | succ n ih =>
    let p := a+(b-a)/3
    let q := a+2*(b-a)/3
    let reply := oracle p q
    let next := trisectionReplyStep reply a b
    have hc : match reply with
        | .lt => f p < f q
        | .gt => f q < f p
        | .eq => f p = f q := by
      have h := hcorrect p q
      cases hr : oracle p q <;> simpa [reply, hr] using h
    have hs := one_reply_step_preserves_min reply hab hf hc hm
    change a ≤ next.1 ∧ next.1 < next.2 ∧ next.2 ≤ b ∧
      next.2-next.1 ≤ (2/3 : ℝ)*(b-a) ∧
      ∃ m ∈ Icc next.1 next.2, ∀ x ∈ target, f m ≤ f x at hs
    obtain ⟨hal, hlt, hhb, hwidth, hmin⟩ := hs
    have hsub : Icc next.1 next.2 ⊆ Icc a b := by
      intro x hx
      exact ⟨hal.trans hx.1, hx.2.trans hhb⟩
    have hconv : ConvexOn ℝ (Icc next.1 next.2) f :=
      hf.subset hsub (convex_Icc _ _)
    have hr := ih hlt hconv hmin
    let out := (evaluate oracle (searchProgram n next.1 next.2)).1
    change next.1 ≤ out.1 ∧ out.1 < out.2 ∧ out.2 ≤ next.2 ∧
      out.2-out.1 ≤ (2/3 : ℝ)^n*(next.2-next.1) ∧
      ∃ m ∈ Icc out.1 out.2, ∀ x ∈ target, f m ≤ f x at hr
    obtain ⟨hlo, hstrict, hhi, hdec, hfinalmin⟩ := hr
    change a ≤ out.1 ∧ out.1 < out.2 ∧ out.2 ≤ b ∧
      out.2-out.1 ≤ (2/3 : ℝ)^(n+1)*(b-a) ∧
      ∃ m ∈ Icc out.1 out.2, ∀ x ∈ target, f m ≤ f x
    refine ⟨hal.trans hlo, hstrict, hhi.trans hhb, ?_, hfinalmin⟩
    calc
      out.2-out.1 ≤ (2/3 : ℝ)^n*(next.2-next.1) := hdec
      _ ≤ (2/3 : ℝ)^n*((2/3 : ℝ)*(b-a)) :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = (2/3 : ℝ)^(n+1)*(b-a) := by ring



noncomputable def horizon (D xi : ℝ) : ℕ :=
  Nat.ceil (Real.log (D/xi) / Real.log (3/2 : ℝ))

theorem horizon_precision {D xi : ℝ} (hxi : 0 < xi) (hD : xi ≤ D) :
    D*(2/3 : ℝ)^(horizon D xi) ≤ xi := by
  have hDpos : 0 < D := hxi.trans_le hD
  have hratio : 0 < D/xi := div_pos hDpos hxi
  have hceil : Real.logb (3/2 : ℝ) (D/xi) ≤ (horizon D xi : ℝ) :=
    Nat.le_ceil _
  have hpow : D/xi ≤ (3/2 : ℝ)^(horizon D xi) := by
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 3/2) hratio).mp hceil
    simpa only [Real.rpow_natCast] using h
  have hmul : D ≤ (3/2 : ℝ)^(horizon D xi)*xi :=
    (div_le_iff₀ hxi).mp hpow
  have hcancel : (3/2 : ℝ)^(horizon D xi)*(2/3 : ℝ)^(horizon D xi) = 1 := by
    rw [← mul_pow]
    norm_num
  have h := mul_le_mul_of_nonneg_right hmul
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2/3) (horizon D xi))
  calc
    D*(2/3 : ℝ)^(horizon D xi) ≤
      ((3/2 : ℝ)^(horizon D xi)*xi)*(2/3 : ℝ)^(horizon D xi) := h
    _ = xi := by nlinarith [hcancel]



theorem search_trace_feasible (oracle : Oracle) (n : ℕ) {a b : ℝ}
    (hab : a < b) :
    ∀ pair ∈ (evaluate oracle (searchProgram n a b)).2,
      pair.1 ∈ Icc a b ∧ pair.2 ∈ Icc a b := by
  induction n generalizing a b with
  | zero => simp [searchProgram, evaluate]
  | succ n ih =>
    have hg := trisection_geometry hab
    dsimp at hg
    obtain ⟨hp,hq,hpq,hwidthL,hwidthR,hwidthM⟩ := hg
    let p := a+(b-a)/3
    let q := a+2*(b-a)/3
    let reply := oracle p q
    let next := trisectionReplyStep reply a b
    have hs : a ≤ next.1 ∧ next.1 < next.2 ∧ next.2 ≤ b := by
      dsimp [next]
      cases reply <;> dsimp [trisectionReplyStep] <;>
        (constructor <;> try constructor) <;> linarith [hp.1,hp.2,hq.1,hq.2]
    change ∀ pair ∈ (p,q)::(evaluate oracle (searchProgram n next.1 next.2)).2,
      pair.1 ∈ Icc a b ∧ pair.2 ∈ Icc a b
    intro pair hmem
    rcases List.mem_cons.mp hmem with heq | hrest
    · subst pair
      exact ⟨hp,hq⟩
    · have ht := ih hs.2.1 pair hrest
      exact ⟨⟨hs.1.trans ht.1.1, ht.1.2.trans hs.2.2⟩,
        ⟨hs.1.trans ht.2.1, ht.2.2.trans hs.2.2⟩⟩

def QueryProgram.map {α β : Type} (g : α → β) : QueryProgram α → QueryProgram β
  | .done value => .done (g value)
  | .query x y next => .query x y fun reply => (next reply).map g

theorem evaluate_map {α β : Type} (oracle : Oracle) (g : α → β)
    (program : QueryProgram α) :
    evaluate oracle (program.map g) =
      (g (evaluate oracle program).1, (evaluate oracle program).2) := by
  induction program with
  | done value => rfl
  | query x y next ih => simp [QueryProgram.map, evaluate, ih]

/-- A public-horizon point-returning program using only trinary comparisons. -/
noncomputable def boundedLineSearch (D xi : ℝ) : QueryProgram ℝ :=
  (searchProgram (horizon D xi) 0 1).map Prod.fst

/-- End-to-end form of main.tex Lemma 274-279. The program is fixed from the
public D and xi; no loop invariant or budget is assumed. It uses exactly the
stated cap, returns a feasible xi-optimal point, and queries only finite points
of the unit interval. -/
theorem tie_safe_bounded_line_search
    {f : ℝ → ℝ} (oracle : Oracle) (hcorrect : CorrectOracle f oracle)
    (D : NNReal) {xi : ℝ} (hxi : 0 < xi) (hD : xi ≤ (D : ℝ))
    (hf : ConvexOn ℝ (Icc (0 : ℝ) 1) f)
    (hLip : LipschitzOnWith D f (Icc (0 : ℝ) 1)) :
    let result := evaluate oracle (boundedLineSearch D xi)
    result.2.length = Nat.ceil (Real.log ((D : ℝ)/xi) / Real.log (3/2 : ℝ)) ∧
      result.1 ∈ Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f result.1-f x ≤ xi) ∧
      ∀ pair ∈ result.2, pair.1 ∈ Icc (0 : ℝ) 1 ∧ pair.2 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨m0,hm0,hmin0⟩ := minimum_exists_of_lipschitz (by norm_num : (0 : ℝ) ≤ 1) hLip
  let n := horizon D xi
  let out := (evaluate oracle (searchProgram n 0 1)).1
  have hs := search_value_invariants oracle hcorrect n (by norm_num : (0 : ℝ) < 1)
    hf ⟨m0,hm0,hmin0⟩
  change 0 ≤ out.1 ∧ out.1 < out.2 ∧ out.2 ≤ 1 ∧
    out.2-out.1 ≤ (2/3 : ℝ)^n*(1-0) ∧
    ∃ m ∈ Icc out.1 out.2, ∀ x ∈ Icc (0 : ℝ) 1, f m ≤ f x at hs
  obtain ⟨hlo,hstrict,hhi,hwidth,m,hm,hmin⟩ := hs
  have hout : out.1 ∈ Icc (0 : ℝ) 1 := ⟨hlo, hstrict.le.trans hhi⟩
  have hmUnit : m ∈ Icc (0 : ℝ) 1 := ⟨hlo.trans hm.1, hm.2.trans hhi⟩
  have hsmall : (D : ℝ)*(out.2-out.1) ≤ xi := by
    calc
      (D : ℝ)*(out.2-out.1) ≤ (D : ℝ)*((2/3 : ℝ)^n*(1-0)) :=
        mul_le_mul_of_nonneg_left hwidth D.coe_nonneg
      _ ≤ xi := by simpa [n] using horizon_precision hxi hD
  have hLipSub : LipschitzOnWith D f (Icc out.1 out.2) :=
    hLip.mono (by intro x hx; exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩)
  have herror : f out.1-f m ≤ xi :=
    endpoint_error_of_lipschitz hLipSub ⟨le_rfl,hstrict.le⟩ hm hsmall
  simp only [boundedLineSearch, evaluate_map]
  refine ⟨search_query_count oracle n 0 1, hout, ?_, ?_⟩
  · intro x hx
    have hmx := hmin x hx
    change f out.1-f x ≤ xi
    linarith
  · exact search_trace_feasible oracle n (by norm_num : (0 : ℝ) < 1)


/-- Existential formulation with exactly the manuscript quantifier order:
the same public program works for every objective satisfying convexity and the
known Lipschitz bound, using its exact comparison oracle. -/
theorem exists_tie_safe_bounded_line_search
    (D : NNReal) {xi : ℝ} (hxi : 0 < xi) (hD : xi ≤ (D : ℝ)) :
    ∃ program : QueryProgram ℝ, ∀ (f : ℝ → ℝ) (oracle : Oracle),
      CorrectOracle f oracle → ConvexOn ℝ (Icc (0 : ℝ) 1) f →
      LipschitzOnWith D f (Icc (0 : ℝ) 1) →
      let result := evaluate oracle program
      result.2.length ≤ Nat.ceil (Real.log ((D : ℝ)/xi) / Real.log (3/2 : ℝ)) ∧
        result.1 ∈ Icc (0 : ℝ) 1 ∧
        (∀ x ∈ Icc (0 : ℝ) 1, f result.1-f x ≤ xi) ∧
        ∀ pair ∈ result.2, pair.1 ∈ Icc (0 : ℝ) 1 ∧ pair.2 ∈ Icc (0 : ℝ) 1 := by
  refine ⟨boundedLineSearch D xi, ?_⟩
  intro f oracle hcorrect hf hLip
  obtain ⟨hcount,hrest⟩ := tie_safe_bounded_line_search oracle hcorrect D hxi hD hf hLip
  exact ⟨hcount.le,hrest⟩


end PaperLineSearchComplete

end SnapshotModule_010
/- END line_search_complete -/

/- BEGIN trinary_program -/
section SnapshotModule_011

namespace PaperOracle.Program
variable {Q R A B : Type*}

def bind (p : Program Q R A) (next : A → Program Q R B) : Program Q R B :=
  match p with
  | .done a => next a
  | .ask q cont => .ask q (fun r => bind (cont r) next)

lemma run_bind (C : Q → R) (p : Program Q R A) (next : A → Program Q R B) :
    run C (bind p next) = run C (next (run C p)) := by
  induction p with
  | done a => rfl
  | ask q cont ih => exact ih (C q)

lemma cap_mono {a b : ℕ} (p : Program Q R A) (ha : Cap a p) (hab : a ≤ b) : Cap b p := by
  induction b generalizing a p with
  | zero =>
    have ha0 : a=0 := by omega
    simpa only [ha0] using ha
  | succ b ih =>
    cases p with
    | done a => trivial
    | ask q next =>
      cases a with
      | zero => exact False.elim ha
      | succ a => exact fun r => ih (next r) (ha r) (by omega)

lemma cap_bind {a b : ℕ} (p : Program Q R A) (next : A → Program Q R B)
    (hp : Cap a p) (hn : ∀ x, Cap b (next x)) : Cap (a+b) (bind p next) := by
  induction a generalizing p with
  | zero =>
    cases p with
    | done x => simpa only [bind,Nat.zero_add] using hn x
    | ask q f => exact False.elim hp
  | succ a ih =>
    cases p with
    | done x => exact cap_mono (next x) (hn x) (by omega)
    | ask q f =>
      have hh : ∀ r, Cap (a+b) (bind (f r) next) := fun r => ih (f r) (hp r)
      simpa only [bind,show a+1+b=(a+b)+1 by omega,Cap] using hh

end PaperOracle.Program

namespace PaperTrinary
open PaperGDE
noncomputable section
abbrev Program (n : ℕ) (A : Type) := PaperOracle.Program (Vec n × Vec n) Ordering A
abbrev Oracle (n : ℕ) := (Vec n × Vec n) → Ordering

def liftGDE {n : ℕ} {A : Type} : PaperGDE.Program n A → Program n A
  | .pure a => .done a
  | .query y x next => .ask (y,x) (fun reply => liftGDE (next (decide (reply ≠ .lt))))

lemma liftGDE_run {n : ℕ} {A : Type} (C : Oracle n) (P : PaperGDE.Program n A) :
    PaperOracle.Program.run C (liftGDE P) =
      PaperGDE.Program.eval (PaperGDE.oracleOfOrdering (fun y x => C (y,x))) P := by
  induction P with
  | pure a => rfl
  | query y x next ih => exact ih (decide (C (y,x) ≠ .lt))

lemma liftGDE_cap {n : ℕ} {A : Type} (P : PaperGDE.Program n A) :
    PaperOracle.Program.Cap (PaperGDE.Program.height P) (liftGDE P) := by
  induction P with
  | pure a => trivial
  | query y x next ih =>
    simp only [PaperGDE.Program.height,show ∀ a : ℕ, 1+a=a+1 from Nat.add_comm 1,
      liftGDE,PaperOracle.Program.Cap]
    intro reply
    apply PaperOracle.Program.cap_mono _ (ih (decide (reply ≠ .lt)))
    cases hb : decide (reply ≠ Ordering.lt)
    · exact le_max_right _ _
    · exact le_max_left _ _

lemma gde_cap {n : ℕ} (x : Vec n) (delta gamma : ℝ) :
    PaperOracle.Program.Cap (2*(n+1)-1+n*rounds n delta)
      (liftGDE (gdeProgram x delta gamma)) :=
  PaperOracle.Program.cap_mono _ (liftGDE_cap _) (gdeProgram_public_height _ _ _)

lemma comparison_correct {n : ℕ} (f : Vec n → ℝ) :
    PaperGDE.OracleCorrect
      (PaperGDE.oracleOfOrdering (fun y x => PaperOracle.comparisonOracle f (y,x))) f := by
  apply PaperGDE.oracleOfOrdering_correct
  intro y x
  exact PaperOracle.realOrder_eq_lt_iff (f y) (f x)

open PaperLineSearchComplete

def liftLine {n : ℕ} {A : Type} (embed : ℝ → Vec n) : QueryProgram A → Program n A
  | .done a => .done a
  | .query x y next => .ask (embed x,embed y) (fun reply => liftLine embed (next reply))

lemma liftLine_run {n : ℕ} {A : Type} (embed : ℝ → Vec n) (C : Oracle n) (P : QueryProgram A) :
    PaperOracle.Program.run C (liftLine embed P) =
      (evaluate (fun x y => C (embed x,embed y)) P).1 := by
  induction P with
  | done a => rfl
  | query x y next ih => exact ih (C (embed x,embed y))

lemma line_search_cap {n : ℕ} (embed : ℝ → Vec n) (k : ℕ) (a b : ℝ)
    {A : Type} (output : ℝ × ℝ → A) :
    PaperOracle.Program.Cap k (liftLine embed ((searchProgram k a b).map output)) := by
  induction k generalizing a b with
  | zero => trivial
  | succ k ih =>
    simp only [searchProgram,QueryProgram.map,liftLine,PaperOracle.Program.Cap]
    intro r
    exact ih _ _

lemma bounded_line_cap {n : ℕ} (embed : ℝ → Vec n) (D xi : ℝ) :
    PaperOracle.Program.Cap (horizon D xi) (liftLine embed (boundedLineSearch D xi)) :=
  line_search_cap embed _ _ _ Prod.fst

lemma realOrder_correct (f : ℝ → ℝ) : CorrectOracle f (fun x y => PaperOracle.realOrder (f x) (f y)) := by
  intro x y
  dsimp only
  cases hh : PaperOracle.realOrder (f x) (f y) with
  | lt => exact (PaperOracle.realOrder_eq_lt_iff _ _).mp hh
  | eq => exact (PaperOracle.realOrder_eq_eq_iff _ _).mp hh
  | gt => exact (PaperOracle.realOrder_eq_gt_iff _ _).mp hh

end
end PaperTrinary

end SnapshotModule_011
/- END trinary_program -/

/- BEGIN centroid_geometry -/
section SnapshotModule_012

namespace PaperCentroid
open Set
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma gradient_norm_bound (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar x : V) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (B : ℝ) (hx : ‖x‖ ≤ B) : ‖grad x‖ ≤ B+1 := by
  have hz := PaperSmooth.gradient_at_global_min f grad hg xstar hmin
  have hh := hLip.norm_sub_le x xstar
  rw [hz, sub_zero, NNReal.coe_one, one_mul] at hh
  exact hh.trans ((norm_sub_le x xstar).trans (add_le_add hx hstar))

lemma small_target_numeric (B tolerance distance : ℝ)
    (hB : 1 ≤ B) (htol : 0 < tolerance) (htol1 : tolerance ≤ 1)
    (hs : 0 ≤ distance)
    (hbound : distance ≤ (2*B+1)*tolerance/(8*(B+1)^2)) :
    (B+1)*distance + distance^2/2 ≤ tolerance/2 := by
  have hD : 0 < B+1 := by linarith
  have hmult := (le_div_iff₀ (by positivity : 0 < 8*(B+1)^2)).mp hbound
  have hcancel : (2*(B+1))*(4*(B+1)*distance) ≤ (2*(B+1))*tolerance := by
    nlinarith
  have hsmall : 4*(B+1)*distance ≤ tolerance := by
    by_contra hn
    have hp := mul_pos (show 0 < 2*(B+1) by positivity) (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  have hs1 : distance ≤ tolerance/4 := by
    have haux := mul_le_mul_of_nonneg_right (show 1 ≤ B+1 by linarith) hs
    nlinarith
  have hsq : distance^2 ≤ distance := by nlinarith
  nlinarith

lemma centroid_target_ball (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : V) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∀ y ∈ Metric.closedBall xstar (Real.sqrt eta), ‖y‖ ≤ 2 ∧ f y-f xstar ≤ eta/2 := by
  intro y hy
  have hdist : ‖y-xstar‖ ≤ Real.sqrt eta := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  have hs := Real.sq_sqrt heta.le
  have hs0 := Real.sqrt_nonneg eta
  have hs1 : Real.sqrt eta ≤ 1 := by nlinarith
  constructor
  · have hn : ‖y‖ ≤ ‖y-xstar‖+‖xstar‖ := by simpa using norm_add_le (y-xstar) xstar
    linarith
  · have hh := PaperSmooth.gap_at_min f grad hg 1 hLip xstar y hmin
    norm_num at hh
    have hdn := norm_nonneg (y-xstar)
    nlinarith

lemma bad_center_gradient_premise (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (x m : V) (B tolerance : ℝ) (hB : 0 < B)
    (hbad : f m+tolerance < f x) (hdiam : ‖m-x‖ ≤ 2*B) :
    tolerance/(2*B) < ‖grad x‖ := by
  have hf := PaperSmooth.convex_first_order f grad hg hc x m
  have hi := real_inner_le_norm (-(grad x)) (m-x)
  rw [inner_neg_left,norm_neg] at hi
  have hm := mul_le_mul_of_nonneg_left hdiam (norm_nonneg (grad x))
  apply (div_lt_iff₀ (by positivity : 0 < 2*B)).mpr
  nlinarith

lemma ballopt_cut_retains_target (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (x y m direction : V) (B D tolerance : ℝ)
    (hB : 0 < B) (hD : 0 < D) (htol : 0 < tolerance)
    (hbad : f m+tolerance < f x) (htarget : f y ≤ f m+tolerance/2)
    (hdiam : ‖y-x‖ ≤ 2*B) (hG : 0 < ‖grad x‖) (hGupper : ‖grad x‖ ≤ D)
    (hdir : ‖direction-NormedSpace.normalize (grad x)‖ ≤ tolerance/(8*B*D)) :
    inner ℝ direction (y-x) < -tolerance/(4*D) := by
  have hf := PaperSmooth.convex_first_order f grad hg hc x y
  have hdot : inner ℝ (grad x) (y-x) < -tolerance/2 := by linarith
  have hnormal : inner ℝ (NormedSpace.normalize (grad x)) (y-x) =
      inner ℝ (grad x) (y-x)/‖grad x‖ := by
    simp only [NormedSpace.normalize,real_inner_smul_left,div_eq_mul_inv]
    ring
  have hnormalized : inner ℝ (NormedSpace.normalize (grad x)) (y-x) <
      -tolerance/(2*‖grad x‖) := by
    rw [hnormal]
    have hh := (div_lt_div_iff_of_pos_right hG).mpr hdot
    convert hh using 1 <;> (first | rfl | ring)
  have hdenom : tolerance/(2*D) ≤ tolerance/(2*‖grad x‖) :=
    div_le_div_of_nonneg_left htol.le (by positivity) (by linarith)
  have herror := real_inner_le_norm (direction-NormedSpace.normalize (grad x)) (y-x)
  have hmul := mul_le_mul hdir hdiam (norm_nonneg _) (by positivity : 0 ≤ tolerance/(8*B*D))
  have htolEq : tolerance/(8*B*D)*(2*B) = tolerance/(4*D) := by
    field_simp
    <;> ring
  rw [inner_sub_left] at herror
  rw [htolEq] at hmul
  have hnormD := hnormalized.trans_le (by simpa only [neg_div] using neg_le_neg hdenom)
  have hfrac : tolerance/(2*D) = 2*(tolerance/(4*D)) := by ring
  simp only [neg_div] at hnormD ⊢
  rw [hfrac] at hnormD
  linarith

variable [FiniteDimensional ℝ V]

def affineBall (A : AffineSubspace ℝ V) (B : ℝ) : Set V :=
  {y | y ∈ A ∧ ‖y‖ ≤ B}

lemma affineBall_compact (A : AffineSubspace ℝ V) (B : ℝ) : IsCompact (affineBall A B) := by
  have hh := (isCompact_closedBall (0:V) B).inter_left A.closed_of_finiteDimensional
  convert hh using 1
  ext y
  simp only [affineBall, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
  rfl

lemma affineBall_minimizer (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (A : AffineSubspace ℝ V) (B : ℝ)
    (p : V) (hp : p ∈ A) (hn : ‖p‖ ≤ B) :
    ∃ m ∈ affineBall A B, ∀ y ∈ affineBall A B, f m ≤ f y := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  exact (affineBall_compact A B).exists_isMinOn ⟨p,hp,hn⟩ hcont.continuousOn

lemma affine_origin_projection (A : AffineSubspace ℝ V) (p : V) (hp : p ∈ A) :
    ∃ c ∈ A, ‖c‖ ≤ ‖p‖ := by
  letI : Nonempty A := ⟨⟨p,hp⟩⟩
  let c : V := EuclideanGeometry.orthogonalProjection A (0:V)
  refine ⟨c,(EuclideanGeometry.orthogonalProjection A (0:V)).property,?_⟩
  have hh : dist (0:V) c ≤ dist (0:V) p := by
    rw [show dist (0:V) c = Metric.infDist (0:V) A from
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist A 0]
    exact Metric.infDist_le_dist_of_mem hp
  simpa using hh

/-- The actual interior target construction for a possibly boundary minimizer.
The relative ball is taken inside the original affine subspace. -/
theorem affine_target_ball (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : V) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (A : AffineSubspace ℝ V) (p : V) (hp : p ∈ A) (B tolerance : ℝ)
    (hpB : ‖p‖ ≤ B-1) (htol : 0 < tolerance) (htol1 : tolerance ≤ 1) :
    ∃ m ∈ affineBall A B, (∀ y ∈ affineBall A B, f m ≤ f y) ∧
      ∃ mprime ∈ A, ‖mprime‖ ≤ B-tolerance/(8*(B+1)^2) ∧
        ∀ y ∈ A, ‖y-mprime‖ ≤ tolerance/(8*(B+1)^2) →
          y ∈ affineBall A B ∧ f y-f m ≤ tolerance/2 := by
  have hB : 1 ≤ B := by linarith [norm_nonneg p]
  obtain ⟨c,hc,hcn⟩ := affine_origin_projection A p hp
  have hcB : ‖c‖ ≤ B-1 := hcn.trans hpB
  have hcB' : ‖c‖ ≤ B := by linarith
  obtain ⟨m,hm,hminimum⟩ := affineBall_minimizer f grad hg A B p hp (by linarith)
  let rho := B-‖c‖
  let r := tolerance/(8*(B+1)^2)
  let lam := r/rho
  have hrho : 1 ≤ rho := by dsimp [rho]; linarith
  have hrhopos : 0 < rho := by linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_iff₀ (by positivity : 0 < 8*(B+1)^2)).mpr
    nlinarith
  have hl0 : 0 ≤ lam := le_of_lt (div_pos hrpos hrhopos)
  have hl1 : lam ≤ 1 := (div_le_one hrhopos).mpr (hr1.trans hrho)
  have hlr : lam ≤ r := div_le_self hrpos.le hrho
  have hprod : lam*rho = r := div_mul_cancel₀ r hrhopos.ne'
  let mprime := (1-lam) • m+lam • c
  have hmpA : mprime ∈ A := A.convex hm.1 hc (sub_nonneg.mpr hl1) hl0 (by ring)
  have hmpnorm : ‖mprime‖ ≤ B-r := by
    calc
      ‖mprime‖ ≤ ‖(1-lam) • m‖+‖lam • c‖ := norm_add_le _ _
      _ = (1-lam)*‖m‖+lam*‖c‖ := by
        rw [norm_smul_of_nonneg (sub_nonneg.mpr hl1), norm_smul_of_nonneg hl0]
      _ ≤ (1-lam)*B+lam*‖c‖ := by
        have hh := mul_le_mul_of_nonneg_left hm.2 (sub_nonneg.mpr hl1)
        linarith
      _ = B-r := by dsimp [rho] at hprod; nlinarith
  refine ⟨m,hm,hminimum,mprime,hmpA,hmpnorm,?_⟩
  intro y hyA hyr
  have hynorm : ‖y‖ ≤ B := by
    have hn : ‖y‖ ≤ ‖y-mprime‖+‖mprime‖ := by simpa using norm_add_le (y-mprime) mprime
    linarith
  have hmc : ‖c-m‖ ≤ 2*B := (norm_sub_le c m).trans (by linarith [hm.2])
  have hdiff : mprime-m = lam • (c-m) := by dsimp [mprime]; module
  have hdist : ‖y-m‖ ≤ (2*B+1)*r := by
    calc
      ‖y-m‖ ≤ ‖y-mprime‖+‖mprime-m‖ := by
        rw [show y-m = (y-mprime)+(mprime-m) by abel]
        exact norm_add_le _ _
      _ = ‖y-mprime‖+lam*‖c-m‖ := by rw [hdiff,norm_smul_of_nonneg hl0]
      _ ≤ r+lam*(2*B) := add_le_add hyr (mul_le_mul_of_nonneg_left hmc hl0)
      _ ≤ (2*B+1)*r := by
        have hh := mul_le_mul_of_nonneg_right hlr (show 0 ≤ 2*B by linarith)
        nlinarith
  have hnum := small_target_numeric B tolerance ‖y-m‖ hB htol htol1 (norm_nonneg _)
    (by simpa only [r,mul_div_assoc] using hdist)
  have hgrad := gradient_norm_bound f grad hg hLip xstar m hmin hstar B hm.2
  have hi := real_inner_le_norm (grad m) (y-m)
  have hmul := mul_le_mul_of_nonneg_right hgrad (norm_nonneg (y-m))
  have hdes := PaperSmooth.descent_upper f grad hg 1 hLip m y
  norm_num at hdes
  exact ⟨⟨hyA,hynorm⟩, by nlinarith⟩

end
end PaperCentroid

end SnapshotModule_012
/- END centroid_geometry -/

/- BEGIN outer_line_search -/
section SnapshotModule_013

namespace PaperOuterLine
open Set PaperGDE PaperTrinary PaperLineSearchComplete
open scoped RealInnerProductSpace
noncomputable section

def linePoint {n : ℕ} (x v : Vec n) (t : ℝ) : Vec n := x-t • v

def lineProgram {n : ℕ} (x v : Vec n) (D xi : ℝ) : PaperTrinary.Program n (Vec n) :=
  PaperOracle.Program.bind (liftLine (linePoint x v) (boundedLineSearch D xi))
    (fun t => .done (linePoint x v t))

lemma line_cap {n : ℕ} (x v : Vec n) (D xi : ℝ) :
    PaperOracle.Program.Cap (horizon D xi) (lineProgram x v D xi) := by
  have h := PaperOracle.Program.cap_bind _ (fun t => PaperOracle.Program.done (linePoint x v t))
    (bounded_line_cap (linePoint x v) D xi) (b := 0) (by intro t; trivial)
  simpa [lineProgram] using h

lemma reply_geometry (r : Ordering) {a b : ℝ} (hab : a<b) :
    a ≤ (trisectionReplyStep r a b).1 ∧
      (trisectionReplyStep r a b).1 < (trisectionReplyStep r a b).2 ∧
      (trisectionReplyStep r a b).2 ≤ b := by
  have hh := trisection_geometry hab
  dsimp at hh
  cases r <;> dsimp [trisectionReplyStep] <;>
    (constructor <;> try constructor) <;> linarith [hh.1.1,hh.1.2,hh.2.1.1,hh.2.1.2,hh.2.2.1]

lemma parameter_feasible (C : PaperLineSearchComplete.Oracle) (k : ℕ) {a b : ℝ} (hab : a<b) :
    let out := (evaluate C (searchProgram k a b)).1
    a ≤ out.1 ∧ out.1 < out.2 ∧ out.2 ≤ b := by
  induction k generalizing a b with
  | zero => exact ⟨le_rfl,hab,le_rfl⟩
  | succ k ih =>
    let r := C (a+(b-a)/3) (a+2*(b-a)/3)
    have hs := reply_geometry r hab
    have ht := ih hs.2.1
    exact ⟨hs.1.trans ht.1,ht.2.1,ht.2.2.trans hs.2.2⟩

lemma lineProgram_parameter {n : ℕ} (C : PaperTrinary.Oracle n) (x v : Vec n) (D xi : ℝ) :
    ∃ t ∈ Icc (0:ℝ) 1, PaperOracle.Program.run C (lineProgram x v D xi)=linePoint x v t := by
  let oracle := fun a b => C (linePoint x v a,linePoint x v b)
  let t := (evaluate oracle (boundedLineSearch D xi)).1
  refine ⟨t,?_,?_⟩
  · have hg := parameter_feasible oracle (horizon D xi) (by norm_num : (0:ℝ)<1)
    have he := evaluate_map oracle Prod.fst (searchProgram (horizon D xi) 0 1)
    change t ∈ Icc (0:ℝ) 1
    dsimp [t,boundedLineSearch]
    rw [he]
    exact ⟨hg.1,hg.2.1.le.trans hg.2.2⟩
  · simp only [lineProgram,PaperOracle.Program.run_bind,PaperOracle.Program.run,liftLine_run]
    rfl

lemma line_point_norm {n : ℕ} (x v : Vec n) (R t : ℝ) (hx : ‖x‖ ≤ R)
    (hv : ‖v‖=1) (ht : t ∈ Icc (0:ℝ) 1) : ‖linePoint x v t‖ ≤ R+1 := by
  have hh := norm_sub_le x (t • v)
  rw [norm_smul,hv,mul_one,Real.norm_eq_abs,abs_of_nonneg ht.1] at hh
  exact hh.trans (by linarith [ht.2])

lemma line_convex {n : ℕ} (f : Vec n → ℝ) (hc : ConvexOn ℝ univ f) (x v : Vec n) :
    ConvexOn ℝ (Icc (0:ℝ) 1) (fun t => f (linePoint x v t)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro a ha b hb s t hs ht hst
  have hh := hc.2 (show linePoint x v a ∈ univ from trivial)
    (show linePoint x v b ∈ univ from trivial) hs ht hst
  have he : s • linePoint x v a+t • linePoint x v b = linePoint x v (s*a+t*b) := by
    calc
      _ = (s+t) • x-(s*a+t*b) • v := by dsimp [linePoint]; module
      _ = _ := by rw [hst,one_smul]; rfl
  simpa only [he,smul_eq_mul] using hh

lemma line_lipschitz {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar x v : Vec n) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (R : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hv : ‖v‖=1) :
    LipschitzOnWith ⟨R+2,by linarith⟩ (fun t => f (linePoint x v t)) (Icc (0:ℝ) 1) := by
  have hder : ∀ t : ℝ, HasDerivAt (fun s => f (linePoint x v s))
      (inner ℝ (grad (linePoint x v t)) (-v)) t := by
    intro t
    simpa only [linePoint,smul_neg,sub_eq_add_neg] using PaperSmooth.line_hasDeriv f grad hg x (-v) t
  apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (hder t).hasDerivWithinAt)
  intro t ht
  have hgn := PaperCentroid.gradient_norm_bound f grad hg hLip xstar (linePoint x v t)
    hmin hstar (R+1) (line_point_norm x v R t hx hv ht)
  have hh := norm_inner_le_norm (𝕜 := ℝ) (grad (linePoint x v t)) (-v)
  rw [norm_neg,hv,mul_one] at hh
  change ‖inner ℝ (grad (linePoint x v t)) (-v)‖ ≤ R+2
  exact hh.trans (by linarith)

lemma lineProgram_accuracy {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (xstar x v : Vec n)
    (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (R xi : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hv : ‖v‖=1)
    (hxi : 0 < xi) (hxiD : xi ≤ R+2) :
    ∀ t ∈ Icc (0:ℝ) 1,
      f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (lineProgram x v (R+2) xi)) ≤
        f (linePoint x v t)+xi := by
  let F : ℝ → ℝ := fun t => f (linePoint x v t)
  let oracle := fun a b => PaperOracle.comparisonOracle f (linePoint x v a,linePoint x v b)
  have hh := tie_safe_bounded_line_search oracle (PaperTrinary.realOrder_correct F)
    ⟨R+2,by linarith⟩ hxi hxiD (line_convex f hc x v)
    (line_lipschitz f grad hg hLip xstar x v hmin hstar R hR hx hv)
  intro t ht
  have herr := hh.2.2.1 t ht
  simp only [lineProgram,PaperOracle.Program.run_bind,PaperOracle.Program.run,liftLine_run]
  change f (linePoint x v (evaluate
    (fun a b => PaperOracle.comparisonOracle f (linePoint x v a,linePoint x v b))
    (boundedLineSearch (R+2) xi)).1)-f (linePoint x v t) ≤ xi at herr
  linarith

end
end PaperOuterLine

end SnapshotModule_013
/- END outer_line_search -/

/- BEGIN PaperCore -/
section SnapshotModule_014

/- Local kernel checks of exact intermediate deductions in main.tex.
   These are not formalizations of the comparison algorithms or the whole paper. -/

open scoped RealInnerProductSpace

theorem potential_expansion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z p h xstar : V) (A Ap a c kap e ep xi delta m K : ℝ)
    (ha : 0 ≤ a) (hAp : 0 ≤ Ap) (hA : Ap = A + a)
    (hweight : a ^ 2 = kap * Ap) (hp : ‖p‖ = m)
    (herr : ‖p - h‖ ≤ delta * m)
    (hdes : e - ep ≥ c * m ^ 2 / 2 - xi)
    (hconv : inner ℝ h (z - xstar) ≥ e - K) :
    (Ap * ep + ‖(z - a • p) - xstar‖ ^ 2 / 2) -
      (A * e + ‖z - xstar‖ ^ 2 / 2) ≤
    -(c - kap) * Ap * m ^ 2 / 2 + a * delta * m * ‖z - xstar‖ +
      Ap * xi + a * K := by
  have hb := abs_real_inner_le_norm (p - h) (z - xstar)
  have hmul := mul_le_mul_of_nonneg_right herr (norm_nonneg (z - xstar))
  have hlow : -(delta * m * ‖z - xstar‖) ≤ inner ℝ (p - h) (z - xstar) :=
    (neg_le_of_abs_le hb).trans' (neg_le_neg hmul)
  rw [inner_sub_left] at hlow
  have hi : e - K - delta * m * ‖z - xstar‖ ≤ inner ℝ p (z - xstar) := by
    linarith
  have hn : ‖(z - a • p) - xstar‖ ^ 2 =
      ‖z - xstar‖ ^ 2 - 2 * a * inner ℝ p (z - xstar) + a ^ 2 * m ^ 2 := by
    rw [show (z - a • p) - xstar = (z - xstar) - a • p by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, hp, real_inner_comm (z - xstar) p]
    ring
  have hd := mul_le_mul_of_nonneg_left hdes hAp
  have hh := mul_le_mul_of_nonneg_left hi ha
  rw [hn]
  have hw2 := congrArg (fun t : ℝ => t * m ^ 2) hweight
  have hAe := congrArg (fun t : ℝ => t * e) hA
  nlinarith [hw2, hAe]

theorem potential_young (a delta m D Ap : ℝ)
    (hw : a ^ 2 = (9 / 32 : ℝ) * Ap) :
    a * delta * m * D ≤ (9 / 32 : ℝ) * Ap * m ^ 2 / 4 + delta ^ 2 * D ^ 2 := by
  nlinarith [sq_nonneg (a * m / 2 - delta * D)]

theorem potential_recurrence (phi phin Ap a delta m D xi K E : ℝ)
    (hAp : 0 ≤ Ap) (ha : 0 ≤ a)
    (hw : a ^ 2 = (9 / 32 : ℝ) * Ap)
    (hD : D ^ 2 ≤ 2 * phi) (hK : K ≤ E)
    (hexpand : phin - phi ≤ -(9 / 32 : ℝ) * Ap * m ^ 2 / 2 +
      a * delta * m * D + Ap * xi + a * K) :
    phin ≤ (1 + 2 * delta ^ 2) * phi + Ap * xi + a * E := by
  have hy := potential_young a delta m D Ap hw
  have hd := mul_le_mul_of_nonneg_left hD (sq_nonneg delta)
  have hk := mul_le_mul_of_nonneg_left hK ha
  have hneg : 0 ≤ (9 / 32 : ℝ) * Ap * m ^ 2 := by positivity
  nlinarith

theorem weight_lower_step (kap a A k : ℝ)
    (hk : 0 ≤ k) (hkap : 0 < kap) (ha : 0 < a)
    (hA : kap * k ^ 2 / 4 ≤ A) (hw : a ^ 2 = kap * (A + a)) :
    kap * (k + 1) / 2 ≤ a ∧ kap * (k + 1) ^ 2 / 4 ≤ A + a := by
  have hmul := mul_le_mul_of_nonneg_left hA (le_of_lt hkap)
  have hroot : kap * (k + 1) / 2 ≤ a := by
    by_contra hn
    have ht : a < kap * (k + 1) / 2 := lt_of_not_ge hn
    have hfac : 0 < (kap * (k + 1) / 2 - a) * (kap * k / 2 + a) := by positivity
    nlinarith [sq_nonneg kap]
  constructor
  · exact hroot
  · nlinarith

theorem weight_upper_step (kap a A k : ℝ)
    (hk : 0 ≤ k) (hkap : 0 < kap) (ha : 0 < a)
    (hA : A ≤ kap * (k + 1) ^ 2) (hw : a ^ 2 = kap * (A + a)) :
    a ≤ kap * (k + 2) ∧ A + a ≤ kap * (k + 2) ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left hA (le_of_lt hkap)
  have hroot : a ≤ kap * (k + 2) := by
    by_contra hn
    have ht : kap * (k + 2) < a := lt_of_not_ge hn
    have hfac : 0 < (a - kap * (k + 2)) * (a + kap * (k + 1)) := by positivity
    nlinarith
  constructor
  · exact hroot
  · nlinarith

theorem potential_numeric_closure (phi P H : ℝ)
    (hphi : phi ≤ P * ((1 / 2 : ℝ) + H)) (hP : 0 ≤ P) (hP2 : P < 2)
    (hH : 0 ≤ H) (hH42 : H < (42 / 100 : ℝ)) : phi < 2 := by
  nlinarith

theorem final_accuracy (A gap N Q : ℝ)
    (hQ : 0 < Q) (hN : 0 ≤ N)
    (hweight : (9 / 128 : ℝ) * (N + 1) ^ 2 ≤ A)
    (hpotential : A * gap < 2)
    (hsteps : (16 / 3 : ℝ) * Real.sqrt Q ≤ N) : gap < 1 / Q := by
  have hs : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hsq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt (le_of_lt hQ)
  have hNQ : (256 / 9 : ℝ) * Q < (N + 1) ^ 2 := by nlinarith
  have hA : 0 < A := by nlinarith
  apply (lt_div_iff₀ hQ).mpr
  by_contra hbad
  have hg : 1 ≤ gap * Q := le_of_not_gt hbad
  have h1 : 0 < gap := by nlinarith
  have hw := mul_le_mul_of_nonneg_right hweight (le_of_lt h1)
  have hnqg := mul_lt_mul_of_pos_right hNQ h1
  nlinarith

theorem lower_transfer_constants (d Q T : ℝ)
    (h : max (5*d/16) (d/4096*min d (Real.sqrt Q)) ≤ 2*T) :
    max (5*d/32) (d/8192*min d (Real.sqrt Q)) ≤ T := by
  apply max_le
  · have := le_trans (le_max_left _ _) h
    linarith
  · have := le_trans (le_max_right _ _) h
    linarith

theorem logarithmic_transfer_constant (d Q T : ℝ)
    (h : (3*d/4000)*(1 + Real.log Q/Real.log 3) ≤ 2*T) :
    (3*d/8000)*(1 + Real.log Q/Real.log 3) ≤ T := by linarith

theorem low_window_dominance (d Q : ℝ) (hq : Q ≤ d) :
    Q * Real.sqrt Q ≤ d * Real.sqrt Q := by
  exact mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg Q)

theorem middle_window_dominance (d Q : ℝ) (hq : d ≤ Q) :
    d * Real.sqrt Q ≤ Q * Real.sqrt Q := by
  exact mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg Q)

theorem weight_sequence_bounds (kap : ℝ) (A a : ℕ → ℝ)
    (hkap : 0 < kap) (hzero : A 0 = 0)
    (ha : ∀ k, 0 < a (k + 1))
    (hstep : ∀ k, A (k + 1) = A k + a (k + 1))
    (hweight : ∀ k, a (k + 1) ^ 2 = kap * A (k + 1)) :
    (∀ k : ℕ, A k ≤ kap * ((k : ℝ) + 1) ^ 2) ∧
    (∀ k : ℕ, 1 ≤ k → kap * ((k : ℝ) + 1) ^ 2 / 4 ≤ A k) := by
  constructor
  · intro k
    induction k with
    | zero => simp [hzero, le_of_lt hkap]
    | succ k ih =>
      have hh := weight_upper_step kap (a (k + 1)) (A k) (k : ℝ)
        (Nat.cast_nonneg k) hkap (ha k) ih (by rw [← hstep]; exact hweight k)
      rw [hstep]
      push_cast
      convert hh.2 using 1 <;> ring
  · have hfirst : A 1 = kap := by
      have hw := hweight 0
      have hs := hstep 0
      have hp := ha 0
      simp only [Nat.zero_add, hzero, zero_add] at hs
      rw [hs] at hw ⊢
      nlinarith
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hz : k = 0
      · subst k
        norm_num [hfirst]
      · have hkpos : 1 ≤ k := by omega
        have hl := ih hkpos
        have hh := weight_lower_step kap (a (k + 1)) (A k) ((k : ℝ) + 1)
          (by positivity) hkap (ha k) hl (by rw [← hstep]; exact hweight k)
        rw [hstep]
        push_cast
        convert hh.2 using 1 <;> ring

theorem finite_recurrence_unroll (phi growth err P H : ℕ → ℝ)
    (hphi0 : 0 ≤ phi 0) (hP0 : P 0 = 1) (hH0 : H 0 = 0)
    (hgrowth : ∀ k, 1 ≤ growth k) (herr : ∀ k, 0 ≤ err k)
    (hP : ∀ k, P (k + 1) = growth k * P k)
    (hH : ∀ k, H (k + 1) = H k + err k)
    (hrec : ∀ k, phi (k + 1) ≤ growth k * phi k + err k) :
    ∀ k, 1 ≤ P k ∧ 0 ≤ H k ∧ phi k ≤ P k * (phi 0 + H k) := by
  intro k
  induction k with
  | zero => simp [hP0, hH0]
  | succ k ih =>
    rcases ih with ⟨hp, hh, hbound⟩
    have hg := hgrowth k
    have he := herr k
    have hpn : 1 ≤ P (k + 1) := by
      rw [hP]
      nlinarith
    refine ⟨hpn, ?_, ?_⟩
    · rw [hH]
      positivity
    · calc
        phi (k + 1) ≤ growth k * phi k + err k := hrec k
        _ ≤ growth k * (P k * (phi 0 + H k)) + err k := by
          gcongr
        _ ≤ P (k + 1) * (phi 0 + H (k + 1)) := by
          rw [hP, hH]
          have hpge : 1 ≤ growth k * P k := by nlinarith
          have := mul_le_mul_of_nonneg_right hpge he
          nlinarith

theorem dual_point_feasibility
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (z xstar : V) (A gap phi : ℝ)
    (hx : ‖xstar‖ ≤ 1) (hA : 0 ≤ A) (hgap : 0 ≤ gap)
    (hphi : phi = A * gap + ‖z - xstar‖ ^ 2 / 2) (hphi2 : phi < 2) :
    ‖z - xstar‖ < 2 ∧ ‖z‖ < 3 := by
  have hprod : 0 ≤ A * gap := mul_nonneg hA hgap
  have hn : 0 ≤ ‖z - xstar‖ := norm_nonneg _
  have hdist : ‖z - xstar‖ < 2 := by nlinarith
  refine ⟨hdist, ?_⟩
  have htri : ‖z‖ ≤ ‖z - xstar‖ + ‖xstar‖ := by
    simpa using (norm_add_le (z - xstar) xstar)
  linarith

theorem middle_residual_cubic_bound (d Q r : ℝ)
    (hd : 0 < d) (hQ : 0 ≤ Q) (hr : 0 < r) (hcube : r ^ 3 = d) :
    min (Q / d) (d / Real.sqrt Q) ≤ r := by
  by_cases hsplit : Q ≤ r ^ 4
  · apply (min_le_left _ _).trans
    apply (div_le_iff₀ hd).mpr
    nlinarith [hcube]
  · apply (min_le_right _ _).trans
    have hsplit' : r ^ 4 < Q := lt_of_not_ge hsplit
    have hsq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
    have hs : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
    have hroot : r ^ 2 < Real.sqrt Q := by
      nlinarith [sq_nonneg (Real.sqrt Q - r ^ 2)]
    have hspos : 0 < Real.sqrt Q := lt_trans (by positivity) hroot
    apply (div_le_iff₀ hspos).mpr
    nlinarith [mul_lt_mul_of_pos_left hroot hr]

theorem error_budget_numerics :
    (41 / 10 : ℝ) * (9 / 32) * (9 / 20000) +
      30 * (9 / 32) * Real.sqrt (2 * (9 / 20000 : ℝ)) * Real.pi ^ 2 / 6 <
      (42 / 100 : ℝ) := by
  have hs : Real.sqrt (2 * (9 / 20000 : ℝ)) = (3 / 100 : ℝ) := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [hs]
  have hpi := Real.pi_lt_d2
  have hpos := Real.pi_pos
  nlinarith [sq_nonneg (Real.pi - (63 / 20 : ℝ))]

theorem clipped_kkt_certificate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h x z : V) (xi R : ℝ) (hxi : 0 < xi)
    (hR : Real.sqrt (2 * xi) ≤ 2 * R) (hdiam : ‖z - x‖ ≤ 2 * R)
    (hsegment : ∀ t : ℝ, 0 < t → t ≤ 1 →
      -(xi / t + ‖z - x‖ ^ 2 * t / 2) ≤ inner ℝ h (z - x)) :
    -(2 * R * Real.sqrt (2 * xi)) ≤ inner ℝ h (z - x) := by
  let s := ‖z - x‖
  let b := Real.sqrt (2 * xi)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb2 : b ^ 2 = 2 * xi := Real.sq_sqrt (by positivity)
  have hs : 0 ≤ s := norm_nonneg _
  by_cases hz : s = 0
  · have heq : z - x = 0 := norm_eq_zero.mp hz
    rw [heq, inner_zero_right]
    exact neg_nonpos.mpr (mul_nonneg (le_trans (le_of_lt hb) hR) (le_of_lt hb))
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    by_cases hlarge : b < s
    · have ht : 0 < b / s := div_pos hb hspos
      have ht1 : b / s ≤ 1 := (div_le_one hspos).mpr (le_of_lt hlarge)
      have hv := hsegment (b / s) ht ht1
      have heq : xi / (b / s) + s ^ 2 * (b / s) / 2 = s * b := by
        field_simp
        nlinarith [hb2]
      change -(xi / (b / s) + s ^ 2 * (b / s) / 2) ≤ _ at hv
      rw [heq] at hv
      have hd := mul_le_mul_of_nonneg_right hdiam (le_of_lt hb)
      exact (neg_le_neg hd).trans hv
    · have hsmall : s ≤ b := le_of_not_gt hlarge
      have hv := hsegment 1 (by norm_num) (by norm_num)
      have hssq : s ^ 2 ≤ b ^ 2 := sq_le_sq₀ hs (le_of_lt hb) |>.mpr hsmall
      have hbr := mul_le_mul_of_nonneg_left hR (le_of_lt hb)
      change -(xi / 1 + s ^ 2 * 1 / 2) ≤ _ at hv
      change -(2 * R * b) ≤ _
      nlinarith


theorem product_budget_numerics : Real.exp (Real.pi ^ 2 / 48) < 2 := by
  have hpos := Real.pi_pos
  have hp := Real.pi_lt_four
  have hx : Real.pi ^ 2 / 48 < (1 / 2 : ℝ) := by nlinarith
  have hexp := Real.exp_bound_div_one_sub_of_interval
    (show 0 ≤ Real.pi ^ 2 / 48 by positivity) (by linarith : Real.pi ^ 2 / 48 < 1)
  apply lt_of_le_of_lt hexp
  apply (div_lt_iff₀ (by linarith : 0 < 1 - Real.pi ^ 2 / 48)).mpr
  nlinarith

theorem shifted_basel_bound (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have hb := Summable.sum_le_tsum (Finset.range (n + 1))
    (fun k _ => show (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2 by positivity) hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq, Finset.sum_range_succ'] at hb
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
    div_zero, add_zero] using hb

theorem angular_product_bound (n : ℕ) :
    (∏ k ∈ Finset.range n, (1 + 2 * (1 / (4 * ((k : ℝ) + 1))) ^ 2)) ≤
      Real.exp (Real.pi ^ 2 / 48) := by
  have hscalar : ∀ k : ℕ,
      2 * (1 / (4 * ((k : ℝ) + 1))) ^ 2 = (1 / 8 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring
  calc
    (∏ k ∈ Finset.range n, (1 + 2 * (1 / (4 * ((k : ℝ) + 1))) ^ 2)) ≤
        ∏ k ∈ Finset.range n, Real.exp (2 * (1 / (4 * ((k : ℝ) + 1))) ^ 2) := by
      apply Finset.prod_le_prod
      · intro k _
        positivity
      · intro k _
        simpa [add_comm] using Real.add_one_le_exp (2 * (1 / (4 * ((k : ℝ) + 1))) ^ 2)
    _ = Real.exp (∑ k ∈ Finset.range n, 2 * (1 / (4 * ((k : ℝ) + 1))) ^ 2) :=
      (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Real.pi ^ 2 / 48) := by
      apply Real.exp_le_exp.mpr
      simp_rw [hscalar]
      rw [← Finset.mul_sum]
      have hb := mul_le_mul_of_nonneg_left (shifted_basel_bound n)
        (by norm_num : (0 : ℝ) ≤ 1 / 8)
      nlinarith [shifted_basel_bound n]

theorem conditional_joint_induction (phi growth err P H : ℕ → ℝ)
    (hphi0 : phi 0 ≤ (1 / 2 : ℝ)) (hP0 : P 0 = 1) (hH0 : H 0 = 0)
    (hgrowth : ∀ k, 1 ≤ growth k) (herr : ∀ k, 0 ≤ err k)
    (hP : ∀ k, P (k + 1) = growth k * P k)
    (hH : ∀ k, H (k + 1) = H k + err k)
    (hP2 : ∀ k, P k < 2) (hH42 : ∀ k, H k < (42 / 100 : ℝ))
    (hrec : ∀ k, phi k < 2 → phi (k + 1) ≤ growth k * phi k + err k) :
    ∀ k, 1 ≤ P k ∧ 0 ≤ H k ∧
      phi k ≤ P k * ((1 / 2 : ℝ) + H k) ∧ phi k < 2 := by
  intro k
  induction k with
  | zero => simp only [hP0, hH0, add_zero, one_mul]; exact ⟨by norm_num, by norm_num, hphi0, by linarith⟩
  | succ k ih =>
    rcases ih with ⟨hp, hh, hbound, hsmall⟩
    have hg := hgrowth k
    have he := herr k
    have hpn : 1 ≤ P (k + 1) := by rw [hP]; nlinarith
    have hhn : 0 ≤ H (k + 1) := by rw [hH]; positivity
    have hbn : phi (k + 1) ≤ P (k + 1) * ((1 / 2 : ℝ) + H (k + 1)) := by
      calc
        phi (k + 1) ≤ growth k * phi k + err k := hrec k hsmall
        _ ≤ growth k * (P k * ((1 / 2 : ℝ) + H k)) + err k := by gcongr
        _ ≤ P (k + 1) * ((1 / 2 : ℝ) + H (k + 1)) := by
          rw [hP, hH]
          have hpge : 1 ≤ growth k * P k := by nlinarith
          have := mul_le_mul_of_nonneg_right hpge he
          nlinarith
    exact ⟨hpn, hhn, hbn, potential_numeric_closure _ _ _ hbn (by linarith)
      (hP2 _) hhn (hH42 _)⟩

theorem full_history_final_analytic_certificate
    (A a gap phi growth err P H : ℕ → ℝ) (N : ℕ) (Q : ℝ)
    (hQ : 0 < Q) (hN : 1 ≤ N) (hsteps : (16 / 3 : ℝ) * Real.sqrt Q ≤ (N : ℝ))
    (hzero : A 0 = 0) (ha : ∀ k, 0 < a (k + 1))
    (hstep : ∀ k, A (k + 1) = A k + a (k + 1))
    (hweight : ∀ k, a (k + 1) ^ 2 = (9 / 32 : ℝ) * A (k + 1))
    (hphi0 : phi 0 ≤ (1 / 2 : ℝ)) (hP0 : P 0 = 1) (hH0 : H 0 = 0)
    (hgrowth : ∀ k, 1 ≤ growth k) (herr : ∀ k, 0 ≤ err k)
    (hP : ∀ k, P (k + 1) = growth k * P k)
    (hH : ∀ k, H (k + 1) = H k + err k)
    (hP2 : ∀ k, P k < 2) (hH42 : ∀ k, H k < (42 / 100 : ℝ))
    (hrec : ∀ k, phi k < 2 → phi (k + 1) ≤ growth k * phi k + err k)
    (hgap : A N * gap N ≤ phi N) :
    (∀ k, phi k < 2) ∧ gap N < 1 / Q := by
  have hjoint := conditional_joint_induction phi growth err P H hphi0 hP0 hH0
    hgrowth herr hP hH hP2 hH42 hrec
  have hweights := weight_sequence_bounds (9 / 32 : ℝ) A a (by norm_num)
    hzero ha hstep hweight
  refine ⟨fun k => (hjoint k).2.2.2, ?_⟩
  apply final_accuracy (A N) (gap N) (N : ℝ) Q hQ (Nat.cast_nonneg N)
  · have hb := hweights.2 N hN
    convert hb using 1 <;> ring
  · exact hgap.trans_lt (hjoint N).2.2.2
  · exact hsteps

theorem ceil_iteration_adequacy (Q : ℝ) (hQ : 0 < Q) :
    (16 / 3 : ℝ) * Real.sqrt Q ≤ (⌈(16 / 3 : ℝ) * Real.sqrt Q⌉₊ : ℝ) ∧
    1 ≤ ⌈(16 / 3 : ℝ) * Real.sqrt Q⌉₊ := by
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hc := Nat.le_ceil ((16 / 3 : ℝ) * Real.sqrt Q)
  refine ⟨hc, ?_⟩
  by_contra hn
  have hz : ⌈(16 / 3 : ℝ) * Real.sqrt Q⌉₊ = 0 := by omega
  rw [hz] at hc
  norm_num at hc
  nlinarith

theorem polynomial_inner_cost_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 2) ^ 2) ≤ ((n : ℝ) + 1) ^ 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]

theorem dual_full_history_membership
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (z v : ℕ → V) (a m : ℕ → ℝ) (hz0 : z 0 = 0)
    (hz : ∀ k, z (k + 1) = z k - a (k + 1) • (m k • v k)) :
    ∀ (n : ℕ) (U : Submodule ℝ V),
      (∀ i < n, v i ∈ U) → z n ∈ U := by
  intro n
  induction n with
  | zero => intro U _; rw [hz0]; exact U.zero_mem
  | succ n ih =>
    intro U hv
    rw [hz]
    apply U.sub_mem
    · apply ih U
      intro i hi
      exact hv i (by omega)
    · exact U.smul_mem _ (U.smul_mem _ (hv n (by omega)))

theorem positive_scale_comparison (a b s : ℝ) (hs : 0 < s) :
    (a / s < b / s ↔ a < b) ∧ (a / s = b / s ↔ a = b) := by
  constructor
  · exact div_lt_div_iff_of_pos_right hs
  · exact div_left_inj' (ne_of_gt hs)

theorem error_first_term_envelope (k : ℝ) (hk : 1 ≤ k) :
    (k + 1) ^ 2 / k ^ 8 ≤ 4 / k ^ 2 := by
  have hkpos : 0 < k := by linarith
  have hnum : (k + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
  have hp4 : 1 ≤ k ^ 4 := one_le_pow₀ hk
  have hp6 : k ^ 2 ≤ k ^ 6 := by
    have hm := mul_le_mul_of_nonneg_left hp4 (sq_nonneg k)
    nlinarith
  calc
    (k + 1) ^ 2 / k ^ 8 ≤ (4 * k ^ 2) / k ^ 8 := by gcongr
    _ = 4 / k ^ 6 := by field_simp [ne_of_gt hkpos] <;> ring
    _ ≤ 4 / k ^ 2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hkpos) hp6

theorem error_second_term_envelope (k : ℝ) (hk : 1 ≤ k) :
    (k + 2) * (k + 4) / k ^ 4 ≤ 15 / k ^ 2 := by
  have hkpos : 0 < k := by linarith
  have hnum : (k + 2) * (k + 4) ≤ 15 * k ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ k - 1 by linarith) (show 0 ≤ 14*k + 8 by linarith)]
  calc
    (k + 2) * (k + 4) / k ^ 4 ≤ (15 * k ^ 2) / k ^ 4 := by gcongr
    _ = 15 / k ^ 2 := by field_simp [ne_of_gt hkpos] <;> ring

theorem finite_error_series_bound (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (9 / 32 : ℝ) * (9 / 20000) * ((k : ℝ) + 2) ^ 2 / ((k : ℝ) + 1) ^ 8) +
    (∑ k ∈ Finset.range n,
      2 * (9 / 32 : ℝ) * (3 / 100) * ((k : ℝ) + 3) * ((k : ℝ) + 5) /
        ((k : ℝ) + 1) ^ 4) < (42 / 100 : ℝ) := by
  have hfirst : (∑ k ∈ Finset.range n,
      (9 / 32 : ℝ) * (9 / 20000) * ((k : ℝ) + 2) ^ 2 / ((k : ℝ) + 1) ^ 8) ≤
      4 * (9 / 32 : ℝ) * (9 / 20000) * (Real.pi ^ 2 / 6) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n,
          (4 * (9 / 32 : ℝ) * (9 / 20000)) * (1 / ((k : ℝ) + 1) ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        have hb := mul_le_mul_of_nonneg_left
          (error_first_term_envelope ((k : ℝ) + 1) (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))
          (by norm_num : (0 : ℝ) ≤ (9 / 32 : ℝ) * (9 / 20000))
        convert hb using 1 <;> ring
      _ = (4 * (9 / 32 : ℝ) * (9 / 20000)) *
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr; exact shifted_basel_bound n
  have hsecond : (∑ k ∈ Finset.range n,
      2 * (9 / 32 : ℝ) * (3 / 100) * ((k : ℝ) + 3) * ((k : ℝ) + 5) /
        ((k : ℝ) + 1) ^ 4) ≤ 30 * (9 / 32 : ℝ) * (3 / 100) * (Real.pi ^ 2 / 6) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n,
          (30 * (9 / 32 : ℝ) * (3 / 100)) * (1 / ((k : ℝ) + 1) ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        have hb := mul_le_mul_of_nonneg_left
          (error_second_term_envelope ((k : ℝ) + 1) (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))
          (by norm_num : (0 : ℝ) ≤ 2 * (9 / 32 : ℝ) * (3 / 100))
        convert hb using 1 <;> ring
      _ = (30 * (9 / 32 : ℝ) * (3 / 100)) *
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr; exact shifted_basel_bound n
  have hp := Real.pi_lt_d2
  have hpos := Real.pi_pos
  nlinarith [sq_nonneg (Real.pi - (63 / 20 : ℝ))]

/- A specification counterexample, not a counterexample to the algorithm theorem:
   the displayed recurrence alone also admits all-zero weights. -/
theorem positive_root_is_required :
    ∃ (A a : ℕ → ℝ), A 0 = 0 ∧
      (∀ k, A (k + 1) = A k + a (k + 1)) ∧
      (∀ k, a (k + 1) ^ 2 = (9 / 32 : ℝ) * (A k + a (k + 1))) ∧
      ¬ ((9 / 32 : ℝ) * ((1 : ℝ) + 1) ^ 2 / 4 ≤ A 1) := by
  refine ⟨fun _ => 0, fun _ => 0, ?_⟩
  norm_num

end SnapshotModule_014
/- END PaperCore -/

/- BEGIN full_history_analysis -/
section SnapshotModule_015

namespace PaperFullHistory
open Set
open scoped RealInnerProductSpace

noncomputable section

def kap : ℝ := 9 / 32
def nu : ℝ := 9 / 20000

def weight : ℕ → ℝ
  | 0 => 0
  | k + 1 => weight k + kap / 2 + Real.sqrt (kap ^ 2 / 4 + kap * weight k)

def stepWeight (k : ℕ) : ℝ := if k = 0 then 0 else weight k - weight (k - 1)
def delta (k : ℕ) : ℝ := 1 / (4 * ((k : ℝ) + 1))
def xi (k : ℕ) : ℝ := nu / ((k : ℝ) + 1) ^ 8
def radius (k : ℕ) : ℝ := (k : ℝ) + 4
def previousError (k : ℕ) : ℝ :=
  if k = 0 then 0 else 2 * radius k * (3 / 100 : ℝ) / (k : ℝ) ^ 4

lemma kap_pos : 0 < kap := by norm_num [kap]
lemma weight_nonneg (k : ℕ) : 0 ≤ weight k := by
  have hkap := kap_pos
  induction k with
  | zero => simp [weight]
  | succ k ih => dsimp [weight]; positivity

lemma stepWeight_formula (k : ℕ) :
    stepWeight (k + 1) = kap / 2 + Real.sqrt (kap ^ 2 / 4 + kap * weight k) := by
  simp [stepWeight, weight]
  ring

lemma stepWeight_pos (k : ℕ) : 0 < stepWeight (k + 1) := by
  rw [stepWeight_formula]
  have := kap_pos
  positivity

lemma weight_step (k : ℕ) : weight (k + 1) = weight k + stepWeight (k + 1) := by
  rw [stepWeight_formula, weight]
  ring

lemma weight_identity (k : ℕ) : stepWeight (k + 1) ^ 2 = kap * weight (k + 1) := by
  have ha := weight_nonneg k
  have hk := kap_pos
  have hs := Real.sq_sqrt (show 0 ≤ kap ^ 2 / 4 + kap * weight k by positivity)
  rw [weight_step, stepWeight_formula]
  nlinarith

lemma weight_bounds :
    (∀ k : ℕ, weight k ≤ kap * ((k : ℝ) + 1) ^ 2) ∧
    (∀ k : ℕ, 1 ≤ k → kap * ((k : ℝ) + 1) ^ 2 / 4 ≤ weight k) := by
  exact weight_sequence_bounds kap weight stepWeight kap_pos rfl stepWeight_pos weight_step weight_identity

lemma stepWeight_bound (k : ℕ) : stepWeight (k + 1) ≤ kap * ((k : ℝ) + 2) := by
  exact (weight_upper_step kap (stepWeight (k + 1)) (weight k) (k : ℝ)
    (Nat.cast_nonneg k) kap_pos (stepWeight_pos k) (weight_bounds.1 k)
    (by rw [← weight_step]; exact weight_identity k)).1

lemma xi_pos (k : ℕ) : 0 < xi k := by unfold xi nu; positivity
lemma delta_pos (k : ℕ) : 0 < delta k := by unfold delta; positivity
lemma delta_le_quarter (k : ℕ) : delta k ≤ 1 / 4 := by
  unfold delta
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  apply (div_le_iff₀ (show 0 < 4 * ((k : ℝ) + 1) by positivity)).mpr
  nlinarith

lemma xi_le_nu (k : ℕ) : xi k ≤ nu := by
  have hp : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 8 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
  unfold xi
  exact div_le_self (by norm_num [nu]) hp

lemma sqrt_xi (k : ℕ) : Real.sqrt (2 * xi k) = (3 / 100 : ℝ) / ((k : ℝ) + 1) ^ 4 := by
  apply (Real.sqrt_eq_iff_eq_sq (by unfold xi nu; positivity) (by positivity)).mpr
  unfold xi nu
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

lemma previousError_succ (k : ℕ) :
    previousError (k + 1) = 2 * radius (k + 1) * Real.sqrt (2 * xi k) := by
  rw [sqrt_xi]
  simp only [previousError, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.cast_add, Nat.cast_one]
  ring

lemma previousError_nonneg (k : ℕ) : 0 ≤ previousError k := by
  unfold previousError radius
  split_ifs
  · rfl
  · positivity

lemma xi_sqrt_small (k : ℕ) : Real.sqrt (2 * xi k) ≤ 2 * radius (k + 1) := by
  have hx := xi_le_nu k
  have hxp := xi_pos k
  have hs := Real.sq_sqrt (show 0 ≤ 2 * xi k by positivity)
  have hp := Real.sqrt_nonneg (2 * xi k)
  unfold nu at hx
  unfold radius
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma weight_xi_envelope (k : ℕ) :
    weight (k + 1) * xi k ≤ kap * nu * ((k : ℝ) + 2) ^ 2 / ((k : ℝ) + 1) ^ 8 := by
  have hw := weight_bounds.1 (k + 1)
  have hm := mul_le_mul_of_nonneg_right hw (le_of_lt (xi_pos k))
  push_cast at hm
  calc
    weight (k + 1) * xi k ≤ kap * ((k : ℝ) + 1 + 1) ^ 2 * xi k := hm
    _ = _ := by unfold xi; ring

lemma previousError_envelope (k : ℕ) :
    stepWeight (k + 2) * previousError (k + 1) ≤
      2 * kap * (3 / 100 : ℝ) * ((k : ℝ) + 3) * ((k : ℝ) + 5) / ((k : ℝ) + 1) ^ 4 := by
  have ha := stepWeight_bound (k + 1)
  have hm := mul_le_mul_of_nonneg_right ha (previousError_nonneg (k + 1))
  push_cast at hm
  calc
    stepWeight (k + 2) * previousError (k + 1) ≤ kap * ((k : ℝ) + 1 + 2) * previousError (k + 1) := hm
    _ = _ := by rw [previousError_succ, sqrt_xi]; unfold radius; push_cast; ring

def additiveError (k : ℕ) : ℝ := weight (k + 1) * xi k + stepWeight (k + 1) * previousError k
def cumulativeError (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, additiveError k
def growth (k : ℕ) : ℝ := 1 + 2 * delta k ^ 2
def perturbationProduct (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, growth k

lemma additiveError_nonneg (k : ℕ) : 0 ≤ additiveError k := by
  unfold additiveError
  exact add_nonneg (mul_nonneg (weight_nonneg _) (le_of_lt (xi_pos _)))
    (mul_nonneg (le_of_lt (stepWeight_pos _)) (previousError_nonneg _))

lemma cumulativeError_bound (n : ℕ) : cumulativeError n < (42 / 100 : ℝ) := by
  have hfirst : (∑ k ∈ Finset.range n, weight (k + 1) * xi k) ≤
      ∑ k ∈ Finset.range n, kap * nu * ((k : ℝ) + 2) ^ 2 / ((k : ℝ) + 1) ^ 8 :=
    Finset.sum_le_sum (fun k _ => weight_xi_envelope k)
  let second : ℕ → ℝ := fun k =>
    2 * kap * (3 / 100 : ℝ) * ((k : ℝ) + 3) * ((k : ℝ) + 5) / ((k : ℝ) + 1) ^ 4
  have hsecond : (∑ k ∈ Finset.range n, stepWeight (k + 1) * previousError k) ≤
      ∑ k ∈ Finset.range n, second k := by
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_range_succ']
      simp only [previousError, ↓reduceIte, mul_zero, add_zero]
      calc
        _ ≤ ∑ k ∈ Finset.range n, second k := by
          apply Finset.sum_le_sum
          intro k _
          simpa [second, Nat.add_assoc, previousError] using previousError_envelope k
        _ ≤ ∑ k ∈ Finset.range (n + 1), second k := by
          rw [Finset.sum_range_succ]
          have hn : 0 ≤ second n := by unfold second kap; positivity
          linarith
  have hb := add_le_add hfirst hsecond
  have hsum : cumulativeError n =
      (∑ k ∈ Finset.range n, weight (k + 1) * xi k) +
      (∑ k ∈ Finset.range n, stepWeight (k + 1) * previousError k) := by
    simp [cumulativeError, additiveError, Finset.sum_add_distrib]
  rw [hsum]
  apply hb.trans_lt
  simpa [second, kap, nu] using finite_error_series_bound n

lemma growth_ge_one (k : ℕ) : 1 ≤ growth k := by unfold growth; nlinarith [sq_nonneg (delta k)]

lemma product_lt_two (n : ℕ) : perturbationProduct n < 2 := by
  have hh := angular_product_bound n
  change perturbationProduct n ≤ Real.exp (Real.pi ^ 2 / 48) at hh
  exact hh.trans_lt product_budget_numerics

lemma product_step (n : ℕ) :
    perturbationProduct (n + 1) = growth n * perturbationProduct n := by
  simp only [perturbationProduct, Finset.prod_range_succ]
  ring

lemma cumulativeError_step (n : ℕ) : cumulativeError (n + 1) = cumulativeError n + additiveError n := by
  exact Finset.sum_range_succ _ _

lemma product_ge_one (n : ℕ) : 1 ≤ perturbationProduct n := by
  induction n with
  | zero => simp [perturbationProduct]
  | succ n ih =>
    rw [product_step]
    have hg := growth_ge_one n
    have hh := mul_le_mul hg ih (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ growth n)
    simpa using hh

lemma cumulativeError_nonneg (n : ℕ) : 0 ≤ cumulativeError n :=
  Finset.sum_nonneg (fun k _ => additiveError_nonneg k)

lemma finite_potential_bounded (phi : ℕ → ℝ) (N : ℕ)
    (hstart : phi 0 ≤ (1 / 2 : ℝ))
    (hrec : ∀ k < N, phi k < 2 → phi (k+1) ≤ growth k * phi k + additiveError k) :
    ∀ k ≤ N, phi k ≤ perturbationProduct k * ((1 / 2 : ℝ) + cumulativeError k) ∧ phi k < 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [perturbationProduct, cumulativeError, Finset.range_zero, Finset.prod_empty,
      Finset.sum_empty, add_zero, one_mul]
    exact ⟨hstart, by linarith⟩
  | succ k ih =>
    intro hk
    have hkle : k ≤ N := by omega
    have hklt : k < N := by omega
    have hb := ih hkle
    have hnew : phi (k+1) ≤ perturbationProduct (k+1) * ((1/2:ℝ)+cumulativeError (k+1)) := by
      calc
        phi (k+1) ≤ growth k * phi k + additiveError k := hrec k hklt hb.2
        _ ≤ growth k * (perturbationProduct k * ((1/2:ℝ)+cumulativeError k)) + additiveError k := by
          have hm := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ growth k by linarith [growth_ge_one k])
          linarith
        _ ≤ perturbationProduct (k+1) * ((1/2:ℝ)+cumulativeError (k+1)) := by
          rw [product_step, cumulativeError_step]
          have hpge := product_ge_one (k+1)
          rw [product_step] at hpge
          have he := mul_le_mul_of_nonneg_right hpge (additiveError_nonneg k)
          nlinarith
    exact ⟨hnew, potential_numeric_closure _ _ _ hnew (by linarith [product_ge_one (k+1)])
      (product_lt_two _) (cumulativeError_nonneg _) (cumulativeError_bound _)⟩

lemma finite_antitone (u : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ k < N, u (k+1) ≤ u k) :
    ∀ i j, i ≤ j → j ≤ N → u j ≤ u i := by
  intro i j
  induction j generalizing i with
  | zero =>
    intro hi _
    have hz : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    intro hi hjN
    by_cases he : i = j+1
    · subst i
      rfl
    · exact (hstep j (by omega)).trans (ih i (by omega) (by omega))

section Objective
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma inner_normalize (h : V) : inner ℝ h (NormedSpace.normalize h) = ‖h‖ := by
  by_cases hh : h = 0
  · simp [hh, NormedSpace.normalize_zero_eq_zero]
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    simp only [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    <;> ring

lemma direction_inner_bounds (h v : V) (err : ℝ) (hv : ‖v‖ = 1)
    (hd : ‖v - NormedSpace.normalize h‖ ≤ err) :
    (1 - err) * ‖h‖ ≤ inner ℝ h v ∧ inner ℝ h v ≤ ‖h‖ := by
  have hi := abs_real_inner_le_norm h (v - NormedSpace.normalize h)
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg h)
  have hlow := neg_le_of_abs_le (hi.trans hm)
  rw [inner_sub_right, inner_normalize] at hlow
  have hup := real_inner_le_norm h v
  rw [hv, mul_one] at hup
  exact ⟨by linarith, hup⟩

lemma direction_error (h v : V) (err : ℝ)
    (hd : ‖v - NormedSpace.normalize h‖ ≤ err) :
    ‖‖h‖ • v - h‖ ≤ err * ‖h‖ := by
  have hi : ‖h‖ • v - h = ‖h‖ • (v - NormedSpace.normalize h) := by
    rw [smul_sub, NormedSpace.norm_smul_normalize]
  rw [hi, norm_smul_of_nonneg (norm_nonneg h)]
  nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg h)]

lemma pre_success_gradient (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (x xstar : V) (R eta : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R)
    (hxstar : ‖xstar‖ ≤ 1) (hgap : eta < f x - f xstar) :
    eta / (R + 1) < ‖grad x‖ := by
  have hf := PaperSmooth.convex_first_order f grad hg hc x xstar
  have hid : inner ℝ (grad x) (xstar - x) = -inner ℝ (grad x) (x - xstar) := by
    simp only [inner_sub_right]
    ring
  rw [hid] at hf
  have hi := real_inner_le_norm (grad x) (x - xstar)
  have hn : ‖x - xstar‖ ≤ R + 1 := (norm_sub_le x xstar).trans (add_le_add hx hxstar)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (grad x))
  apply (div_lt_iff₀ (by linarith : 0 < R + 1)).mpr
  nlinarith

lemma direction_descent (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (x next xstar v : V) (err tolerance : ℝ) (hmin : ∀ y, f xstar ≤ f y)
    (hgap : f x - f xstar ≤ 1 / 2) (hv : ‖v‖ = 1)
    (hd : ‖v - NormedSpace.normalize (grad x)‖ ≤ err) (herr : err ≤ 1 / 4)
    (hline : ∀ t ∈ Icc (0 : ℝ) 1, f next ≤ f (x - t • v) + tolerance) :
    f x - f next ≥ (9 / 16 : ℝ) * ‖grad x‖ ^ 2 / 2 - tolerance := by
  let q := inner ℝ (grad x) v
  let m := ‖grad x‖
  have hm0 : 0 ≤ m := norm_nonneg _
  have hmsq := PaperSmooth.normalized_gradient_gap f grad hg hLip xstar x hmin
  have hm1 : m ≤ 1 := by dsimp [m]; nlinarith
  have hi := direction_inner_bounds (grad x) v err hv hd
  have hqlo : (3 / 4 : ℝ) * m ≤ q := by
    dsimp [m, q]
    nlinarith [mul_nonneg (sub_nonneg.mpr herr) hm0]
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q ≤ 1 := hi.2.trans hm1
  have hsearch := hline q ⟨hq0, hq1⟩
  have ht := PaperSmooth.descent_upper f grad hg 1 hLip x (x - q • v)
  have hsub : (x - q • v) - x = (-q) • v := by module
  rw [hsub, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs] at ht
  norm_num at ht
  have hqsql : (9 / 16 : ℝ) * m ^ 2 ≤ q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ q - 3 / 4 * m by linarith)
      (show 0 ≤ q + 3 / 4 * m by positivity)]
  change f x - f next ≥ (9 / 16 : ℝ) * m ^ 2 / 2 - tolerance
  change f (x - q • v) ≤ f x + -(q * q) + 1 / 2 * q ^ 2 at ht
  nlinarith

lemma approximate_optimum_kkt (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (K : Set V) (hK : Convex ℝ K) (x z : V) (hx : x ∈ K) (hz : z ∈ K)
    (tolerance R : ℝ) (htol : 0 < tolerance)
    (hsmall : Real.sqrt (2 * tolerance) ≤ 2 * R) (hdiam : ‖z - x‖ ≤ 2 * R)
    (happrox : ∀ u ∈ K, f x ≤ f u + tolerance) :
    inner ℝ (grad x) (x - z) ≤ 2 * R * Real.sqrt (2 * tolerance) := by
  have hcert := clipped_kkt_certificate (grad x) x z tolerance R htol hsmall hdiam
    (by
      intro t ht ht1
      have hmem : x + t • (z - x) ∈ K := by
        rw [show x + t • (z - x) = (1 - t) • x + t • z by module]
        exact hK hx hz (sub_nonneg.mpr ht1) ht.le (by ring)
      have ha := happrox _ hmem
      have hd := PaperSmooth.descent_upper f grad hg 1 hLip x (x + t • (z - x))
      rw [add_sub_cancel_left, real_inner_smul_right, norm_smul_of_nonneg ht.le] at hd
      norm_num at hd
      have hscalar : -tolerance - ‖z-x‖^2 * t^2 / 2 ≤ t * inner ℝ (grad x) (z-x) := by nlinarith
      have hdiv : (-tolerance-‖z-x‖^2*t^2/2)/t ≤ inner ℝ (grad x) (z-x) :=
        (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hscalar)
      calc
        -(tolerance / t + ‖z-x‖^2*t/2) = (-tolerance - ‖z-x‖^2*t^2/2)/t := by
          field_simp
          <;> ring
        _ ≤ _ := hdiv)
  have hi : inner ℝ (grad x) (x-z) = -inner ℝ (grad x) (z-x) := by
    simp only [inner_sub_right]
    ring
  rw [hi]
  linarith

lemma initial_gap (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : V) (hmin : ∀ y, f xstar ≤ f y) (hxstar : ‖xstar‖ ≤ 1) :
    f 0 - f xstar ≤ 1 / 2 := by
  have hh := PaperSmooth.gap_at_min f grad hg 1 hLip xstar 0 hmin
  simp only [zero_sub, norm_neg, NNReal.coe_one] at hh
  have hn := norm_nonneg xstar
  nlinarith

def potential (f : V → ℝ) (xstar x z : V) (k : ℕ) : ℝ :=
  weight k * (f x - f xstar) + ‖z - xstar‖ ^ 2 / 2

lemma one_step_potential (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (x next xstar z v : V) (k : ℕ)
    (hmin : ∀ y, f xstar ≤ f y) (hgap : f x - f xstar ≤ 1 / 2)
    (hv : ‖v‖ = 1) (hd : ‖v - NormedSpace.normalize (grad x)‖ ≤ delta k)
    (hline : ∀ t ∈ Icc (0 : ℝ) 1, f next ≤ f (x - t • v) + xi k)
    (hKKT : inner ℝ (grad x) (x - z) ≤ previousError k) :
    potential f xstar next (z - stepWeight (k + 1) • (‖grad x‖ • v)) (k + 1) ≤
      growth k * potential f xstar x z k + additiveError k := by
  let p := ‖grad x‖ • v
  have hp : ‖p‖ = ‖grad x‖ := by simp [p, norm_smul_of_nonneg (norm_nonneg (grad x)), hv]
  have herror := direction_error (grad x) v (delta k) hd
  have hdes := direction_descent f grad hg hLip x next xstar v (delta k) (xi k)
    hmin hgap hv hd (delta_le_quarter k) hline
  have hconv : inner ℝ (grad x) (z-xstar) ≥ f x-f xstar-previousError k := by
    have hf := PaperSmooth.convex_first_order f grad hg hc x xstar
    simp only [inner_sub_right] at hf hKKT ⊢
    linarith
  have hgapdes : (f x-f xstar)-(f next-f xstar) ≥
      (9 / 16 : ℝ)*‖grad x‖^2/2-xi k := by linarith
  have he := potential_expansion z p (grad x) xstar (weight k) (weight (k+1))
    (stepWeight (k+1)) (9/16) kap (f x-f xstar) (f next-f xstar)
    (xi k) (delta k) ‖grad x‖ (previousError k)
    (stepWeight_pos k).le (weight_nonneg _) (weight_step k) (weight_identity k)
    hp herror hgapdes hconv
  have hD : ‖z-xstar‖^2 ≤ 2*potential f xstar x z k := by
    have hp := mul_nonneg (weight_nonneg k) (sub_nonneg.mpr (hmin x))
    dsimp [potential]
    linarith
  have hw : stepWeight (k+1)^2 = (9/32:ℝ)*weight (k+1) := weight_identity k
  have hcnum : (9/16:ℝ)-kap = 9/32 := by norm_num [kap]
  rw [hcnum] at he
  have hr := potential_recurrence (potential f xstar x z k)
    (potential f xstar next (z-stepWeight (k+1) • p) (k+1))
    (weight (k+1)) (stepWeight (k+1)) (delta k) ‖grad x‖ ‖z-xstar‖
    (xi k) (previousError k) (previousError k)
    (weight_nonneg _) (stepWeight_pos k).le hw hD le_rfl he
  simpa only [potential, growth, additiveError, p, add_assoc] using hr

def historySpace (x v : ℕ → V) (k : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ ({x k} ∪ {u | ∃ i : ℕ, i ≤ k ∧ v i = u})

def historyBall (x v : ℕ → V) (k : ℕ) : Set V :=
  {u | u ∈ historySpace x v k ∧ ‖u‖ ≤ radius (k + 1)}

lemma direction_in_history (x v : ℕ → V) (i k : ℕ) (hi : i ≤ k) :
    v i ∈ historySpace x v k := by
  apply Submodule.subset_span
  exact Or.inr ⟨i, hi, rfl⟩

lemma historyBall_convex (x v : ℕ → V) (k : ℕ) : Convex ℝ (historyBall x v k) := by
  intro u hu w hw a b ha hb hab
  constructor
  · exact (historySpace x v k).add_mem ((historySpace x v k).smul_mem a hu.1)
      ((historySpace x v k).smul_mem b hw.1)
  · calc
      ‖a • u + b • w‖ ≤ ‖a • u‖ + ‖b • w‖ := norm_add_le _ _
      _ = a * ‖u‖ + b * ‖w‖ := by rw [norm_smul_of_nonneg ha, norm_smul_of_nonneg hb]
      _ ≤ a * radius (k+1) + b * radius (k+1) :=
        add_le_add (mul_le_mul_of_nonneg_left hu.2 ha) (mul_le_mul_of_nonneg_left hw.2 hb)
      _ = radius (k+1) := by rw [← add_mul, hab, one_mul]

def dual (grad : V → V) (x v : ℕ → V) : ℕ → V
  | 0 => 0
  | k + 1 => dual grad x v k - stepWeight (k+1) • (‖grad (x k)‖ • v k)

def trajectoryPotential (f : V → ℝ) (grad : V → V) (xstar : V) (x v : ℕ → V) (k : ℕ) : ℝ :=
  potential f xstar (x k) (dual grad x v k) k

lemma dual_in_history (grad : V → V) (x v : ℕ → V) (k : ℕ) :
    dual grad x v (k+1) ∈ historySpace x v k := by
  apply dual_full_history_membership (dual grad x v) v stepWeight (fun i => ‖grad (x i)‖)
    rfl (fun _ => rfl) (k+1) (historySpace x v k)
  intro i hi
  exact direction_in_history x v i k (by omega)

lemma trajectory_potential_start (f : V → ℝ) (grad : V → V) (xstar : V)
    (x v : ℕ → V) (hxstar : ‖xstar‖ ≤ 1) :
    trajectoryPotential f grad xstar x v 0 ≤ 1/2 := by
  dsimp [trajectoryPotential, potential, weight, dual]
  simp only [zero_mul, zero_sub, norm_neg, zero_add]
  have hn := norm_nonneg xstar
  nlinarith

lemma trajectory_kkt (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : V) (hmin : ∀ y, f xstar ≤ f y) (hxstar : ‖xstar‖ ≤ 1)
    (x v : ℕ → V) (hx0 : x 0 = 0) (N k : ℕ) (hk : k < N)
    (hfeasible : ∀ j ≤ N, ‖x j‖ ≤ radius j)
    (hspan : ∀ j < N, x (j+1) ∈ historySpace x v j)
    (happrox : ∀ j < N, ∀ u ∈ historyBall x v j, f (x (j+1)) ≤ f u + xi j)
    (hsmall : trajectoryPotential f grad xstar x v k < 2) :
    inner ℝ (grad (x k)) (x k - dual grad x v k) ≤ previousError k := by
  cases k with
  | zero => simp [hx0, dual, previousError]
  | succ j =>
    have hprev : j < N := by omega
    have hxn := hfeasible (j+1) (by omega)
    have hdual := dual_point_feasibility (dual grad x v (j+1)) xstar
      (weight (j+1)) (f (x (j+1))-f xstar)
      (trajectoryPotential f grad xstar x v (j+1)) hxstar (weight_nonneg _)
      (sub_nonneg.mpr (hmin _)) rfl hsmall
    have hzr : ‖dual grad x v (j+1)‖ ≤ radius (j+1) := by
      unfold radius
      push_cast
      linarith [hdual.2, Nat.cast_nonneg (α := ℝ) j]
    have hxmem : x (j+1) ∈ historyBall x v j := ⟨hspan j hprev, hxn⟩
    have hzmem : dual grad x v (j+1) ∈ historyBall x v j := ⟨dual_in_history grad x v j, hzr⟩
    have hdiam : ‖dual grad x v (j+1)-x (j+1)‖ ≤ 2*radius (j+1) :=
      (norm_sub_le _ _).trans (by linarith)
    have hh := approximate_optimum_kkt f grad hg hLip (historyBall x v j)
      (historyBall_convex x v j) (x (j+1)) (dual grad x v (j+1)) hxmem hzmem
      (xi j) (radius (j+1)) (xi_pos _) (xi_sqrt_small _) hdiam (happrox j hprev)
    rw [previousError_succ]
    exact hh

/-- Full finite-horizon analytic chain, under exactly the direction/affine/line
subroutine guarantees and feasibility/selection rules of the actual program.
No potential, cumulative error, or weight bounds are assumed here. -/
theorem accuracy_from_subroutines (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (xstar : V) (hmin : ∀ y, f xstar ≤ f y)
    (hxstar : ‖xstar‖ ≤ 1) (x v : ℕ → V) (hx0 : x 0 = 0) (Q : ℝ) (hQ : 0 < Q)
    (N : ℕ) (hNdef : N = ⌈(16/3:ℝ)*Real.sqrt Q⌉₊)
    (hfeasible : ∀ k ≤ N, ‖x k‖ ≤ radius k)
    (hspan : ∀ k < N, x (k+1) ∈ historySpace x v k)
    (hunit : ∀ k < N, ‖v k‖ = 1)
    (hdirection : ∀ k < N, (1/Q)/(radius k+1) ≤ ‖grad (x k)‖ →
      ‖v k-NormedSpace.normalize (grad (x k))‖ ≤ delta k)
    (haffine : ∀ k < N, ∀ u ∈ historyBall x v k, f (x (k+1)) ≤ f u+xi k)
    (hline : ∀ k < N, ∀ t ∈ Icc (0:ℝ) 1, f (x (k+1)) ≤ f (x k-t • v k)+xi k)
    (hmono : ∀ k < N, f (x (k+1)) ≤ f (x k)) :
    f (x N)-f xstar ≤ 1/Q := by
  classical
  have hanti := finite_antitone (fun k => f (x k)) N hmono
  by_cases hearly : ∃ k < N, f (x k)-f xstar ≤ 1/Q
  · obtain ⟨k,hk,hgood⟩ := hearly
    have hh := hanti k N hk.le le_rfl
    linarith
  · have hbad : ∀ k < N, 1/Q < f (x k)-f xstar := by
      intro k hk
      by_contra hn
      exact hearly ⟨k,hk,le_of_not_gt hn⟩
    have hhalf : ∀ k ≤ N, f (x k)-f xstar ≤ 1/2 := by
      intro k hk
      have hh := hanti 0 k (Nat.zero_le _) hk
      have hstart := initial_gap f grad hg hLip xstar hmin hxstar
      rw [hx0] at hh
      linarith
    let phi := trajectoryPotential f grad xstar x v
    have hstart : phi 0 ≤ 1/2 := trajectory_potential_start f grad xstar x v hxstar
    have hrec : ∀ k < N, phi k < 2 → phi (k+1) ≤ growth k * phi k + additiveError k := by
      intro k hk hsmall
      have hgrad := pre_success_gradient f grad hg hc (x k) xstar (radius k) (1/Q)
        (by unfold radius; positivity) (hfeasible k hk.le) hxstar (hbad k hk)
      have hd := hdirection k hk hgrad.le
      have hKKT := trajectory_kkt f grad hg hLip xstar hmin hxstar x v hx0 N k hk
        hfeasible hspan haffine hsmall
      have hh := one_step_potential f grad hg hc hLip (x k) (x (k+1)) xstar
        (dual grad x v k) (v k) k hmin (hhalf k hk.le) (hunit k hk) hd (hline k hk) hKKT
      simpa only [phi, trajectoryPotential, dual] using hh
    have hphi := (finite_potential_bounded phi N hstart hrec N le_rfl).2
    have hcount := ceil_iteration_adequacy Q hQ
    rw [← hNdef] at hcount
    have hw := weight_bounds.2 N hcount.2
    have hw' : (9/128:ℝ)*((N:ℝ)+1)^2 ≤ weight N := by
      unfold kap at hw
      nlinarith
    have hAgap : weight N*(f (x N)-f xstar) < 2 := by
      dsimp [phi, trajectoryPotential, potential] at hphi
      nlinarith [sq_nonneg ‖dual grad x v N-xstar‖]
    exact (final_accuracy (weight N) (f (x N)-f xstar) (N:ℝ) Q hQ (Nat.cast_nonneg _)
      hw' hAgap hcount.1).le

end Objective
end
end PaperFullHistory

end SnapshotModule_015
/- END full_history_analysis -/

/- BEGIN history_dimension -/
section SnapshotModule_016

namespace PaperFullHistory
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

lemma history_generators (x v : ℕ → V) (k : ℕ) :
    {x k} ∪ {u | ∃ i : ℕ, i ≤ k ∧ v i=u} =
      Set.range (Fin.cons (x k) (fun i : Fin (k+1) => v i.val)) := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | ⟨i,hi,heq⟩
    · exact ⟨0,by simpa only [Fin.cons_zero] using hy.symm⟩
    · refine ⟨(⟨i,by omega⟩ : Fin (k+1)).succ,?_⟩
      rw [Fin.cons_succ]
      exact heq
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl (by simp)
    · exact Or.inr ⟨j.val,by omega,by simp⟩

lemma history_dimension_bound (x v : ℕ → V) (k : ℕ) :
    Module.finrank ℝ (historySpace x v k) ≤ min (Module.finrank ℝ V) (k+2) := by
  apply le_min (Submodule.finrank_le _)
  rw [historySpace,history_generators]
  have h := finrank_range_le_card (R := ℝ) (Fin.cons (x k) (fun i : Fin (k+1) => v i.val))
  simpa only [Set.finrank,Fintype.card_fin] using h

lemma history_positive_dimension (x v : ℕ → V) (k : ℕ) (hv : ‖v k‖=1) :
    0 < Module.finrank ℝ (historySpace x v k) := by
  have hmem := direction_in_history x v k k le_rfl
  have hne : v k ≠ 0 := by intro hz; rw [hz,norm_zero] at hv; norm_num at hv
  have hnon : Nontrivial (historySpace x v k) := ⟨⟨⟨v k,hmem⟩,0,by
    intro hh
    have : v k=0 := congrArg Subtype.val hh
    exact hne this⟩⟩
  letI := hnon
  exact Module.finrank_pos

end
end PaperFullHistory

end SnapshotModule_016
/- END history_dimension -/

/- BEGIN full_history_program -/
section SnapshotModule_017

namespace PaperFullHistoryProgram
open Set PaperGDE PaperTrinary PaperFullHistory
open scoped RealInnerProductSpace
noncomputable section

structure State (n : ℕ) where
  point : Vec n
  directions : ℕ → Vec n

def initial {n : ℕ} : State n := ⟨0,fun _ => 0⟩

def stateSpace {n : ℕ} (x : Vec n) (v : ℕ → Vec n) (k : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ ({x} ∪ {u | ∃ i : ℕ, i ≤ k ∧ v i=u})

abbrev InnerProgram (n : ℕ) := (k : ℕ) → (x : Vec n) → (v : ℕ → Vec n) →
  PaperTrinary.Program n (Vec n)

def selectProgram {n : ℕ} (old candidate : Vec n) : PaperTrinary.Program n (Vec n) :=
  .ask (candidate,old) (fun r => .done (if r = .lt then candidate else old))

lemma select_cap {n : ℕ} (a b : Vec n) : PaperOracle.Program.Cap 1 (selectProgram a b) := by
  intro r
  trivial

lemma select_mem {n : ℕ} (C : PaperTrinary.Oracle n) {K : Set (Vec n)} (a b : Vec n)
    (ha : a ∈ K) (hb : b ∈ K) : PaperOracle.Program.run C (selectProgram a b) ∈ K := by
  simp only [selectProgram,PaperOracle.Program.run]
  split_ifs <;> assumption

lemma select_values {n : ℕ} (f : Vec n → ℝ) (a b : Vec n) :
    f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (selectProgram a b)) ≤ f a ∧
    f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (selectProgram a b)) ≤ f b := by
  simp only [selectProgram,PaperOracle.Program.run,PaperOracle.comparisonOracle]
  split_ifs with h
  · exact ⟨((PaperOracle.realOrder_eq_lt_iff _ _).mp h).le,le_rfl⟩
  · exact ⟨le_rfl,le_of_not_gt (fun hlt => h ((PaperOracle.realOrder_eq_lt_iff _ _).mpr hlt))⟩

def directionProgram {n : ℕ} (Q : ℝ) (k : ℕ) (x : Vec n) : PaperTrinary.Program n (Vec n) :=
  liftGDE (gdeProgram x (delta k) ((1/Q)/(radius k+1)))

def stepProgram {n : ℕ} (inner : InnerProgram n) (Q : ℝ) (k : ℕ) (s : State n) :
    PaperTrinary.Program n (State n) :=
  PaperOracle.Program.bind (directionProgram Q k s.point) (fun v =>
    let vs := Function.update s.directions k v
    PaperOracle.Program.bind (inner k s.point vs) (fun y =>
      PaperOracle.Program.bind (PaperOuterLine.lineProgram s.point v (radius k+2) (xi k)) (fun l =>
        PaperOracle.Program.bind (selectProgram s.point y) (fun b =>
          PaperOracle.Program.bind (selectProgram b l) (fun best => .done ⟨best,vs⟩)))))

def loopProgram {n : ℕ} (inner : InnerProgram n) (Q : ℝ) :
    (k m : ℕ) → State n → PaperTrinary.Program n (State n)
  | _,0,s => .done s
  | k,m+1,s => PaperOracle.Program.bind (stepProgram inner Q k s)
      (fun next => loopProgram inner Q (k+1) m next)

def directionValue {n : ℕ} (C : PaperTrinary.Oracle n) (Q : ℝ) (k : ℕ) (s : State n) : Vec n :=
  PaperOracle.Program.run C (directionProgram Q k s.point)

def updatedDirections {n : ℕ} (C : PaperTrinary.Oracle n) (Q : ℝ) (k : ℕ) (s : State n) : ℕ → Vec n :=
  Function.update s.directions k (directionValue C Q k s)

def innerValue {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k : ℕ) (s : State n) : Vec n :=
  PaperOracle.Program.run C (inner k s.point (updatedDirections C Q k s))

def lineValue {n : ℕ} (C : PaperTrinary.Oracle n) (Q : ℝ) (k : ℕ) (s : State n) : Vec n :=
  PaperOracle.Program.run C (PaperOuterLine.lineProgram s.point (directionValue C Q k s)
    (radius k+2) (xi k))

def stepState {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k : ℕ) (s : State n) : State n :=
  ⟨PaperOracle.Program.run C (selectProgram
      (PaperOracle.Program.run C (selectProgram s.point (innerValue C inner Q k s)))
      (lineValue C Q k s)),updatedDirections C Q k s⟩

lemma step_eval {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k : ℕ) (s : State n) :
    PaperOracle.Program.run C (stepProgram inner Q k s)=stepState C inner Q k s := by
  simp only [stepProgram,PaperOracle.Program.run_bind,PaperOracle.Program.run]
  rfl

def forward {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n) (Q : ℝ) : ℕ → State n
  | 0 => initial
  | k+1 => stepState C inner Q k (forward C inner Q k)

def trajectory {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n) (Q : ℝ) (k : ℕ) : Vec n :=
  (forward C inner Q k).point

def directions {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n) (Q : ℝ) (k : ℕ) : Vec n :=
  directionValue C Q k (forward C inner Q k)

lemma loop_eval {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k m : ℕ) :
    PaperOracle.Program.run C (loopProgram inner Q k m (forward C inner Q k)) =
      forward C inner Q (k+m) := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    simp only [loopProgram,PaperOracle.Program.run_bind,step_eval]
    change PaperOracle.Program.run C (loopProgram inner Q (k+1) m (forward C inner Q (k+1))) = _
    rw [ih]
    congr 1
    omega

lemma direction_unit {n : ℕ} (C : PaperTrinary.Oracle n) (Q : ℝ) (k : ℕ) (s : State n) :
    ‖directionValue C Q k s‖=1 := by
  rw [directionValue,directionProgram,liftGDE_run]
  exact gdeProgram_total_unit _ _ _ _

lemma forward_history {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k i : ℕ) (hi : i<k) :
    (forward C inner Q k).directions i = directions C inner Q i := by
  induction k with
  | zero => omega
  | succ k ih =>
    change Function.update (forward C inner Q k).directions k (directions C inner Q k) i = _
    by_cases heq : i=k
    · subst i
      simp
    · rw [Function.update_of_ne heq]
      exact ih (by omega)

lemma updated_history {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k i : ℕ) (hi : i≤k) :
    updatedDirections C Q k (forward C inner Q k) i = directions C inner Q i := by
  by_cases heq : i=k
  · subst i
    simp [updatedDirections,directions]
  · rw [updatedDirections,Function.update_of_ne heq]
    exact forward_history C inner Q k i (by omega)

lemma actual_history_space {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (Q : ℝ) (k : ℕ) :
    stateSpace (trajectory C inner Q k) (updatedDirections C Q k (forward C inner Q k)) k =
      historySpace (trajectory C inner Q) (directions C inner Q) k := by
  unfold stateSpace historySpace
  congr 1
  ext u
  constructor
  · rintro (h | ⟨i,hi,heq⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi,by rw [← updated_history C inner Q k i hi]; exact heq⟩
  · rintro (h | ⟨i,hi,heq⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi,by rw [updated_history C inner Q k i hi]; exact heq⟩

def stepBudget (n : ℕ) (innerCap : ℕ → ℕ) (k : ℕ) : ℕ :=
  2*(n+1)-1+n*rounds n (delta k)+innerCap k+
    PaperLineSearchComplete.horizon (radius k+2) (xi k)+2

lemma step_public_cap {n : ℕ} (inner : InnerProgram n) (innerCap : ℕ → ℕ)
    (hinner : ∀ k x vs, PaperOracle.Program.Cap (innerCap k) (inner k x vs))
    (Q : ℝ) (k : ℕ) (s : State n) :
    PaperOracle.Program.Cap (stepBudget n innerCap k) (stepProgram inner Q k s) := by
  have h : PaperOracle.Program.Cap
      ((2*(n+1)-1+n*rounds n (delta k))+(innerCap k+
        (PaperLineSearchComplete.horizon (radius k+2) (xi k)+2)))
      (stepProgram inner Q k s) := by
    unfold stepProgram directionProgram
    apply PaperOracle.Program.cap_bind _ _ (gde_cap _ _ _)
    intro v
    apply PaperOracle.Program.cap_bind _ _ (hinner _ _ _)
    intro y
    apply PaperOracle.Program.cap_bind _ _ (PaperOuterLine.line_cap _ _ _ _)
    intro l
    apply PaperOracle.Program.cap_bind _ _ (select_cap _ _) (b := 1)
    intro b
    exact PaperOracle.Program.cap_bind _ _ (select_cap _ _) (b := 0) (by intro a; trivial)
  convert h using 1
  unfold stepBudget
  omega

lemma loop_public_cap {n : ℕ} (inner : InnerProgram n) (innerCap : ℕ → ℕ)
    (hinner : ∀ k x vs, PaperOracle.Program.Cap (innerCap k) (inner k x vs))
    (Q : ℝ) (k m : ℕ) (s : State n) :
    PaperOracle.Program.Cap (∑ i ∈ Finset.range m, stepBudget n innerCap (k+i))
      (loopProgram inner Q k m s) := by
  induction m generalizing k s with
  | zero => trivial
  | succ m ih =>
    have h := PaperOracle.Program.cap_bind _ _ (step_public_cap inner innerCap hinner Q k s)
      (fun snext => ih (k+1) snext)
    convert h using 1
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
    all_goals rfl

end
end PaperFullHistoryProgram

end SnapshotModule_017
/- END full_history_program -/

/- BEGIN full_history_implementation -/
section SnapshotModule_018

namespace PaperFullHistoryProgram
open Set PaperGDE PaperTrinary PaperFullHistory
open scoped RealInnerProductSpace
noncomputable section

abbrev InnerFeasible {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n) : Prop :=
  ∀ k x vs, ‖x‖ ≤ radius k →
    PaperOracle.Program.run C (inner k x vs) ∈ stateSpace x vs k ∧
      ‖PaperOracle.Program.run C (inner k x vs)‖ ≤ radius (k+1)

abbrev InnerAccurate {n : ℕ} (f : Vec n → ℝ) (inner : InnerProgram n) : Prop :=
  ∀ k x vs, ‖x‖ ≤ radius k → ∀ u, u ∈ stateSpace x vs k → ‖u‖ ≤ radius (k+1) →
    f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (inner k x vs)) ≤ f u+xi k

lemma radius_succ (k : ℕ) : radius (k+1)=radius k+1 := by simp [radius]; ring

lemma step_feasible {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (hinner : InnerFeasible C inner) (Q : ℝ) (k : ℕ) (s : State n) (hs : ‖s.point‖ ≤ radius k) :
    (stepState C inner Q k s).point ∈ stateSpace s.point (updatedDirections C Q k s) k ∧
      ‖(stepState C inner Q k s).point‖ ≤ radius (k+1) := by
  let U := stateSpace s.point (updatedDirections C Q k s) k
  let K : Set (Vec n) := {u | u ∈ U ∧ ‖u‖ ≤ radius (k+1)}
  have hp : s.point ∈ K := by
    refine ⟨Submodule.subset_span (Or.inl rfl),?_⟩
    rw [radius_succ]
    linarith
  have hy : innerValue C inner Q k s ∈ K := hinner k s.point _ hs
  have hv : directionValue C Q k s ∈ U := by
    apply Submodule.subset_span
    exact Or.inr ⟨k,le_rfl,by simp [updatedDirections]⟩
  obtain ⟨t,ht,heq⟩ := PaperOuterLine.lineProgram_parameter C s.point (directionValue C Q k s)
    (radius k+2) (xi k)
  have hl : lineValue C Q k s ∈ K := by
    change lineValue C Q k s ∈ U ∧ ‖lineValue C Q k s‖ ≤ radius (k+1)
    have hline : lineValue C Q k s=PaperOuterLine.linePoint s.point (directionValue C Q k s) t := heq
    rw [hline]
    refine ⟨U.sub_mem hp.1 (U.smul_mem t hv),?_⟩
    rw [radius_succ]
    exact PaperOuterLine.line_point_norm _ _ _ _ hs (direction_unit C Q k s) ht
  exact select_mem C _ _ (select_mem C _ _ hp hy) hl

lemma trajectory_feasible {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (hinner : InnerFeasible C inner) (Q : ℝ) (k : ℕ) :
    ‖trajectory C inner Q k‖ ≤ radius k := by
  induction k with
  | zero => norm_num [trajectory,forward,initial,radius]
  | succ k ih => exact (step_feasible C inner hinner Q k (forward C inner Q k) ih).2

lemma trajectory_span {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n)
    (hinner : InnerFeasible C inner) (Q : ℝ) (k : ℕ) :
    trajectory C inner Q (k+1) ∈ historySpace (trajectory C inner Q) (directions C inner Q) k := by
  rw [← actual_history_space]
  exact (step_feasible C inner hinner Q k (forward C inner Q k)
    (trajectory_feasible C inner hinner Q k)).1

lemma step_values {n : ℕ} (f : Vec n → ℝ) (inner : InnerProgram n)
    (Q : ℝ) (k : ℕ) (s : State n) :
    f (stepState (PaperOracle.comparisonOracle f) inner Q k s).point ≤ f s.point ∧
    f (stepState (PaperOracle.comparisonOracle f) inner Q k s).point ≤
      f (innerValue (PaperOracle.comparisonOracle f) inner Q k s) ∧
    f (stepState (PaperOracle.comparisonOracle f) inner Q k s).point ≤
      f (lineValue (PaperOracle.comparisonOracle f) Q k s) := by
  let C := PaperOracle.comparisonOracle f
  let b := PaperOracle.Program.run C (selectProgram s.point (innerValue C inner Q k s))
  have hfirst := select_values f s.point (innerValue C inner Q k s)
  have hlast := select_values f b (lineValue C Q k s)
  exact ⟨hlast.1.trans hfirst.1,hlast.1.trans hfirst.2,hlast.2⟩

lemma trajectory_direction_accuracy {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (inner : InnerProgram n) (Q : ℝ) (hQ : 0 < Q) (k : ℕ)
    (hpremise : (1/Q)/(radius k+1) ≤ ‖grad (trajectory (PaperOracle.comparisonOracle f) inner Q k)‖) :
    ‖directions (PaperOracle.comparisonOracle f) inner Q k-
      NormedSpace.normalize (grad (trajectory (PaperOracle.comparisonOracle f) inner Q k))‖ ≤ delta k := by
  unfold directions directionValue directionProgram
  rw [liftGDE_run]
  exact (full_gde_certificate f grad hg hLip (PaperTrinary.comparison_correct f) _
    (delta k) ((1/Q)/(radius k+1)) (delta_pos k)
    ((delta_le_quarter k).trans (by norm_num)) (by unfold radius; positivity) hpremise).2.1

def iterationCount (Q : ℝ) : ℕ := ⌈(16/3:ℝ)*Real.sqrt Q⌉₊

def algorithm {n : ℕ} (inner : InnerProgram n) (Q : ℝ) : PaperTrinary.Program n (Vec n) :=
  PaperOracle.Program.bind (loopProgram inner Q 0 (iterationCount Q) initial) (fun s => .done s.point)

lemma algorithm_eval {n : ℕ} (C : PaperTrinary.Oracle n) (inner : InnerProgram n) (Q : ℝ) :
    PaperOracle.Program.run C (algorithm inner Q)=trajectory C inner Q (iterationCount Q) := by
  simp only [algorithm,PaperOracle.Program.run_bind,PaperOracle.Program.run]
  have h := loop_eval C inner Q 0 (iterationCount Q)
  simpa only [forward,Nat.zero_add,trajectory] using congrArg State.point h

lemma algorithm_public_cap {n : ℕ} (inner : InnerProgram n) (innerCap : ℕ → ℕ)
    (hinner : ∀ k x vs, PaperOracle.Program.Cap (innerCap k) (inner k x vs)) (Q : ℝ) :
    PaperOracle.Program.Cap (∑ k ∈ Finset.range (iterationCount Q),stepBudget n innerCap k)
      (algorithm inner Q) := by
  have h := PaperOracle.Program.cap_bind _ (fun s => PaperOracle.Program.done s.point)
    (loop_public_cap inner innerCap hinner Q 0 (iterationCount Q) initial)
    (b := 0) (by intro s; trivial)
  simpa only [algorithm,Nat.zero_add,Nat.add_zero] using h

/-- End-to-end outer finite-program correctness. Inner feasibility and accuracy
are supplied by the actual BALL-OPT program in the separate assembly module. -/
theorem accuracy_from_actual_inner {n : ℕ}
    (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (xstar : Vec n)
    (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (inner : InnerProgram n) (hfeasible : InnerFeasible (PaperOracle.comparisonOracle f) inner)
    (haccurate : InnerAccurate f inner) (Q : ℝ) (hQ : 0 < Q) :
    f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (algorithm inner Q))-f xstar ≤ 1/Q := by
  let C := PaperOracle.comparisonOracle f
  let x := trajectory C inner Q
  let v := directions C inner Q
  rw [algorithm_eval]
  apply accuracy_from_subroutines f grad hg hc hLip xstar hmin hstar x v rfl Q hQ
    (iterationCount Q) rfl
  · intro k hk; exact trajectory_feasible C inner hfeasible Q k
  · intro k hk; exact trajectory_span C inner hfeasible Q k
  · intro k hk; exact direction_unit C Q k (forward C inner Q k)
  · intro k hk hpremise; exact trajectory_direction_accuracy f grad hg hLip inner Q hQ k hpremise
  · intro k hk u hu
    have hs := trajectory_feasible C inner hfeasible Q k
    have hh := haccurate k (x k) (updatedDirections C Q k (forward C inner Q k)) hs u
      (by rw [actual_history_space]; exact hu.1) hu.2
    exact (step_values f inner Q k (forward C inner Q k)).2.1.trans hh
  · intro k hk t ht
    have hs := trajectory_feasible C inner hfeasible Q k
    have hr : 0 ≤ radius k := by unfold radius; positivity
    have htol : xi k ≤ radius k+2 := by
      have hx := xi_le_nu k
      unfold nu radius at *
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hh := PaperOuterLine.lineProgram_accuracy f grad hg hc hLip xstar (x k) (v k)
      hmin hstar (radius k) (xi k) hr hs (direction_unit C Q k (forward C inner Q k)) (xi_pos k) htol t ht
    exact (step_values f inner Q k (forward C inner Q k)).2.2.trans hh
  · intro k hk
    exact (step_values f inner Q k (forward C inner Q k)).1

end
end PaperFullHistoryProgram

end SnapshotModule_018
/- END full_history_implementation -/

/- BEGIN grunbaum_development -/
section SnapshotModule_019

/- Work toward the centroid halfspace theorem. No custom axioms or placeholders.
   The one-dimensional theorem below has explicit analytic CDF-shape hypotheses;
   the high-dimensional convex-volume-to-shape bridge is NOT assumed proved. -/

namespace GrunbaumDevelopment

open Set MeasureTheory
open scoped Topology ENNReal

/-- A concave differentiable scalar function lies below its tangent at zero. -/
theorem concave_tangent_at_zero {g : ℝ → ℝ} {a b slope0 : ℝ}
    (ha : a < 0) (hb : 0 < b) (hg : ConcaveOn ℝ (Ioo a b) g)
    (hderiv : HasDerivAt g slope0 0) :
    ∀ x ∈ Ioo a b, g x ≤ g 0+slope0*x := by
  intro x hx
  have hz : (0 : ℝ) ∈ Ioo a b := ⟨ha,hb⟩
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hs := hg.le_slope_of_hasDerivAt hx hz hneg hderiv
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (by linarith : (0 : ℝ) < 0-x)).mp hs
    nlinarith
  · subst x
    simp
  · have hs := hg.slope_le_of_hasDerivAt hz hx hpos hderiv
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (by linarith : (0 : ℝ) < x-0)).mp hs
    nlinarith

/-- The CDF log moment equals -1. Its value is derived by monotone change of
variables, not supplied as a hypothesis. -/
theorem cdf_log_moment {F density : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt F (density x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ density x)
    (hFa : F a=0) (hFb : F b=1) :
    (∫ x in a..b, density x*Real.log (F x)) = -1 := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := Real.log) hF hderiv hpos
  simpa [Function.comp_apply, smul_eq_mul, hFa,hFb, integral_log] using h

theorem cdf_density_mass {F density : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt F (density x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ density x)
    (hFa : F a=0) (hFb : F b=1) :
    (∫ x in a..b, density x) = 1 := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun _ : ℝ => (1 : ℝ)) hF hderiv hpos
  simpa [Function.comp_apply, smul_eq_mul, hFa,hFb] using h

theorem integrable_cdf_log_moment {F density : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt F (density x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ density x)
    (hFa : F a=0) (hFb : F b=1) :
    IntervalIntegrable (fun x => density x*Real.log (F x)) volume a b := by
  have h := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (g := Real.log) hF hderiv hpos
  apply h.mpr
  simpa [hFa,hFb] using (intervalIntegrable_log' :
    IntervalIntegrable Real.log volume (0 : ℝ) 1)

/-- Dimension-free one-dimensional analytic core: a normalized differentiable
CDF whose logarithm is concave has at least exp(-1) mass below its zero mean.
Every regularity/shape hypothesis is explicit; no mass lower bound is assumed. -/
theorem log_concave_cdf_mean_zero_mass_bound
    {F density : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (hF : ContinuousOn F (uIcc a b))
    (hdensity : ContinuousOn density (uIcc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (density x) x)
    (hnonneg : ∀ x ∈ Ioo a b, 0 ≤ density x)
    (hFpos : ∀ x ∈ Ioo a b, 0 < F x)
    (hFa : F a=0) (hFb : F b=1)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (F x)))
    (hmean : (∫ x in a..b, x*density x) = 0) :
    Real.exp (-1) ≤ F 0 := by
  have hab : a ≤ b := by linarith
  have hdr : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt F (density x) x := by
    simpa [min_eq_left hab,max_eq_right hab] using hderiv
  have hnn : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ density x := by
    simpa [min_eq_left hab,max_eq_right hab] using hnonneg
  have hmass := cdf_density_mass hF hdr hnn hFa hFb
  have hlogmass := cdf_log_moment hF hdr hnn hFa hFb
  have hintlog := integrable_cdf_log_moment hF hdr hnn hFa hFb
  have hintdensity : IntervalIntegrable density volume a b :=
    hdensity.intervalIntegrable
  have hintmoment : IntervalIntegrable (fun x => x*density x) volume a b :=
    (continuous_id.continuousOn.mul hdensity).intervalIntegrable
  have hzero : (0 : ℝ) ∈ Ioo a b := ⟨ha,hb⟩
  have hFzero : 0 < F 0 := hFpos 0 hzero
  let slope0 := density 0/F 0
  have hlogderiv : HasDerivAt (fun x => Real.log (F x)) slope0 0 :=
    (hderiv 0 hzero).log hFzero.ne'
  have htangent := concave_tangent_at_zero ha hb hshape hlogderiv
  have hupperInt : IntervalIntegrable
      (fun x => Real.log (F 0)*density x+slope0*(x*density x)) volume a b :=
    (hintdensity.const_mul _).add (hintmoment.const_mul _)
  have hupper : (∫ x in a..b, density x*Real.log (F x)) ≤
      ∫ x in a..b, Real.log (F 0)*density x+slope0*(x*density x) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab hintlog hupperInt
    intro x hx
    have hmul := mul_le_mul_of_nonneg_left (htangent x hx) (hnonneg x hx)
    nlinarith
  rw [intervalIntegral.integral_add (hintdensity.const_mul _) (hintmoment.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    hmass,hmean] at hupper
  have hlogbound : (-1 : ℝ) ≤ Real.log (F 0) := by
    rw [hlogmass] at hupper
    nlinarith
  have h := Real.exp_le_exp.mpr hlogbound
  simpa [Real.exp_log hFzero] using h

/-- The geometric cap-mixture inclusion that precedes Brunn-Minkowski. -/
theorem convex_cap_mixture
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} (hK : Convex ℝ K) (ell : E →ₗ[ℝ] ℝ)
    {s t alpha beta : ℝ} (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hab : alpha+beta=1) {x y : E}
    (hx : x ∈ K ∧ ell x ≤ s) (hy : y ∈ K ∧ ell y ≤ t) :
    alpha • x+beta • y ∈ K ∧
      ell (alpha • x+beta • y) ≤ alpha*s+beta*t := by
  refine ⟨hK hx.1 hy.1 ha hb hab, ?_⟩
  simp only [map_add,map_smul,smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
    (mul_le_mul_of_nonneg_left hy.2 hb)

/-- Scalar projection of a probability measure, centered at its actual Bochner
centroid, has mean zero. This supplies the centroid part of the slice bridge. -/
theorem centered_projection_mean_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (ell : E →L[ℝ] ℝ) (hidentity : Integrable (fun x : E => x) mu) :
    (∫ x, ell (x-(∫ y, y ∂mu)) ∂mu) = 0 := by
  simp_rw [map_sub]
  rw [integral_sub (ell.integrable_comp hidentity) (integrable_const _),
    ell.integral_comp_comm hidentity]
  simp

theorem projection_halfspace_mass
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) (ell : E →L[ℝ] ℝ) (t : ℝ) :
    mu.map ell (Iic t) = mu {x | ell x ≤ t} := by
  rw [Measure.map_apply ell.measurable measurableSet_Iic]
  rfl


/-- Log-concavity of a positive differentiable density controls the curvature of
its primitive. The CDF curvature bound is proved by integrating score monotonicity. -/
theorem log_concave_density_cdf_curvature
    {F density densityPrime : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hdensity : ContinuousOn density (Icc a b))
    (hdensityPrime : IntervalIntegrable densityPrime volume a b)
    (hFderiv : ∀ x ∈ Ioo a b, HasDerivAt F (density x) x)
    (hdensityDeriv : ∀ x ∈ Ioo a b, HasDerivAt density (densityPrime x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hleft : 0 ≤ density a) (hFa : F a=0)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (density x))) :
    ∀ x ∈ Ioo a b, densityPrime x*F x-(density x)^2 ≤ 0 := by
  have hscore : AntitoneOn (fun x => densityPrime x/density x) (Ioo a b) := by
    have hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ (fun y => Real.log (density y)) x := by
      intro x hx
      exact ((hdensityDeriv x hx).log (hpos x hx).ne').differentiableAt
    have h := hshape.antitoneOn_deriv hd
    intro x hx y hy hxy
    have hh := h hx hy hxy
    rw [((hdensityDeriv x hx).log (hpos x hx).ne').deriv,
      ((hdensityDeriv y hy).log (hpos y hy).ne').deriv] at hh
    exact hh
  intro x hx
  have hax : a ≤ x := hx.1.le
  have hsub : Icc a x ⊆ Icc a b := by
    intro t ht
    exact ⟨ht.1,ht.2.trans hx.2.le⟩
  have hpc : ContinuousOn density (Icc a x) := hdensity.mono hsub
  have hfi : IntervalIntegrable density volume a x := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hax] using hpc
  have hfpi : IntervalIntegrable densityPrime volume a x := by
    apply hdensityPrime.mono_set
    simpa [uIcc_of_le hax,uIcc_of_le hab.le] using hsub
  have hdf : ∀ t ∈ Ioo a x, HasDerivAt F (density t) t := by
    intro t ht
    exact hFderiv t ⟨ht.1,ht.2.trans hx.2⟩
  have hdp : ∀ t ∈ Ioo a x, HasDerivAt density (densityPrime t) t := by
    intro t ht
    exact hdensityDeriv t ⟨ht.1,ht.2.trans hx.2⟩
  have hintF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax
    (hF.mono hsub) hdf hfi
  have hintp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax hpc hdp hfpi
  have hbound : (∫ t in a..x, densityPrime x*density t) ≤
      ∫ t in a..x, density x*densityPrime t := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hax
      (hfi.const_mul _) (hfpi.const_mul _)
    intro t ht
    have ht' : t ∈ Ioo a b := ⟨ht.1,ht.2.trans hx.2⟩
    have hh := hscore ht' hx ht.2.le
    have hh' := (div_le_div_iff₀ (hpos x hx) (hpos t ht')).mp hh
    nlinarith
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    hintF,hintp,hFa] at hbound
  have hnonneg : 0 ≤ density x*density a := mul_nonneg (hpos x hx).le hleft
  nlinarith

/-- The smooth positive-density log-concavity to CDF log-concavity bridge. -/
theorem log_concave_density_implies_log_concave_cdf
    {F density densityPrime : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hdensity : ContinuousOn density (Icc a b))
    (hdensityPrime : IntervalIntegrable densityPrime volume a b)
    (hFderiv : ∀ x ∈ Ioo a b, HasDerivAt F (density x) x)
    (hdensityDeriv : ∀ x ∈ Ioo a b, HasDerivAt density (densityPrime x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hFpos : ∀ x ∈ Ioo a b, 0 < F x)
    (hleft : 0 ≤ density a) (hFa : F a=0)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (density x))) :
    ConcaveOn ℝ (Ioo a b) (fun x => Real.log (F x)) := by
  have hcurvature := log_concave_density_cdf_curvature hab hF hdensity hdensityPrime
    hFderiv hdensityDeriv hpos hleft hFa hshape
  have hlogcont : ContinuousOn (fun x => Real.log (F x)) (Ioo a b) :=
    (hF.mono Ioo_subset_Icc_self).log (fun x hx => (hFpos x hx).ne')
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioo a b) hlogcont
    (f' := fun x => density x/F x)
    (f'' := fun x => (densityPrime x*F x-(density x)^2)/(F x)^2)
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa using hx
    exact ((hFderiv x hx').log (hFpos x hx').ne').hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa using hx
    have h := (hdensityDeriv x hx').fun_div (hFderiv x hx') (hFpos x hx').ne'
    convert h.hasDerivWithinAt (s := interior (Ioo a b)) using 1 <;>
      first | rfl | exact Subsingleton.elim _ _ | ring
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa using hx
    exact div_nonpos_of_nonpos_of_nonneg (hcurvature x hx') (sq_nonneg _)

/-- A primitive of a positive density, starting from zero, is positive inside
its support. This removes an otherwise redundant CDF hypothesis. -/
theorem primitive_positive_of_density_positive
    {F density : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hFderiv : ∀ x ∈ Ioo a b, HasDerivAt F (density x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x) (hFa : F a=0) :
    ∀ x ∈ Ioo a b, 0 < F x := by
  have hstrict : StrictMonoOn F (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hF
    intro x hx
    have hx' : x ∈ Ioo a b := by simpa using hx
    rw [(hFderiv x hx').deriv]
    exact hpos x hx'
  intro x hx
  have h := hstrict (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
    (show x ∈ Icc a b from ⟨hx.1.le,hx.2.le⟩) hx.1
  simpa [hFa] using h

/-- A genuine smooth log-concave-density mean-zero mass theorem. The CDF
log-concavity used by the preceding analytic argument is now derived rather
than included among the premises. -/
theorem smooth_log_concave_density_mean_zero_mass_bound
    {F density densityPrime : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (hF : ContinuousOn F (Icc a b))
    (hdensity : ContinuousOn density (Icc a b))
    (hdensityPrime : IntervalIntegrable densityPrime volume a b)
    (hFderiv : ∀ x ∈ Ioo a b, HasDerivAt F (density x) x)
    (hdensityDeriv : ∀ x ∈ Ioo a b, HasDerivAt density (densityPrime x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hleft : 0 ≤ density a) (hFa : F a=0) (hFb : F b=1)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (density x)))
    (hmean : (∫ x in a..b, x*density x) = 0) :
    Real.exp (-1) ≤ F 0 := by
  have hab : a < b := lt_trans ha hb
  have hFpos := primitive_positive_of_density_positive hab hF hFderiv hpos hFa
  have hCDFshape := log_concave_density_implies_log_concave_cdf hab hF hdensity hdensityPrime
    hFderiv hdensityDeriv hpos hFpos hleft hFa hshape
  apply log_concave_cdf_mean_zero_mass_bound ha hb
    (by simpa [uIcc_of_le hab.le] using hF)
    (by simpa [uIcc_of_le hab.le] using hdensity)
    hFderiv (fun x hx => (hpos x hx).le) hFpos hFa hFb hCDFshape hmean

theorem log_of_positive_concave {S : Set ℝ} {G : ℝ → ℝ}
    (hG : ConcaveOn ℝ S G) (hpos : ∀ x ∈ S, 0 < G x) :
    ConcaveOn ℝ S (fun x => Real.log (G x)) := by
  refine ⟨hG.1, ?_⟩
  intro x hx y hy alpha beta ha hb hab
  have hmix := hG.2 hx hy ha hb hab
  have hmixpos : 0 < alpha • G x+beta • G y :=
    (convex_Ioi (0 : ℝ)) (hpos x hx) (hpos y hy) ha hb hab
  have hlogmix := strictConcaveOn_log_Ioi.concaveOn.2
    (hpos x hx) (hpos y hy) ha hb hab
  exact hlogmix.trans (Real.log_le_log hmixpos hmix)

theorem log_power_of_positive_concave {S : Set ℝ} {G : ℝ → ℝ}
    (hG : ConcaveOn ℝ S G) (hpos : ∀ x ∈ S, 0 < G x) (dimension : ℕ) :
    ConcaveOn ℝ S (fun x => Real.log ((G x)^dimension)) := by
  have hlog := log_of_positive_concave hG hpos
  have hscaled := hlog.smul (Nat.cast_nonneg (α := ℝ) dimension)
  simpa [Real.log_pow,smul_eq_mul] using hscaled


/-- Reflection yields the upper as well as lower dimension-free mass bound for
smooth positive log-concave densities. This is a one-dimensional theorem, not
an assertion that arbitrary convex-body marginals already meet the hypotheses. -/
theorem smooth_log_concave_density_two_sided_centroid_bound
    {F density densityPrime : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (hF : ContinuousOn F (Icc a b))
    (hdensity : ContinuousOn density (Icc a b))
    (hdensityPrime : IntervalIntegrable densityPrime volume a b)
    (hFderiv : ∀ x ∈ Ioo a b, HasDerivAt F (density x) x)
    (hdensityDeriv : ∀ x ∈ Ioo a b, HasDerivAt density (densityPrime x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hleft : 0 ≤ density a) (hright : 0 ≤ density b)
    (hFa : F a=0) (hFb : F b=1)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (density x)))
    (hmean : (∫ x in a..b, x*density x) = 0) :
    Real.exp (-1) ≤ F 0 ∧ F 0 ≤ 1-Real.exp (-1) := by
  have hlower := smooth_log_concave_density_mean_zero_mass_bound ha hb hF hdensity
    hdensityPrime hFderiv hdensityDeriv hpos hleft hFa hFb hshape hmean
  have hnegMap : MapsTo (fun x : ℝ => -x) (Icc (-b) (-a)) (Icc a b) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hnegMapOpen : MapsTo (fun x : ℝ => -x) (Ioo (-b) (-a)) (Ioo a b) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hFR : ContinuousOn (fun x => 1-F (-x)) (Icc (-b) (-a)) :=
    continuousOn_const.sub (hF.comp continuous_neg.continuousOn hnegMap)
  have hpR : ContinuousOn (fun x => density (-x)) (Icc (-b) (-a)) :=
    hdensity.comp continuous_neg.continuousOn hnegMap
  have hppR : IntervalIntegrable (fun x => -densityPrime (-x)) volume (-b) (-a) := by
    have hpcomp : IntervalIntegrable (fun x => densityPrime (-x)) volume (-b) (-a) := by
      simpa only [zero_sub] using (hdensityPrime.comp_sub_left (0 : ℝ)).symm
    have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-b) (-a) := intervalIntegrable_const
    simpa only [zero_sub] using hz.sub hpcomp
  have hdFR : ∀ x ∈ Ioo (-b) (-a), HasDerivAt (fun y => 1-F (-y)) (density (-x)) x := by
    intro x hx
    have h := ((hFderiv (-x) (hnegMapOpen hx)).comp x (hasDerivAt_neg x)).const_sub 1
    simpa using h
  have hdpR : ∀ x ∈ Ioo (-b) (-a), HasDerivAt (fun y => density (-y)) (-densityPrime (-x)) x := by
    intro x hx
    have h := (hdensityDeriv (-x) (hnegMapOpen hx)).comp x (hasDerivAt_neg x)
    convert h using 1 <;> first | rfl | exact Subsingleton.elim _ _ | simp | ring
  have hshapeR : ConcaveOn ℝ (Ioo (-b) (-a)) (fun x => Real.log (density (-x))) := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy alpha beta halpha hbeta hsum
    have h := hshape.2 (hnegMapOpen hx) (hnegMapOpen hy) halpha hbeta hsum
    simpa only [smul_eq_mul,mul_neg,neg_add] using h
  have hmeanR : (∫ x in (-b)..(-a), x*density (-x)) = 0 := by
    have h := intervalIntegral.integral_comp_neg (fun x => x*density x) (a := -b) (b := -a)
    simp only [neg_mul,intervalIntegral.integral_neg,neg_neg] at h
    rw [hmean] at h
    linarith
  have hupper := smooth_log_concave_density_mean_zero_mass_bound
    (by linarith : -b<0) (by linarith : 0 < -a) hFR hpR hppR hdFR hdpR
    (fun x hx => hpos (-x) (hnegMapOpen hx))
    (by simpa using hright) (by simpa [hFb]) (by simpa [hFa]) hshapeR hmeanR
  simp only [neg_zero] at hupper
  exact ⟨hlower,by linarith⟩

noncomputable def normalizedRestriction {E : Type*} [MeasurableSpace E]
    (nu : Measure E) (K : Set E) : Measure E :=
  (nu K)⁻¹ • nu.restrict K

theorem normalizedRestriction_isProbability {E : Type*} [MeasurableSpace E]
    (nu : Measure E) (K : Set E) (hpositive : nu K ≠ 0) (hfinite : nu K ≠ ∞) :
    IsProbabilityMeasure (normalizedRestriction nu K) := by
  constructor
  simp [normalizedRestriction,Measure.smul_apply,ENNReal.inv_mul_cancel hpositive hfinite]

theorem normalizedRestriction_halfspace_mass
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (nu : Measure E) (K : Set E) (ell : E →L[ℝ] ℝ) (t : ℝ) :
    (normalizedRestriction nu K).map ell (Iic t) =
      (nu K)⁻¹*nu ({x | ell x ≤ t} ∩ K) := by
  rw [projection_halfspace_mass]
  rw [normalizedRestriction,Measure.smul_apply,Measure.restrict_apply]
  · rfl
  · exact measurableSet_le ell.measurable measurable_const


/-- The normalized restriction of an actual compact body has a well-defined
Bochner centroid and every centered continuous scalar projection has mean zero.
No centroid or projection moment is postulated. -/
theorem compact_body_centered_projection_mean_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (nu : Measure E) (K : Set E) (hK : IsCompact K)
    (hpositive : nu K ≠ 0) (hfinite : nu K ≠ ∞) (ell : E →L[ℝ] ℝ) :
    (∫ x, ell (x-(∫ y, y ∂(normalizedRestriction nu K)))
      ∂(normalizedRestriction nu K)) = 0 := by
  have hidentity : Integrable (fun x : E => x) (nu.restrict K) :=
    continuous_id.continuousOn.integrableOn_of_subset_isCompact hK hK.measurableSet
      Subset.rfl hfinite
  have hinv : (nu K)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpositive
  have hnormalized : Integrable (fun x : E => x) (normalizedRestriction nu K) :=
    hidentity.smul_measure hinv
  letI := normalizedRestriction_isProbability nu K hpositive hfinite
  exact centered_projection_mean_zero (normalizedRestriction nu K) ell hnormalized


/-- A normalized one-dimensional log-concave density has the exact e^{-1}
centroid mass bound. The CDF is constructed from the density in this theorem;
its normalization, differentiability and log-concavity are not assumed. -/
theorem one_dimensional_log_concave_density_centroid_bound
    {density densityPrime : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (hdensity : ContinuousOn density (Icc a b))
    (hdensityPrime : IntervalIntegrable densityPrime volume a b)
    (hdensityDeriv : ∀ x ∈ Ioo a b, HasDerivAt density (densityPrime x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hleft : 0 ≤ density a) (hright : 0 ≤ density b)
    (hnormalized : (∫ x in a..b, density x) = 1)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (density x)))
    (hmean : (∫ x in a..b, x*density x) = 0) :
    Real.exp (-1) ≤ (∫ x in a..0, density x) ∧
      (∫ x in a..0, density x) ≤ 1-Real.exp (-1) := by
  let F := fun t => ∫ x in a..t, density x
  have hab : a < b := lt_trans ha hb
  have hi : IntervalIntegrable density volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab.le] using hdensity
  have hFcont : ContinuousOn F (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
    simpa [F,uIcc_of_le hab.le] using h
  have hFderiv : ∀ t ∈ Ioo a b, HasDerivAt F (density t) t := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := by
      intro x hx
      exact ⟨hx.1,hx.2.trans ht.2.le⟩
    have hit : IntervalIntegrable density volume a t := by
      apply hi.mono_set
      simpa [uIcc_of_le ht.1.le,uIcc_of_le hab.le] using hsub
    have hmeas : StronglyMeasurableAtFilter density (𝓝 t) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hdensity.mono Ioo_subset_Icc_self) t ht
    have hct : ContinuousAt density t :=
      hdensity.continuousAt (Icc_mem_nhds ht.1 ht.2)
    exact intervalIntegral.integral_hasDerivAt_right hit hmeas hct
  have h := smooth_log_concave_density_two_sided_centroid_bound ha hb hFcont hdensity
    hdensityPrime hFderiv hdensityDeriv hpos hleft hright
    (by simp [F]) (by simpa [F] using hnormalized) hshape hmean
  exact h


/-- The zero mean of a genuine positive density forces the support to straddle
zero; this conclusion is not an extra geometric localization assumption. -/
theorem mean_zero_positive_density_support_straddles_zero
    {density : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hdensity : ContinuousOn density (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hleft : 0 ≤ density a) (hright : 0 ≤ density b)
    (hmean : (∫ x in a..b, x*density x) = 0) :
    a < 0 ∧ 0 < b := by
  have hnonneg : ∀ x ∈ Icc a b, 0 ≤ density x := by
    intro x hx
    by_cases hxa : x=a
    · simpa [hxa] using hleft
    by_cases hxb : x=b
    · simpa [hxb] using hright
    exact (hpos x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),lt_of_le_of_ne hx.2 hxb⟩).le
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith
  have hmc : m ∈ Icc a b := ⟨hm.1.le,hm.2.le⟩
  constructor
  · by_contra hn
    have ha0 : 0 ≤ a := not_lt.mp hn
    have hpint := intervalIntegral.integral_pos hab
      (continuous_id.continuousOn.mul hdensity)
      (fun x hx => mul_nonneg (ha0.trans hx.1.le) (hnonneg x ⟨hx.1.le,hx.2⟩))
      (show ∃ c ∈ Icc a b, 0 < c*density c from
        ⟨m,hmc,mul_pos (by linarith [hm.1]) (hpos m hm)⟩)
    change 0 < ∫ x in a..b, x*density x at hpint
    rw [hmean] at hpint
    linarith
  · by_contra hn
    have hb0 : b ≤ 0 := not_lt.mp hn
    have hpint := intervalIntegral.integral_pos hab
      (continuous_id.continuousOn.mul hdensity).neg
      (fun x hx => neg_nonneg.mpr
        (mul_nonpos_of_nonpos_of_nonneg (hx.2.trans hb0) (hnonneg x ⟨hx.1.le,hx.2⟩)))
      (show ∃ c ∈ Icc a b, 0 < -(c*density c) from
        ⟨m,hmc,neg_pos.mpr (mul_neg_of_neg_of_pos (by linarith [hm.2]) (hpos m hm))⟩)
    change 0 < ∫ x in a..b, -(x*density x) at hpint
    rw [intervalIntegral.integral_neg,hmean] at hpint
    linarith

/-- A finite-support normalized differentiable log-concave density has the
centroid halfspace mass bounds, with no supplied CDF and no assumed support
straddling. The outstanding high-dimensional marginal construction is separate. -/
theorem finite_support_log_concave_mean_zero_mass_bound
    {density densityPrime : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hdensity : ContinuousOn density (Icc a b))
    (hdensityPrime : IntervalIntegrable densityPrime volume a b)
    (hdensityDeriv : ∀ x ∈ Ioo a b, HasDerivAt density (densityPrime x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < density x)
    (hleft : 0 ≤ density a) (hright : 0 ≤ density b)
    (hnormalized : (∫ x in a..b, density x) = 1)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (density x)))
    (hmean : (∫ x in a..b, x*density x) = 0) :
    Real.exp (-1) ≤ (∫ x in a..0, density x) ∧
      (∫ x in a..0, density x) ≤ 1-Real.exp (-1) := by
  obtain ⟨ha,hb⟩ := mean_zero_positive_density_support_straddles_zero hab hdensity hpos
    hleft hright hmean
  exact one_dimensional_log_concave_density_centroid_bound ha hb hdensity hdensityPrime
    hdensityDeriv hpos hleft hright hnormalized hshape hmean


end GrunbaumDevelopment

end SnapshotModule_019
/- END grunbaum_development -/

/- BEGIN centroid_program -/
section SnapshotModule_020

namespace PaperCentroidProgram
open Set MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
open PaperGDE

abbrev Space (n : ℕ) := Vec n

def center {n : ℕ} (P : Set (Space n)) : Space n :=
  ∫ x, x ∂(GrunbaumDevelopment.normalizedRestriction volume P)

def cut {n : ℕ} (P : Set (Space n)) (x v : Space n) : Set (Space n) :=
  P ∩ {z | inner ℝ v (z-x) ≤ 0}

lemma cut_subset {n : ℕ} (P : Set (Space n)) (x v : Space n) : cut P x v ⊆ P :=
  inter_subset_left

lemma cut_compact {n : ℕ} {P : Set (Space n)} (hP : IsCompact P) (x v : Space n) :
    IsCompact (cut P x v) := by
  exact hP.inter_right (isClosed_le (continuous_const.inner (continuous_id.sub continuous_const))
    continuous_const)

lemma cut_convex {n : ℕ} {P : Set (Space n)} (hP : Convex ℝ P) (x v : Space n) :
    Convex ℝ (cut P x v) := by
  apply hP.inter
  intro a ha b hb s t hs ht hst
  simp only [Set.mem_setOf_eq] at *
  have hi : inner ℝ v (s • a+t • b-x) =
      s*inner ℝ v (a-x)+t*inner ℝ v (b-x) := by
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right]
    have he := congrArg (fun r : ℝ => r*inner ℝ v x) hst
    nlinarith only [he]
  rw [hi]
  nlinarith

lemma center_mem {n : ℕ} {P : Set (Space n)} (hPc : IsCompact P)
    (hPv : Convex ℝ P) (hPi : (interior P).Nonempty) : center P ∈ P := by
  have hp : volume P ≠ 0 := (Measure.measure_pos_of_nonempty_interior volume hPi).ne'
  letI := GrunbaumDevelopment.normalizedRestriction_isProbability volume P hp hPc.measure_ne_top
  have hint : Integrable (fun x : Space n => x) (volume.restrict P) :=
    continuous_id.continuousOn.integrableOn_of_subset_isCompact hPc hPc.measurableSet
      Subset.rfl hPc.measure_ne_top
  have hnint : Integrable (fun x : Space n => x)
      (GrunbaumDevelopment.normalizedRestriction volume P) :=
    hint.smul_measure (ENNReal.inv_ne_top.mpr hp)
  exact hPv.integral_mem hPc.isClosed
    (Measure.ae_smul_measure (ae_restrict_mem hPc.measurableSet) _) hnint

structure State (n : ℕ) where
  body : Set (Space n)
  best : Space n

def selectProgram {n : ℕ} (incumbent candidate : Space n) : Program n (Space n) :=
  .query candidate incumbent (fun b => .pure (if b then incumbent else candidate))

lemma select_height {n : ℕ} (a b : Space n) : Program.height (selectProgram a b) = 1 := by
  simp [selectProgram,Program.height]

lemma select_eval_le {n : ℕ} (C : Oracle n) (f : Space n → ℝ) (hC : OracleCorrect C f)
    (a b : Space n) :
    f (Program.eval C (selectProgram a b)) ≤ f a ∧
      f (Program.eval C (selectProgram a b)) ≤ f b := by
  simp only [selectProgram,Program.eval]
  split_ifs with h
  · exact ⟨le_rfl,(hC b a).mp h⟩
  · have hh : f b ≤ f a := le_of_lt (lt_of_not_ge (fun hn => h ((hC b a).mpr hn)))
    exact ⟨hh,le_rfl⟩

lemma select_eval_mem {n : ℕ} (C : Oracle n) {K : Set (Space n)}
    {a b : Space n} (ha : a ∈ K) (hb : b ∈ K) :
    Program.eval C (selectProgram a b) ∈ K := by
  simp only [selectProgram,Program.eval]
  split_ifs <;> assumption

def loopProgram {n : ℕ} (delta gamma : ℝ) : ℕ → State n → Program n (State n)
  | 0, s => .pure s
  | k+1, s => by
    classical
    exact if (interior s.body).Nonempty then
      let x := center s.body
      Program.bind (gdeProgram x delta gamma) (fun v =>
        Program.bind (selectProgram s.best x) (fun best =>
          loopProgram delta gamma k ⟨cut s.body x v,best⟩))
    else .pure s

/-- Every branch, including arbitrary inconsistent comparison replies, is bounded. -/
lemma loop_public_height {n : ℕ} (delta gamma : ℝ) (k : ℕ) (s : State n) :
    Program.height (loopProgram delta gamma k s) ≤
      k*(2*(n+1)-1+n*rounds n delta+1) := by
  induction k generalizing s with
  | zero => simp [loopProgram,Program.height]
  | succ k ih =>
    simp only [loopProgram]
    split_ifs with hfull
    · apply (Program.height_bind_le _ _ (2*(n+1)-1+n*rounds n delta)
        (1+k*(2*(n+1)-1+n*rounds n delta+1)) (gdeProgram_public_height _ _ _) ?_).trans
        (by simp only [Nat.add_mul, Nat.one_mul]; omega)
      intro v
      apply Program.height_bind_le _ _ 1 (k*(2*(n+1)-1+n*rounds n delta+1))
      · exact (select_height _ _).le
      · intro best; exact ih _
    · simp [Program.height]

/-- The first center needs no comparison with an older center. -/
def firstProgram {n : ℕ} (delta gamma : ℝ) (k : ℕ) (P : Set (Space n)) :
    Program n (State n) :=
  let x := center P
  Program.bind (gdeProgram x delta gamma) (fun v =>
    loopProgram delta gamma k ⟨cut P x v,x⟩)

lemma first_public_height {n : ℕ} (delta gamma : ℝ) (k : ℕ) (P : Set (Space n)) :
    Program.height (firstProgram delta gamma k P) ≤
      (k+1)*(2*(n+1)-1+n*rounds n delta+1)-1 := by
  apply (Program.height_bind_le _ _ (2*(n+1)-1+n*rounds n delta)
    (k*(2*(n+1)-1+n*rounds n delta+1)) (gdeProgram_public_height _ _ _)
    (fun _ => loop_public_height _ _ _ _)).trans
  simp only [Nat.add_mul, Nat.one_mul]
  omega

lemma loop_body_subset {n : ℕ} (C : Oracle n) (delta gamma : ℝ) (k : ℕ) (s : State n) :
    (Program.eval C (loopProgram delta gamma k s)).body ⊆ s.body := by
  induction k generalizing s with
  | zero => exact Subset.rfl
  | succ k ih =>
    simp only [loopProgram]
    split_ifs
    · simp only [Program.eval_bind]
      exact (ih _).trans (cut_subset _ _ _)
    · exact Subset.rfl

lemma loop_body_geometry {n : ℕ} (C : Oracle n) (delta gamma : ℝ) (k : ℕ) (s : State n)
    (hsc : IsCompact s.body) (hsv : Convex ℝ s.body) :
    IsCompact (Program.eval C (loopProgram delta gamma k s)).body ∧
      Convex ℝ (Program.eval C (loopProgram delta gamma k s)).body := by
  induction k generalizing s with
  | zero => exact ⟨hsc,hsv⟩
  | succ k ih =>
    simp only [loopProgram]
    split_ifs
    · simp only [Program.eval_bind]
      exact ih _ (cut_compact hsc _ _) (cut_convex hsv _ _)
    · exact ⟨hsc,hsv⟩

lemma loop_best_feasible {n : ℕ} (C : Oracle n) (delta gamma : ℝ) (k : ℕ) (s : State n)
    (K : Set (Space n)) (hsc : IsCompact s.body) (hsv : Convex ℝ s.body)
    (hsub : s.body ⊆ K) (hbest : s.best ∈ K) :
    (Program.eval C (loopProgram delta gamma k s)).best ∈ K := by
  induction k generalizing s with
  | zero => exact hbest
  | succ k ih =>
    simp only [loopProgram]
    split_ifs with hfull
    · simp only [Program.eval_bind]
      exact ih _ (cut_compact hsc _ _) (cut_convex hsv _ _)
        ((cut_subset _ _ _).trans hsub)
        (select_eval_mem C hbest (hsub (center_mem hsc hsv hfull)))
    · exact hbest

lemma loop_best_nonincreasing {n : ℕ} (C : Oracle n) (f : Space n → ℝ)
    (hC : OracleCorrect C f) (delta gamma : ℝ) (k : ℕ) (s : State n) :
    f (Program.eval C (loopProgram delta gamma k s)).best ≤ f s.best := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [loopProgram]
    split_ifs
    · simp only [Program.eval_bind]
      exact (ih _).trans (select_eval_le C f hC _ _).1
    · exact le_rfl

end
end PaperCentroidProgram

end SnapshotModule_020
/- END centroid_program -/

/- BEGIN centroid_loop_analysis -/
section SnapshotModule_021

namespace PaperCentroidProgram
open Set MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
open PaperGDE

/-- A trace-level induction for the actual program. It derives all intermediate
volume inequalities from one-step geometry and retains the target until success. -/
theorem loop_no_success_certificate {n : ℕ} (C : Oracle n) (f : Space n → ℝ)
    (hC : OracleCorrect C f) (delta gamma threshold q : ℝ) (hq : 0 ≤ q)
    (K T : Set (Space n)) (hTi : (interior T).Nonempty)
    (hretain : ∀ P, IsCompact P → Convex ℝ P → P ⊆ K → T ⊆ P →
      threshold < f (center P) →
      T ⊆ cut P (center P) (Program.eval C (gdeProgram (center P) delta gamma)))
    (hshrink : ∀ P, IsCompact P → Convex ℝ P → P ⊆ K → (interior P).Nonempty →
      ∀ v : Space n, ‖v‖=1 →
      (volume (cut P (center P) v)).toReal ≤ q*(volume P).toReal)
    (k : ℕ) (s : State n) (hsc : IsCompact s.body) (hsv : Convex ℝ s.body)
    (hsK : s.body ⊆ K) (hTs : T ⊆ s.body)
    (hbad : threshold < f (Program.eval C (loopProgram delta gamma k s)).best) :
    T ⊆ (Program.eval C (loopProgram delta gamma k s)).body ∧
      (volume (Program.eval C (loopProgram delta gamma k s)).body).toReal ≤
        q^k*(volume s.body).toReal := by
  induction k generalizing s with
  | zero => exact ⟨hTs,by simp [loopProgram,Program.eval]⟩
  | succ k ih =>
    have hfull : (interior s.body).Nonempty := hTi.mono (interior_mono hTs)
    let x := center s.body
    let v := Program.eval C (gdeProgram x delta gamma)
    let b := Program.eval C (selectProgram s.best x)
    let snext : State n := ⟨cut s.body x v,b⟩
    have heval : Program.eval C (loopProgram delta gamma (k+1) s) =
        Program.eval C (loopProgram delta gamma k snext) := by
      simp only [loopProgram,if_pos hfull,Program.eval_bind]
      rfl
    rw [heval] at hbad ⊢
    have hb : threshold < f b := hbad.trans_le
      (loop_best_nonincreasing C f hC delta gamma k snext)
    have hx : threshold < f x := hb.trans_le (select_eval_le C f hC s.best x).2
    have hnext : T ⊆ snext.body := hretain s.body hsc hsv hsK hTs hx
    obtain ⟨hT,hV⟩ := ih snext (cut_compact hsc _ _) (cut_convex hsv _ _)
      ((cut_subset _ _ _).trans hsK) hnext hbad
    refine ⟨hT,?_⟩
    have hcut : (volume snext.body).toReal ≤ q*(volume s.body).toReal :=
      hshrink s.body hsc hsv hsK hfull v (gdeProgram_total_unit C x delta gamma)
    calc
      (volume (Program.eval C (loopProgram delta gamma k snext)).body).toReal ≤
          q^k*(volume snext.body).toReal := hV
      _ ≤ q^k*(q*(volume s.body).toReal) :=
        mul_le_mul_of_nonneg_left hcut (pow_nonneg hq k)
      _ = q^(k+1)*(volume s.body).toReal := by ring

/-- The finite centroid program succeeds once its explicit volume bound is below
the actual retained target volume. Later degeneracy is handled by its incumbent. -/
theorem firstProgram_accuracy_from_geometry {n : ℕ} (C : Oracle n) (f : Space n → ℝ)
    (hC : OracleCorrect C f) (delta gamma threshold q : ℝ) (hq : 0 ≤ q)
    (K T : Set (Space n)) (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hTK : T ⊆ K) (hTi : (interior T).Nonempty)
    (hretain : ∀ P, IsCompact P → Convex ℝ P → P ⊆ K → T ⊆ P →
      threshold < f (center P) →
      T ⊆ cut P (center P) (Program.eval C (gdeProgram (center P) delta gamma)))
    (hshrink : ∀ P, IsCompact P → Convex ℝ P → P ⊆ K → (interior P).Nonempty →
      ∀ v : Space n, ‖v‖=1 →
      (volume (cut P (center P) v)).toReal ≤ q*(volume P).toReal)
    (k : ℕ) (hsmall : q^(k+1)*(volume K).toReal < (volume T).toReal) :
    f (Program.eval C (firstProgram delta gamma k K)).best ≤ threshold := by
  by_contra hn
  have hbad : threshold < f (Program.eval C (firstProgram delta gamma k K)).best :=
    lt_of_not_ge hn
  let x := center K
  let v := Program.eval C (gdeProgram x delta gamma)
  let s : State n := ⟨cut K x v,x⟩
  have heval : Program.eval C (firstProgram delta gamma k K) =
      Program.eval C (loopProgram delta gamma k s) := by
    simp only [firstProgram,Program.eval_bind]
    rfl
  rw [heval] at hbad
  have hx : threshold < f x := hbad.trans_le (loop_best_nonincreasing C f hC delta gamma k s)
  have hfull : (interior K).Nonempty := hTi.mono (interior_mono hTK)
  have hTs : T ⊆ s.body := hretain K hKc hKv Subset.rfl hTK hx
  have hsc : IsCompact s.body := cut_compact hKc _ _
  have hsv : Convex ℝ s.body := cut_convex hKv _ _
  obtain ⟨hT,hV⟩ := loop_no_success_certificate C f hC delta gamma threshold q hq K T hTi
    hretain hshrink k s hsc hsv (cut_subset _ _ _) hTs hbad
  have hcut : (volume s.body).toReal ≤ q*(volume K).toReal :=
    hshrink K hKc hKv Subset.rfl hfull v (gdeProgram_total_unit C x delta gamma)
  have hFinal := (loop_body_geometry C delta gamma k s hsc hsv).1
  have hlower : (volume T).toReal ≤
      (volume (Program.eval C (loopProgram delta gamma k s)).body).toReal :=
    ENNReal.toReal_mono hFinal.measure_ne_top (measure_mono hT)
  have hupper : (volume (Program.eval C (loopProgram delta gamma k s)).body).toReal ≤
      q^(k+1)*(volume K).toReal := by
    calc
      _ ≤ q^k*(volume s.body).toReal := hV
      _ ≤ q^k*(q*(volume K).toReal) :=
        mul_le_mul_of_nonneg_left hcut (pow_nonneg hq k)
      _ = _ := by ring
  linarith

end
end PaperCentroidProgram

end SnapshotModule_021
/- END centroid_loop_analysis -/

/- BEGIN centroid_retention -/
section SnapshotModule_022

namespace PaperCentroid
open Set
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma bad_global_center_gradient_premise (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (xstar x : V) (hstar : ‖xstar‖ ≤ 1) (hx : ‖x‖ ≤ 2)
    (eta : ℝ) (hbad : f xstar+eta < f x) : eta/3 < ‖grad x‖ := by
  have hf := PaperSmooth.convex_first_order f grad hg hc x xstar
  have hi := real_inner_le_norm (-(grad x)) (xstar-x)
  rw [inner_neg_left,norm_neg] at hi
  have hdist : ‖xstar-x‖ ≤ 3 := (norm_sub_le xstar x).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_left hdist (norm_nonneg (grad x))
  nlinarith

lemma bad_center_scalar_margin (a eta G : ℝ) (heta : 0 < eta) (hbad : eta < a)
    (hG : 0 ≤ G) (hGsq : G^2 ≤ 2*a) :
    G*Real.sqrt eta/3 < a-eta/2 := by
  have hs := Real.sq_sqrt heta.le
  have hs0 := Real.sqrt_nonneg eta
  have ha : 0 < a := heta.trans hbad
  have hm := mul_le_mul_of_nonneg_right hGsq heta.le
  have hprod : G*Real.sqrt eta ≤ 3*a/2 := by
    nlinarith [sq_nonneg (G*Real.sqrt eta-3*a/2)]
  nlinarith

/-- The actual centroid angular tolerance sqrt(eta)/16 retains every target point. -/
lemma global_cut_retains_target (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (xstar x y direction : V)
    (hmin : ∀ z, f xstar ≤ f z) (eta : ℝ) (heta : 0 < eta)
    (hbad : f xstar+eta < f x) (htarget : f y ≤ f xstar+eta/2)
    (hdiam : ‖y-x‖ ≤ 4) (hG : 0 < ‖grad x‖)
    (hdir : ‖direction-NormedSpace.normalize (grad x)‖ ≤ Real.sqrt eta/16) :
    inner ℝ direction (y-x) < 0 := by
  have hf := PaperSmooth.convex_first_order f grad hg hc x y
  have hsq := PaperSmooth.normalized_gradient_gap f grad hg hLip xstar x hmin
  have hm := bad_center_scalar_margin (f x-f xstar) eta ‖grad x‖ heta (by linarith)
    (norm_nonneg _) hsq
  have hdot : inner ℝ (grad x) (y-x) < -‖grad x‖*Real.sqrt eta/3 := by linarith
  have hnormal : inner ℝ (NormedSpace.normalize (grad x)) (y-x) =
      inner ℝ (grad x) (y-x)/‖grad x‖ := by
    simp only [NormedSpace.normalize,real_inner_smul_left,div_eq_mul_inv]
    ring
  have hn : inner ℝ (NormedSpace.normalize (grad x)) (y-x) < -Real.sqrt eta/3 := by
    rw [hnormal]
    apply (div_lt_iff₀ hG).mpr
    nlinarith
  have he := real_inner_le_norm (direction-NormedSpace.normalize (grad x)) (y-x)
  rw [inner_sub_left] at he
  have her := mul_le_mul hdir hdiam (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt eta/16)
  have hs : 0 < Real.sqrt eta := Real.sqrt_pos.mpr heta
  linarith

end
end PaperCentroid

end SnapshotModule_022
/- END centroid_retention -/

/- BEGIN volume_budget -/
section SnapshotModule_023

namespace PaperVolumeBudget
noncomputable section

/-- The paper's floor-plus-one horizon is strictly beyond the volume threshold. -/
theorem public_horizon (d : ℕ) (q A r : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hA : 0 < A) (hr : 0 < r) :
    q^(⌊(d : ℝ)*Real.log (A/r)/(-Real.log q)⌋₊+1) * A^d < r^d := by
  let M := ⌊(d : ℝ)*Real.log (A/r)/(-Real.log q)⌋₊+1
  have hlq : Real.log q < 0 := Real.log_neg hq hq1
  have hlambda : 0 < -Real.log q := by linarith
  have hM : (d : ℝ)*Real.log (A/r)/(-Real.log q) < (M : ℝ) := by
    simpa [M] using Nat.lt_floor_add_one ((d : ℝ)*Real.log (A/r)/(-Real.log q))
  have hproduct := (div_lt_iff₀ hlambda).mp hM
  have hlogs : (M : ℝ)*Real.log q+(d : ℝ)*Real.log A < (d : ℝ)*Real.log r := by
    rw [Real.log_div hA.ne' hr.ne'] at hproduct
    nlinarith
  apply (Real.log_lt_log_iff (mul_pos (pow_pos hq M) (pow_pos hA d)) (pow_pos hr d)).mp
  rw [Real.log_mul (pow_ne_zero M hq.ne') (pow_ne_zero d hA.ne'),Real.log_pow,Real.log_pow,
    Real.log_pow]
  exact hlogs

lemma grunbaum_ratio_pos : 0 < 1-Real.exp (-1) := by
  have hh : Real.exp (-1) < 1 := by simpa using Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ)<0)
  linarith

lemma grunbaum_ratio_lt_one : 1-Real.exp (-1) < 1 := by
  linarith [Real.exp_pos (-1)]

lemma grunbaum_lambda_pos : 0 < -Real.log (1-Real.exp (-1)) := by
  have h := Real.log_neg grunbaum_ratio_pos grunbaum_ratio_lt_one
  linarith

/-- The geometric stopping bound also holds with any looser enclosing radius. -/
theorem volume_contradiction (d : ℕ) (q A r unitVolume currentVolume : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hA : 0 < A) (hr : 0 < r)
    (hu : 0 < unitVolume)
    (hlower : r^d*unitVolume ≤ currentVolume)
    (hupper : currentVolume ≤ q^(⌊(d : ℝ)*Real.log (A/r)/(-Real.log q)⌋₊+1) *
      (A^d*unitVolume)) : False := by
  have hs := mul_lt_mul_of_pos_right (public_horizon d q A r hq hq1 hA hr) hu
  nlinarith

end
end PaperVolumeBudget

end SnapshotModule_023
/- END volume_budget -/

/- BEGIN centroid_normalized -/
section SnapshotModule_024

namespace PaperCentroidNormalized
open Set MeasureTheory PaperGDE PaperCentroidProgram
open scoped RealInnerProductSpace
noncomputable section

abbrev Space (n : ℕ) := PaperGDE.Vec n

def target {n : ℕ} (f : Space n → ℝ) (xstar : Space n) (eta : ℝ) : Set (Space n) :=
  Metric.closedBall 0 2 ∩ {y | f y ≤ f xstar+eta/2}

def roundsBeforeLast (n : ℕ) (eta : ℝ) : ℕ :=
  ⌊((n+1 : ℕ) : ℝ)*Real.log (2/Real.sqrt eta)/
    (-Real.log (1-Real.exp (-1)))⌋₊

def algorithm {n : ℕ} (eta : ℝ) : Program n (State n) :=
  firstProgram (Real.sqrt eta/16) (eta/3) (roundsBeforeLast n eta) (Metric.closedBall 0 2)

lemma target_has_interior {n : ℕ} (f : Space n → ℝ) (grad : Space n → Space n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : Space n) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (interior (target f xstar eta)).Nonempty ∧
      Metric.closedBall xstar (Real.sqrt eta) ⊆ target f xstar eta := by
  have ht : Metric.closedBall xstar (Real.sqrt eta) ⊆ target f xstar eta := by
    intro y hy
    have hh := PaperCentroid.centroid_target_ball f grad hg hLip xstar hmin hstar eta heta heta1 y hy
    exact ⟨by simpa [Metric.mem_closedBall,dist_zero_right] using hh.1,by dsimp; linarith [hh.2]⟩
  refine ⟨?_,ht⟩
  refine ⟨xstar,interior_maximal ((Metric.ball_subset_closedBall).trans ht) Metric.isOpen_ball ?_⟩
  exact Metric.mem_ball_self (Real.sqrt_pos.mpr heta)

lemma actual_gde_retains_target {n : ℕ} (C : Oracle n)
    (f : Space n → ℝ) (grad : Space n → Space n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (hC : OracleCorrect C f)
    (xstar : Space n) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (P : Set (Space n)) (hPc : IsCompact P) (hPv : Convex ℝ P)
    (hsub : P ⊆ Metric.closedBall 0 2) (hTP : target f xstar eta ⊆ P)
    (hbad : f xstar+eta < f (center P)) :
    target f xstar eta ⊆ cut P (center P)
      (Program.eval C (gdeProgram (center P) (Real.sqrt eta/16) (eta/3))) := by
  have hfull := ((target_has_interior f grad hg hLip xstar hmin hstar eta heta heta1).1).mono
    (interior_mono hTP)
  have hxP := center_mem hPc hPv hfull
  have hxn : ‖center P‖ ≤ 2 := by
    simpa [Metric.mem_closedBall,dist_zero_right] using hsub hxP
  have hgamma := PaperCentroid.bad_global_center_gradient_premise f grad hg hc xstar (center P)
    hstar hxn eta hbad
  have hdelta : 0 < Real.sqrt eta/16 := by positivity
  have hdelta1 : Real.sqrt eta/16 ≤ 1 := by
    have hs := Real.sq_sqrt heta.le
    have hs0 := Real.sqrt_nonneg eta
    nlinarith
  have hG : 0 < ‖grad (center P)‖ := (by positivity : 0 < eta/3).trans hgamma
  have hcert := full_gde_certificate f grad hg hLip hC (center P) (Real.sqrt eta/16)
    (eta/3) hdelta hdelta1 (by positivity) hgamma.le
  intro y hy
  refine ⟨hTP hy,?_⟩
  have hyn : ‖y‖ ≤ 2 := by
    simpa [target,Metric.mem_closedBall,dist_zero_right] using hy.1
  have hdist : ‖y-center P‖ ≤ 4 := (norm_sub_le y (center P)).trans (by linarith)
  exact (PaperCentroid.global_cut_retains_target f grad hg hc hLip xstar (center P) y _
    hmin eta heta hbad hy.2 hdist hG hcert.2.1).le

lemma volume_threshold {n : ℕ} (f : Space n → ℝ) (grad : Space n → Space n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : Space n) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (1-Real.exp (-1))^(roundsBeforeLast n eta+1)*
      (volume (Metric.closedBall (0 : Space n) 2)).toReal <
      (volume (target f xstar eta)).toReal := by
  have hr : 0 < Real.sqrt eta := Real.sqrt_pos.mpr heta
  have hT := (target_has_interior f grad hg hLip xstar hmin hstar eta heta heta1).2
  have hTfin : volume (target f xstar eta) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) 2).measure_ne_top (measure_mono inter_subset_left)
  have hlower := ENNReal.toReal_mono hTfin (measure_mono hT)
  have hunitpos : 0 < (volume (Metric.closedBall (0 : Space n) 1)).toReal := by
    apply ENNReal.toReal_pos
    · have hp : 0 < volume (Metric.ball (0 : Space n) 1) :=
        Metric.isOpen_ball.measure_pos volume ⟨0,Metric.mem_ball_self (by norm_num)⟩
      exact (hp.trans_le (measure_mono Metric.ball_subset_closedBall)).ne'
    · exact (isCompact_closedBall (0 : Space n) 1).measure_ne_top
  have hs := mul_lt_mul_of_pos_right
    (PaperVolumeBudget.public_horizon (n+1) (1-Real.exp (-1)) 2 (Real.sqrt eta)
      PaperVolumeBudget.grunbaum_ratio_pos PaperVolumeBudget.grunbaum_ratio_lt_one (by norm_num) hr)
    hunitpos
  have hd : Module.finrank ℝ (Space n) = n+1 := by simp [Space,PaperGDE.Vec]
  have hbig := Measure.addHaar_real_closedBall' (volume : Measure (Space n)) (0 : Space n)
    (by norm_num : (0:ℝ)≤2)
  have hsmall := Measure.addHaar_real_closedBall' (volume : Measure (Space n)) xstar hr.le
  change (volume (Metric.closedBall (0 : Space n) 2)).toReal = _ at hbig
  change (volume (Metric.closedBall xstar (Real.sqrt eta))).toReal = _ at hsmall
  rw [hd] at hbig hsmall
  rw [hsmall] at hlower
  rw [hbig]
  unfold roundsBeforeLast
  simp only [measureReal_def] at hlower ⊢
  nlinarith

/-- This modular assembly uses one-step centroid geometry, rather than assuming
an entire convergence or volume recurrence. The geometry is instantiated separately. -/
lemma accuracy_from_centroid_geometry {n : ℕ} (C : Oracle n)
    (f : Space n → ℝ) (grad : Space n → Space n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (hC : OracleCorrect C f)
    (xstar : Space n) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hshrink : ∀ P : Set (Space n), IsCompact P → Convex ℝ P →
      P ⊆ Metric.closedBall 0 2 → (interior P).Nonempty →
      ∀ v : Space n, ‖v‖=1 →
      (volume (cut P (center P) v)).toReal ≤ (1-Real.exp (-1))*(volume P).toReal) :
    f (Program.eval C (algorithm eta)).best-f xstar ≤ eta := by
  have htarget := target_has_interior f grad hg hLip xstar hmin hstar eta heta heta1
  have h := firstProgram_accuracy_from_geometry C f hC (Real.sqrt eta/16) (eta/3)
    (f xstar+eta) (1-Real.exp (-1)) PaperVolumeBudget.grunbaum_ratio_pos.le
    (Metric.closedBall 0 2) (target f xstar eta) (isCompact_closedBall _ _) (convex_closedBall _ _)
    inter_subset_left htarget.1
    (actual_gde_retains_target C f grad hg hc hLip hC xstar hmin hstar eta heta heta1)
    hshrink (roundsBeforeLast n eta) (volume_threshold f grad hg hLip xstar hmin hstar eta heta heta1)
  change f (Program.eval C (firstProgram (Real.sqrt eta/16) (eta/3)
    (roundsBeforeLast n eta) (Metric.closedBall 0 2))).best-f xstar ≤ eta
  linarith

end
end PaperCentroidNormalized

end SnapshotModule_024
/- END centroid_normalized -/

/- BEGIN grunbaum_cdf_general -/
section SnapshotModule_025

/- Derivative-free CDF/Jensen development. The general convex-body/BM theorem
   is not postulated here. -/
namespace GrunbaumCDFGeneral
open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- Every concave scalar function on an open interval has a global supporting
line at an interior point. No differentiability hypothesis is used. -/
theorem concave_supporting_line_at_zero {g : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hg : ConcaveOn ℝ (Ioo a b) g) :
    ∃ slope0 : ℝ, ∀ x ∈ Ioo a b, g x ≤ g 0+slope0*x := by
  let phi := fun x => -g x
  have hc : ConvexOn ℝ (Ioo a b) phi := hg.neg
  have hz : (0 : ℝ) ∈ interior (Ioo a b) := by simp; exact ⟨ha,hb⟩
  let k := derivWithin phi (Ioi 0) 0
  refine ⟨-k, ?_⟩
  intro x hx
  rcases lt_trichotomy x 0 with hn | he | hp
  · have hleft := hc.slope_le_leftDeriv_of_mem_interior hx hz hn
    have hright := hc.leftDeriv_le_rightDeriv_of_mem_interior hz
    have hs := hleft.trans hright
    rw [slope_def_field] at hs
    change ((-g 0)-(-g x))/(0-x) ≤ k at hs
    have hm := (div_le_iff₀ (by linarith : (0 : ℝ) < 0-x)).mp hs
    nlinarith
  · subst x
    simp
  · have hs := hc.rightDeriv_le_slope_of_mem_interior hz hx hp
    rw [slope_def_field] at hs
    change k ≤ ((-g x)-(-g 0))/(x-0) at hs
    have hm := (le_div_iff₀ (by linarith : (0 : ℝ) < x-0)).mp hs
    nlinarith

/-- Jensen at the actual zero mean, on an open interval and without a
pointwise derivative assumption. The singular CDF boundary is not included. -/
theorem concave_integral_le_at_zero
    {mu : Measure ℝ} [IsProbabilityMeasure mu] {g : ℝ → ℝ} {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hg : ConcaveOn ℝ (Ioo a b) g)
    (hmem : ∀ᵐ x ∂mu, x ∈ Ioo a b)
    (hid : Integrable (fun x : ℝ => x) mu) (hgint : Integrable g mu)
    (hmean : (∫ x, x ∂mu)=0) :
    (∫ x, g x ∂mu) ≤ g 0 := by
  obtain ⟨s,hs⟩ := concave_supporting_line_at_zero ha hb hg
  have hupperInt : Integrable (fun x => g 0+s*x) mu :=
    (integrable_const _).add (hid.const_mul s)
  have hpoint : ∀ᵐ x ∂mu, g x ≤ g 0+s*x := hmem.mono fun x hx => hs x hx
  have h := integral_mono_ae hgint hupperInt hpoint
  have hupper : (∫ x, g 0+s*x ∂mu)=g 0 := by
    rw [integral_add (integrable_const _) (hid.const_mul s),integral_const_mul,hmean]
    simp
  rw [hupper] at h
  exact h

/-- Exact sublevel preimage for a continuous-distribution CDF with a strict
support interval. This is a structural CDF identity, not a mass bound premise. -/
theorem cdf_sublevel_preimage
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {a b x : ℝ}
    (hstrict : StrictMonoOn (cdf mu) (Icc a b)) (hFb : cdf mu b=1)
    (hx : x ∈ Icc a b) (hFx : cdf mu x < 1) :
    (cdf mu) ⁻¹' Iic (cdf mu x) = Iic x := by
  ext y
  constructor
  · intro hy
    change cdf mu y ≤ cdf mu x at hy
    by_contra hn
    have hxy : x < y := lt_of_not_ge hn
    by_cases hyb : y ≤ b
    · have hyin : y ∈ Icc a b := ⟨hx.1.trans hxy.le,hyb⟩
      exact (not_le_of_gt (hstrict hx hyin hxy)) hy
    · have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
      have hh := monotone_cdf mu hby
      rw [hFb] at hh
      linarith
  · intro hy
    exact monotone_cdf mu hy

theorem uniform_unit_Iic_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume.restrict (Icc (0 : ℝ) 1)) (Iic t) = ENNReal.ofReal t := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · intro h
      exact ⟨h.2.1,h.1⟩
    · intro h
      exact ⟨h.2,h.1,h.2.trans ht.2⟩
  rw [hset,Real.volume_Icc]
  simp

/-- Probability integral transform on a finite continuous strict support.
No density or differentiability is assumed. -/
theorem cdf_probability_integral_transform
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {a b : ℝ} (hab : a < b)
    (hcont : Continuous (cdf mu)) (hstrict : StrictMonoOn (cdf mu) (Icc a b))
    (hFa : cdf mu a=0) (hFb : cdf mu b=1) :
    mu.map (cdf mu) = volume.restrict (Icc (0 : ℝ) 1) := by
  have hmeas : Measurable (cdf mu) := (monotone_cdf mu).measurable
  apply Measure.ext_of_Iic
  intro t
  by_cases htneg : t < 0
  · rw [Measure.map_apply hmeas measurableSet_Iic]
    have hempty : (cdf mu) ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      exact not_le_of_gt (lt_of_lt_of_le htneg (cdf_nonneg mu x))
    have hempty' : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff,mem_Iic,mem_Icc,mem_empty_iff_false,iff_false,not_and]
      intro hx h0
      linarith
    rw [hempty,measure_empty,Measure.restrict_apply measurableSet_Iic,hempty',measure_empty]
  by_cases htge : 1 ≤ t
  · rw [Measure.map_apply hmeas measurableSet_Iic]
    have huniv : (cdf mu) ⁻¹' Iic t = univ := by
      ext x
      simp only [mem_preimage,mem_Iic,mem_univ,iff_true]
      exact (cdf_le_one mu x).trans htge
    have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      apply inter_eq_right.mpr
      intro x hx
      exact hx.2.trans htge
    rw [huniv,measure_univ,Measure.restrict_apply measurableSet_Iic,hset,Real.volume_Icc]
    norm_num
  have ht0 : 0 ≤ t := le_of_not_gt htneg
  have ht1 : t < 1 := lt_of_not_ge htge
  rw [uniform_unit_Iic_of_mem ⟨ht0,ht1.le⟩,Measure.map_apply hmeas measurableSet_Iic]
  have htRange : t ∈ Icc (cdf mu a) (cdf mu b) := by simpa [hFa,hFb] using (show t ∈ Icc (0 : ℝ) 1 from ⟨ht0,ht1.le⟩)
  obtain ⟨x,hx,hFx⟩ := intermediate_value_Icc hab.le hcont.continuousOn htRange
  have hFx1 : cdf mu x < 1 := by simpa [hFx] using ht1
  rw [← hFx,cdf_sublevel_preimage mu hstrict hFb hx hFx1,← ofReal_cdf]


theorem uniform_unit_log_integral :
    (∫ u, Real.log u ∂(volume.restrict (Icc (0 : ℝ) 1))) = -1 := by
  have h : (∫ u in (0 : ℝ)..1, Real.log u) = -1 := by simp [integral_log]
  have heq : (∫ u in Icc (0 : ℝ) 1, Real.log u) =
      ∫ u in (0 : ℝ)..1, Real.log u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc]
  exact heq.trans h

/-- The CDF log moment and integrability follow from the probability integral
transform, so neither is a premise of the eventual centroid mass theorem. -/
theorem cdf_log_moment_no_density
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {a b : ℝ} (hab : a < b)
    (hcont : Continuous (cdf mu)) (hstrict : StrictMonoOn (cdf mu) (Icc a b))
    (hFa : cdf mu a=0) (hFb : cdf mu b=1) :
    Integrable (fun x => Real.log (cdf mu x)) mu ∧
      (∫ x, Real.log (cdf mu x) ∂mu) = -1 := by
  have hmeas : Measurable (cdf mu) := (monotone_cdf mu).measurable
  have hmap := cdf_probability_integral_transform mu hab hcont hstrict hFa hFb
  have hintUniform : Integrable Real.log (volume.restrict (Icc (0 : ℝ) 1)) := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_log' : IntervalIntegrable Real.log volume (0 : ℝ) 1)
  have hintMap : Integrable Real.log (mu.map (cdf mu)) := by rw [hmap]; exact hintUniform
  have hint : Integrable (fun x => Real.log (cdf mu x)) mu := hintMap.comp_measurable hmeas
  refine ⟨hint, ?_⟩
  have hIntegral := integral_map_of_stronglyMeasurable (μ := mu) hmeas Real.measurable_log.stronglyMeasurable
  rw [hmap] at hIntegral
  exact hIntegral.symm.trans uniform_unit_log_integral

/-- General one-dimensional log-CDF centroid mass bound, with no density or
pointwise derivative assumptions. All moment identities are actual integrals.
The remaining convex-body task is to prove these CDF shape/support properties
from convexity, rather than assume them for the body's CDF. -/
theorem cdf_centroid_mass_bound_no_density
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {a b : ℝ}
    (ha : a < 0) (hb : 0 < b)
    (hcont : Continuous (cdf mu)) (hstrict : StrictMonoOn (cdf mu) (Icc a b))
    (hFa : cdf mu a=0) (hFb : cdf mu b=1)
    (hshape : ConcaveOn ℝ (Ioo a b) (fun x => Real.log (cdf mu x)))
    (hmem : ∀ᵐ x ∂mu, x ∈ Ioo a b)
    (hid : Integrable (fun x : ℝ => x) mu) (hmean : (∫ x, x ∂mu)=0) :
    Real.exp (-1) ≤ cdf mu 0 := by
  have hab : a < b := lt_trans ha hb
  obtain ⟨hint,hlogmoment⟩ := cdf_log_moment_no_density mu hab hcont hstrict hFa hFb
  have hJ := concave_integral_le_at_zero ha hb hshape hmem hid hint hmean
  rw [hlogmoment] at hJ
  have hzero : 0 < cdf mu 0 := by
    have h := hstrict (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
      (show (0 : ℝ) ∈ Icc a b from ⟨ha.le,hb.le⟩) ha
    simpa [hFa] using h
  have h := Real.exp_le_exp.mpr hJ
  simpa [Real.exp_log hzero] using h


end GrunbaumCDFGeneral

end SnapshotModule_025
/- END grunbaum_cdf_general -/

/- BEGIN convex_body_cdf -/
section SnapshotModule_026

namespace ConvexBodyCDF
open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section

lemma continuous_cdf_of_noAtoms (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (cdf mu) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hzero : (cdf mu).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
  rw [StieltjesFunction.measure_singleton,ENNReal.ofReal_eq_zero] at hzero
  have hleft := (cdf mu).mono.leftLim_le (le_rfl : x ≤ x)
  have heq : Function.leftLim (cdf mu) x = cdf mu x := by linarith
  have hl := (Monotone.continuousWithinAt_Iio_iff_leftLim_eq (cdf mu).mono).mpr heq
  have hr := (cdf mu).right_continuous x
  have hc := hl.union hr
  have hc' : ContinuousWithinAt (cdf mu) Set.univ x := by simpa using hc
  exact hc'.continuousAt (by simp)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V] [Measure.IsAddHaarMeasure (volume : Measure V)]

lemma linear_fiber_zero (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) (t : ℝ) :
    volume {x : V | ell x = t} = 0 := by
  obtain ⟨v,hv⟩ : ∃ v : V, ell v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hell (by ext x; exact hn x)
  let z := (t/ell v) • v
  have hz : ell z = t := by dsimp [z]; rw [map_smul]; dsimp; field_simp
  have hker : ell.ker ≠ ⊤ := by
    intro htop
    have hh : v ∈ ell.ker := by rw [htop]; trivial
    exact hv hh
  have hn := Measure.addHaar_submodule (volume : Measure V) ell.ker hker
  have hs : {x : V | ell x=t} = (fun x : V => x+ -z) ⁻¹' (ell.ker : Set V) := by
    ext x
    change (ell x = t) ↔ (ell (x + -z) = 0)
    rw [map_add,map_neg,hz]
    constructor <;> intro h <;> linarith
  rw [hs,measure_preimage_add_right]
  exact hn

lemma normalized_projection_noAtoms (K : Set V) (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) :
    NullSingletonClass ((GrunbaumDevelopment.normalizedRestriction volume K).map ell) := by
  constructor
  intro t
  rw [Measure.map_apply ell.measurable (measurableSet_singleton t),
    GrunbaumDevelopment.normalizedRestriction,Measure.smul_apply,
    Measure.restrict_apply (ell.measurable (measurableSet_singleton t))]
  have hz : volume (ell ⁻¹' {t} ∩ K) = 0 :=
    measure_mono_null inter_subset_left (linear_fiber_zero ell hell t)
  simp only [hz,smul_eq_mul,mul_zero]

lemma normalized_projection_continuous (K : Set V) (hpositive : volume K ≠ 0)
    (hfinite : volume K ≠ ∞) (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) :
    Continuous (cdf ((GrunbaumDevelopment.normalizedRestriction volume K).map ell)) := by
  letI := GrunbaumDevelopment.normalizedRestriction_isProbability volume K hpositive hfinite
  letI : IsProbabilityMeasure ((GrunbaumDevelopment.normalizedRestriction volume K).map ell) :=
    Measure.isProbabilityMeasure_map ell.measurable.aemeasurable
  letI := normalized_projection_noAtoms K ell hell
  exact continuous_cdf_of_noAtoms _

lemma interior_projection_between {K : Set V} (hK : Convex ℝ K)
    (ell : V →L[ℝ] ℝ) {x p : V} (hx : x ∈ K) (hp : p ∈ interior K)
    {t : ℝ} (htx : ell x < t) (htp : t ≤ ell p) :
    ∃ z ∈ interior K, ell z = t := by
  have hden : 0 < ell p-ell x := by linarith
  let c := (t-ell x)/(ell p-ell x)
  have hc : 0 < c := div_pos (by linarith) hden
  have hc1 : c ≤ 1 := (div_le_one hden).mpr (by linarith)
  refine ⟨c • p+(1-c) • x,
    hK.combo_interior_self_mem_interior hp hx hc (by linarith) (by ring),?_⟩
  simp only [map_add,map_smul,smul_eq_mul]
  dsimp [c]
  field_simp
  <;> ring

lemma interior_projection_of_extrema {K : Set V} (hK : Convex ℝ K)
    (hKi : (interior K).Nonempty) (ell : V →L[ℝ] ℝ)
    {x y : V} (hx : x ∈ K) (hy : y ∈ K) {t : ℝ}
    (htx : ell x < t) (hty : t < ell y) :
    ∃ z ∈ interior K, ell z=t := by
  obtain ⟨p,hp⟩ := hKi
  by_cases htp : t ≤ ell p
  · exact interior_projection_between hK ell hx hp htx htp
  · have hpt : ell p < t := lt_of_not_ge htp
    obtain ⟨z,hz,heq⟩ := interior_projection_between hK (-ell) hy hp
      (t := -t) (by simpa only [ContinuousLinearMap.neg_apply] using neg_lt_neg hty)
      (by simpa only [ContinuousLinearMap.neg_apply] using (neg_le_neg hpt.le))
    exact ⟨z,hz,by simpa only [ContinuousLinearMap.neg_apply,neg_inj] using heq⟩

lemma open_strip_positive {K : Set V} (hK : Convex ℝ K)
    (hKi : (interior K).Nonempty) (ell : V →L[ℝ] ℝ)
    {x y : V} (hx : x ∈ K) (hy : y ∈ K) {s t : ℝ}
    (hxs : ell x ≤ s) (hst : s<t) (hty : t ≤ ell y) :
    0 < volume (ell ⁻¹' Ioo s t ∩ K) := by
  obtain ⟨z,hz,heq⟩ := interior_projection_of_extrema hK hKi ell hx hy
    (t := (s+t)/2) (by linarith) (by linarith)
  have hopen : IsOpen (ell ⁻¹' Ioo s t ∩ interior K) :=
    (isOpen_Ioo.preimage ell.continuous).inter isOpen_interior
  have hne : (ell ⁻¹' Ioo s t ∩ interior K).Nonempty := by
    refine ⟨z,?_,hz⟩
    change s < ell z ∧ ell z < t
    rw [heq]
    constructor <;> linarith
  exact (hopen.measure_pos volume hne).trans_le
    (measure_mono (inter_subset_inter_right _ interior_subset))


def shiftedLaw (K : Set V) (ell : V →L[ℝ] ℝ) (offset : ℝ) : Measure ℝ :=
  (GrunbaumDevelopment.normalizedRestriction volume K).map (fun x => ell x-offset)

def centroid (K : Set V) : V :=
  ∫ x, x ∂(GrunbaumDevelopment.normalizedRestriction volume K)

lemma shiftedLaw_probability (K : Set V) (hpositive : volume K ≠ 0)
    (hfinite : volume K ≠ ∞) (ell : V →L[ℝ] ℝ) (offset : ℝ) :
    IsProbabilityMeasure (shiftedLaw K ell offset) := by
  letI := GrunbaumDevelopment.normalizedRestriction_isProbability volume K hpositive hfinite
  exact Measure.isProbabilityMeasure_map (ell.measurable.sub measurable_const).aemeasurable

lemma shiftedLaw_noAtoms (K : Set V) (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) (offset : ℝ) :
    NullSingletonClass (shiftedLaw K ell offset) := by
  constructor
  intro t
  have hm : Measurable (fun x => ell x-offset) := ell.measurable.sub measurable_const
  rw [shiftedLaw,Measure.map_apply hm (measurableSet_singleton t),
    GrunbaumDevelopment.normalizedRestriction,Measure.smul_apply,
    Measure.restrict_apply (hm (measurableSet_singleton t))]
  have hset : (fun x => ell x-offset) ⁻¹' {t} = {x | ell x=t+offset} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  have hz : volume ({x | ell x=t+offset} ∩ K) = 0 :=
    measure_mono_null inter_subset_left (linear_fiber_zero ell hell (t+offset))
  simp only [hz,smul_eq_mul,mul_zero]

lemma shiftedLaw_continuous (K : Set V) (hpositive : volume K ≠ 0)
    (hfinite : volume K ≠ ∞) (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) (offset : ℝ) :
    Continuous (cdf (shiftedLaw K ell offset)) := by
  letI := shiftedLaw_probability K hpositive hfinite ell offset
  letI := shiftedLaw_noAtoms K ell hell offset
  exact continuous_cdf_of_noAtoms _

lemma shiftedLaw_open_strip_positive {K : Set V} (hK : Convex ℝ K)
    (hKi : (interior K).Nonempty) (hfinite : volume K ≠ ∞)
    (ell : V →L[ℝ] ℝ) (offset : ℝ)
    {x y : V} (hx : x ∈ K) (hy : y ∈ K) {s t : ℝ}
    (hxs : ell x-offset ≤ s) (hst : s<t) (hty : t ≤ ell y-offset) :
    0 < shiftedLaw K ell offset (Ioo s t) := by
  have hm : Measurable (fun x => ell x-offset) := ell.measurable.sub measurable_const
  rw [shiftedLaw,Measure.map_apply hm measurableSet_Ioo,
    GrunbaumDevelopment.normalizedRestriction,Measure.smul_apply,
    Measure.restrict_apply (hm measurableSet_Ioo)]
  have hset : (fun x => ell x-offset) ⁻¹' Ioo s t = ell ⁻¹' Ioo (s+offset) (t+offset) := by
    ext z
    simp only [mem_preimage,mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [hset,smul_eq_mul]
  apply ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hfinite)
  exact (open_strip_positive hK hKi ell hx hy (by linarith) (by linarith) (by linarith)).ne'

lemma shiftedLaw_cdf_strict_of_extrema {K : Set V} (hK : Convex ℝ K)
    (hKi : (interior K).Nonempty) (hpositive : volume K ≠ 0) (hfinite : volume K ≠ ∞)
    (ell : V →L[ℝ] ℝ) (offset : ℝ) {xmin xmax : V}
    (hxmin : xmin ∈ K) (hxmax : xmax ∈ K) :
    StrictMonoOn (cdf (shiftedLaw K ell offset)) (Icc (ell xmin-offset) (ell xmax-offset)) := by
  letI := shiftedLaw_probability K hpositive hfinite ell offset
  intro s hs t ht hst
  have hp := shiftedLaw_open_strip_positive hK hKi hfinite ell offset hxmin hxmax hs.1 hst ht.2
  have hp' : 0 < shiftedLaw K ell offset (Ioc s t) :=
    hp.trans_le (measure_mono Ioo_subset_Ioc_self)
  rw [← measure_cdf (shiftedLaw K ell offset),StieltjesFunction.measure_Ioc] at hp'
  have hh : 0 < cdf (shiftedLaw K ell offset) t-cdf (shiftedLaw K ell offset) s :=
    ENNReal.ofReal_pos.mp hp'
  linarith

lemma shiftedLaw_cdf_endpoints {K : Set V} (hpositive : volume K ≠ 0)
    (hfinite : volume K ≠ ∞) (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) (offset : ℝ)
    {xmin xmax : V} (hmin : ∀ x ∈ K, ell xmin ≤ ell x) (hmax : ∀ x ∈ K, ell x ≤ ell xmax) :
    cdf (shiftedLaw K ell offset) (ell xmin-offset)=0 ∧
      cdf (shiftedLaw K ell offset) (ell xmax-offset)=1 := by
  letI := shiftedLaw_probability K hpositive hfinite ell offset
  have hm : Measurable (fun x => ell x-offset) := ell.measurable.sub measurable_const
  constructor
  · rw [cdf_eq_real,measureReal_def,shiftedLaw,Measure.map_apply hm measurableSet_Iic,
      GrunbaumDevelopment.normalizedRestriction,Measure.smul_apply,
      Measure.restrict_apply (hm measurableSet_Iic)]
    have hz : volume ((fun x => ell x-offset) ⁻¹' Iic (ell xmin-offset) ∩ K) = 0 := by
      apply measure_mono_null (t := {x | ell x=ell xmin})
      · intro x hx
        have hh := hmin x hx.2
        have hlow : ell x-offset ≤ ell xmin-offset := hx.1
        change ell x=ell xmin
        linarith
      · exact linear_fiber_zero ell hell (ell xmin)
    simp [hz]
  · rw [cdf_eq_real,measureReal_def,shiftedLaw,Measure.map_apply hm measurableSet_Iic,
      GrunbaumDevelopment.normalizedRestriction,Measure.smul_apply,
      Measure.restrict_apply (hm measurableSet_Iic)]
    have hset : (fun x => ell x-offset) ⁻¹' Iic (ell xmax-offset) ∩ K = K := by
      apply inter_eq_right.mpr
      intro x hx
      change ell x-offset ≤ ell xmax-offset
      exact sub_le_sub_right (hmax x hx) offset
    rw [hset]
    simp [smul_eq_mul,ENNReal.inv_mul_cancel hpositive hfinite]

lemma ae_mem_open_support_of_cdf_endpoints (mu : Measure ℝ) [IsProbabilityMeasure mu]
    [NullSingletonClass mu] {a b : ℝ} (hFa : cdf mu a=0) (hFb : cdf mu b=1) :
    ∀ᵐ x ∂mu, x ∈ Ioo a b := by
  have ha : mu (Iic a)=0 := by rw [← ofReal_cdf mu a,hFa]; simp
  have hb : mu (Ioi b)=0 := by
    rw [← compl_Iic,measure_compl measurableSet_Iic (by finiteness),← ofReal_cdf mu b,hFb]
    simp
  have hbc : mu (Ici b)=0 := by
    apply measure_mono_null (t := Ioi b ∪ {b})
    · intro x hx
      change b ≤ x at hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr (by simp [heq])
    · exact measure_union_null hb (measure_singleton b)
  apply ae_iff.mpr
  have hset : {x | x ∉ Ioo a b} = Iic a ∪ Ici b := by
    ext x
    simp only [mem_setOf_eq,mem_Ioo,not_and_or,not_lt,mem_union,mem_Iic,mem_Ici]
  rw [hset]
  exact measure_union_null ha hbc

lemma normalized_identity_integrable {K : Set V} (hK : IsCompact K)
    (hpositive : volume K ≠ 0) (hfinite : volume K ≠ ∞) :
    Integrable (fun x : V => x) (GrunbaumDevelopment.normalizedRestriction volume K) := by
  have hi : Integrable (fun x : V => x) ((volume : Measure V).restrict K) :=
    continuous_id.continuousOn.integrableOn_of_subset_isCompact hK hK.measurableSet Subset.rfl hfinite
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr hpositive)

lemma shiftedLaw_identity_integrable {K : Set V} (hK : IsCompact K)
    (hpositive : volume K ≠ 0) (hfinite : volume K ≠ ∞) (ell : V →L[ℝ] ℝ) (offset : ℝ) :
    Integrable (fun x : ℝ => x) (shiftedLaw K ell offset) := by
  letI := GrunbaumDevelopment.normalizedRestriction_isProbability volume K hpositive hfinite
  have hi := normalized_identity_integrable hK hpositive hfinite
  have hm : Measurable (fun x => ell x-offset) := ell.measurable.sub measurable_const
  apply (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).mpr
  exact (ell.integrable_comp hi).sub (integrable_const offset)

lemma shiftedLaw_mean {K : Set V} (hK : IsCompact K)
    (hpositive : volume K ≠ 0) (hfinite : volume K ≠ ∞) (ell : V →L[ℝ] ℝ) (offset : ℝ) :
    (∫ x, x ∂(shiftedLaw K ell offset)) = ell (centroid K)-offset := by
  letI := GrunbaumDevelopment.normalizedRestriction_isProbability volume K hpositive hfinite
  have hi := normalized_identity_integrable hK hpositive hfinite
  have hm : Measurable (fun x => ell x-offset) := ell.measurable.sub measurable_const
  have hmap := integral_map_of_stronglyMeasurable
    (μ := GrunbaumDevelopment.normalizedRestriction volume K) (f := fun x : ℝ => x)
    hm stronglyMeasurable_id
  have hlin : (∫ x, ell x ∂(GrunbaumDevelopment.normalizedRestriction volume K)) =
      ell (∫ x, x ∂(GrunbaumDevelopment.normalizedRestriction volume K)) := ell.integral_comp_comm hi
  calc
    (∫ x, x ∂(shiftedLaw K ell offset)) =
        ∫ x, ell x-offset ∂(GrunbaumDevelopment.normalizedRestriction volume K) := hmap
    _ = ell (centroid K)-offset := by
      rw [integral_sub (ell.integrable_comp hi) (integrable_const offset),hlin]
      simp [centroid]


def centeredLaw (K : Set V) (ell : V →L[ℝ] ℝ) : Measure ℝ :=
  shiftedLaw K ell (ell (centroid K))

lemma body_volume_positive {K : Set V} (hKi : (interior K).Nonempty) : 0 < volume K :=
  (isOpen_interior.measure_pos volume hKi).trans_le (measure_mono interior_subset)

lemma mean_zero_open_support_straddles
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {a b : ℝ}
    (hmem : ∀ᵐ x ∂mu, x ∈ Ioo a b)
    (hid : Integrable (fun x : ℝ => x) mu) (hmean : (∫ x, x ∂mu)=0) :
    a < 0 ∧ 0 < b := by
  constructor
  · by_contra hn
    have ha : 0 ≤ a := not_lt.mp hn
    have hnonneg : ∀ᵐ x ∂mu, 0 ≤ x := hmem.mono fun x hx => ha.trans hx.1.le
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hid).mp hmean
    obtain ⟨x,hx,hz⟩ := (hmem.and hzero).exists
    change x=0 at hz
    linarith [hx.1]
  · by_contra hn
    have hb : b ≤ 0 := not_lt.mp hn
    have hnonneg : ∀ᵐ x ∂mu, 0 ≤ -x := hmem.mono fun x hx => by linarith [hx.2]
    have hi : Integrable (fun x : ℝ => -x) mu := by
      convert hid.neg using 1 <;> rfl
    have hm : (∫ x, -x ∂mu)=0 := by rw [integral_neg,hmean,neg_zero]
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hm
    obtain ⟨x,hx,hz⟩ := (hmem.and hzero).exists
    change -x=0 at hz
    linarith [hx.2]

/-- Every actual compact convex full-dimensional body has a finite strict
projection support around its true centroid. All scalar-law properties needed
by the derivative-free CDF mass theorem are derived here. -/
lemma centeredLaw_support_data {K : Set V} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (ell : V →L[ℝ] ℝ) (hell : ell ≠ 0) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      Continuous (cdf (centeredLaw K ell)) ∧
      StrictMonoOn (cdf (centeredLaw K ell)) (Icc a b) ∧
      cdf (centeredLaw K ell) a=0 ∧ cdf (centeredLaw K ell) b=1 ∧
      (∀ᵐ x ∂(centeredLaw K ell), x ∈ Ioo a b) ∧
      Integrable (fun x : ℝ => x) (centeredLaw K ell) ∧
      (∫ x, x ∂(centeredLaw K ell))=0 := by
  have hpositive : volume K ≠ 0 := (body_volume_positive hKi).ne'
  have hfinite : volume K ≠ ∞ := hKc.measure_ne_top
  have hKne : K.Nonempty := hKi.mono interior_subset
  obtain ⟨xmin,hxmin,hmin⟩ := hKc.exists_isMinOn hKne ell.continuous.continuousOn
  obtain ⟨xmax,hxmax,hmax⟩ := hKc.exists_isMaxOn hKne ell.continuous.continuousOn
  let offset := ell (centroid K)
  let mu := shiftedLaw K ell offset
  let a := ell xmin-offset
  let b := ell xmax-offset
  letI := shiftedLaw_probability K hpositive hfinite ell offset
  letI := shiftedLaw_noAtoms K ell hell offset
  have hends := shiftedLaw_cdf_endpoints hpositive hfinite ell hell offset hmin hmax
  have hcont := shiftedLaw_continuous K hpositive hfinite ell hell offset
  have hstrict := shiftedLaw_cdf_strict_of_extrema hKv hKi hpositive hfinite ell offset hxmin hxmax
  have hmem : ∀ᵐ x ∂mu, x ∈ Ioo a b :=
    ae_mem_open_support_of_cdf_endpoints mu hends.1 hends.2
  have hi : Integrable (fun x : ℝ => x) mu :=
    shiftedLaw_identity_integrable hKc hpositive hfinite ell offset
  have hm : (∫ x, x ∂mu)=0 := by
    simpa [mu,offset] using shiftedLaw_mean hKc hpositive hfinite ell offset
  obtain ⟨ha,hb⟩ := mean_zero_open_support_straddles mu hmem hi hm
  exact ⟨a,b,ha,hb,hcont,hstrict,hends.1,hends.2,hmem,hi,hm⟩

end
end ConvexBodyCDF

end SnapshotModule_026
/- END convex_body_cdf -/

/- BEGIN ported_isoperimetric.basic -/
section SnapshotModule_027

/- Ported from Jonathan Ho's isoperimetric proof repository, Apache-2.0.
   Upstream: https://github.com/hojonathanho/isoperimetric
   Commit: 29768f8beeaf17295cdf3853d37da35d7e2b0a5f
   Original source and license: ../vendor/isoperimetric_original/.
   Port target: Lean 4.32.1, pinned Mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6.
   Only namespacing/import/API adjustments may be made; final kernel/axiom checks required. -/

namespace AuditedIsoperimetric

lemma biSup_add_biSup
    {ι κ : Sort*}
    {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ENNReal} {g : κ → ENNReal} :
    (⨆ i, ⨆ _ : p i, f i) + (⨆ j, ⨆ _ : q j, g j) =
    (⨆ i, ⨆ j, ⨆ _ : p i, ⨆ _ : q j, f i + g j) := by
  apply le_antisymm
  · calc
      (⨆ x, ⨆ _ : p x, f x) + (⨆ y, ⨆ _ : q y, g y)
          = ⨆ x, ⨆ _ : p x, (f x + (⨆ y, ⨆ _ : q y, g y)) := by apply ENNReal.biSup_add' hp
      _ ≤ (⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, f x + g y) := by
        apply iSup₂_le
        intro x hx
        calc
          f x + (⨆ y, ⨆ _ : q y, g y) = ⨆ y, ⨆ _ : q y, (f x + g y) := by
            apply ENNReal.add_biSup' hq
          _ ≤ ⨆ x, ⨆ _ : p x, (⨆ y, ⨆ _ : q y, (f x + g y)) := by
            apply le_iSup₂ x hx
          _ = ⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, (f x + g y) := by
            apply iSup_congr; intro; exact iSup_comm
  simp only [iSup_le_iff]
  intro i j hi hj
  calc
    f i + g j ≤ (⨆ i, ⨆ (_ : p i), f i) + g j := by gcongr; apply le_iSup₂ i hi
    _ ≤ (⨆ i, ⨆ (_ : p i), f i) + ⨆ j, ⨆ (_ : q j), g j := by gcongr; apply le_iSup₂ j hj

lemma iSup_nonzero_of_nonzero {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by
  intro h
  apply hf_nonzero
  ext x
  simpa using le_iSup f x |>.trans_eq h

lemma iSup_min_nat (a : ENNReal) : ⨆ (n : ℕ), min a n = a := by
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt (by simp)
  intro w hw
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hw.trans_le le_top).ne
  exact ⟨n, by simp_all⟩

lemma iSup_min_nat_ne_top {ι : Sort*} (n : ℕ) (f : ι → ENNReal) :
    iSup (fun x ↦ min (f x) n) ≠ ⊤ := by
  apply ne_of_lt
  rw [iSup_lt_iff]
  use n
  exact ⟨ENNReal.natCast_lt_top n, fun x ↦ min_le_right (f x) ↑n⟩

lemma iSup_rpow_of_pos {ι : Sort*} {r : ℝ} (hr : r > 0) (f : ι → ENNReal) :
    (⨆ (i : ι), f i) ^ r = ⨆ (i : ι), f i ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iSup f

end AuditedIsoperimetric

end SnapshotModule_027
/- END ported_isoperimetric.basic -/

/- BEGIN ported_isoperimetric.prekopa_leindler -/
section SnapshotModule_028

/- Ported from Jonathan Ho's isoperimetric proof repository, Apache-2.0.
   Upstream: https://github.com/hojonathanho/isoperimetric
   Commit: 29768f8beeaf17295cdf3853d37da35d7e2b0a5f
   Original source and license: ../vendor/isoperimetric_original/.
   Port target: Lean 4.32.1, pinned Mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6.
   Only namespacing/import/API adjustments may be made; final kernel/axiom checks required. -/

namespace AuditedIsoperimetric


open MeasureTheory Set
open scoped Pointwise

lemma brunn_minkowski_1d_compact
    {A B C : Set ℝ}
    (h : A + B ⊆ C)
    (hA_nonempty : A.Nonempty) (hA_compact : IsCompact A)
    (hB_nonempty : B.Nonempty) (hB_compact : IsCompact B)
    : volume A + volume B ≤ volume C := by
  -- Translate A, B to A', B' so that their intersection is {0}
  let A' := A + {-sSup A}
  let B' := B + {-sInf B}
  have h_inter_zero : A' ∩ B' = {0} := by
    ext x
    simp only [add_singleton, image_add_right, neg_neg, mem_inter_iff, mem_preimage,
      mem_singleton_iff, A', B']
    constructor
    · intro ⟨ha, hb⟩
      exact le_antisymm
        (nonpos_of_add_le_left (le_csSup hA_compact.bddAbove ha))
        (nonneg_of_le_add_left (csInf_le hB_compact.bddBelow hb))
    · intro hx
      simp only [hx, zero_add]
      exact ⟨hA_compact.sSup_mem hA_nonempty, hB_compact.sInf_mem hB_nonempty⟩
  calc
    volume C ≥ volume (A + B) := measure_mono h
    -- Replacing A+B with A'+B' preserves volume
    _ = volume (A + B + {-sSup A} + {-sInf B}) := by simp
    _ = volume (A' + B') := by
      congr 1; nth_rw 2 [add_assoc]; nth_rw 3 [add_comm]; rw [← add_assoc]; rw [add_assoc]
    -- The volume of A'+B' is at least that of A'∪B', since both A' and B' contain 0.
    _ ≥ volume (A' ∪ B') := by
      apply measure_mono
      rw [union_subset_iff]
      have h_zero_in_inter : 0 ∈ A' ∩ B' := by simp [h_inter_zero]
      exact ⟨subset_add_left A' h_zero_in_inter.2, subset_add_right B' h_zero_in_inter.1⟩
    -- Finish the proof using the fact that A' and B' have intersection {0}
    -- and using translation invariance of volume.
    _ = volume (A' ∪ B') + volume (A' ∩ B') := by simp [h_inter_zero]
    _ = volume A' + volume B' := by
      rw [measure_union_add_inter]
      exact (hB_compact.add isCompact_singleton).measurableSet
    _ = volume A + volume B := by simp [A', B']

lemma brunn_minkowski_1d_infinite
    {A B C : Set ℝ} (ha : volume A = ⊤) (hb : B.Nonempty) (hc : A + B ⊆ C) :
    volume A + volume B ≤ volume C := calc
  volume A + volume B = volume (A + {hb.some}) := by simp [ha]  -- since both sides = ⊤
  _ ≤ volume (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb.some_mem))
  _ ≤ volume C := measure_mono hc

lemma brunn_minkowski_1d
    {A B C : Set ℝ}
    (h : A + B ⊆ C)
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    : volume A + volume B ≤ volume C := by

  -- Deal with the cases when A or B have infinite volume.
  by_cases hvolAfinite : volume A = ⊤
  · exact brunn_minkowski_1d_infinite hvolAfinite hB_nonempty h
  by_cases hvolBfinite : volume B = ⊤
  · rw [add_comm] at ⊢ h
    exact brunn_minkowski_1d_infinite hvolBfinite hA_nonempty h

  -- Use inner regularity of Lebesgue measure to reduce to the case of compact A, B
  rw [hA_measurable.measure_eq_iSup_isCompact_of_ne_top hvolAfinite,
    hB_measurable.measure_eq_iSup_isCompact_of_ne_top hvolBfinite]

  -- Want to prove:
  --   (⨆ K, ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K)
  --   + (⨆ K, ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K)
  --   ≤ volume C
  -- We'll proceed by rewriting the LHS.
  have combine_sup_conditions {A : Set ℝ} :
      (⨆ K, ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K) =
      (⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K) := by
    simp only [iSup_and]
  simp only [combine_sup_conditions]

  -- First, add in a nonempty condition:
  -- e.g. sup_{K ⊆ A} vol(K) = sup_{K ⊆ A, K nonempty} vol(K).
  have sup_vol_eq_sup_nonempty_vol {A : Set ℝ} :
      ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K =
      ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty), volume K := by
    apply le_antisymm
    · apply iSup_le; intro K
      apply iSup_le; intro hK
      by_cases h : K.Nonempty
      · apply le_iSup₂_of_le K (by simp [hK, h])
        exact le_refl (volume K)
      rw [not_nonempty_iff_eq_empty] at h
      simp [h]
    apply iSup_le; intro K
    apply iSup_le; intro hK
    apply le_iSup₂_of_le K
    · exact le_refl (volume K)
    simp [hK]
  simp only [sup_vol_eq_sup_nonempty_vol]

  -- Next, write the sum of sups as a sup of sums.
  -- sup_{K ⊆ A, K nonempty} vol(K) + sup_{L ⊆ B, L nonempty} vol(L)
  -- == sup_{K, L ⊆ A, K and L nonempty} vol(K) + vol(L).
  have combine_sups :
      (⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty), volume K)
      + (⨆ L, ⨆ (_ : L ⊆ B ∧ IsCompact L ∧ L.Nonempty), volume L)
      = ⨆ K, ⨆ L,
        ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty),
        ⨆ (_ : L ⊆ B ∧ IsCompact L ∧ L.Nonempty),
        volume K + volume L :=
    biSup_add_biSup
      (by use {hA_nonempty.some}; simp [hA_nonempty.some_mem])
      (by use {hB_nonempty.some}; simp [hB_nonempty.some_mem])
  rw [combine_sups]

  -- Finish using brunn_minkowski_1d_compact.
  apply iSup_le; intro K; apply iSup_le; intro L
  apply iSup_le; intro ⟨hKsubA, hKcompact, hKnonempty⟩
  apply iSup_le; intro ⟨hLsubA, hLcompact, hLnonempty⟩
  have hKplusLsubC : K + L ⊆ C := calc
    K + L ⊆ A + L := add_subset_add_right hKsubA
    _ ⊆ A + B := add_subset_add_left hLsubA
    _ ⊆ C := h
  exact brunn_minkowski_1d_compact hKplusLsubC hKnonempty hKcompact hLnonempty hLcompact

-- Utilities
lemma vol_superlevelset_measurable (f : ℝ → ENNReal)
    : Measurable (fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}) := by
  apply Antitone.measurable
  intro a b hab
  apply measure_mono
  simp only [setOf_subset_setOf]
  intro z hz
  calc
    ENNReal.ofReal a ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hab
    _ ≤ f z := hz

-- This is the layer cake formula.
-- The version of this theorem in mathlib (MeasureTheory.lintegral_eq_lintegral_meas_lt)
-- is for a ℝ-valued function instead of ENNReal-valued function.
lemma layercake {f : ℝ → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : ℝ), f x = ∫⁻ (t : ℝ) in Ioi 0, volume {x : ℝ | ENNReal.ofReal t ≤ f x} := by
  let ind (x t : ℝ) : ENNReal := if ENNReal.ofReal t ≤ f x then 1 else 0
  calc
    ∫⁻ (x : ℝ), f x = ∫⁻ (x : ℝ), ∫⁻ (t : ℝ) in Ioi 0, ind x t := by
      congr; ext x; symm
      calc
        ∫⁻ (t : ℝ) in Ioi 0, ind x t
            = ∫⁻ (t : ℝ) in Ioi 0, {t : ℝ | ENNReal.ofReal t ≤ f x}.indicator 1 t := by
          simp [ind, indicator]
        _ = ∫⁻ (t : ℝ) in {t : ℝ | ENNReal.ofReal t ≤ f x} ∩ (Ioi 0), 1 := by
          apply setLIntegral_indicator
          exact measurableSet_le ENNReal.measurable_ofReal measurable_const
        _ = volume {t : ℝ | ENNReal.ofReal t ≤ f x ∧ 0 < t} := by apply setLIntegral_one
        _ = f x := by
          by_cases hinf : f x = ⊤
          · simp only [hinf, le_top, true_and]; exact Real.volume_Ioi
          calc
            volume {t | ENNReal.ofReal t ≤ f x ∧ 0 < t}
                = volume {t | t ≤ (f x).toReal ∧ 0 < t} := by
              congr; ext t; simp only [and_congr_left_iff]; intro
              exact ENNReal.ofReal_le_iff_le_toReal hinf
            _ = volume (Ioc 0 (f x).toReal) := by congr; aesop
            _ = ENNReal.ofReal (f x).toReal := by simp
            _ = f x := ENNReal.ofReal_toReal_eq_iff.mpr hinf
    _ = ∫⁻ (t : ℝ) in Ioi 0, ∫⁻ (x : ℝ), ind x t := by
      apply lintegral_lintegral_swap
      exact Measurable.aemeasurable <|
        Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)
    _ = ∫⁻ (t : ℝ) in Ioi 0, volume {x : ℝ | ENNReal.ofReal t ≤ f x} := by
      congr; ext t
      calc
        ∫⁻ (x : ℝ), ind x t = ∫⁻ (x : ℝ), {x : ℝ | ENNReal.ofReal t ≤ f x}.indicator 1 x := by
          simp [ind, indicator]
        _ = ∫⁻ (x : ℝ) in {x : ℝ | ENNReal.ofReal t ≤ f x}, 1 := by
          apply lintegral_indicator
          exact measurableSet_le measurable_const hf_measurable
        _ = volume {x | ENNReal.ofReal t ≤ f x} := by apply setLIntegral_one

lemma lintegral_eq_vol_superlevelset_lintegral_01
    {f : ℝ → ENNReal} (hf_bound : f ≤ 1) (hf_measurable : Measurable f)
    : ∫⁻ x, f x = ∫⁻ t in Ioo 0 1, (fun t ↦ volume {x | ENNReal.ofReal t ≤ f x}) t := by
  let vf := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}
  calc
    ∫⁻ x, f x = ∫⁻ t in Ioi 0, vf t := layercake hf_measurable
    _ = ∫⁻ t in (Ioo 0 1 ∪ Ici 1), vf t := by simp
    _ = (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ici 1, vf t) :=
      lintegral_union measurableSet_Ici (by simp [disjoint_left])
    _ = ∫⁻ t in Ioo 0 1, vf t := by
      suffices ∫⁻ t in Ici 1, vf t = 0 by simp [this]
      rw [setLIntegral_eq_zero_iff measurableSet_Ici (vol_superlevelset_measurable f)]
      suffices ∀ x : ℝ, x ∈ Ioi 1 → volume {x_1 | ENNReal.ofReal x ≤ f x_1} = 0 by
        apply ae_of_mem_of_ae_of_mem_inter_Ioo; intros; filter_upwards; intro c _
        simp_all only [mem_Ioi, mem_Ici, mem_inter_iff, mem_Ioo]
        exact this c (by linarith)
      intro a ha
      suffices {x | ENNReal.ofReal a ≤ f x} = ∅ by rw [this]; exact measure_empty
      apply eq_empty_of_forall_notMem
      intro x hx
      have : 1 < f x := calc
        1 < ENNReal.ofReal a := ENNReal.one_lt_ofReal.mpr ha
        _ ≤ f x := hx
      exact absurd this (not_lt.mpr (hf_bound x))

-- A form of the weighted AM-GM inequality
lemma weighted_amgm {θ a b : ℝ} (hθ : 0 < θ ∧ θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    : ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ ≤ a + b := calc
  ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ = ((1-θ)^(1-θ))⁻¹ * a^(1-θ) * (θ^θ)⁻¹ * b^θ := by grind
  _ = ((1-θ)⁻¹)^(1-θ) * a^(1-θ) * (θ⁻¹)^θ * b^θ := by
    rw [Real.inv_rpow (by linarith), Real.inv_rpow (by linarith)]
  _ = ((1-θ)⁻¹*a)^(1-θ) * (θ⁻¹*b)^θ := by
    rw [Real.mul_rpow (by simp only [inv_nonneg, sub_nonneg]; linarith) ha,
      Real.mul_rpow (by simp only [inv_nonneg]; linarith) hb]
    ring
  _ ≤ (1-θ)*((1-θ)⁻¹*a) + θ*(θ⁻¹*b) :=
    Real.geom_mean_le_arith_mean2_weighted
      (by linarith) (by linarith) (by simp [hθ.2, ha]) (by simp [hθ.1, hb]) (by ring)
  _ = a + b := by grind

-- Prekopa-Leindler in 1 dimension assuming sup norm 1.
lemma prekopa_leindler_1d_normalized
    {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_sup1 : iSup f = 1)
    (hg_measurable : Measurable g) (hg_sup1 : iSup g = 1)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ (∫⁻ x, h x) := by

  -- {f>t} + {g>t} ⊆ {h>t}
  have h_superlevelset_incl : ∀ t : ℝ, 0 < t →
      {x | ENNReal.ofReal t ≤ f x} + {x | ENNReal.ofReal t ≤ g x}
      ⊆ {x | ENNReal.ofReal t ≤ h x} := by
    intro t ht
    rw [add_subset_iff]
    intro x hx y hy
    simp only [mem_setOf_eq] at hx hy ⊢
    calc
      ENNReal.ofReal t = (ENNReal.ofReal t) ^ (1 - θ) * (ENNReal.ofReal t) ^ θ := by
        rw [← ENNReal.rpow_add (1-θ) θ (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top]
        simp
      _ ≤ f x ^ (1 - θ) * g y ^ θ := by
        gcongr
        · linarith
        linarith
      _ ≤ h (x + y) := hfgh x y

  -- vol({f>t}) + vol({g>t}) ≤ vol({h>t})
  let vf : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}
  let vg : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ g x}
  let vh : ℝ → ENNReal := fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ h x}

  have h_vol_ineq : ∀ t : ℝ, 0 < t ∧ t < 1 → vf t + vg t ≤ vh t := by
    intro t ht
    have superlevelset_nonempty {f : ℝ → ENNReal} (hf_sup1 : iSup f = 1)
        : {x | ENNReal.ofReal t ≤ f x}.Nonempty := by
      apply nonempty_def.mpr
      suffices ∃ x, x ∈ {x | ENNReal.ofReal t < f x} by
        simp only [mem_setOf_eq] at this ⊢
        rcases this with ⟨x, hx⟩
        use x
        exact le_of_lt hx
      simp only [mem_setOf_eq]
      apply exists_lt_of_lt_ciSup
      simp only [hf_sup1, ENNReal.ofReal_lt_one, ht.2]
    exact brunn_minkowski_1d
      (h_superlevelset_incl t ht.1)
      (superlevelset_nonempty hf_sup1) (measurableSet_le measurable_const hf_measurable)
      (superlevelset_nonempty hg_sup1) (measurableSet_le measurable_const hg_measurable)

  -- integrate the volume inequality
  -- ∫_0^1 vol({f>t}) + vol({g>t}) dt ≤ ∫_0^1 vol({h>t}) dt ≤ ∫_0^∞ vol({h>t}) dt
  have h_vol_ineq_integral :
      (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ioo 0 1, vg t) ≤ ∫⁻ t in Ioi 0, vh t := calc
    (∫⁻ t in Ioo 0 1, vf t) + (∫⁻ t in Ioo 0 1, vg t)
        = ∫⁻ t in Ioo 0 1, (vf t + vg t) := by
      rw [lintegral_add_left (vol_superlevelset_measurable f)]
    _ ≤ ∫⁻ t in Ioo 0 1, vh t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact h_vol_ineq t ht
    _ ≤ ∫⁻ t in Ioi 0, vh t := by apply lintegral_mono_set; grind

  -- "layer cake" formulas
  -- ∫ h = ∫_0^∞ vol({h>t}) dt, ∫ f = ∫_0^1 vol({f>t}) dt, ∫ g = ∫_0^1 vol({g>t}) dt
  let fint : ENNReal := ∫⁻ x, f x
  let gint : ENNReal := ∫⁻ x, g x
  let hint : ENNReal := ∫⁻ x, h x
  have hfint : fint = ∫⁻ t in Ioo 0 1, vf t :=
    have hf_bound : f ≤ 1 := by
      intro x; simp only [Pi.one_apply]; rw [← hf_sup1]; exact le_iSup_iff.mpr fun _ a ↦ a x
    lintegral_eq_vol_superlevelset_lintegral_01 hf_bound hf_measurable
  have hgint : gint = ∫⁻ t in Ioo 0 1, vg t :=
    have hg_bound : g ≤ 1 := by
      intro x; simp only [Pi.one_apply]; rw [← hg_sup1]; exact le_iSup_iff.mpr fun _ a ↦ a x
    lintegral_eq_vol_superlevelset_lintegral_01 hg_bound hg_measurable
  have hhint : hint = ∫⁻ t in Ioi 0, vh t := layercake hh_measurable

  -- implies ∫ f + ∫ g ≤ ∫ h
  have h_ineq_integral : fint + gint ≤ hint := by
    rw [← hhint, ← hfint, ← hgint] at h_vol_ineq_integral
    exact h_vol_ineq_integral

  -- quickly prove the result in the case of fint = ⊤ or gint = ⊤
  by_cases h_fint_eq_top : fint = ⊤
  · simp only [h_fint_eq_top, top_add, top_le_iff] at h_ineq_integral
    unfold fint at h_fint_eq_top; unfold hint at h_ineq_integral
    simp [h_fint_eq_top, h_ineq_integral]
  by_cases h_gint_eq_top : gint = ⊤
  · simp only [h_gint_eq_top, add_top, top_le_iff] at h_ineq_integral
    unfold gint at h_gint_eq_top; unfold hint at h_ineq_integral
    simp [h_gint_eq_top, h_ineq_integral]

  -- now fint and gint are both finite
  have weighted_amgm_factor_nonneg : 0 ≤ ((1-θ)^(1-θ) * θ^θ)⁻¹ := by
    rw [inv_nonneg]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) (1 - θ)) (Real.rpow_nonneg (by linarith) θ)

  calc
    ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * fint^(1-θ) * gint^θ =
        ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * ENNReal.ofReal ((fint^(1-θ)).toReal) * gint^θ := by
      congr; rw [ENNReal.ofReal_toReal]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) h_fint_eq_top
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * ENNReal.ofReal (fint.toReal^(1-θ)) * gint^θ := by
      rw [← ENNReal.toReal_rpow]
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ)) * gint^θ := by
      rw [← ENNReal.ofReal_mul]; exact weighted_amgm_factor_nonneg
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ))
        * ENNReal.ofReal ((gint^θ).toReal) := by
      congr; rw [ENNReal.ofReal_toReal]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) h_gint_eq_top
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ))
        * ENNReal.ofReal (gint.toReal^θ) := by
      rw [← ENNReal.toReal_rpow]
    _ = ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹ * fint.toReal^(1-θ) * gint.toReal^θ) := by
      rw [← ENNReal.ofReal_mul]
      exact mul_nonneg weighted_amgm_factor_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg (1-θ))
    _ ≤ ENNReal.ofReal (fint.toReal + gint.toReal) :=
      ENNReal.ofReal_le_ofReal (weighted_amgm hθ ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    _ = ENNReal.ofReal (fint.toReal) + ENNReal.ofReal (gint.toReal) :=
      ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = fint + gint := by simp [h_fint_eq_top, h_gint_eq_top]
    _ ≤ hint := by exact h_ineq_integral


-- Prekopa-Leindler in 1 dimension assuming boundedness.
-- This removes the sup norm 1 assumption of prekopa_leindler_1d_normalized by scaling.
lemma prekopa_leindler_1d_bounded {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_bounded : iSup f ≠ ⊤)
    (hg_measurable : Measurable g) (hg_bounded : iSup g ≠ ⊤)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by

  -- If f = 0 or g = 0, the conclusion follows easily.
  by_cases hf_zero : f = 0
  · aesop
  by_cases hg_zero : g = 0
  · aesop

  -- From here on, we have f ≠ 0 and g ≠ 0.
  let f' := fun x ↦ (f x) * (iSup f)⁻¹
  let g' := fun x ↦ (g x) * (iSup g)⁻¹
  let h' := fun x ↦ (h x) * ((iSup f)⁻¹)^(1-θ) * ((iSup g)⁻¹)^θ
  let fint := ∫⁻ x, f x
  let gint := ∫⁻ x, g x
  let hint := ∫⁻ x, h x
  let f'int := ∫⁻ x, f' x
  let g'int := ∫⁻ x, g' x
  let h'int := ∫⁻ x, h' x
  let factor : ENNReal := ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹

  have iSupf_ne_zero : iSup f ≠ 0 := iSup_nonzero_of_nonzero hf_zero
  have iSupg_ne_zero : iSup g ≠ 0 := iSup_nonzero_of_nonzero hg_zero
  have iSupf_pos : 0 < iSup f := pos_of_ne_zero iSupf_ne_zero
  have iSupg_pos : 0 < iSup g := pos_of_ne_zero iSupg_ne_zero
  have iSupf_pow_ne_zero : (iSup f)^(1-θ) ≠ 0 :=
    (ne_of_lt (ENNReal.rpow_pos_of_nonneg iSupf_pos (by linarith))).symm
  have iSupg_pow_ne_zero : (iSup g)^θ ≠ 0 :=
    (ne_of_lt (ENNReal.rpow_pos_of_nonneg iSupg_pos (by linarith))).symm
  have iSupf_pow_ne_top : (iSup f)^(1-θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' iSupf_pos hf_bounded
  have iSupg_pow_ne_top : (iSup g)^θ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' iSupg_pos hg_bounded

  -- This is the result for the normalized functions f', g', h'.
  have normalized_result : factor * f'int^(1-θ) * g'int^θ ≤ h'int :=
    have f'_isup1 : iSup f' = 1 := by
      rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel iSupf_ne_zero hf_bounded]
    have g'_isup1 : iSup g' = 1 := by
      rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel iSupg_ne_zero hg_bounded]
    have hf'g'h' : ∀ x y, (f' x)^(1-θ) * (g' y)^θ ≤ h' (x + y) := by
      unfold f' g' h'
      intro x y
      calc
        (f x * (iSup f)⁻¹) ^ (1 - θ) * (g y * (iSup g)⁻¹) ^ θ
            = (f x)^(1 - θ) * ((iSup f)⁻¹) ^ (1 - θ) * (g y) ^ θ * ((iSup g)⁻¹)^θ := by
          rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
          · ring
          · linarith
          linarith
        _ = (f x)^(1 - θ) * (g y) ^ θ * ((iSup f)⁻¹) ^ (1 - θ) * ((iSup g)⁻¹)^θ := by ring
        _ ≤ h' (x + y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hfgh x y) (by apply zero_le)) (by apply zero_le)
    prekopa_leindler_1d_normalized
      hθ
      (by fun_prop) f'_isup1
      (by fun_prop) g'_isup1
      (by fun_prop)
      hf'g'h'

  -- Manipulate the constant factors in normalized_result to obtain the final result for f, g, h.
  have f'int_to_fint : f'int = fint * (iSup f)⁻¹ := lintegral_mul_const (iSup f)⁻¹ hf_measurable
  have g'int_to_gint : g'int = gint * (iSup g)⁻¹ := lintegral_mul_const (iSup g)⁻¹ hg_measurable
  have h'int_to_hint : h'int = hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ := calc
    h'int = ∫⁻ x, ((h x) * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) := by rfl
    _ = ∫⁻ x, ((h x) * ((iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ)) := by congr; ext x; ring
    _ = hint * ((iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) := by rw [lintegral_mul_const]; exact hh_measurable
    _ = hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ := by ring

  change factor * fint^(1-θ) * gint^θ ≤ hint
  calc
    factor * fint^(1-θ) * gint^θ = factor * (f'int * iSup f)^(1-θ) * (g'int * iSup g)^θ := by
      rw [f'int_to_fint, g'int_to_gint]
      congr
      · exact (ENNReal.inv_mul_cancel_right iSupf_ne_zero hf_bounded).symm
      exact (ENNReal.inv_mul_cancel_right iSupg_ne_zero hg_bounded).symm
    _ = (factor * f'int^(1-θ) * g'int^θ) * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
      · ring
      · linarith
      linarith
    _ ≤ h'int * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [ENNReal.mul_le_mul_iff_left]
      · exact normalized_result
      · rw [← pos_iff_ne_zero]; exact ENNReal.mul_pos iSupf_pow_ne_zero iSupg_pow_ne_zero
      · exact ENNReal.mul_ne_top iSupf_pow_ne_top iSupg_pow_ne_top
    _ = (hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [h'int_to_hint]
    _ = hint * ((iSup f)⁻¹^(1-θ) * (iSup f)^(1-θ)) * ((iSup g)⁻¹^θ * (iSup g)^θ) := by ring
    _ = hint * (((iSup f)^(1-θ))⁻¹ * (iSup f)^(1-θ)) * (((iSup g)^θ)⁻¹ * (iSup g)^θ) := by
      congr
      · rw [ENNReal.inv_rpow]
      rw [ENNReal.inv_rpow]
    _ = hint * 1 * 1 := by
      congr
      · exact ENNReal.inv_mul_cancel iSupf_pow_ne_zero iSupf_pow_ne_top
      exact ENNReal.inv_mul_cancel iSupg_pow_ne_zero iSupg_pow_ne_top
    _ = hint := by ring

-- Prekopa-Leindler in 1 dimension. This removes the boundedness assumption of
-- prekopa_leindler_1d_bounded using an approximation argument.
lemma prekopa_leindler_1d {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹ * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by
  let c : ENNReal := ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹
  let f_bounded (n : ℕ) : ℝ → ENNReal := fun x ↦ min (f x) n
  let g_bounded (n : ℕ) : ℝ → ENNReal := fun x ↦ min (g x) n

  have f_bounded_mono : Monotone f_bounded := by
    intro _ _ hab; rw [Pi.le_def]; intro x; exact min_le_min_left (f x) (by simp [hab])
  have g_bounded_mono : Monotone g_bounded := by
    intro _ _ hab; rw [Pi.le_def]; intro x; exact min_le_min_left (g x) (by simp [hab])

  have f_as_sup : ∫⁻ x, f x = ⨆ n, ∫⁻ x, f_bounded n x := calc
    _ = ∫⁻ x, ⨆ n, f_bounded n x := by congr; ext; symm; apply iSup_min_nat
    _ = _ := lintegral_iSup (by fun_prop) f_bounded_mono
  have g_as_sup : ∫⁻ x, g x = ⨆ n, ∫⁻ x, g_bounded n x := calc
    _ = ∫⁻ x, ⨆ n, g_bounded n x := by congr; ext; symm; apply iSup_min_nat
    _ = _ := lintegral_iSup (by fun_prop) g_bounded_mono

  have result_for_bounded : ∀ n m,
      c * (∫⁻ x, f_bounded n x)^(1-θ) * (∫⁻ x, g_bounded m x)^θ ≤ ∫⁻ x, h x := by
    intro n m
    apply prekopa_leindler_1d_bounded hθ (by fun_prop) (iSup_min_nat_ne_top n _)
      (by fun_prop) (iSup_min_nat_ne_top m _) hh_measurable
    intro x y
    calc
      (f_bounded n x)^(1-θ) * (g_bounded m y)^θ ≤ (f x)^(1-θ) * (g y)^θ := by
        gcongr
        · linarith
        · aesop
        · linarith
        aesop
      _ ≤ h (x + y) := hfgh x y

  calc
    c * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ
        = c * (⨆ n, ∫⁻ x, f_bounded n x)^(1-θ) * (⨆ m, ∫⁻ x, g_bounded m x)^θ := by
      rw [f_as_sup, g_as_sup]
    _ = ⨆ n, c * (∫⁻ x, f_bounded n x)^(1-θ) * (⨆ m, ∫⁻ x, g_bounded m x)^θ := by
      rw [← ENNReal.iSup_mul, ← ENNReal.mul_iSup, iSup_rpow_of_pos (by linarith)]
    _ = ⨆ n, ⨆ m, c * (∫⁻ x, f_bounded n x)^(1-θ) * (∫⁻ x, g_bounded m x)^θ := by
      congr; ext; rw [← ENNReal.mul_iSup, iSup_rpow_of_pos hθ.1]
    _ ≤ ∫⁻ x, h x := by apply iSup₂_le; exact result_for_bounded

lemma lintegral_fin1 (F : (Fin 1 → ℝ) → ENNReal) :
    ∫⁻ v : (Fin 1 → ℝ), F v = ∫⁻ x : ℝ, F (fun _ ↦ x) := by
  convert (MeasurePreserving.lintegral_map_equiv F
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
    (volume_preserving_funUnique (Fin 1) ℝ).symm) using 1 <;> rfl

-- Append to the end of a vector
def append {d : ℕ} (x : Fin d → ℝ) (t : Fin 1 → ℝ) : Fin (d + 1) → ℝ :=
  fun i ↦ if h : i.val < d then x ⟨i.val, h⟩ else t default

lemma append_measurable {d : ℕ} (x : Fin d → ℝ) : Measurable (append x) := by
  unfold append
  apply measurable_pi_lambda
  intro
  split
  · fun_prop
  fun_prop

lemma append_measurable' {d : ℕ} (t : Fin 1 → ℝ) : Measurable (fun x : Fin d → ℝ ↦ append x t) := by
  unfold append
  apply measurable_pi_lambda
  intro
  split
  · fun_prop
  fun_prop

lemma append_linear {d : ℕ} (x1 y1 : Fin (d + 1) → ℝ) (x y : Fin 1 → ℝ)
    : append x1 x + append y1 y = append (x1 + y1) (x + y) := by
  unfold append
  aesop

-- Turn a function F : R^(d+1) → R into a function R^1 → R by fixing the first d components to x.
def fix {d : ℕ} (F : (Fin (d + 1) → ℝ) → ENNReal) (x : Fin d → ℝ) : (Fin 1 → ℝ) → ENNReal :=
  F ∘ (append x)

lemma fix_measurable {d : ℕ} {F : (Fin (d + 1) → ℝ) → ENNReal} (hF : Measurable F) (x : Fin d → ℝ)
    : Measurable (fix F x) := by
  exact hF.comp (append_measurable x)

lemma fix_apply {d : ℕ} (F : (Fin (d + 1) → ℝ) → ENNReal) (x : Fin d → ℝ) (y : Fin 1 → ℝ)
    : fix F x y = F (append x y) := by
  rfl

lemma lintegral_fix_eq_lmarginal {d : ℕ}
    (F : (Fin (d + 2) → ℝ) → ENNReal) (x1 : Fin (d + 1) → ℝ)
    : ∫⁻ y : Fin 1 → ℝ, (fix F x1) y = (∫⋯∫⁻_{⟨d+1, by simp⟩}, F) (append x1 default) := by
  have h_lmarginal_singleton := lmarginal_singleton F ⟨d+1, by simp⟩ (μ := fun _ ↦ volume)
  suffices ∫⁻ (y : ℝ), F (Function.update (append x1 default) ⟨d + 1, by simp⟩ y)
      = ∫⁻ (y : Fin 1 → ℝ), fix F x1 y by
    rw [congrFun h_lmarginal_singleton (append x1 default), this]
  rw [lintegral_fin1]
  unfold fix append Function.update
  simp_all only [Pi.default_def, eq_rec_constant, Fin.default_eq_zero, Fin.isValue, dite_eq_ite,
    Function.comp_apply]
  congr; ext; congr; ext i; split
  case e_f.isTrue => simp_all
  case e_f.isFalse h => simp [Fin.val_lt_last h]

lemma lintegral_fix_lintegral_eq_lintegral
    {d : ℕ} {f : (Fin (d + 2) → ℝ) → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
    = ∫⁻ (x : Fin (d + 2) → ℝ), f x := by
  -- This proof works by rewriting the LHS until we can use the volume preserving
  -- measurable equivalence for piFinSuccAbove in mathlib.

  -- Rewrite the integral over Fin 1 → ℝ as an integral over ℝ
  have : ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : Fin 1 → ℝ), (fix f x) t
      = ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : ℝ), f (append x (fun _ ↦ t)) := by
    congr; ext; rw [lintegral_fin1]; rfl
  rw [this]

  -- Rewrite the iterated integral ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ (t : ℝ) ...
  -- as a single integral over ℝ × (Fin (d + 1) → ℝ). The order is swapped for compatibility with
  -- MeasurableEquiv.piFinSuccAbove.
  let equiv : (Fin (d + 2) → ℝ) ≃ᵐ ℝ × (Fin (d + 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) ↦ ℝ) (Fin.last (d + 1))
  let g : ℝ × (Fin (d + 1) → ℝ) → (Fin (d + 2) → ℝ) := fun tx ↦ (append tx.2 fun _ ↦ tx.1)
  have hg_eq_equiv_invFun : g = equiv.invFun := by aesop
  have hg_measurable : Measurable g := by rw [hg_eq_equiv_invFun]; exact equiv.measurable_invFun
  let f' : (ℝ × (Fin (d + 1) → ℝ)) → ENNReal := fun tx ↦ f (append tx.2 fun x ↦ tx.1)
  have hf'_measurable : Measurable f' := by
    apply Measurable.comp hf_measurable; unfold g at hg_measurable; exact hg_measurable
  rw [← MeasureTheory.lintegral_prod_symm' f' hf'_measurable]

  -- Clean up ∂volume.prod volume from lintegral_prod_symm'
  have : ∫⁻ (z : ℝ × (Fin (d + 1) → ℝ)), f' z ∂volume.prod volume
    = ∫⁻ (z : ℝ × (Fin (d + 1) → ℝ)), f' z := by rfl
  rw [this]

  -- Rewrite the integral over ℝ × (Fin (d + 1) → ℝ as an integral over Fin (d + 2) → ℝ
  rw [← MeasureTheory.lintegral_map hf_measurable hg_measurable]
  -- Use the fact that the equivalence is volume preserving
  congr
  rw [hg_eq_equiv_invFun]
  exact (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 2) ↦ ℝ) (Fin.last (d + 1))).symm.map_eq

def PLConditions (n : ℕ) (θ : ℝ) (f g h : (Fin n → ℝ) → ENNReal) : Prop :=
  0 < θ ∧ θ < 1 ∧
  Measurable f ∧ Measurable g ∧ Measurable h ∧
  (∀ x y, (f x)^(1-θ) * (g y)^θ ≤ h (x + y))

-- This is a small wrapper around prekopa_leindler_1d.
lemma prekopa_leindler_1d_fin1
    {θ : ℝ} {f g h : (Fin 1 → ℝ) → ENNReal} (hθfgh : PLConditions 1 θ f g h)
    : ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹ * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by
  let ⟨hθ0, hθ1, hf_measurable, hg_measurable, hh_measurable, hfgh⟩ := hθfgh
  rw [lintegral_fin1 f, lintegral_fin1 g, lintegral_fin1 h]
  exact prekopa_leindler_1d
    ⟨hθ0, hθ1⟩
    (by fun_prop)
    (by fun_prop)
    (by fun_prop)
    (fun x y ↦ hfgh (fun _ ↦ x) (fun _ ↦ y))

-- The Prekopa-Leindler inequality in arbitrary dimension, proved using induction over dimension.
theorem prekopa_leindler
    {d : ℕ} {θ : ℝ} {f g h : (Fin (d + 1) → ℝ) → ENNReal} (hθfgh : PLConditions (d + 1) θ f g h)
    : ENNReal.ofReal ((1 - θ) ^ ((d + 1) * (1 - θ)) * θ ^ ((d + 1) * θ))⁻¹
      * (∫⁻ x, f x) ^ (1 - θ) * (∫⁻ x, g x) ^ θ ≤ ∫⁻ x, h x := by

  induction d using Nat.case_strong_induction_on with
  | hz => simpa using (prekopa_leindler_1d_fin1 hθfgh)
  | hi d hd =>

  -- The goal is to prove the result for Fin (d + 2) → ℝ.
  let ⟨hθ0, hθ1, hf_measurable, hg_measurable, hh_measurable, hfgh⟩ := hθfgh

  -- The inductive hypotheses for Fin 1 → ℝ and Fin (d + 1) → ℝ
  have hyp_0 : ∀ {f g h : (Fin 1 → ℝ) → ENNReal}, PLConditions 1 θ f g h →
      ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹
      * (∫⁻ (x : Fin 1 → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin 1 → ℝ), g x)^θ
      ≤ ∫⁻ (x : Fin 1 → ℝ), h x := by
    have := hd 0
    simp_all
  have hyp_d : ∀ {f g h : (Fin (d + 1) → ℝ) → ENNReal}, PLConditions (d + 1) θ f g h →
      ENNReal.ofReal ((1-θ)^((d+1)*(1-θ)) * θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 1) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 1) → ℝ), g x)^θ
      ≤ ∫⁻ (x : Fin (d + 1) → ℝ), h x := by
    have := hd d
    simp_all

  -- F, G, H are f, g, h with the last coordinate marginalized out
  let F : (Fin (d + 1) → ℝ) → ENNReal := fun x1 ↦ ∫⁻ x, (fix f x1) x
  let G : (Fin (d + 1) → ℝ) → ENNReal := fun x1 ↦ ∫⁻ x, (fix g x1) x
  let H : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ) * ∫⁻ x, (fix h x1) x
  -- F', G', H' are F, G, H written using lmarginal, to use theorems written for lmarginal
  let F' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ (∫⋯∫⁻_{⟨d + 1, by simp⟩}, f ∂fun _ ↦ volume) (append x1 default)
  let G' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ (∫⋯∫⁻_{⟨d + 1, by simp⟩}, g ∂fun _ ↦ volume) (append x1 default)
  let H' : (Fin (d + 1) → ℝ) → ENNReal :=
    fun x1 ↦ ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)
      * (∫⋯∫⁻_{⟨d + 1, by simp⟩}, h ∂fun _ ↦ volume) (append x1 default)
  have h_F_eq_F' : F = F' := by unfold F F'; ext; rw [lintegral_fix_eq_lmarginal]
  have h_G_eq_G' : G = G' := by unfold G G'; ext; rw [lintegral_fix_eq_lmarginal]
  have h_H_eq_H' : H = H' := by unfold H H'; ext; rw [lintegral_fix_eq_lmarginal]
  -- Apply the inductive hypothesis to F, G, H
  have hF_measurable : Measurable F := by
    rw [h_F_eq_F']; unfold F'
    apply Measurable.fun_comp
    · apply Measurable.lmarginal; exact hf_measurable
    exact append_measurable' default
  have hG_measurable : Measurable G := by
    rw [h_G_eq_G']; unfold G'
    apply Measurable.fun_comp
    · apply Measurable.lmarginal; exact hg_measurable
    exact append_measurable' default
  have hH_measurable : Measurable H := by
    rw [h_H_eq_H']; unfold H'
    apply Measurable.fun_comp
    · fun_prop
    apply Measurable.fun_comp
    · apply Measurable.lmarginal; exact hh_measurable
    exact append_measurable' default
  have factor_pos : 0 < (1-θ)^(1-θ)*θ^θ :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) (1-θ)) (Real.rpow_pos_of_pos (by linarith) θ)
  have fix_plconditions : ∀ x1 y1 : Fin (d + 1) → ℝ,
      PLConditions 1 θ (fix f x1) (fix g y1) (fix h (x1 + y1)) := by
    intro x1 y1
    exact ⟨
      hθ0, hθ1, fix_measurable hf_measurable x1, fix_measurable hg_measurable y1,
      fix_measurable hh_measurable (x1+y1), by
        intro x y
        rw [fix_apply, fix_apply, fix_apply]
        have h_result : f (append x1 x)^(1-θ) * g (append y1 y)^θ ≤ h (append x1 x + append y1 y) :=
          hfgh (append x1 x) (append y1 y)
        rw [append_linear x1 y1 x y] at h_result
        exact h_result
    ⟩
  have marginal_pl_condition : ∀ x1 y1 : Fin (d + 1) → ℝ,
      (F x1)^(1-θ) * (G y1)^θ ≤ H (x1 + y1) := by
    intro x1 y1
    calc
      (F x1)^(1-θ) * (G y1)^θ = 1 * (F x1)^(1-θ) * (G y1)^θ := by ring
      _ = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹)
          * (F x1)^(1-θ) * (G y1)^θ := by
        congr
        symm
        exact ENNReal.mul_inv_cancel
          (ENNReal.ofReal_ne_zero_iff.mpr factor_pos) (Ne.symm ENNReal.top_ne_ofReal)
      _ = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ENNReal.ofReal ((1 - θ)^(1-θ)*θ^θ)⁻¹)
          * (F x1)^(1-θ) * (G y1)^θ := by
        congr
        rw [ENNReal.ofReal_inv_of_pos (by linarith)]
      _ = ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)
          * (ENNReal.ofReal ((1 - θ)^(1-θ)*θ^θ)⁻¹ * (F x1)^(1-θ) * (G y1)^θ) := by
        ring
      _ ≤ H (x1 + y1) := by
        rw [ENNReal.mul_le_mul_iff_right
          (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
          (by simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true])]
        exact hyp_0 (fix_plconditions x1 y1)
  have result_d : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 1) → ℝ), F x)^(1-θ)
      * (∫⁻ (x : Fin (d + 1) → ℝ), G x)^θ
      ≤ ∫⁻ (x : Fin (d + 1) → ℝ), H x :=
    hyp_d ⟨hθ0, hθ1, hF_measurable, hG_measurable, hH_measurable, marginal_pl_condition⟩

  -- Now perform manipulations and use Fubini-Tonelli to conclude the theorem for f, g, h.
  have result_d_2 : (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ *
      (ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) *
      (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ) ≤ ∫⁻ (x : Fin (d + 2) → ℝ), h x := by
    unfold F G H at result_d
    have extract_constant :
        ∫⁻ (x : Fin (d + 1) → ℝ), ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ∫⁻ t, (fix h x) t
        = ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ) * ∫⁻ (x : Fin (d + 1) → ℝ), ∫⁻ t, (fix h x) t := by
      rw [lintegral_const_mul']
      exact Ne.symm ENNReal.top_ne_ofReal
    rw [lintegral_fix_lintegral_eq_lintegral hf_measurable,
      lintegral_fix_lintegral_eq_lintegral hg_measurable,
      extract_constant,
      lintegral_fix_lintegral_eq_lintegral hh_measurable,
      ← ENNReal.inv_mul_le_iff
        (ENNReal.ofReal_ne_zero_iff.mpr factor_pos) (Ne.symm ENNReal.top_ne_ofReal)] at result_d
    exact result_d
  have rewrite_lhs_of_result_d_2 :
      (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ * (ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ)
      = (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹ * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ := by ring
  have combine_consts_of_result_d_2 : (ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ))⁻¹
      * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹ =
      ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ := calc
    _ = ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ)⁻¹
        * ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹ := by
      congr; exact Eq.symm (ENNReal.ofReal_inv_of_pos factor_pos)
    _ = ENNReal.ofReal (((1-θ)^(1-θ)*θ^θ)⁻¹ * ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹) :=
      Eq.symm (ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt factor_pos)))
    _ = ENNReal.ofReal (((1-θ)^(1-θ)*(1-θ)^((d+1)*(1-θ))) * (θ^θ * θ^((d+1)*θ)))⁻¹ := by grind
    _ = ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ := by
      congr
      · exact Eq.symm <| Real.rpow_of_add_eq
          (by linarith) (ne_of_gt <| mul_pos (by linarith) (by linarith)) (by grind)
      exact Eq.symm <| Real.rpow_of_add_eq
        (by linarith) (ne_of_gt <| mul_pos (by linarith) (by linarith)) (by grind)
  have result_d_3 : ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹
      * (∫⁻ (x : Fin (d + 2) → ℝ), f x) ^ (1 - θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x) ^ θ ≤
      ∫⁻ (x : Fin (d + 2) → ℝ), h x := by
    rw [rewrite_lhs_of_result_d_2, combine_consts_of_result_d_2] at result_d_2
    exact result_d_2
  have rewrite_const_of_result_d_3 :
      ENNReal.ofReal ((1-θ)^((d+2)*(1-θ))*θ^((d+2)*θ))⁻¹ =
      ENNReal.ofReal ((1-θ)^((↑(d+1)+1)*(1-θ))*θ^((↑(d+1)+1)*θ))⁻¹ := by
    congr 5
    · simp only [Nat.cast_add, Nat.cast_one]
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  change ENNReal.ofReal ((1-θ)^((↑(d+1)+1)*(1-θ))*θ^((↑(d+1)+1)*θ))⁻¹
    * (∫⁻ (x : Fin (d + 2) → ℝ), f x)^(1-θ) * (∫⁻ (x : Fin (d + 2) → ℝ), g x)^θ
    ≤ ∫⁻ (x : Fin (d + 2) → ℝ), h x
  rw [rewrite_const_of_result_d_3] at result_d_3
  exact result_d_3

end AuditedIsoperimetric

end SnapshotModule_028
/- END ported_isoperimetric.prekopa_leindler -/

/- BEGIN ported_isoperimetric.brunn_minkowski -/
section SnapshotModule_029

/- Ported from Jonathan Ho's isoperimetric proof repository, Apache-2.0.
   Upstream: https://github.com/hojonathanho/isoperimetric
   Commit: 29768f8beeaf17295cdf3853d37da35d7e2b0a5f
   Original source and license: ../vendor/isoperimetric_original/.
   Port target: Lean 4.32.1, pinned Mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6.
   Only namespacing/import/API adjustments may be made; final kernel/axiom checks required. -/

namespace AuditedIsoperimetric

open MeasureTheory Set
open scoped Pointwise

lemma brunn_minkowski_infinite
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA : volume A = ⊤) (hB : B.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_top_pow : (⊤ : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = ⊤ :=
    ENNReal.top_rpow_of_pos Nat.inv_pos_of_nat
  calc
    (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ =
        (volume (A + {hB.some}))^((d:ℝ)+1)⁻¹ := by
      simp [hA, h_top_pow]
    _ ≤ (volume (A + B))^((d:ℝ)+1)⁻¹ := by gcongr; exact singleton_subset_iff.mpr hB.some_mem
    _ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by gcongr

lemma brunn_minkowski_zero
    {d : ℕ} {A B C : Set (Fin (d + 1) → ℝ)}
    (hA_zero : volume A = 0) (hA_nonempty : A.Nonempty) (hABC : A + B ⊆ C)
    : (volume A)^((d:ℝ)+1)⁻¹ + (volume B)^((d:ℝ)+1)⁻¹ ≤ (volume C)^((d:ℝ)+1)⁻¹ := by
  have h_zero_pow : (0 : ENNReal) ^ ((d : ℝ) + 1)⁻¹ = 0 :=
    ENNReal.zero_rpow_of_pos Nat.inv_pos_of_nat
  simp [hA_zero, h_zero_pow]
  gcongr 1
  calc
    volume B = volume ({hA_nonempty.some} + B) := by simp
    _ ≤ volume (A + B) := by gcongr; exact singleton_subset_iff.mpr hA_nonempty.some_mem
    _ ≤ volume C := by gcongr

-- Prekopa-Leindler for indicator functions
lemma prekopa_leindler_indicator
    {d : ℕ} {θ : ℝ} {A B : Set (Fin (d + 1) → ℝ)}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hA_measurable : MeasurableSet A) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * volume A^(1-θ) * volume B^θ ≤ volume (A + B) := by
  have : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ x, (A.indicator fun _ ↦ (1 : ENNReal)) x)^(1-θ)
      * (∫⁻ x, (B.indicator fun _ ↦ (1 : ENNReal)) x)^θ
      ≤ ∫⁻ x, ((A + B).indicator fun _ ↦ (1 : ENNReal)) x := prekopa_leindler ⟨
    hθ0, hθ1, by measurability, by measurability, by measurability, by
    show ∀ (x y : Fin (d + 1) → ℝ),
      ((A.indicator fun _ ↦ (1 : ENNReal)) x) ^ (1 - θ)
      * ((B.indicator fun _ ↦ (1 : ENNReal)) y) ^ θ
      ≤ ((A + B).indicator fun _ ↦ (1 : ENNReal)) (x + y)
    intro x y
    unfold indicator
    simp_all only [ite_pow, ENNReal.one_rpow, sub_pos, ENNReal.zero_rpow_of_pos, mul_ite, mul_one,
      mul_zero]
    split
    · split
      · split
        · rfl
        · expose_names; exact False.elim (h_2 (add_mem_add h_1 h))
      · simp only [zero_le]
    simp only [zero_le]⟩
  simp_all  -- Rewrite the integrals of indicators as volumes

-- The Brunn-Minkowski inequality in arbitrary dimension.
theorem brunn_minkowski
    {d : ℕ} {A B : Set (Fin (d + 1) → ℝ)}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : volume A ^ ((d:ℝ)+1)⁻¹ + volume B ^ ((d:ℝ)+1)⁻¹ ≤ volume (A + B) ^ ((d:ℝ)+1)⁻¹ := by
  -- Handle the cases of 0 volume or infinite volume
  have hAB : A + B ⊆ A + B := by rfl
  by_cases hvolAinf : volume A = ⊤
  · exact brunn_minkowski_infinite hvolAinf hB_nonempty hAB
  by_cases hvolAzero : volume A = 0
  · exact brunn_minkowski_zero hvolAzero hA_nonempty hAB
  by_cases hvolBinf : volume B = ⊤
  · rw [add_comm]; nth_rw 1 [add_comm A B] at hAB
    exact brunn_minkowski_infinite hvolBinf hA_nonempty hAB
  by_cases hvolBzero : volume B = 0
  · rw [add_comm]; nth_rw 1 [add_comm A B] at hAB
    exact brunn_minkowski_zero hvolBzero hB_nonempty hAB

  -- Apply Prekopa-Leindler to the indicator functions for A, B, and A + B
  let f : (Fin (d + 1) → ℝ) → ENNReal := A.indicator fun _ ↦ 1
  let g : (Fin (d + 1) → ℝ) → ENNReal := B.indicator fun _ ↦ 1
  let h : (Fin (d + 1) → ℝ) → ENNReal := (A + B).indicator fun _ ↦ 1
  let D : ℝ := d + 1
  let va : ℝ := (volume A).toReal^D⁻¹
  let vb : ℝ := (volume B).toReal^D⁻¹
  let θ : ℝ := vb * (va + vb)⁻¹
  have h_va_pos : 0 < va := by
    apply Real.rpow_pos_of_pos; exact ENNReal.toReal_pos hvolAzero hvolAinf
  have h_vb_pos : 0 < vb := by
    apply Real.rpow_pos_of_pos; exact ENNReal.toReal_pos hvolBzero hvolBinf
  have h_va_plus_vb_pos : 0 < va + vb := by linarith
  -- We have θ ∈ (0, 1) since A and B both have nonzero and non-infinite volume.
  have hθ0 : 0 < θ := div_pos h_vb_pos (add_pos' h_va_pos h_vb_pos)
  have hθ1 : θ < 1 := (mul_inv_lt_iff₀ h_va_plus_vb_pos).mpr (by linarith)
  have h_result : ENNReal.ofReal ((1-θ)^(D*(1-θ))*θ^(D*θ))⁻¹
      * volume A^(1-θ) * volume B^θ ≤ volume (A + B) :=
    prekopa_leindler_indicator hθ0 hθ1 hA_measurable hB_measurable hAB_measurable

  -- Raise both sides to the 1/D power
  have h_result_simp : ENNReal.ofReal ((1-θ)^(1-θ)*θ^θ)⁻¹
      * (volume A^(1-θ))^D⁻¹ * (volume B^θ)^D⁻¹ ≤ volume (A + B)^D⁻¹ := by
    have h_D_θ_expr_pos : 0 < (1-θ)^(D*(1-θ))*θ^(D*θ) := by
      apply mul_pos
      · apply Real.rpow_pos_of_pos; linarith
      apply Real.rpow_pos_of_pos hθ0
    have h_Dinv_pos : 0 < D⁻¹ := Nat.inv_pos_of_nat
    have h_Dinv_nonneg : 0 ≤ D⁻¹ := le_of_lt h_Dinv_pos
    rw [← ENNReal.rpow_le_rpow_iff h_Dinv_pos,
      ENNReal.mul_rpow_of_nonneg _ _ h_Dinv_nonneg,
      ENNReal.mul_rpow_of_nonneg _ _ h_Dinv_nonneg,
      ENNReal.ofReal_rpow_of_pos (by rw [inv_pos]; exact h_D_θ_expr_pos)] at h_result
    have : ((1-θ)^(D*(1-θ))*θ^(D*θ))⁻¹^D⁻¹ = ((1-θ)^(1-θ)*θ^θ)⁻¹ := by
      rw [Real.inv_rpow (le_of_lt h_D_θ_expr_pos),
        Real.mul_rpow
          (Real.rpow_nonneg (by linarith) (D * (1 - θ))) (Real.rpow_nonneg (le_of_lt hθ0) (D * θ)),
        ← Real.rpow_mul (by linarith), ← Real.rpow_mul (le_of_lt hθ0)]
      congr 3
      · grind
      grind
    rw [this] at h_result
    exact h_result

  -- Simplify to get the desired result
  have h_result_simp_2 : ENNReal.ofReal (va + vb) ≤ volume (A + B) ^ D⁻¹ := by
    have h_cancel_D : D⁻¹ * D = 1 := by unfold D; field_simp
    have hva : volume A = (ENNReal.ofReal va)^D := by
      rw [ENNReal.ofReal_rpow_of_pos h_va_pos, ← Real.rpow_mul ENNReal.toReal_nonneg]
      simp [h_cancel_D, hvolAinf]
    have hvb : volume B = (ENNReal.ofReal vb)^D := by
      rw [ENNReal.ofReal_rpow_of_pos h_vb_pos, ← Real.rpow_mul ENNReal.toReal_nonneg]
      simp [h_cancel_D, hvolBinf]
    have h_va_vb : 1 - vb * (va + vb)⁻¹ = va * (va + vb)⁻¹ := by grind
    have h_vapvb_inv_pos: 0 < (va + vb)⁻¹ := inv_pos.mpr h_va_plus_vb_pos
    have h_expr_nonneg : 0 ≤
        ((va*(va + vb)⁻¹)^(va*(va + vb)⁻¹) * (vb*(va + vb)⁻¹)^(vb*(va + vb)⁻¹))⁻¹ := by
      rw [inv_nonneg]
      exact mul_nonneg
        (Real.rpow_nonneg
          (mul_nonneg (le_of_lt h_va_pos) (le_of_lt h_vapvb_inv_pos)) (va * (va + vb)⁻¹))
        (Real.rpow_nonneg
          (mul_nonneg (le_of_lt h_vb_pos) (le_of_lt h_vapvb_inv_pos)) (vb * (va + vb)⁻¹))
    have h_expr_2_nonneg : 0 ≤
        ((va*(va + vb)⁻¹)^(va*(va + vb)⁻¹) * (vb*(va + vb)⁻¹)^(vb*(va + vb)⁻¹))⁻¹
        * ((va^D)^(va*(va + vb)⁻¹))^D⁻¹ := by
      apply mul_nonneg h_expr_nonneg
      apply Real.rpow_nonneg; apply Real.rpow_nonneg; apply Real.rpow_nonneg (le_of_lt h_va_pos)
    rw [hva, hvb, h_va_vb,
      ENNReal.ofReal_rpow_of_pos h_va_pos,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h_va_pos D),
      ENNReal.ofReal_rpow_of_pos
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos h_va_pos D) (va * (va + vb)⁻¹)),
      ENNReal.ofReal_rpow_of_pos h_vb_pos,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h_vb_pos D),
      ENNReal.ofReal_rpow_of_pos
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos h_vb_pos D) (vb * (va + vb)⁻¹)),
      ← ENNReal.ofReal_mul h_expr_nonneg, ← ENNReal.ofReal_mul h_expr_2_nonneg,
      mul_inv] at h_result_simp
    have : ((va^D)^(va*(va + vb)⁻¹))^D⁻¹ = va^(va*(va + vb)⁻¹) := by
      rw [← Real.rpow_mul (Real.rpow_nonneg (le_of_lt h_va_pos) D),
        ← Real.rpow_mul (le_of_lt h_va_pos)]
      grind
    rw [this] at h_result_simp
    have : ((vb^D)^(vb*(va + vb)⁻¹))^D⁻¹ = vb^(vb*(va + vb)⁻¹) := by
      rw [← Real.rpow_mul (Real.rpow_nonneg (le_of_lt h_vb_pos) D),
        ← Real.rpow_mul (le_of_lt h_vb_pos)]
      congr 1; unfold D; field_simp
    rw [this] at h_result_simp
    have : ((va*(va+vb)⁻¹) ^ (va*(va+vb)⁻¹))⁻¹
        = (va^(va*(va+vb)⁻¹))⁻¹ * (va+vb)^(va*(va+vb)⁻¹) := by
      rw [← Real.inv_rpow ((le_mul_inv_iff₀ h_va_plus_vb_pos).mpr (by linarith)),
        mul_inv, inv_inv,
        Real.mul_rpow (inv_nonneg.mpr (le_of_lt h_va_pos)) (le_of_lt h_va_plus_vb_pos)]
      congr
      rw [Real.inv_rpow (le_of_lt h_va_pos)]
    rw [this] at h_result_simp
    have : ((vb*(va+vb)⁻¹) ^ (vb*(va+vb)⁻¹))⁻¹
        = (vb^(vb*(va+vb)⁻¹))⁻¹ * (va+vb)^(vb*(va+vb)⁻¹) := by
      rw [← Real.inv_rpow ((le_mul_inv_iff₀ h_va_plus_vb_pos).mpr (by linarith)),
        mul_inv, inv_inv,
        Real.mul_rpow (inv_nonneg.mpr (le_of_lt h_vb_pos)) (le_of_lt h_va_plus_vb_pos)]
      congr
      rw [Real.inv_rpow (le_of_lt h_vb_pos)]
    rw [this] at h_result_simp
    have : (va^(va*(va + vb)⁻¹))⁻¹ * (va + vb)^(va*(va + vb)⁻¹)
        * ((vb^(vb*(va + vb)⁻¹))⁻¹ * (va + vb)^(vb*(va + vb)⁻¹))
        * va^(va*(va + vb)⁻¹) * vb^(vb*(va + vb)⁻¹) = va + vb := calc
      _ = ((va^(va*(va + vb)⁻¹))⁻¹ * va^(va*(va + vb)⁻¹))
          * ((vb^(vb*(va + vb)⁻¹))⁻¹ * vb^(vb*(va + vb)⁻¹))
          * ((va + vb)^(va*(va + vb)⁻¹) * (va + vb)^(vb*(va + vb)⁻¹)) := by ring
      _ = ((va + vb)^(va*(va + vb)⁻¹) * (va + vb)^(vb*(va + vb)⁻¹)) := by
        field_simp
      _ = (va + vb)^(va*(va + vb)⁻¹ + vb*(va + vb)⁻¹) := by rw [Real.rpow_add h_va_plus_vb_pos]
      _ = va + vb := by field_simp; apply Real.rpow_one
    rw [this] at h_result_simp
    exact h_result_simp

  -- Final manipulation to remove ENNReal.ofReal and .toReal
  have h_result_simp_3 : volume A^D⁻¹ + volume B^D⁻¹ ≤ volume (A + B)^D⁻¹ := by
    rw [ENNReal.ofReal_add (le_of_lt h_va_pos) (le_of_lt h_vb_pos),
      ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hvolAzero hvolAinf),
      ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hvolBzero hvolBinf),
      ENNReal.ofReal_toReal hvolAinf, ENNReal.ofReal_toReal hvolBinf] at h_result_simp_2
    exact h_result_simp_2

  exact h_result_simp_3

-- This is a wrapper around brunn_minkowski for EuclideanSpace ℝ (Fin (d + 1)).
theorem brunn_minkowski_euclideanSpace
    {d : ℕ} {A B : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : volume A ^ ((d:ℝ)+1)⁻¹ + volume B ^ ((d:ℝ)+1)⁻¹ ≤ volume (A + B) ^ ((d:ℝ)+1)⁻¹ := by
  let e : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm
  have h_add : e '' A + e '' B = e '' (A + B) := by
    ext
    simp only [mem_image, mem_add, exists_exists_and_eq_and]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a + b, add_mem_add ha hb, rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have h_vol : ∀ S, MeasurableSet S → volume (e '' S) = volume S := by
    intro S hS
    rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 1))).symm.map_eq,
      Measure.map_apply (by fun_prop) hS]
    congr
    aesop
  let h_bm : volume (e '' A) ^ ((d:ℝ)+1)⁻¹ + volume (e '' B) ^ ((d:ℝ)+1)⁻¹
      ≤ volume (e '' A + e '' B) ^ ((d:ℝ)+1)⁻¹ :=
    brunn_minkowski
      (hA_nonempty.image ⇑e) (e.measurableSet_image.mpr hA_measurable)
      (hB_nonempty.image ⇑e) (e.measurableSet_image.mpr hB_measurable)
      (by rw [h_add]; exact e.measurableSet_image.mpr hAB_measurable)
  rw [h_vol _ hA_measurable, h_vol _ hB_measurable, h_add, h_vol _ hAB_measurable] at h_bm
  exact h_bm

end AuditedIsoperimetric

end SnapshotModule_029
/- END ported_isoperimetric.brunn_minkowski -/

/- BEGIN grunbaum_bm_algebra -/
section SnapshotModule_030

namespace GrunbaumBM
open Set MeasureTheory
open scoped Pointwise ENNReal

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin (d+1))

noncomputable def rootVolume (d : ℕ) (K : Set (Space d)) : ℝ :=
  (volume K).toReal ^ ((d : ℝ)+1)⁻¹

theorem rootVolume_nonneg (d : ℕ) (K : Set (Space d)) : 0 ≤ rootVolume d K :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

theorem rootVolume_smul (d : ℕ) (K : Set (Space d)) {alpha : ℝ} (ha : 0 ≤ alpha) :
    rootVolume d (alpha • K) = alpha*rootVolume d K := by
  unfold rootVolume
  rw [Measure.addHaar_smul_of_nonneg volume ha]
  simp only [finrank_euclideanSpace,Fintype.card_fin,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha (d+1))]
  rw [Real.mul_rpow (pow_nonneg ha _) ENNReal.toReal_nonneg]
  have hpower : (alpha^(d+1) : ℝ)^((d : ℝ)+1)⁻¹ = alpha := by
    rw [← Real.rpow_natCast alpha (d+1),← Real.rpow_mul ha]
    have hcancel : ((d+1 : ℕ) : ℝ)*((d : ℝ)+1)⁻¹ = 1 := by
      push_cast
      field_simp
    rw [hcancel,Real.rpow_one]
  rw [hpower]

theorem rootVolume_mono (d : ℕ) {A B : Set (Space d)} (hAB : A ⊆ B)
    (hB : volume B ≠ ∞) : rootVolume d A ≤ rootVolume d B := by
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hB (measure_mono hAB))
  positivity

end GrunbaumBM

end SnapshotModule_030
/- END grunbaum_bm_algebra -/

/- BEGIN grunbaum_bm_bridge -/
section SnapshotModule_031

namespace GrunbaumBM
open Set MeasureTheory
open scoped Pointwise ENNReal

/-- The actual audited BM theorem, converted to finite real root volumes. -/
theorem rootVolume_brunn_minkowski (d : ℕ) {A B : Set (Space d)}
    (hAne : A.Nonempty) (hAc : IsCompact A) (hBne : B.Nonempty) (hBc : IsCompact B) :
    rootVolume d A+rootVolume d B ≤ rootVolume d (A+B) := by
  have h := AuditedIsoperimetric.brunn_minkowski_euclideanSpace hAne hAc.measurableSet
    hBne hBc.measurableSet (hAc.add hBc).measurableSet
  have hr : 0 ≤ ((d : ℝ)+1)⁻¹ := by positivity
  have hAfin : (volume A)^((d : ℝ)+1)⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr hAc.measure_ne_top
  have hBfin : (volume B)^((d : ℝ)+1)⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr hBc.measure_ne_top
  have hABfin : (volume (A+B))^((d : ℝ)+1)⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr (hAc.add hBc).measure_ne_top
  have ht := ENNReal.toReal_mono hABfin h
  rw [ENNReal.toReal_add hAfin hBfin] at ht
  simpa only [rootVolume,← ENNReal.toReal_rpow] using ht

noncomputable def cap {d : ℕ} (K : Set (Space d)) (ell : Space d →L[ℝ] ℝ)
    (offset t : ℝ) : Set (Space d) := K ∩ {x | ell x ≤ offset+t}

theorem cap_compact {d : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    (ell : Space d →L[ℝ] ℝ) (offset t : ℝ) : IsCompact (cap K ell offset t) :=
  hK.inter_right (isClosed_Iic.preimage ell.continuous)

theorem cap_scaled_sum_subset {d : ℕ} {K : Set (Space d)} (hK : Convex ℝ K)
    (ell : Space d →L[ℝ] ℝ) (offset s t alpha beta : ℝ)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hab : alpha+beta=1) :
    alpha • cap K ell offset s+beta • cap K ell offset t ⊆
      cap K ell offset (alpha*s+beta*t) := by
  rintro z ⟨u,hu,v,hv,rfl⟩
  rcases hu with ⟨x,hx,rfl⟩
  rcases hv with ⟨y,hy,rfl⟩
  refine ⟨hK hx.1 hy.1 ha hb hab, ?_⟩
  change ell (alpha • x+beta • y) ≤ offset+(alpha*s+beta*t)
  simp only [map_add,map_smul,smul_eq_mul]
  calc
    alpha*ell x+beta*ell y ≤ alpha*(offset+s)+beta*(offset+t) :=
      add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    _ = (alpha+beta)*offset+(alpha*s+beta*t) := by ring
    _ = offset+(alpha*s+beta*t) := by rw [hab,one_mul]

/-- General high-dimensional cap-volume root concavity derived from the proved
BM inequality, not supplied as a concavity hypothesis. -/
theorem cap_rootVolume_concave {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (ell : Space d →L[ℝ] ℝ) (offset : ℝ)
    {S : Set ℝ} (hS : Convex ℝ S)
    (hne : ∀ t ∈ S, (cap K ell offset t).Nonempty) :
    ConcaveOn ℝ S (fun t => rootVolume d (cap K ell offset t)) := by
  refine ⟨hS, ?_⟩
  intro s hs t ht alpha beta ha hb hab
  change alpha*rootVolume d (cap K ell offset s)+beta*rootVolume d (cap K ell offset t) ≤
    rootVolume d (cap K ell offset (alpha*s+beta*t))
  have hAc : IsCompact (alpha • cap K ell offset s) :=
    IsCompact.smul alpha (cap_compact hKc ell offset s)
  have hBc : IsCompact (beta • cap K ell offset t) :=
    IsCompact.smul beta (cap_compact hKc ell offset t)
  have hAne : (alpha • cap K ell offset s).Nonempty := by
    obtain ⟨x,hx⟩ := hne s hs
    exact ⟨alpha • x,x,hx,rfl⟩
  have hBne : (beta • cap K ell offset t).Nonempty := by
    obtain ⟨x,hx⟩ := hne t ht
    exact ⟨beta • x,x,hx,rfl⟩
  calc
    alpha*rootVolume d (cap K ell offset s)+beta*rootVolume d (cap K ell offset t) =
        rootVolume d (alpha • cap K ell offset s)+rootVolume d (beta • cap K ell offset t) := by
      rw [rootVolume_smul d _ ha,rootVolume_smul d _ hb]
    _ ≤ rootVolume d (alpha • cap K ell offset s+beta • cap K ell offset t) :=
      rootVolume_brunn_minkowski d hAne hAc hBne hBc
    _ ≤ rootVolume d (cap K ell offset (alpha*s+beta*t)) :=
      rootVolume_mono d (cap_scaled_sum_subset hKv ell offset s t alpha beta ha hb hab)
        (cap_compact hKc ell offset (alpha*s+beta*t)).measure_ne_top

/-- Log-concavity of the true normalized cap volume for every general compact
convex body. Only positivity on the selected interval remains to select its
support; no density, smoothness or cap concavity is assumed. -/
theorem log_normalized_cap_volume_concave {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (ell : Space d →L[ℝ] ℝ) (offset : ℝ)
    {S : Set ℝ} (hS : Convex ℝ S)
    (hpositive : ∀ t ∈ S, 0 < (volume (cap K ell offset t)).toReal)
    (hKpositive : 0 < (volume K).toReal) :
    ConcaveOn ℝ S (fun t => Real.log ((volume (cap K ell offset t)).toReal/(volume K).toReal)) := by
  have hne : ∀ t ∈ S, (cap K ell offset t).Nonempty := by
    intro t ht
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    have hh := hpositive t ht
    rw [hn,measure_empty,ENNReal.toReal_zero] at hh
    linarith
  have hroot := cap_rootVolume_concave hKc hKv ell offset hS hne
  have hrootpos : ∀ t ∈ S, 0 < rootVolume d (cap K ell offset t) := by
    intro t ht
    exact Real.rpow_pos_of_pos (hpositive t ht) _
  have hlog := GrunbaumDevelopment.log_of_positive_concave hroot hrootpos
  have hscaled := hlog.smul (show 0 ≤ (d : ℝ)+1 by positivity)
  have hshifted := hscaled.add_const (-Real.log (volume K).toReal)
  apply hshifted.congr
  intro t ht
  change ((d : ℝ)+1)*Real.log (rootVolume d (cap K ell offset t)) + (-Real.log (volume K).toReal) =
    Real.log ((volume (cap K ell offset t)).toReal/(volume K).toReal)
  rw [Real.log_div (hpositive t ht).ne' hKpositive.ne']
  unfold rootVolume
  rw [Real.log_rpow (hpositive t ht)]
  have hcancel : ((d : ℝ)+1)*((d : ℝ)+1)⁻¹ = 1 := by field_simp
  rw [← mul_assoc,hcancel,one_mul]
  ring

end GrunbaumBM

end SnapshotModule_031
/- END grunbaum_bm_bridge -/

/- BEGIN grunbaum_bm_cdf -/
section SnapshotModule_032

namespace GrunbaumBM
open Set MeasureTheory ProbabilityTheory GrunbaumDevelopment
open scoped ENNReal

/-- Exact CDF of the actual centered scalar projection of normalized volume. -/
theorem projected_cdf_eq_cap_ratio {d : ℕ} (K : Set (Space d))
    (ell : Space d →L[ℝ] ℝ) (offset t : ℝ)
    (hKpositive : volume K ≠ 0) (hKfinite : volume K ≠ ∞) :
    cdf ((normalizedRestriction volume K).map (fun x => ell x-offset)) t =
      (volume (cap K ell offset t)).toReal/(volume K).toReal := by
  letI := normalizedRestriction_isProbability volume K hKpositive hKfinite
  have hm : Measurable (fun x => ell x-offset) := ell.measurable.sub measurable_const
  letI : IsProbabilityMeasure ((normalizedRestriction volume K).map (fun x => ell x-offset)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  rw [cdf_eq_real,measureReal_def,Measure.map_apply hm measurableSet_Iic,
    normalizedRestriction,Measure.smul_apply,Measure.restrict_apply (hm measurableSet_Iic)]
  have hset : ((fun x => ell x-offset) ⁻¹' Iic t) ∩ K = cap K ell offset t := by
    ext x
    simp only [cap,mem_inter_iff,mem_preimage,mem_Iic,mem_setOf_eq]
    constructor
    · intro h
      exact ⟨h.2,by linarith [h.1]⟩
    · intro h
      exact ⟨by linarith [h.2],h.1⟩
  rw [hset]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  ring

/-- The log-CDF shape of the actual projection law follows from audited BM,
with positivity on S selecting the nontrivial support. No log-concavity of the
CDF or of any marginal density is supplied as a premise. -/
theorem projected_cdf_log_concave {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKpositive : volume K ≠ 0)
    (ell : Space d →L[ℝ] ℝ) (offset : ℝ) {S : Set ℝ} (hS : Convex ℝ S)
    (hpositive : ∀ t ∈ S,
      0 < cdf ((normalizedRestriction volume K).map (fun x => ell x-offset)) t) :
    ConcaveOn ℝ S
      (fun t => Real.log (cdf ((normalizedRestriction volume K).map (fun x => ell x-offset)) t)) := by
  have htotal : 0 < (volume K).toReal := ENNReal.toReal_pos hKpositive hKc.measure_ne_top
  have hcapPos : ∀ t ∈ S, 0 < (volume (cap K ell offset t)).toReal := by
    intro t ht
    have h := hpositive t ht
    rw [projected_cdf_eq_cap_ratio K ell offset t hKpositive hKc.measure_ne_top] at h
    have hmul := mul_pos h htotal
    simpa only [div_mul_cancel₀ _ htotal.ne'] using hmul
  have hlog := log_normalized_cap_volume_concave hKc hKv ell offset hS hcapPos htotal
  apply hlog.congr
  intro t ht
  change Real.log ((volume (cap K ell offset t)).toReal/(volume K).toReal) =
    Real.log (cdf ((normalizedRestriction volume K).map (fun x => ell x-offset)) t)
  rw [projected_cdf_eq_cap_ratio K ell offset t hKpositive hKc.measure_ne_top]

end GrunbaumBM

end SnapshotModule_032
/- END grunbaum_bm_cdf -/

/- BEGIN grunbaum_complete -/
section SnapshotModule_033

namespace GrunbaumComplete
open Set MeasureTheory ProbabilityTheory GrunbaumBM ConvexBodyCDF
open scoped ENNReal Pointwise

/-- The complete dimension-free centroid probability bound for the actual
normalized-volume projection of an arbitrary full-dimensional convex body. -/
theorem centroid_projection_probability_lower {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (ell : Space d →L[ℝ] ℝ) (hell : ell ≠ 0) :
    Real.exp (-1) ≤ cdf (centeredLaw K ell) 0 := by
  have hpositive : volume K ≠ 0 := (body_volume_positive hKi).ne'
  have hfinite : volume K ≠ ∞ := hKc.measure_ne_top
  letI : IsProbabilityMeasure (centeredLaw K ell) :=
    shiftedLaw_probability K hpositive hfinite ell (ell (centroid K))
  obtain ⟨a,b,ha,hb,hcont,hstrict,hFa,hFb,hmem,hi,hm⟩ :=
    centeredLaw_support_data hKc hKv hKi ell hell
  have hCDFpos : ∀ t ∈ Ioo a b, 0 < cdf (centeredLaw K ell) t := by
    intro t ht
    have h := hstrict (show a ∈ Icc a b from ⟨le_rfl,(lt_trans ha hb).le⟩)
      (show t ∈ Icc a b from ⟨ht.1.le,ht.2.le⟩) ht.1
    simpa [hFa] using h
  have hshape : ConcaveOn ℝ (Ioo a b) (fun t => Real.log (cdf (centeredLaw K ell) t)) :=
    projected_cdf_log_concave hKc hKv hpositive ell (ell (centroid K)) (convex_Ioo a b) hCDFpos
  exact GrunbaumCDFGeneral.cdf_centroid_mass_bound_no_density
    (centeredLaw K ell) ha hb hcont hstrict hFa hFb hshape hmem hi hm

theorem centroid_cap_volume_lower_real {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (ell : Space d →L[ℝ] ℝ) (hell : ell ≠ 0) :
    Real.exp (-1)*(volume K).toReal ≤
      (volume (cap K ell (ell (centroid K)) 0)).toReal := by
  have hpositive : volume K ≠ 0 := (body_volume_positive hKi).ne'
  have hfinite : volume K ≠ ∞ := hKc.measure_ne_top
  have htotal : 0 < (volume K).toReal := ENNReal.toReal_pos hpositive hfinite
  have h := centroid_projection_probability_lower hKc hKv hKi ell hell
  have hratio : cdf (centeredLaw K ell) 0 =
      (volume (cap K ell (ell (centroid K)) 0)).toReal/(volume K).toReal :=
    projected_cdf_eq_cap_ratio K ell (ell (centroid K)) 0 hpositive hfinite
  rw [hratio] at h
  have hm := mul_le_mul_of_nonneg_right h htotal.le
  simpa only [div_mul_cancel₀ _ htotal.ne'] using hm

theorem centroid_cap_volume_upper_real {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (ell : Space d →L[ℝ] ℝ) (hell : ell ≠ 0) :
    (volume (cap K ell (ell (centroid K)) 0)).toReal ≤
      (1-Real.exp (-1))*(volume K).toReal := by
  let A := cap K ell (ell (centroid K)) 0
  let B := cap K (-ell) ((-ell) (centroid K)) 0
  have hAc : IsCompact A := cap_compact hKc ell (ell (centroid K)) 0
  have hBc : IsCompact B := cap_compact hKc (-ell) ((-ell) (centroid K)) 0
  have hUnion : A ∪ B=K := by
    ext x
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro hx
      rcases le_total (ell x) (ell (centroid K)) with hle | hge
      · exact Or.inl ⟨hx,by simpa only [mem_setOf_eq,add_zero] using hle⟩
      · exact Or.inr ⟨hx,by simpa only [mem_setOf_eq,ContinuousLinearMap.neg_apply,add_zero] using neg_le_neg hge⟩
  have hInter : volume (A ∩ B)=0 := by
    apply measure_mono_null (t := {x | ell x=ell (centroid K)})
    · intro x hx
      have hl : ell x ≤ ell (centroid K) := by simpa only [mem_setOf_eq,add_zero] using hx.1.2
      have hr : -ell x ≤ -ell (centroid K) := by
        simpa only [mem_setOf_eq,ContinuousLinearMap.neg_apply,add_zero] using hx.2.2
      change ell x=ell (centroid K)
      linarith
    · exact linear_fiber_zero ell hell (ell (centroid K))
  have hMass := measure_union_add_inter (μ := (volume : Measure (Space d))) A hBc.measurableSet
  rw [hUnion,hInter,add_zero] at hMass
  have hReal := congrArg ENNReal.toReal hMass
  rw [ENNReal.toReal_add hAc.measure_ne_top hBc.measure_ne_top] at hReal
  have hneg : -ell ≠ 0 := by simpa only [neg_ne_zero] using hell
  have hLower : Real.exp (-1)*(volume K).toReal ≤ (volume B).toReal :=
    centroid_cap_volume_lower_real hKc hKv hKi (-ell) hneg
  change (volume A).toReal ≤ (1-Real.exp (-1))*(volume K).toReal
  nlinarith

theorem centroid_cap_volume_upper {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (ell : Space d →L[ℝ] ℝ) (hell : ell ≠ 0) :
    volume (cap K ell (ell (centroid K)) 0) ≤
      ENNReal.ofReal (1-Real.exp (-1))*volume K := by
  have hreal := centroid_cap_volume_upper_real hKc hKv hKi ell hell
  have hcoef : 0 ≤ 1-Real.exp (-1) := by
    have h := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
    have hh : Real.exp (-1) ≤ 1 := by simpa using h
    linarith
  have hleft : volume (cap K ell (ell (centroid K)) 0) ≠ ∞ :=
    (cap_compact hKc ell (ell (centroid K)) 0).measure_ne_top
  have hright : ENNReal.ofReal (1-Real.exp (-1))*volume K ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hKc.measure_ne_top
  apply (ENNReal.toReal_le_toReal hleft hright).mp
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hcoef] using hreal

/-- Grunbaum's exact centroid halfspace-volume theorem, in every positive
Euclidean dimension. The centroid is the actual normalized-volume Bochner
integral. No body regularity beyond compact convex nonempty interior is assumed. -/
theorem centroid_halfspace_volume_le {d : ℕ} {K : Set (Space d)}
    (hKc : IsCompact K) (hKv : Convex ℝ K) (hKi : (interior K).Nonempty)
    (ell : Space d →L[ℝ] ℝ) (hell : ell ≠ 0) :
    volume (K ∩ {x | ell (x-centroid K) ≤ 0}) ≤
      ENNReal.ofReal (1-Real.exp (-1))*volume K := by
  have hset : K ∩ {x | ell (x-centroid K) ≤ 0} = cap K ell (ell (centroid K)) 0 := by
    ext x
    simp only [cap,mem_inter_iff,mem_setOf_eq,map_sub,sub_nonpos,add_zero]
  rw [hset]
  exact centroid_cap_volume_upper hKc hKv hKi ell hell

end GrunbaumComplete

end SnapshotModule_033
/- END grunbaum_complete -/

/- BEGIN grunbaum_centroid_program -/
section SnapshotModule_034

namespace PaperCentroidProgram
open Set MeasureTheory
open scoped RealInnerProductSpace
noncomputable section

/-- The actual one-step shrink fact required by the real finite centroid
program. It is proved from the complete Grunbaum theorem, not assumed. -/
theorem actual_centroid_shrink {n : ℕ} {P : Set (Space n)}
    (hPc : IsCompact P) (hPv : Convex ℝ P) (hPi : (interior P).Nonempty)
    (v : Space n) (hv : ‖v‖=1) :
    (volume (cut P (center P) v)).toReal ≤
      (1-Real.exp (-1))*(volume P).toReal := by
  let ell : Space n →L[ℝ] ℝ := innerSL ℝ v
  have hell : ell ≠ 0 := by
    intro hz
    have hi : inner ℝ v v=0 := by
      change ell v=0
      rw [hz]
      simp
    rw [real_inner_self_eq_norm_sq,hv] at hi
    norm_num at hi
  have h := GrunbaumComplete.centroid_cap_volume_upper_real hPc hPv hPi ell hell
  have hset : cut P (center P) v =
      GrunbaumBM.cap P ell (ell (ConvexBodyCDF.centroid P)) 0 := by
    ext x
    simp only [cut,GrunbaumBM.cap,mem_inter_iff,mem_setOf_eq,add_zero]
    have hc : center P=ConvexBodyCDF.centroid P := rfl
    rw [hc]
    change (x ∈ P ∧ inner ℝ v (x-ConvexBodyCDF.centroid P) ≤ 0) ↔
      (x ∈ P ∧ inner ℝ v x ≤ inner ℝ v (ConvexBodyCDF.centroid P))
    rw [inner_sub_right,sub_nonpos]
  rw [hset]
  exact h

end
end PaperCentroidProgram

end SnapshotModule_034
/- END grunbaum_centroid_program -/

/- BEGIN PaperNormalization -/
section SnapshotModule_035

namespace PaperNormalization
open Set
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

noncomputable def objective (f : V → ℝ) (beta R : ℝ) (x : V) : ℝ :=
  f (R • x) / (beta * R ^ 2)

noncomputable def scaledGradient (grad : V → V) (beta R : ℝ) (x : V) : V :=
  (R / (beta * R ^ 2)) • grad (R • x)

lemma hasGradient (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (beta R : ℝ) (x : V) :
    HasGradientAt (objective f beta R) (scaledGradient grad beta R x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hh := (((hg (R • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul R)).const_smul ((beta * R ^ 2)⁻¹)
  convert! hh using 1
  · funext y
    change f (R • y) / (beta * R ^ 2) = (beta * R ^ 2)⁻¹ * f (R • y)
    ring
  · ext v
    simp only [scaledGradient, InnerProductSpace.toDual_apply_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_smul_right,
      smul_eq_mul, div_eq_mul_inv]
    ring

lemma gradient_lipschitz (grad : V → V) (beta : NNReal) (R : ℝ)
    (hb : 0 < beta) (hR : 0 < R) (hl : LipschitzWith beta grad) :
    LipschitzWith 1 (scaledGradient grad beta R) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have hbR : (0 : ℝ) < beta := hb
  have hs : 0 < R / ((beta : ℝ) * R ^ 2) := by positivity
  have hh := hl.norm_sub_le (R • x) (R • y)
  rw [← smul_sub, norm_smul_of_nonneg hR.le] at hh
  have hm := mul_le_mul_of_nonneg_left hh hs.le
  have hcoeff : R / ((beta : ℝ) * R ^ 2) * (beta : ℝ) * R = 1 := by
    field_simp
    <;> ring
  simpa only [scaledGradient, ← smul_sub, norm_smul_of_nonneg hs.le,
    NNReal.coe_one, one_mul, ← mul_assoc, hcoeff] using hm

lemma convex_objective (f : V → ℝ) (hc : ConvexOn ℝ univ f)
    (beta R : ℝ) (hs : 0 < beta * R ^ 2) : ConvexOn ℝ univ (objective f beta R) := by
  let l : V →ₗ[ℝ] V := R • LinearMap.id
  have hl := hc.comp_linearMap l
  have hm := hl.smul (le_of_lt (inv_pos.mpr hs))
  change ConvexOn ℝ univ (fun x => f (R • x) / (beta * R ^ 2))
  simpa [l, div_eq_mul_inv, mul_comm] using hm

lemma localized_minimizer (f : V → ℝ) (beta R : ℝ) (a : V)
    (hb : 0 < beta) (hR : 0 < R) (ha : ‖a‖ ≤ R) (hmin : ∀ y, f a ≤ f y) :
    ‖(R⁻¹) • a‖ ≤ 1 ∧
    (∀ y, objective f beta R ((R⁻¹) • a) ≤ objective f beta R y) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hinv : 0 ≤ R⁻¹ := le_of_lt (inv_pos.mpr hR)
  constructor
  · rw [norm_smul_of_nonneg hinv]
    calc
      R⁻¹ * ‖a‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left ha hinv
      _ = 1 := inv_mul_cancel₀ hRne
  · intro y
    dsimp [objective]
    rw [smul_smul, mul_inv_cancel₀ hRne, one_smul]
    exact div_le_div_of_nonneg_right (hmin (R • y)) (by positivity)

lemma original_gap (f : V → ℝ) (beta R epsilon : ℝ) (x a : V)
    (hb : 0 < beta) (hR : 0 < R) (he : 0 < epsilon)
    (hgap : objective f beta R x - objective f beta R a ≤ epsilon / (beta * R ^ 2)) :
    f (R • x) - f (R • a) ≤ epsilon := by
  have hs : 0 < beta * R ^ 2 := by positivity
  dsimp [objective] at hgap
  rw [← sub_div] at hgap
  exact (div_le_div_iff_of_pos_right hs).mp hgap

end PaperNormalization

end SnapshotModule_035
/- END PaperNormalization -/

/- BEGIN query_lift -/
section SnapshotModule_036

namespace PaperGDE.Program
noncomputable section

def mapQueries {n m : ℕ} {α : Type} (F : Vec n → Vec m) : Program n α → Program m α
  | .pure a => .pure a
  | .query y x next => .query (F y) (F x) (fun b => mapQueries F (next b))

lemma eval_mapQueries {n m : ℕ} {α : Type} (F : Vec n → Vec m)
    (C : Oracle m) (P : Program n α) :
    eval C (mapQueries F P) = eval (fun y x => C (F y) (F x)) P := by
  induction P with
  | pure a => rfl
  | query y x next ih => simp only [mapQueries, eval, ih]

lemma count_mapQueries {n m : ℕ} {α : Type} (F : Vec n → Vec m)
    (C : Oracle m) (P : Program n α) :
    count C (mapQueries F P) = count (fun y x => C (F y) (F x)) P := by
  induction P with
  | pure a => rfl
  | query y x next ih => simp only [mapQueries, count, ih]

def scaleProgram {n : ℕ} (R : ℝ) (P : Program n (Vec n)) : Program n (Vec n) :=
  bind (mapQueries (fun x => R • x) P) (fun x => .pure (R • x))

lemma eval_scaleProgram {n : ℕ} (R : ℝ) (C : Oracle n) (P : Program n (Vec n)) :
    eval C (scaleProgram R P) = R • eval (fun y x => C (R • y) (R • x)) P := by
  simp only [scaleProgram, eval_bind, eval_mapQueries, eval]

lemma count_scaleProgram {n : ℕ} (R : ℝ) (C : Oracle n) (P : Program n (Vec n)) :
    count C (scaleProgram R P) = count (fun y x => C (R • y) (R • x)) P := by
  simp only [scaleProgram, count_bind, count, Nat.add_zero, count_mapQueries]

end
end PaperGDE.Program

end SnapshotModule_036
/- END query_lift -/

/- BEGIN query_lift_public_cap -/
section SnapshotModule_037

namespace PaperGDE.Program
noncomputable section
lemma height_mapQueries {n m : ℕ} {α : Type} (F : Vec n → Vec m) (P : Program n α) :
    height (mapQueries F P)=height P := by
  induction P with
  | pure a => rfl
  | query y x next ih => simp only [mapQueries,height,ih]

lemma height_scaleProgram {n : ℕ} (R : ℝ) (P : Program n (Vec n)) :
    height (scaleProgram R P) ≤ height P := by
  have h := height_bind_le (mapQueries (fun x => R • x) P) (fun x => Program.pure (R • x))
    (height P) 0 (by rw [height_mapQueries]) (by intro x; rfl)
  simpa [scaleProgram] using h
end
end PaperGDE.Program

namespace PaperOracle.Program
variable {Q R A Q' : Type*}

def mapQueries (F : Q → Q') : Program Q R A → Program Q' R A
  | .done a => .done a
  | .ask q next => .ask (F q) (fun r => mapQueries F (next r))

lemma run_mapQueries (F : Q → Q') (C : Q' → R) (P : Program Q R A) :
    run C (mapQueries F P)=run (fun q => C (F q)) P := by
  induction P with
  | done a => rfl
  | ask q next ih => exact ih (C (F q))

lemma cap_mapQueries (F : Q → Q') (k : ℕ) (P : Program Q R A) (hP : Cap k P) :
    Cap k (mapQueries F P) := by
  induction k generalizing P with
  | zero => cases P <;> trivial
  | succ k ih =>
    cases P with
    | done a => trivial
    | ask q next => exact fun r => ih (next r) (hP r)

end PaperOracle.Program

end SnapshotModule_037
/- END query_lift_public_cap -/

/- BEGIN centroid_complete -/
section SnapshotModule_038

namespace PaperCentroidComplete
open Set PaperGDE PaperCentroidProgram PaperCentroidNormalized
open scoped RealInnerProductSpace
noncomputable section

def output {n : ℕ} (eta : ℝ) : PaperGDE.Program n (Vec n) :=
  PaperGDE.Program.bind (algorithm eta) (fun s => .pure s.best)

def cap (n : ℕ) (eta : ℝ) : ℕ :=
  (roundsBeforeLast n eta+1)*(2*(n+1)-1+n*rounds n (Real.sqrt eta/16)+1)-1

lemma output_height {n : ℕ} (eta : ℝ) : PaperGDE.Program.height (output (n := n) eta) ≤ cap n eta := by
  have h := PaperGDE.Program.height_bind_le (algorithm (n := n) eta) (fun s => .pure s.best)
    (cap n eta) 0 (first_public_height _ _ _ _) (by intro s; rfl)
  simpa [output] using h

/-- The normalized centroid theorem, with its actual finite program, all reply
branches, and a fully proved convex-body centroid contraction. -/
theorem normalized_centroid_complete {n : ℕ} (C : PaperGDE.Oracle n)
    (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (hC : OracleCorrect C f)
    (xstar : Vec n) (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    f (PaperGDE.Program.eval C (output eta))-f xstar ≤ eta ∧
      PaperGDE.Program.height (output (n := n) eta) ≤ cap n eta := by
  constructor
  · simp only [output,PaperGDE.Program.eval_bind,PaperGDE.Program.eval]
    apply accuracy_from_centroid_geometry C f grad hg hc hLip hC xstar hmin hstar eta heta heta1
    intro P hPc hPv hsub hPi v hv
    exact actual_centroid_shrink hPc hPv hPi v hv
  · exact output_height eta

def originalProgram {n : ℕ} (R Q : ℝ) : PaperGDE.Program n (Vec n) :=
  PaperGDE.Program.scaleProgram R (output (1/Q))

lemma original_height {n : ℕ} (R Q : ℝ) :
    PaperGDE.Program.height (originalProgram (n := n) R Q) ≤ cap n (1/Q) :=
  (PaperGDE.Program.height_scaleProgram R _).trans (output_height _)

/-- Original beta,R,epsilon assumptions imply the manuscript's epsilon accuracy;
normalization is implemented by legal query rescaling and leaves the cap fixed. -/
theorem original_centroid_complete {n : ℕ} (C : PaperGDE.Oracle n)
    (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (beta : NNReal) (hb : 0 < beta) (hLip : LipschitzWith beta grad)
    (xstar : Vec n) (R epsilon Q : ℝ) (hR : 0 < R) (heps : 0 < epsilon)
    (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ R)
    (hQ : 32 ≤ Q) (hQdef : Q=(beta:ℝ)*R^2/epsilon) (hC : OracleCorrect C f) :
    f (PaperGDE.Program.eval C (originalProgram R Q))-f xstar ≤ epsilon ∧
      PaperGDE.Program.height (originalProgram (n := n) R Q) ≤ cap n (1/Q) := by
  have hbR : (0:ℝ) < beta := hb
  have hscale : 0 < (beta:ℝ)*R^2 := by positivity
  let g := PaperNormalization.objective f beta R
  let gg := PaperNormalization.scaledGradient grad beta R
  let a := R⁻¹ • xstar
  let Cs : PaperGDE.Oracle n := fun y x => C (R • y) (R • x)
  have hnorm := PaperNormalization.localized_minimizer f beta R xstar hbR hR hstar hmin
  have hCs : OracleCorrect Cs g := by
    intro y x
    rw [show Cs y x=C (R • y) (R • x) from rfl,hC (R • y) (R • x)]
    exact (div_le_div_iff_of_pos_right hscale).symm
  have hgNorm : ∀ x, HasGradientAt g (gg x) x := PaperNormalization.hasGradient f grad hg beta R
  have hconv := PaperNormalization.convex_objective f hc beta R hscale
  have hL := PaperNormalization.gradient_lipschitz grad beta R hb hR hLip
  have hQpos : 0 < Q := by linarith
  have hgap := (normalized_centroid_complete Cs g gg hgNorm hconv hL hCs a hnorm.2 hnorm.1
    (1/Q) (by positivity) ((div_le_one hQpos).mpr (by linarith))).1
  have hrecip : 1/Q=epsilon/((beta:ℝ)*R^2) := by rw [hQdef]; field_simp
  have horig := PaperNormalization.original_gap f beta R epsilon
    (PaperGDE.Program.eval Cs (output (1/Q))) a hbR hR heps (by rw [← hrecip]; exact hgap)
  have ha : R • a=xstar := by
    dsimp [a]
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  rw [ha] at horig
  constructor
  · simpa only [originalProgram,PaperGDE.Program.eval_scaleProgram,Cs] using horig
  · exact original_height R Q

end
end PaperCentroidComplete

end SnapshotModule_038
/- END centroid_complete -/

/- BEGIN adangd_complete -/
section SnapshotModule_039

/- Phase 2: executed projected AdaNGD trajectory and its regret proof. -/

namespace PaperAdaNGD

open Set
open scoped RealInnerProductSpace

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def projectUnitBall (x : V) : V :=
  if ‖x‖ ≤ 1 then x else ‖x‖⁻¹ • x

theorem projectUnitBall_norm (x : V) : ‖projectUnitBall x‖ ≤ 1 := by
  unfold projectUnitBall
  split_ifs with hx
  · exact hx
  · have hp : 0 < ‖x‖ := lt_trans (by norm_num) (lt_of_not_ge hx)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]

theorem projectUnitBall_distance (x a : V) (ha : ‖a‖ ≤ 1) :
    ‖projectUnitBall x-a‖^2 ≤ ‖x-a‖^2 := by
  unfold projectUnitBall
  split_ifs with hx
  · exact le_rfl
  · have hnorm : 1 < ‖x‖ := lt_of_not_ge hx
    have hp : 0 < ‖x‖ := lt_trans (by norm_num) hnorm
    have hi : inner ℝ x a ≤ ‖x‖ := by
      have hb := (le_abs_self (inner ℝ x a)).trans (abs_real_inner_le_norm x a)
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left ha (norm_nonneg x)])
    have heq : ‖x‖⁻¹*‖x‖ = 1 := inv_mul_cancel₀ (ne_of_gt hp)
    have hnormscaled : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
      exact heq
    rw [norm_sub_sq_real, norm_sub_sq_real, hnormscaled, real_inner_smul_left]
    have hinv : ‖x‖⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (le_of_lt hnorm)
    have hfactor : 0 ≤ (‖x‖-1)*(‖x‖-1) := sq_nonneg (‖x‖-1) |>.trans_eq (by ring)
    have hmul := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1-‖x‖⁻¹ by linarith)
    nlinarith

noncomputable def stepSize (k : ℕ) : ℝ := Real.sqrt 2 / Real.sqrt ((k:ℝ)+1)

noncomputable def weight (k : ℕ) : ℝ := Real.sqrt (k:ℝ)/(2*Real.sqrt 2)

theorem stepSize_pos (k : ℕ) : 0 < stepSize k := by unfold stepSize; positivity

theorem weight_nonneg (k : ℕ) : 0 ≤ weight k := by unfold weight; positivity

theorem weight_mono (k : ℕ) : weight k ≤ weight (k+1) := by
  unfold weight
  apply div_le_div_of_nonneg_right
  · apply Real.sqrt_le_sqrt
    push_cast
    linarith
  · positivity

theorem stepSize_weight (k : ℕ) : 2*stepSize k*weight (k+1) = 1 := by
  unfold stepSize weight
  push_cast
  have hs : Real.sqrt ((k:ℝ)+1) ≠ 0 := ne_of_gt (by positivity)
  have htwo : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem stepSize_source_formula (k : ℕ) : stepSize k = Real.sqrt (2/((k:ℝ)+1)) := by
  unfold stepSize
  rw [Real.sqrt_div (by norm_num)]

noncomputable def trajectory (direction : V → V) : ℕ → V
  | 0 => 0
  | k+1 => projectUnitBall (trajectory direction k-stepSize k • direction (trajectory direction k))

theorem trajectory_norm (direction : V → V) (k : ℕ) : ‖trajectory direction k‖ ≤ 1 := by
  cases k with
  | zero => simp [trajectory]
  | succ k => exact projectUnitBall_norm _

theorem trajectory_distance (direction : V → V) (a : V) (ha : ‖a‖ ≤ 1) (k : ℕ) :
    ‖trajectory direction k-a‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [trajectory_norm direction k])

theorem projected_step_regret (x a v : V) (eta : ℝ)
    (ha : ‖a‖ ≤ 1) (hv : ‖v‖ = 1) (_heta : 0 < eta) :
    2*eta*inner ℝ v (x-a) ≤
      ‖x-a‖^2-‖projectUnitBall (x-eta • v)-a‖^2+eta^2 := by
  have hp := projectUnitBall_distance (x-eta • v) a ha
  have hn : ‖(x-eta • v)-a‖^2 =
      ‖x-a‖^2-2*eta*inner ℝ v (x-a)+eta^2 := by
    rw [show (x-eta • v)-a = (x-a)-eta • v by abel,
      norm_sub_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_right,
      real_inner_comm (x-a) v, hv, mul_pow, sq_abs]
    ring
  rw [hn] at hp
  linarith

theorem trajectory_step_regret (direction : V → V) (hunit : ∀ x, ‖direction x‖ = 1)
    (a : V) (ha : ‖a‖ ≤ 1) (k : ℕ) :
    inner ℝ (direction (trajectory direction k)) (trajectory direction k-a) ≤
      weight (k+1)*(‖trajectory direction k-a‖^2-‖trajectory direction (k+1)-a‖^2)+stepSize k/2 := by
  have h := projected_step_regret (trajectory direction k) a (direction (trajectory direction k))
    (stepSize k) ha (hunit _) (stepSize_pos k)
  have hm := mul_le_mul_of_nonneg_left h (weight_nonneg (k+1))
  have hw := stepSize_weight k
  have hcancel : weight (k+1)*(2*stepSize k*inner ℝ (direction (trajectory direction k))
      (trajectory direction k-a)) = inner ℝ (direction (trajectory direction k)) (trajectory direction k-a) := by
    nlinarith [congrArg (fun t : ℝ => t*inner ℝ (direction (trajectory direction k)) (trajectory direction k-a)) hw]
  have hsquare : weight (k+1)*stepSize k^2 = stepSize k/2 := by
    nlinarith [congrArg (fun t : ℝ => t*stepSize k) hw]
  rw [hcancel] at hm
  change _ ≤ weight (k+1)*(‖trajectory direction k-a‖^2-‖trajectory direction (k+1)-a‖^2+stepSize k^2) at hm
  nlinarith

theorem weighted_distance_telescope (direction : V → V) (a : V) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, weight (k+1)*(‖trajectory direction k-a‖^2-
      ‖trajectory direction (k+1)-a‖^2)) ≤ 4*weight n := by
  have hstrong : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, weight (k+1)*(‖trajectory direction k-a‖^2-
        ‖trajectory direction (k+1)-a‖^2)) ≤
        4*weight n-weight n*‖trajectory direction n-a‖^2 := by
    intro n
    induction n with
    | zero => simp [weight]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hm := weight_mono n
      have hd : ‖trajectory direction n-a‖^2 ≤ 4 := by
        nlinarith [trajectory_distance direction a ha n, norm_nonneg (trajectory direction n-a)]
      have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ weight (n+1)-weight n by linarith)
      nlinarith
  have hn := hstrong n
  have hp : 0 ≤ weight n*‖trajectory direction n-a‖^2 := mul_nonneg (weight_nonneg n) (sq_nonneg _)
  linarith

theorem stepSize_sqrt_increment (k : ℕ) :
    stepSize k ≤ 2*Real.sqrt 2*(Real.sqrt ((k:ℝ)+1)-Real.sqrt (k:ℝ)) := by
  have hs : 0 < Real.sqrt ((k:ℝ)+1) := by positivity
  have hs2 : (Real.sqrt ((k:ℝ)+1))^2 = (k:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hr2 : (Real.sqrt (k:ℝ))^2 = (k:ℝ) := Real.sq_sqrt (by positivity)
  have hbase : 1 ≤ 2*Real.sqrt ((k:ℝ)+1)*(Real.sqrt ((k:ℝ)+1)-Real.sqrt (k:ℝ)) := by
    nlinarith [sq_nonneg (Real.sqrt ((k:ℝ)+1)-Real.sqrt (k:ℝ))]
  have hmul := mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg 2)
  unfold stepSize
  apply (div_le_iff₀ hs).mpr
  nlinarith

theorem stepSize_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, stepSize k) ≤ 2*Real.sqrt 2*Real.sqrt (n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := stepSize_sqrt_increment n
    push_cast
    linarith

theorem projected_trajectory_regret (direction : V → V) (hunit : ∀ x, ‖direction x‖ = 1)
    (a : V) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, inner ℝ (direction (trajectory direction k))
      (trajectory direction k-a)) ≤ 2*Real.sqrt (2*(n:ℝ)) := by
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        (weight (k+1)*(‖trajectory direction k-a‖^2-‖trajectory direction (k+1)-a‖^2)+stepSize k/2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact trajectory_step_regret direction hunit a ha k
    _ = (∑ k ∈ Finset.range n, weight (k+1)*(‖trajectory direction k-a‖^2-
        ‖trajectory direction (k+1)-a‖^2))+(∑ k ∈ Finset.range n, stepSize k)/2 := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ 4*weight n+(2*Real.sqrt 2*Real.sqrt (n:ℝ))/2 := by
      gcongr
      · exact weighted_distance_telescope direction a ha n
      · exact stepSize_sum n
    _ = 2*Real.sqrt (2*(n:ℝ)) := by
      unfold weight
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have htwo : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      rw [htwo]
      ring

theorem angular_trajectory_regret
    (direction : V → V) (hunit : ∀ x, ‖direction x‖ = 1)
    (truth : ℕ → V) (a : V) (ha : ‖a‖ ≤ 1) (delta : ℝ) (n : ℕ)
    (hdelta : 0 ≤ delta)
    (hangle : ∀ k < n, ‖truth k-direction (trajectory direction k)‖ ≤ delta) :
    (∑ k ∈ Finset.range n, inner ℝ (truth k) (trajectory direction k-a)) ≤
      2*Real.sqrt (2*(n:ℝ))+2*delta*(n:ℝ) := by
  have hpoint : ∀ k < n, inner ℝ (truth k) (trajectory direction k-a) ≤
      inner ℝ (direction (trajectory direction k)) (trajectory direction k-a)+2*delta := by
    intro k hk
    have hb := (le_abs_self (inner ℝ (truth k-direction (trajectory direction k))
      (trajectory direction k-a))).trans (abs_real_inner_le_norm _ _)
    have hm := mul_le_mul_of_nonneg_right (hangle k hk) (norm_nonneg (trajectory direction k-a))
    have hd := mul_le_mul_of_nonneg_left (trajectory_distance direction a ha k) hdelta
    rw [inner_sub_left] at hb
    linarith
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        (inner ℝ (direction (trajectory direction k)) (trajectory direction k-a)+2*delta) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hpoint k (Finset.mem_range.mp hk)
    _ = (∑ k ∈ Finset.range n, inner ℝ (direction (trajectory direction k))
        (trajectory direction k-a))+2*delta*(n:ℝ) := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ ≤ _ := by linarith [projected_trajectory_regret direction hunit a ha n]

section Smooth

variable [CompleteSpace V]

theorem gradient_threshold_from_bad_gap
    (f : V → ℝ) (grad : V → V) (hg : ∀ x, HasGradientAt f (grad x) x)
    (hf : ConvexOn ℝ univ f) (a x : V) (ha : ‖a‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (epsilon : ℝ) (_hepsilon : 0 < epsilon) (hbad : epsilon < f x-f a) :
    epsilon/2 < ‖grad x‖ := by
  have hc := PaperSmooth.convex_first_order f grad hg hf x a
  have hd : ‖x-a‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hi := (le_abs_self (inner ℝ (grad x) (x-a))).trans (abs_real_inner_le_norm _ _)
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg (grad x))
  have hin : inner ℝ (grad x) (x-a) = -(inner ℝ (grad x) (a-x)) := by
    rw [show x-a = -(a-x) by abel, inner_neg_right]
  rw [hin] at hi
  linarith

theorem normalized_gradient_convex_gap
    (f : V → ℝ) (grad : V → V) (hg : ∀ x, HasGradientAt f (grad x) x)
    (hf : ConvexOn ℝ univ f) (a x : V) (hG : 0 < ‖grad x‖) :
    (f x-f a)/‖grad x‖ ≤ inner ℝ (NormedSpace.normalize (grad x)) (x-a) := by
  have hc := PaperSmooth.convex_first_order f grad hg hf x a
  have hin : inner ℝ (grad x) (a-x) = -(inner ℝ (grad x) (x-a)) := by
    rw [show a-x = -(x-a) by abel, inner_neg_right]
  rw [hin] at hc
  have hdiv := div_le_div_of_nonneg_right (show f x-f a ≤ inner ℝ (grad x) (x-a) by linarith)
    (le_of_lt hG)
  simpa only [NormedSpace.normalize, real_inner_smul_left, div_eq_mul_inv, mul_comm] using hdiv

theorem reciprocal_cauchy (G : ℕ → ℝ) (n : ℕ) (hG : ∀ k < n, 0 < G k) :
    (n:ℝ)^2 ≤ (∑ k ∈ Finset.range n, G k)*(∑ k ∈ Finset.range n, (G k)⁻¹) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
    (fun k hk => le_of_lt (hG k (Finset.mem_range.mp hk)))
    (fun k hk => inv_nonneg.mpr (le_of_lt (hG k (Finset.mem_range.mp hk))))
    (fun k hk => show (1:ℝ)^2 ≤ G k*(G k)⁻¹ by
      rw [mul_inv_cancel₀ (ne_of_gt (hG k (Finset.mem_range.mp hk)))]
      norm_num)
  simpa using h

noncomputable def angularTolerance (Q : ℝ) : ℝ := 1/(4*Real.sqrt (2*Q))

noncomputable def regretEnvelope (n : ℕ) (Q : ℝ) : ℝ :=
  2*Real.sqrt (2*(n:ℝ))+2*angularTolerance Q*(n:ℝ)

theorem regretEnvelope_pos (n : ℕ) (Q : ℝ) (hn : 0 < n) (hQ : 0 < Q) :
    0 < regretEnvelope n Q := by unfold regretEnvelope angularTolerance; positivity

theorem regretEnvelope_budget (n : ℕ) (Q : ℝ) (hQ : 0 < Q) (hsteps : 64*Q ≤ (n:ℝ)) :
    2*(regretEnvelope n Q)^2 ≤ (n:ℝ)^2/Q := by
  have hn : 0 < (n:ℝ) := lt_of_lt_of_le (by positivity) hsteps
  have hqroot : 0 < Real.sqrt (2*Q) := by positivity
  have hnroot : 0 < Real.sqrt (2*(n:ℝ)) := by positivity
  have hq2 : (Real.sqrt (2*Q))^2 = 2*Q := Real.sq_sqrt (by positivity)
  have hn2 : (Real.sqrt (2*(n:ℝ)))^2 = 2*(n:ℝ) := Real.sq_sqrt (by positivity)
  have hprod := mul_le_mul_of_nonneg_right hsteps (le_of_lt hn)
  have hsquare : (4*Real.sqrt (2*Q)*Real.sqrt (2*(n:ℝ)))^2 = 64*Q*(n:ℝ) := by
    calc
      _ = 16*(Real.sqrt (2*Q))^2*(Real.sqrt (2*(n:ℝ)))^2 := by ring
      _ = _ := by rw [hq2, hn2]; ring
  have hsmall : 4*Real.sqrt (2*Q)*Real.sqrt (2*(n:ℝ)) ≤ (n:ℝ) := by
    nlinarith [sq_nonneg (4*Real.sqrt (2*Q)*Real.sqrt (2*(n:ℝ))-(n:ℝ))]
  have hA : regretEnvelope n Q ≤ (n:ℝ)/Real.sqrt (2*Q) := by
    unfold regretEnvelope angularTolerance
    apply (le_div_iff₀ hqroot).mpr
    have hcancel : (2*(1/(4*Real.sqrt (2*Q)))*(n:ℝ))*Real.sqrt (2*Q) = (n:ℝ)/2 := by
      field_simp
      ring
    rw [add_mul, hcancel]
    nlinarith
  have hAnonneg : 0 ≤ regretEnvelope n Q := le_of_lt (regretEnvelope_pos n Q (by exact_mod_cast hn) hQ)
  have hsq := (sq_le_sq₀ hAnonneg (show 0 ≤ (n:ℝ)/Real.sqrt (2*Q) by positivity)).mpr hA
  have hbound : ((n:ℝ)/Real.sqrt (2*Q))^2 = (n:ℝ)^2/(2*Q) := by rw [div_pow, hq2]
  rw [hbound] at hsq
  have hm := mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ 2 by norm_num)
  calc
    2*(regretEnvelope n Q)^2 ≤ 2*((n:ℝ)^2/(2*Q)) := hm
    _ = (n:ℝ)^2/Q := by field_simp

theorem trajectory_has_good_iterate
    (f : V → ℝ) (grad : V → V) (hg : ∀ x, HasGradientAt f (grad x) x)
    (hf : ConvexOn ℝ univ f) (hLip : LipschitzWith 1 grad)
    (a : V) (ha : ‖a‖ ≤ 1) (hmin : ∀ x, f a ≤ f x)
    (Q : ℝ) (hQ : 0 < Q) (n : ℕ) (hsteps : 64*Q ≤ (n:ℝ))
    (direction : V → V) (hunit : ∀ x, ‖direction x‖ = 1)
    (haccuracy : ∀ x, 1/(2*Q) ≤ ‖grad x‖ →
      ‖direction x-NormedSpace.normalize (grad x)‖ ≤ angularTolerance Q) :
    ∃ k < n, f (trajectory direction k)-f a ≤ 1/Q := by
  by_contra hnone
  have hbad : ∀ k < n, 1/Q < f (trajectory direction k)-f a := by
    intro k hk
    exact lt_of_not_ge (fun h => hnone ⟨k,hk,h⟩)
  have hn : 0 < n := by
    have : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le (by positivity) hsteps
    exact_mod_cast this
  let G : ℕ → ℝ := fun k => ‖grad (trajectory direction k)‖
  let u : ℕ → V := fun k => NormedSpace.normalize (grad (trajectory direction k))
  let S : ℝ := ∑ k ∈ Finset.range n, inner ℝ (u k) (trajectory direction k-a)
  let A : ℝ := regretEnvelope n Q
  let B : ℝ := ∑ k ∈ Finset.range n, (G k)⁻¹
  have hGthreshold : ∀ k < n, 1/(2*Q) < G k := by
    intro k hk
    have h := gradient_threshold_from_bad_gap f grad hg hf a (trajectory direction k) ha
      (trajectory_norm direction k) (1/Q) (by positivity) (hbad k hk)
    change 1/(2*Q) < ‖grad (trajectory direction k)‖
    convert h using 1
    ring
  have hG : ∀ k < n, 0 < G k := fun k hk => lt_trans (by positivity) (hGthreshold k hk)
  have hangle : ∀ k < n, ‖u k-direction (trajectory direction k)‖ ≤ angularTolerance Q := by
    intro k hk
    rw [norm_sub_rev]
    exact haccuracy _ (le_of_lt (hGthreshold k hk))
  have hS : S ≤ A := angular_trajectory_regret direction hunit u a ha (angularTolerance Q) n
    (by unfold angularTolerance; positivity) hangle
  have hpoint : ∀ k < n, (1/Q)*(G k)⁻¹ < inner ℝ (u k) (trajectory direction k-a) := by
    intro k hk
    have hc := normalized_gradient_convex_gap f grad hg hf a (trajectory direction k) (hG k hk)
    have hl := (div_lt_div_iff_of_pos_right (hG k hk)).mpr (hbad k hk)
    have hl' : (1/Q)*(G k)⁻¹ < (f (trajectory direction k)-f a)/G k := by
      simpa only [div_eq_mul_inv] using hl
    exact hl'.trans_le hc
  have hB : (1/Q)*B < S := by
    dsimp [B, S]
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨0, Finset.mem_range.mpr hn⟩
    · intro k hk
      exact hpoint k (Finset.mem_range.mp hk)
  have hnormpoint : ∀ k < n, G k ≤ 2*inner ℝ (u k) (trajectory direction k-a) := by
    intro k hk
    have hs := PaperSmooth.normalized_gradient_gap f grad hg hLip a (trajectory direction k) hmin
    have hc := normalized_gradient_convex_gap f grad hg hf a (trajectory direction k) (hG k hk)
    have hcmul := (div_le_iff₀ (hG k hk)).mp hc
    change G k^2 ≤ 2*(f (trajectory direction k)-f a) at hs
    nlinarith [hG k hk]
  have hsumG : (∑ k ∈ Finset.range n, G k) ≤ 2*S := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact hnormpoint k (Finset.mem_range.mp hk)
  have hBnonneg : 0 ≤ B := Finset.sum_nonneg (fun k hk => inv_nonneg.mpr (le_of_lt (hG k (Finset.mem_range.mp hk))))
  have hApos : 0 < A := regretEnvelope_pos n Q hn hQ
  have hcauchy := reciprocal_cauchy G n hG
  have hnormA : (∑ k ∈ Finset.range n, G k) ≤ 2*A := hsumG.trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hnormA hBnonneg
  have hBA : (1/Q)*B < A := hB.trans_le hS
  have hfinal := mul_lt_mul_of_pos_left hBA (show 0 < 2*A by positivity)
  have hcQ := mul_le_mul_of_nonneg_left (hcauchy.trans hmul) (show 0 ≤ 1/Q by positivity)
  have hbudget := regretEnvelope_budget n Q hQ hsteps
  change 2*A^2 ≤ (n:ℝ)^2/Q at hbudget
  have hbudget' : 2*A^2 ≤ (1/Q)*(n:ℝ)^2 := by
    convert hbudget using 1
    ring
  nlinarith

end Smooth

noncomputable def incumbent (C : V → V → Bool) (direction : V → V) : ℕ → V
  | 0 => 0
  | k+1 => if C (trajectory direction (k+1)) (incumbent C direction k) then
      incumbent C direction k else trajectory direction (k+1)

theorem incumbent_step_bounds (f : V → ℝ) (C : V → V → Bool)
    (hC : ∀ y x, C y x = true ↔ f x ≤ f y) (direction : V → V) (k : ℕ) :
    f (incumbent C direction (k+1)) ≤ f (incumbent C direction k) ∧
      f (incumbent C direction (k+1)) ≤ f (trajectory direction (k+1)) := by
  simp only [incumbent]
  split_ifs with hreply
  · exact ⟨le_rfl, (hC _ _).mp hreply⟩
  · have hlt : f (trajectory direction (k+1)) < f (incumbent C direction k) :=
      lt_of_not_ge (fun h => hreply ((hC _ _).mpr h))
    exact ⟨le_of_lt hlt, le_rfl⟩

theorem incumbent_le_generated (f : V → ℝ) (C : V → V → Bool)
    (hC : ∀ y x, C y x = true ↔ f x ≤ f y) (direction : V → V) :
    ∀ n k : ℕ, k ≤ n → f (incumbent C direction n) ≤ f (trajectory direction k) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have : k=0 := by omega
    subst k
    exact le_rfl
  | succ n ih =>
    intro k hk
    by_cases heq : k=n+1
    · subst k
      exact (incumbent_step_bounds f C hC direction n).2
    · exact (incumbent_step_bounds f C hC direction n).1.trans (ih k (by omega))

section Program

open PaperGDE

/-- Every outer iteration executes GDE, the projected update, and one selection query. -/
noncomputable def adangdProgram {d : ℕ} (delta gamma : ℝ) : ℕ → Program d (Vec d × Vec d)
  | 0 => .pure (0,0)
  | k+1 => Program.bind (adangdProgram delta gamma k) (fun state =>
      Program.bind (gdeProgram state.1 delta gamma) (fun v =>
        let candidate := projectUnitBall (state.1-stepSize k • v)
        .query candidate state.2 (fun reply =>
          .pure (candidate, if reply then state.2 else candidate))))

theorem adangdProgram_eval {d : ℕ} (C : Oracle d) (delta gamma : ℝ) (n : ℕ) :
    Program.eval C (adangdProgram delta gamma n) =
      (trajectory (fun x => gde C x delta gamma) n,
        incumbent C (fun x => gde C x delta gamma) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [adangdProgram, Program.eval_bind, ih, gdeProgram_eval, Program.eval,
      trajectory, incumbent]

noncomputable def directionCost (d : ℕ) (delta : ℝ) : ℕ :=
  2*(d+1)-1+d*rounds d delta

theorem adangdProgram_exact_count {d : ℕ} (C : Oracle d) (delta gamma : ℝ) (n : ℕ) :
    Program.count C (adangdProgram delta gamma n) = n*(directionCost d delta+1) := by
  induction n with
  | zero => simp [adangdProgram, Program.count]
  | succ n ih =>
    simp only [adangdProgram, Program.count_bind, gdeProgram_exact_count, Program.count, ih]
    unfold directionCost
    ring

noncomputable def iterationCount (Q : ℝ) : ℕ := ⌈64*Q⌉₊

theorem iterationCount_adequate (Q : ℝ) : 64*Q ≤ (iterationCount Q:ℝ) := Nat.le_ceil _

theorem angularTolerance_parameters (Q : ℝ) (hQ : 32 ≤ Q) :
    0 < angularTolerance Q ∧ angularTolerance Q ≤ 1 ∧ 0 < 1/(2*Q) := by
  have hQpos : 0 < Q := by linarith
  have hs : 0 < Real.sqrt (2*Q) := by positivity
  have hs2 : (Real.sqrt (2*Q))^2 = 2*Q := Real.sq_sqrt (by positivity)
  have hsone : 1 ≤ Real.sqrt (2*Q) := by nlinarith [Real.sqrt_nonneg (2*Q)]
  refine ⟨by unfold angularTolerance; positivity, ?_, by positivity⟩
  unfold angularTolerance
  exact (div_le_iff₀ (by positivity : 0 < 4*Real.sqrt (2*Q))).mpr (by linarith)

/-- Full normalized AdaNGD theorem, including the executed program and every query. -/
theorem normalized_adangd_complete {d : ℕ}
    (f : Vec d → ℝ) (grad : Vec d → Vec d)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hf : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (a : Vec d) (ha : ‖a‖ ≤ 1) (hmin : ∀ x, f a ≤ f x)
    (Q : ℝ) (hQ : 32 ≤ Q) (C : Oracle d) (hC : OracleCorrect C f) :
    let P := adangdProgram (angularTolerance Q) (1/(2*Q)) (iterationCount Q)
    f (Program.eval C P).2-f a ≤ 1/Q ∧
      Program.count C P = iterationCount Q*(directionCost d (angularTolerance Q)+1) := by
  have hp := angularTolerance_parameters Q hQ
  have hgood := trajectory_has_good_iterate f grad hg hf hLip a ha hmin Q (by linarith)
    (iterationCount Q) (iterationCount_adequate Q)
    (fun x => gde C x (angularTolerance Q) (1/(2*Q)))
    (fun x => gde_unit C x _ _)
    (fun x hnorm => gde_accuracy f grad hg hLip hC x _ _ hp.1 hp.2.1 hp.2.2 hnorm)
  obtain ⟨k,hk,hgap⟩ := hgood
  have hbest := incumbent_le_generated f C hC
    (fun x => gde C x (angularTolerance Q) (1/(2*Q))) (iterationCount Q) k (le_of_lt hk)
  dsimp only
  rw [adangdProgram_eval]
  constructor
  · linarith
  · exact adangdProgram_exact_count C _ _ _

noncomputable def adangdOutput {d : ℕ} (delta gamma : ℝ) (n : ℕ) : Program d (Vec d) :=
  Program.bind (adangdProgram delta gamma n) (fun state => .pure state.2)

theorem adangdOutput_eval {d : ℕ} (C : Oracle d) (delta gamma : ℝ) (n : ℕ) :
    Program.eval C (adangdOutput delta gamma n) = (Program.eval C (adangdProgram delta gamma n)).2 := by
  simp only [adangdOutput, Program.eval_bind, Program.eval]

theorem adangdOutput_count {d : ℕ} (C : Oracle d) (delta gamma : ℝ) (n : ℕ) :
    Program.count C (adangdOutput delta gamma n) = n*(directionCost d delta+1) := by
  simp only [adangdOutput, Program.count_bind, Program.count, Nat.add_zero, adangdProgram_exact_count]

theorem angularTolerance_original (beta R epsilon Q : ℝ)
    (hbeta : 0 < beta) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (hQdef : Q=beta*R^2/epsilon) :
    angularTolerance Q = (1/(4*R))*Real.sqrt (epsilon/(2*beta)) := by
  have hQ : 0 < Q := by rw [hQdef]; positivity
  have hleftpos : 0 < angularTolerance Q := by unfold angularTolerance; positivity
  have hrightpos : 0 < (1/(4*R))*Real.sqrt (epsilon/(2*beta)) := by positivity
  have hleftsq : (angularTolerance Q)^2 = epsilon/(32*beta*R^2) := by
    unfold angularTolerance
    rw [div_pow, mul_pow, Real.sq_sqrt (show 0 ≤ 2*Q by positivity), hQdef]
    field_simp
    ring
  have hrightsq : ((1/(4*R))*Real.sqrt (epsilon/(2*beta)))^2 = epsilon/(32*beta*R^2) := by
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ epsilon/(2*beta) by positivity)]
    field_simp
    ring
  nlinarith

/-- The implemented original-scale algorithm; it receives only public parameters. -/
noncomputable def originalAdangd {d : ℕ} (R Q : ℝ) : Program d (Vec d) :=
  Program.scaleProgram R (adangdOutput (angularTolerance Q) (1/(2*Q)) (iterationCount Q))

theorem originalAdangd_count {d : ℕ} (C : Oracle d) (R Q : ℝ) :
    Program.count C (originalAdangd R Q) =
      iterationCount Q*(directionCost d (angularTolerance Q)+1) := by
  rw [originalAdangd, Program.count_scaleProgram, adangdOutput_count]

/-- Original smooth-convex objective assumptions imply accuracy of the actual finite program. -/
theorem original_adangd_complete {d : ℕ}
    (f : Vec d → ℝ) (grad : Vec d → Vec d)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hf : ConvexOn ℝ univ f)
    (beta : NNReal) (hbeta : 0 < beta) (hLip : LipschitzWith beta grad)
    (a : Vec d) (R epsilon Q : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (ha : ‖a‖ ≤ R) (hmin : ∀ x, f a ≤ f x)
    (hQ : 32 ≤ Q) (hQdef : Q=(beta:ℝ)*R^2/epsilon)
    (C : Oracle d) (hC : OracleCorrect C f) :
    f (Program.eval C (originalAdangd R Q))-f a ≤ epsilon ∧
      Program.count C (originalAdangd R Q) =
        iterationCount Q*(directionCost d ((1/(4*R))*Real.sqrt (epsilon/(2*(beta:ℝ))))+1) := by
  let g := PaperNormalization.objective f beta R
  let ggrad := PaperNormalization.scaledGradient grad beta R
  let astar := R⁻¹ • a
  let Cscaled : Oracle d := fun y x => C (R • y) (R • x)
  have hb : 0 < (beta:ℝ) := hbeta
  have hs : 0 < (beta:ℝ)*R^2 := by positivity
  have hscaledC : OracleCorrect Cscaled g := by
    intro y x
    change C (R • y) (R • x) = true ↔ f (R • x)/((beta:ℝ)*R^2) ≤ f (R • y)/((beta:ℝ)*R^2)
    rw [hC]
    exact (div_le_div_iff_of_pos_right hs).symm
  have hlocal := PaperNormalization.localized_minimizer f beta R a hb hR ha hmin
  have hnorm := normalized_adangd_complete g ggrad
    (PaperNormalization.hasGradient f grad hg beta R)
    (PaperNormalization.convex_objective f hf beta R hs)
    (PaperNormalization.gradient_lipschitz grad beta R hbeta hR hLip)
    astar hlocal.1 hlocal.2 Q hQ Cscaled hscaledC
  have hgap : g (Program.eval Cscaled (adangdOutput (angularTolerance Q) (1/(2*Q)) (iterationCount Q)))-g astar ≤ 1/Q := by
    rw [adangdOutput_eval]
    exact hnorm.1
  have hreciprocal : 1/Q = epsilon/((beta:ℝ)*R^2) := by rw [hQdef]; field_simp
  have horiginal := PaperNormalization.original_gap f beta R epsilon
    (Program.eval Cscaled (adangdOutput (angularTolerance Q) (1/(2*Q)) (iterationCount Q)))
    astar hb hR hepsilon (by rw [← hreciprocal]; exact hgap)
  have hscalea : R • astar = a := by
    dsimp [astar]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
  rw [hscalea] at horiginal
  constructor
  · simpa only [originalAdangd, Program.eval_scaleProgram, Cscaled] using horiginal
  · rw [originalAdangd_count, angularTolerance_original (beta:ℝ) R epsilon Q hb hR hepsilon hQdef]

/-- Trinary oracle adaptation preserves ties and charges one original query per node. -/
theorem original_adangd_from_exact_comparisons {d : ℕ}
    (f : Vec d → ℝ) (grad : Vec d → Vec d)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hf : ConvexOn ℝ univ f)
    (beta : NNReal) (hbeta : 0 < beta) (hLip : LipschitzWith beta grad)
    (a : Vec d) (R epsilon Q : ℝ) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (ha : ‖a‖ ≤ R) (hmin : ∀ x, f a ≤ f x)
    (hQ : 32 ≤ Q) (hQdef : Q=(beta:ℝ)*R^2/epsilon)
    (comparison : Vec d → Vec d → Ordering)
    (hcomparison : ∀ y x, comparison y x = .lt ↔ f y < f x) :
    f (Program.eval (oracleOfOrdering comparison) (originalAdangd R Q))-f a ≤ epsilon ∧
      Program.count (oracleOfOrdering comparison) (originalAdangd R Q) =
        iterationCount Q*(directionCost d ((1/(4*R))*Real.sqrt (epsilon/(2*(beta:ℝ))))+1) := by
  exact original_adangd_complete f grad hg hf beta hbeta hLip a R epsilon Q hR hepsilon
    ha hmin hQ hQdef (oracleOfOrdering comparison) (oracleOfOrdering_correct comparison f hcomparison)

end Program

end PaperAdaNGD


end SnapshotModule_039
/- END adangd_complete -/

/- BEGIN rate_envelopes -/
section SnapshotModule_040

/- Uniform, explicit arithmetic envelopes for the paper's exact public caps. -/
namespace PaperRates

open PaperAdaNGD PaperGDE

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem log_two_lower : (1/2:ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
  norm_num at h
  exact h

theorem dimension_log_lower (d : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    1 ≤ Real.log ((d+1:ℝ)*Q) := by
  have hD : 1 ≤ (d+1:ℝ) := by have h := Nat.cast_nonneg (α:=ℝ) d; linarith
  have hDQ : 4 ≤ (d+1:ℝ)*Q := by
    have hm := mul_le_mul_of_nonneg_right hD (show 0 ≤ Q by linarith)
    nlinarith
  have hl := Real.log_le_log (show (0:ℝ) < 4 by norm_num) hDQ
  have hfour : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hl
  linarith [log_two_lower]

theorem gde_rounds_uniform (d : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    (rounds d (angularTolerance Q):ℝ) ≤ 1000*Real.log ((d+1:ℝ)*Q) := by
  have hQpos : 0 < Q := by linarith
  have hD : 1 ≤ (d+1:ℝ) := by have h := Nat.cast_nonneg (α:=ℝ) d; linarith
  have hDpos : 0 < (d+1:ℝ) := by positivity
  have hs : 0 < Real.sqrt (2*Q) := by positivity
  have hs2 : (Real.sqrt (2*Q))^2 = 2*Q := Real.sq_sqrt (by positivity)
  have hsone : 1 ≤ Real.sqrt (2*Q) := by nlinarith [Real.sqrt_nonneg (2*Q)]
  have hsQ : Real.sqrt (2*Q) ≤ Q := by nlinarith [Real.sqrt_nonneg (2*Q)]
  have hfive : 0 < Real.sqrt (5:ℝ) := by positivity
  have hfive2 : (Real.sqrt (5:ℝ))^2 = 5 := Real.sq_sqrt (by norm_num)
  have hfiveone : 1 ≤ Real.sqrt (5:ℝ) := by nlinarith [Real.sqrt_nonneg (5:ℝ)]
  have hfivethree : Real.sqrt (5:ℝ) ≤ 3 := by nlinarith [Real.sqrt_nonneg (5:ℝ)]
  let arg : ℝ := 60*(d+1:ℝ)/(Real.sqrt 5*angularTolerance Q)
  have harg : arg = 240*(d+1:ℝ)*Real.sqrt (2*Q)/Real.sqrt 5 := by
    dsimp [arg, angularTolerance]
    field_simp
    ring
  have hargone : 1 ≤ arg := by
    rw [harg]
    apply (le_div_iff₀ hfive).mpr
    have hm := mul_le_mul hD hsone (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hDpos)
    nlinarith
  have hargupper : arg ≤ 240*(d+1:ℝ)*Q := by
    rw [harg]
    calc
      _ ≤ 240*(d+1:ℝ)*Real.sqrt (2*Q) := div_le_self (by positivity) hfiveone
      _ ≤ _ := mul_le_mul_of_nonneg_left hsQ (by positivity)
  have hL := dimension_log_lower d Q hQ
  have hlogarg := Real.log_le_log (show 0 < arg by linarith) hargupper
  have hnonzero : (d+1:ℝ)*Q ≠ 0 := ne_of_gt (by positivity)
  rw [show 240*(d+1:ℝ)*Q = 240*((d+1:ℝ)*Q) by ring,
    Real.log_mul (by norm_num : (240:ℝ) ≠ 0) hnonzero] at hlogarg
  have hlog240 : Real.log (240:ℝ) ≤ 240 := Real.log_le_self (by norm_num)
  have hlogarg' : Real.log arg ≤ 240+Real.log ((d+1:ℝ)*Q) := by linarith
  have hlog2pos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hbase : Real.logb 2 arg ≤ 2*(240+Real.log ((d+1:ℝ)*Q)) := by
    rw [Real.logb]
    apply (div_le_iff₀ hlog2pos).mpr
    have hm := mul_le_mul_of_nonneg_left log_two_lower
      (show 0 ≤ 2*(240+Real.log ((d+1:ℝ)*Q)) by linarith)
    nlinarith
  have hceil := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hargone)
  change (rounds d (angularTolerance Q):ℝ) < Real.logb 2 arg+1 at hceil
  linarith

theorem directionCost_uniform (d : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    (directionCost d (angularTolerance Q)+1:ℝ) ≤
      1003*(d+1:ℝ)*Real.log ((d+1:ℝ)*Q) := by
  have hround := gde_rounds_uniform d Q hQ
  have hL := dimension_log_lower d Q hQ
  have hD : 1 ≤ (d+1:ℝ) := by have h := Nat.cast_nonneg (α:=ℝ) d; linarith
  have hnat : directionCost d (angularTolerance Q)+1 ≤
      2*(d+1)+(d+1)*rounds d (angularTolerance Q)+1 := by
    have hs : 2*(d+1)-1 ≤ 2*(d+1) := Nat.sub_le _ _
    have hm : d*rounds d (angularTolerance Q) ≤ (d+1)*rounds d (angularTolerance Q) :=
      Nat.mul_le_mul_right _ (by omega)
    unfold directionCost
    exact Nat.add_le_add_right (Nat.add_le_add hs hm) 1
  have hcast : (directionCost d (angularTolerance Q)+1:ℝ) ≤
      2*(d+1:ℝ)+(d+1:ℝ)*(rounds d (angularTolerance Q):ℝ)+1 := by exact_mod_cast hnat
  have hm := mul_le_mul_of_nonneg_left hround (show 0 ≤ (d+1:ℝ) by positivity)
  have hDL : (d+1:ℝ) ≤ (d+1:ℝ)*Real.log ((d+1:ℝ)*Q) := by
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ (d+1:ℝ) by positivity)]
  nlinarith

theorem iterationCount_uniform (Q : ℝ) (hQ : 32 ≤ Q) :
    (iterationCount Q:ℝ) ≤ 65*Q := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 64*Q by linarith)
  change (iterationCount Q:ℝ) < 64*Q+1 at hc
  linarith

/-- One absolute constant works simultaneously for every positive dimension and Q>=32. -/
theorem adangd_cap_uniform (d : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    ((iterationCount Q*(directionCost d (angularTolerance Q)+1):ℕ):ℝ) ≤
      1000000*(d+1:ℝ)*Q*Real.log ((d+1:ℝ)*Q) := by
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have ht := iterationCount_uniform Q hQ
  have hd := directionCost_uniform d Q hQ
  have hL := dimension_log_lower d Q hQ
  have hQnonneg : 0 ≤ Q := by linarith
  calc
    _ ≤ (65*Q)*(1003*(d+1:ℝ)*Real.log ((d+1:ℝ)*Q)) :=
      mul_le_mul ht hd (by positivity) (by positivity)
    _ ≤ 1000000*(d+1:ℝ)*Q*Real.log ((d+1:ℝ)*Q) := by
      have hp : 0 ≤ (d+1:ℝ)*Q*Real.log ((d+1:ℝ)*Q) := mul_nonneg (mul_nonneg (by positivity) hQnonneg) (by linarith)
      nlinarith

theorem originalAdangd_queries_uniform {d : ℕ} (C : Oracle d) (R Q : ℝ) (hQ : 32 ≤ Q) :
    (Program.count C (originalAdangd R Q):ℝ) ≤
      1000000*(d+1:ℝ)*Q*Real.log ((d+1:ℝ)*Q) := by
  rw [originalAdangd_count]
  exact adangd_cap_uniform d Q hQ

theorem adangd_cap_uniform_positive_dimension (D : ℕ) (hD : 1 ≤ D)
    (Q : ℝ) (hQ : 32 ≤ Q) :
    ((iterationCount Q*(directionCost (D-1) (angularTolerance Q)+1):ℕ):ℝ) ≤
      1000000*(D:ℝ)*Q*Real.log ((D:ℝ)*Q) := by
  have h := adangd_cap_uniform (D-1) Q hQ
  have heq : ((D-1:ℕ):ℝ)+1 = (D:ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hD
  simpa only [heq] using h

end PaperRates


end SnapshotModule_040
/- END rate_envelopes -/

/- BEGIN centroid_rates -/
section SnapshotModule_041

namespace PaperCentroidRates
open PaperGDE PaperCentroidComplete PaperCentroidNormalized PaperAdaNGD
noncomputable section

lemma lambda_lower : (1/3:ℝ) ≤ -Real.log (1-Real.exp (-1)) := by
  have hp := Real.exp_pos (-1)
  have hq := PaperVolumeBudget.grunbaum_ratio_pos
  have hl := Real.log_le_sub_one_of_pos hq
  have he := Real.exp_one_lt_three
  have hprod : Real.exp (-1)*Real.exp 1=1 := by rw [← Real.exp_add]; norm_num
  have hm := mul_lt_mul_of_pos_left he hp
  nlinarith

lemma logQ_lower (Q : ℝ) (hQ : 32 ≤ Q) : 1 ≤ Real.log Q := by
  have h := PaperRates.dimension_log_lower 0 Q hQ
  simpa using h

lemma normalized_delta (Q : ℝ) (hQ : 0 < Q) :
    Real.sqrt (1/Q)/16=angularTolerance (8*Q) := by
  have hroot : Real.sqrt (1/Q)=1/Real.sqrt Q := by rw [Real.sqrt_div (by norm_num),Real.sqrt_one]
  have h16 : Real.sqrt (2*(8*Q))=4*Real.sqrt Q := by
    rw [show 2*(8*Q)=(4:ℝ)^2*Q by ring,Real.sqrt_mul (by positivity),Real.sqrt_sq (by norm_num)]
  rw [hroot,angularTolerance,h16]
  ring

lemma centroid_rounds_bound (n : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    ((roundsBeforeLast n (1/Q)+1 : ℕ) : ℝ) ≤ 4*(n+1:ℝ)*Real.log Q := by
  have hQpos : 0 < Q := by linarith
  have hs := Real.sq_sqrt hQpos.le
  have hs0 := Real.sqrt_nonneg Q
  have hspos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hroot : Real.sqrt (1/Q)=1/Real.sqrt Q := by rw [Real.sqrt_div (by norm_num),Real.sqrt_one]
  have hratio : 2/Real.sqrt (1/Q)=2*Real.sqrt Q := by rw [hroot]; field_simp
  have hratioQ : 2*Real.sqrt Q ≤ Q := by nlinarith
  have hlog := Real.log_le_log (show 0 < 2*Real.sqrt Q by positivity) hratioQ
  have hlogpos : 0 ≤ Real.log (2*Real.sqrt Q) := by
    apply Real.log_nonneg
    have hh : 1 ≤ Real.sqrt Q := by nlinarith
    linarith
  have hn : 1 ≤ (n+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnpos : 0 < (n+1:ℝ) := by positivity
  have hlambda := PaperVolumeBudget.grunbaum_lambda_pos
  have hfloor := Nat.floor_le (show 0 ≤ (n+1:ℝ)*Real.log (2*Real.sqrt Q)/
      (-Real.log (1-Real.exp (-1))) by positivity)
  have hf : ((roundsBeforeLast n (1/Q)+1 : ℕ) : ℝ) ≤
      (n+1:ℝ)*Real.log (2*Real.sqrt Q)/(-Real.log (1-Real.exp (-1)))+1 := by
    dsimp [roundsBeforeLast]
    rw [hratio]
    push_cast
    linarith [hfloor]
  have hlogQpos : 0 ≤ Real.log Q := by linarith [logQ_lower Q hQ]
  have hdiv : (n+1:ℝ)*Real.log (2*Real.sqrt Q)/(-Real.log (1-Real.exp (-1))) ≤
      3*(n+1:ℝ)*Real.log Q := by
    apply (div_le_iff₀ hlambda).mpr
    have hm := mul_le_mul_of_nonneg_left hlog hnpos.le
    have hconst := mul_le_mul_of_nonneg_left lambda_lower
      (show 0 ≤ 3*(n+1:ℝ)*Real.log Q by positivity)
    nlinarith
  have hL := logQ_lower Q hQ
  have hDL : 1 ≤ (n+1:ℝ)*Real.log Q := by nlinarith
  linarith

lemma centroid_direction_bound (n : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    ((2*(n+1)-1+n*rounds n (Real.sqrt (1/Q)/16)+1 : ℕ) : ℝ) ≤
      10000*(n+1:ℝ)*Real.log ((n+1:ℝ)*Real.sqrt Q) := by
  have hQpos : 0 < Q := by linarith
  have hspos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hn : 1 ≤ (n+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnpos : 0 < (n+1:ℝ) := by positivity
  have hlogn : 0 ≤ Real.log (n+1:ℝ) := Real.log_nonneg hn
  have hlogQ := logQ_lower Q hQ
  have hlogsqrt := Real.log_sqrt hQpos.le
  have hL : 1 ≤ Real.log ((n+1:ℝ)*Real.sqrt Q) := by
    have hs := Real.sq_sqrt hQpos.le
    have hsr : 4 ≤ Real.sqrt Q := by nlinarith [Real.sqrt_nonneg Q]
    have hprod : 4 ≤ (n+1:ℝ)*Real.sqrt Q := by nlinarith
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) hprod
    have hfour : Real.log (4:ℝ)=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    rw [hfour] at hh
    linarith [PaperRates.log_two_lower]
  have hlogmul := Real.log_mul hnpos.ne' hspos.ne'
  have hcost := PaperRates.directionCost_uniform n (8*Q) (by linarith)
  rw [← normalized_delta Q hQpos] at hcost
  have heq : (n+1:ℝ)*(8*Q)=8*((n+1:ℝ)*Q) := by ring
  have hlog8 : Real.log (8:ℝ) ≤ 3 := by
    have he : Real.log (8:ℝ)=3*Real.log 2 := by rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]; norm_num
    rw [he]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hbig : Real.log ((n+1:ℝ)*(8*Q)) ≤ 5*Real.log ((n+1:ℝ)*Real.sqrt Q) := by
    rw [heq,Real.log_mul (by norm_num : (8:ℝ)≠0) (mul_ne_zero hnpos.ne' hQpos.ne'),
      Real.log_mul hnpos.ne' hQpos.ne']
    rw [hlogmul]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hbig (show 0 ≤ 1003*(n+1:ℝ) by positivity)
  change ((directionCost n (Real.sqrt (1/Q)/16)+1 : ℕ):ℝ) ≤ _
  simp only [Nat.cast_add,Nat.cast_one]
  have hnon : 0 ≤ (n+1:ℝ)*Real.log ((n+1:ℝ)*Real.sqrt Q) := by positivity
  nlinarith

/-- A single numerical constant proves the manuscript's uniform centroid rate. -/
theorem centroid_cap_uniform (n : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    (cap n (1/Q):ℝ) ≤ 100000000*(n+1:ℝ)^2*Real.log Q*
      Real.log ((n+1:ℝ)*Real.sqrt Q) := by
  have hM := centroid_rounds_bound n Q hQ
  have hG := centroid_direction_bound n Q hQ
  have hnat : cap n (1/Q) ≤ (roundsBeforeLast n (1/Q)+1)*
      (2*(n+1)-1+n*rounds n (Real.sqrt (1/Q)/16)+1) := Nat.sub_le _ _
  have hcast : (cap n (1/Q):ℝ) ≤
      ((roundsBeforeLast n (1/Q)+1:ℕ):ℝ)*
      ((2*(n+1)-1+n*rounds n (Real.sqrt (1/Q)/16)+1:ℕ):ℝ) := by exact_mod_cast hnat
  have hMpos : 0 ≤ 4*(n+1:ℝ)*Real.log Q := by linarith [Nat.cast_nonneg (α:=ℝ) (roundsBeforeLast n (1/Q)+1)]
  have hGpos : 0 ≤ 10000*(n+1:ℝ)*Real.log ((n+1:ℝ)*Real.sqrt Q) := by linarith [Nat.cast_nonneg (α:=ℝ) (2*(n+1)-1+n*rounds n (Real.sqrt (1/Q)/16)+1)]
  have hh := mul_le_mul hM hG (Nat.cast_nonneg _) hMpos
  have hbase : 0 ≤ (n+1:ℝ)^2*Real.log Q*Real.log ((n+1:ℝ)*Real.sqrt Q) := by
    have hprod := mul_nonneg hMpos hGpos
    nlinarith
  nlinarith

lemma one_dimension_cap (Q : ℝ) (hQ : 32 ≤ Q) : (cap 0 (1/Q):ℝ) ≤ 8*Real.log Q := by
  have hM := centroid_rounds_bound 0 Q hQ
  have hn : cap 0 (1/Q) ≤ 2*(roundsBeforeLast 0 (1/Q)+1) := by simp [cap]; omega
  have hc : (cap 0 (1/Q):ℝ) ≤ 2*((roundsBeforeLast 0 (1/Q)+1:ℕ):ℝ) := by exact_mod_cast hn
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add,mul_one,one_mul] at hM hc
  linarith

end
end PaperCentroidRates

end SnapshotModule_041
/- END centroid_rates -/

/- BEGIN full_history_rate_parameters -/
section SnapshotModule_042

namespace PaperFullHistoryRates
open PaperGDE PaperFullHistory PaperFullHistoryProgram PaperAdaNGD
noncomputable section
set_option maxHeartbeats 1000000

lemma gde_rounds_antitone (n : ℕ) {a b : ℝ} (ha : 0<a) (hab : a≤b) : rounds n b≤rounds n a := by
  have hb : 0 < b := ha.trans_le hab
  unfold rounds
  apply Nat.ceil_mono
  apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)

lemma direction_cost_antitone (n : ℕ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    directionCost n b≤directionCost n a := by
  unfold directionCost
  exact Nat.add_le_add_left (Nat.mul_le_mul_left n (gde_rounds_antitone n ha hab)) _

lemma horizon_sqrt_bound (Q : ℝ) (hQ : 32≤Q) :
    (PaperFullHistoryProgram.iterationCount Q:ℝ)≤6*Real.sqrt Q ∧ 5≤Real.sqrt Q := by
  have hp : 0<Q := by linarith
  have hs := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg Q
  have hfive : 5≤Real.sqrt Q := by nlinarith
  have hc := Nat.ceil_lt_add_one (show 0≤(16/3:ℝ)*Real.sqrt Q by positivity)
  change (PaperFullHistoryProgram.iterationCount Q:ℝ)<(16/3:ℝ)*Real.sqrt Q+1 at hc
  exact ⟨by linarith,hfive⟩

lemma small_iteration_bounds (Q : ℝ) (hQ : 32≤Q) (k : ℕ) (hk : k< PaperFullHistoryProgram.iterationCount Q) :
    (k:ℝ)+6≤7*Real.sqrt Q ∧ (k:ℝ)+1≤7*Real.sqrt Q ∧
      (PaperFullHistoryProgram.iterationCount Q:ℝ)+1≤7*Real.sqrt Q ∧ 7*Real.sqrt Q≤2*Q := by
  have hs := horizon_sqrt_bound Q hQ
  have hcast : (k:ℝ)+1≤(PaperFullHistoryProgram.iterationCount Q:ℝ) := by exact_mod_cast hk
  have hsq := Real.sq_sqrt (show 0≤Q by linarith)
  have hm := mul_le_mul_of_nonneg_right (show (7:ℝ)≤2*Real.sqrt Q by linarith) (Real.sqrt_nonneg Q)
  refine ⟨by linarith,by linarith,by linarith,by nlinarith⟩

def innerDelta (k : ℕ) : ℝ := xi k/(8*((k:ℝ)+5)*((k:ℝ)+6))
def innerVolumeArg (k : ℕ) : ℝ :=
  4*((k:ℝ)+5)/(xi k/(8*((k:ℝ)+6)^2))
def largeAccuracyParameter (Q : ℝ) : ℝ := (10:ℝ)^30*Q^10

lemma inner_delta_positive (k : ℕ) : 0 < innerDelta k := by
  unfold innerDelta xi nu
  positivity

lemma inner_delta_comparison (Q : ℝ) (hQ : 32≤Q) (k : ℕ) (hk : k< PaperFullHistoryProgram.iterationCount Q) :
    angularTolerance (largeAccuracyParameter Q)≤ innerDelta k := by
  have hp : 0<Q := by linarith
  have hb := small_iteration_bounds Q hQ k hk
  have hs := Real.sq_sqrt hp.le
  have hspos := Real.sqrt_pos.mpr hp
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hpow : ((k:ℝ)+1)^8≤(7*Real.sqrt Q)^8 :=
    pow_le_pow_left₀ (by positivity) hb.2.1 8
  have hprod : ((k:ℝ)+5)*((k:ℝ)+6)≤(7*Real.sqrt Q)^2 := by
    nlinarith [mul_le_mul (show (k:ℝ)+5≤7*Real.sqrt Q by linarith) hb.1 (by positivity) (by positivity)]
  have hden : ((k:ℝ)+1)^8*(8*((k:ℝ)+5)*((k:ℝ)+6))≤
      8*(7:ℝ)^10*Q^5 := by
    have hm := mul_le_mul hpow hprod (by positivity) (by positivity)
    have hsqpow : (Real.sqrt Q)^10=Q^5 := by
      rw [show (10:ℕ)=2*5 by norm_num,pow_mul,hs]
    have he : (7*Real.sqrt Q)^8*(7*Real.sqrt Q)^2=(7:ℝ)^10*Q^5 := by
      calc
        _ = (7:ℝ)^10*(Real.sqrt Q)^10 := by ring
        _ = _ := by rw [hsqpow]
    nlinarith [hm]
  have hroot : (10:ℝ)^15*Q^5≤Real.sqrt (2*largeAccuracyParameter Q) := by
    apply (sq_le_sq₀ (by positivity : 0≤(10:ℝ)^15*Q^5)
      (Real.sqrt_nonneg (2*largeAccuracyParameter Q))).mp
    have he : ((10:ℝ)^15*Q^5)^2=(10:ℝ)^30*Q^10 := by ring
    rw [he,Real.sq_sqrt (by unfold largeAccuracyParameter; positivity)]
    unfold largeAccuracyParameter
    nlinarith [pow_nonneg hp.le 10]
  have hrootpos : 0<Real.sqrt (2*largeAccuracyParameter Q) := by unfold largeAccuracyParameter; positivity
  have hlarge : ((k:ℝ)+1)^8*(8*((k:ℝ)+5)*((k:ℝ)+6)) ≤
      (9/20000:ℝ)*(4*Real.sqrt (2*largeAccuracyParameter Q)) := by
    have hqp : 0≤Q^5 := by positivity
    nlinarith
  have heq : innerDelta k=(9/20000:ℝ)/
      (((k:ℝ)+1)^8*(8*((k:ℝ)+5)*((k:ℝ)+6))) := by
    unfold innerDelta xi nu
    field_simp
  rw [heq,angularTolerance]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using hlarge

end
end PaperFullHistoryRates

end SnapshotModule_042
/- END full_history_rate_parameters -/

/- BEGIN ballopt_chart_calculus -/
section SnapshotModule_043

namespace PaperBallOptChart
open Set
open scoped RealInnerProductSpace
noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def chart (p : V) (L : E →ₗᵢ[ℝ] V) (z : E) : V := p+L z

def chartAffine (p : V) (L : E →ₗᵢ[ℝ] V) : E →ᵃ[ℝ] V :=
  AffineMap.const ℝ E p+L.toLinearMap.toAffineMap

def chartGradient (p : V) (L : E →ₗᵢ[ℝ] V) (grad : V → V) (z : E) : E :=
  ContinuousLinearMap.adjoint L.toContinuousLinearMap (grad (chart p L z))

lemma chart_sub (p : V) (L : E →ₗᵢ[ℝ] V) (x y : E) :
    chart p L x-chart p L y = L (x-y) := by
  simp only [chart,map_sub]
  abel

lemma chart_norm_sub (p : V) (L : E →ₗᵢ[ℝ] V) (x y : E) :
    ‖chart p L x-chart p L y‖=‖x-y‖ := by
  rw [chart_sub,L.norm_map]

lemma adjoint_norm_le (L : E →ₗᵢ[ℝ] V) (v : V) :
    ‖ContinuousLinearMap.adjoint L.toContinuousLinearMap v‖ ≤ ‖v‖ := by
  have hL : ‖L.toContinuousLinearMap‖ ≤ 1 :=
    L.toContinuousLinearMap.opNorm_le_bound (by norm_num) (fun x => by simp)
  have hnorm : ‖ContinuousLinearMap.adjoint L.toContinuousLinearMap‖ = ‖L.toContinuousLinearMap‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hh := (ContinuousLinearMap.adjoint L.toContinuousLinearMap).le_opNorm v
  rw [hnorm] at hh
  exact hh.trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg v))

lemma chart_hasGradient (f : V → ℝ) (grad : V → V)
    (hg : ∀ x, HasGradientAt f (grad x) x) (p : V) (L : E →ₗᵢ[ℝ] V) :
    ∀ z, HasGradientAt (fun x => f (chart p L x)) (chartGradient p L grad z) z := by
  intro z
  have hchart : HasFDerivAt (chart p L) L.toContinuousLinearMap z := by
    convert L.toContinuousLinearMap.hasFDerivAt.const_add p using 1 <;> rfl
  have hcomp := (hg (chart p L z)).hasFDerivAt.comp z hchart
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual : InnerProductSpace.toDual ℝ E (chartGradient p L grad z) =
      (InnerProductSpace.toDual ℝ V (grad (chart p L z))).comp L.toContinuousLinearMap := by
    ext x
    simp only [chartGradient,InnerProductSpace.toDual_apply_apply,ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_left L.toContinuousLinearMap x (grad (chart p L z))
  rw [hdual]
  exact hcomp

lemma chart_gradient_lipschitz (grad : V → V) (hLip : LipschitzWith 1 grad)
    (p : V) (L : E →ₗᵢ[ℝ] V) : LipschitzWith 1 (chartGradient p L grad) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  change ‖ContinuousLinearMap.adjoint L.toContinuousLinearMap (grad (chart p L x))-
    ContinuousLinearMap.adjoint L.toContinuousLinearMap (grad (chart p L y))‖ ≤ ‖x-y‖
  rw [← map_sub]
  have hh := hLip.norm_sub_le (chart p L x) (chart p L y)
  simp only [NNReal.coe_one,one_mul] at hh
  exact (adjoint_norm_le L _).trans (hh.trans_eq (chart_norm_sub p L x y))

lemma chart_convex (f : V → ℝ) (hc : ConvexOn ℝ univ f)
    (p : V) (L : E →ₗᵢ[ℝ] V) : ConvexOn ℝ univ (fun x => f (chart p L x)) := by
  have h := hc.comp_affineMap (chartAffine p L)
  convert h using 1 <;> first | rfl | simp [chartAffine]

lemma chart_gradient_norm_le (grad : V → V) (p : V) (L : E →ₗᵢ[ℝ] V) (z : E) :
    ‖chartGradient p L grad z‖ ≤ ‖grad (chart p L z)‖ := adjoint_norm_le L _

end
end PaperBallOptChart

end SnapshotModule_043
/- END ballopt_chart_calculus -/

/- BEGIN ballopt_chart_geometry -/
section SnapshotModule_044

namespace PaperBallOptChart
open Set
open scoped RealInnerProductSpace
noncomputable section

abbrev Space (n : ℕ) := PaperGDE.Vec n

def directionChart {d n : ℕ} (A : AffineSubspace ℝ (Space d))
    (hdim : Module.finrank ℝ A.direction = n+1) : Space n →ₗᵢ[ℝ] Space d :=
  A.direction.subtypeₗᵢ.comp
    (((stdOrthonormalBasis ℝ A.direction).reindex (finCongr hdim)).repr.symm.toLinearIsometry)

lemma directionChart_range {d n : ℕ} (A : AffineSubspace ℝ (Space d))
    (hdim : Module.finrank ℝ A.direction = n+1) (p : Space d) (hp : p∈A) :
    ∀ x, x∈A ↔ ∃ z, chart p (directionChart A hdim) z=x := by
  intro x
  constructor
  · intro hx
    let v : A.direction := ⟨x-p, A.vsub_mem_direction hx hp⟩
    let b := (stdOrthonormalBasis ℝ A.direction).reindex (finCongr hdim)
    refine ⟨b.repr v,?_⟩
    change p+(b.repr.symm (b.repr v) : Space d)=x
    rw [b.repr.symm_apply_apply]
    change p+(x-p)=x
    abel
  · rintro ⟨z,rfl⟩
    have hh := A.vadd_mem_of_mem_direction (show directionChart A hdim z∈A.direction from
      (((stdOrthonormalBasis ℝ A.direction).reindex (finCongr hdim)).repr.symm z).property) hp
    simpa [chart,add_comm] using hh

lemma direction_zero_singleton {d : ℕ} (A : AffineSubspace ℝ (Space d))
    (hdim : Module.finrank ℝ A.direction=0) (p : Space d) (hp : p∈A) :
    ∀ x∈A, x=p := by
  have ht : A.direction=⊥ := Submodule.finrank_eq_zero.mp hdim
  intro x hx
  have hh := A.vsub_mem_direction hx hp
  rw [ht,Submodule.mem_bot] at hh
  exact sub_eq_zero.mp hh

def body {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (B : ℝ) : Set (Space n) :=
  {z | ‖chart p L z‖≤B}

lemma chart_continuous {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) :
    Continuous (chart p L) := by
  exact continuous_const.add L.continuous

lemma body_convex {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (B : ℝ) :
    Convex ℝ (body p L B) := by
  have hh := (convex_closedBall (0 : Space d) B).affine_preimage (chartAffine p L)
  convert hh using 1 <;> first | rfl | exact Subsingleton.elim _ _ | (ext x; simp [body,chart,chartAffine,Metric.mem_closedBall,dist_zero_right])

lemma body_subset_enclosing_ball {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d)
    (B : ℝ) (hB : 1≤B) (hpB : ‖p‖≤B-1) : body p L B ⊆ Metric.closedBall 0 (4*B) := by
  intro z hz
  have hn := norm_sub_le (chart p L z) p
  have he : chart p L z-p=L z := by simp [chart]
  rw [he,L.norm_map] at hn
  have hh : ‖z‖≤4*B := by
    change ‖chart p L z‖≤B at hz
    linarith
  simpa [Metric.mem_closedBall,dist_zero_right] using hh

lemma body_compact {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d)
    (B : ℝ) (hB : 1≤B) (hpB : ‖p‖≤B-1) : IsCompact (body p L B) := by
  have hc : IsClosed (body p L B) :=
    isClosed_le (chart_continuous p L).norm continuous_const
  exact (isCompact_closedBall (0 : Space n) (4*B)).of_isClosed_subset hc
    (body_subset_enclosing_ball p L B hB hpB)

lemma body_interior {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d)
    (B : ℝ) (hpB : ‖p‖≤B-1) : (interior (body p L B)).Nonempty := by
  have hs : Metric.ball (0 : Space n) 1 ⊆ body p L B := by
    intro z hz
    have hn : ‖z‖<1 := by simpa [Metric.mem_ball,dist_zero_right] using hz
    have hh := norm_add_le p (L z)
    rw [L.norm_map] at hh
    change ‖p+L z‖≤B
    linarith
  exact ⟨0,interior_maximal hs Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))⟩

lemma body_diameter {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d)
    (B : ℝ) {x y : Space n} (hx : x∈body p L B) (hy : y∈body p L B) : ‖x-y‖≤2*B := by
  rw [← chart_norm_sub p L x y]
  exact (norm_sub_le _ _).trans (by change ‖chart p L x‖≤B at hx; change ‖chart p L y‖≤B at hy; linarith)

end
end PaperBallOptChart

end SnapshotModule_044
/- END ballopt_chart_geometry -/

/- BEGIN ballopt_core -/
section SnapshotModule_045

namespace PaperBallOpt
open Set MeasureTheory PaperGDE PaperCentroidProgram
open scoped RealInnerProductSpace
noncomputable section

abbrev Space (n : ℕ) := PaperGDE.Vec n

def radius (B tol : ℝ) : ℝ := tol/(8*(B+1)^2)
def delta (B tol : ℝ) : ℝ := tol/(8*B*(B+1))
def gamma (B tol : ℝ) : ℝ := tol/(2*B)
def roundsBeforeLast (n : ℕ) (B tol : ℝ) : ℕ :=
  ⌊((n+1:ℕ):ℝ)*Real.log ((4*B)/radius B tol)/(-Real.log (1-Real.exp (-1)))⌋₊
def objective {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (f : Space d→ℝ) : Space n→ℝ :=
  fun z=>f (PaperBallOptChart.chart p L z)
def target {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (f : Space d→ℝ)
    (m : Space d) (B tol : ℝ) : Set (Space n) :=
  PaperBallOptChart.body p L B ∩ {z | objective p L f z≤f m+tol/2}
def algorithm {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (B tol : ℝ) : Program n (State n) :=
  firstProgram (delta B tol) (gamma B tol) (roundsBeforeLast n B tol) (PaperBallOptChart.body p L B)

lemma target_data {n d : ℕ} (f : Space d→ℝ) (grad : Space d→Space d)
    (hg : ∀x,HasGradientAt f (grad x) x) (hLip : LipschitzWith 1 grad)
    (xstar : Space d) (hmin : ∀y,f xstar≤f y) (hstar : ‖xstar‖≤1)
    (A : AffineSubspace ℝ (Space d)) (p : Space d) (hp : p∈A)
    (L : Space n →ₗᵢ[ℝ] Space d) (hL : ∀x,x∈A ↔∃z,PaperBallOptChart.chart p L z=x)
    (B tol : ℝ) (hpB : ‖p‖≤B-1) (htol : 0<tol) (htol1 : tol≤1) :
    ∃m∈PaperCentroid.affineBall A B, (∀y∈PaperCentroid.affineBall A B,f m≤f y) ∧
      ∃z0, Metric.closedBall z0 (radius B tol) ⊆ target p L f m B tol ∧
      (interior (target p L f m B tol)).Nonempty := by
  obtain ⟨m,hm,hminimum,mprime,hmpA,hmpnorm,hball⟩ :=
    PaperCentroid.affine_target_ball f grad hg hLip xstar hmin hstar A p hp B tol hpB htol htol1
  obtain ⟨z0,hz0⟩ := (hL mprime).mp hmpA
  have hs : Metric.closedBall z0 (radius B tol) ⊆ target p L f m B tol := by
    intro z hz
    have hzA := (hL (PaperBallOptChart.chart p L z)).mpr ⟨z,rfl⟩
    have hdist : ‖PaperBallOptChart.chart p L z-mprime‖≤radius B tol := by
      rw [←hz0,PaperBallOptChart.chart_norm_sub]
      simpa [Metric.mem_closedBall,dist_eq_norm] using hz
    have hh := hball _ hzA hdist
    exact ⟨hh.1.2,by dsimp [objective]; linarith [hh.2]⟩
  have hB : 1≤B := by linarith [norm_nonneg p]
  have hr : 0<radius B tol := by dsimp [radius]; positivity
  refine ⟨m,hm,hminimum,z0,hs,?_⟩
  exact ⟨z0,interior_maximal (Metric.ball_subset_closedBall.trans hs) Metric.isOpen_ball
    (Metric.mem_ball_self hr)⟩

lemma actual_gde_retains_target {n d : ℕ} (C : Oracle n)
    (f : Space d→ℝ) (grad : Space d→Space d)
    (hg : ∀x,HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f) (hLip : LipschitzWith 1 grad)
    (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (xstar : Space d)
    (hmin : ∀y,f xstar≤f y) (hstar : ‖xstar‖≤1)
    (hC : OracleCorrect C (objective p L f)) (m : Space d)
    (B tol : ℝ) (zm : Space n) (hzm : PaperBallOptChart.chart p L zm=m) (hm : ‖m‖≤B) (hB : 1≤B) (htol : 0<tol) (htol1 : tol≤1)
    (P : Set (Space n)) (hPc : IsCompact P) (hPv : Convex ℝ P)
    (hsub : P⊆PaperBallOptChart.body p L B) (hTP : target p L f m B tol⊆P)
    (hTi : (interior (target p L f m B tol)).Nonempty)
    (hbad : f m+tol<objective p L f (center P)) :
    target p L f m B tol⊆cut P (center P)
      (Program.eval C (gdeProgram (center P) (delta B tol) (gamma B tol))) := by
  let g := objective p L f
  let G := PaperBallOptChart.chartGradient p L grad
  have hg' : ∀z,HasGradientAt g (G z) z := PaperBallOptChart.chart_hasGradient f grad hg p L
  have hc' : ConvexOn ℝ univ g := PaperBallOptChart.chart_convex f hc p L
  have hLip' : LipschitzWith 1 G := PaperBallOptChart.chart_gradient_lipschitz grad hLip p L
  have hfull := hTi.mono (interior_mono hTP)
  have hxP := center_mem hPc hPv hfull
  have hxK := hsub hxP
  have hzmK : zm∈PaperBallOptChart.body p L B := by change ‖PaperBallOptChart.chart p L zm‖≤B; rw[hzm]; exact hm
  have hbad' : g zm+tol<g (center P) := by simpa [g,objective,hzm] using hbad
  have hgamma := PaperCentroid.bad_center_gradient_premise g G hg' hc' (center P) zm B tol
    (by linarith) hbad' (PaperBallOptChart.body_diameter p L B hzmK hxK)
  have hdelta : 0<delta B tol := by dsimp [delta]; positivity
  have hdelta1 : delta B tol≤1 := by
    dsimp [delta]
    apply (div_le_one (by positivity : 0<8*B*(B+1))).mpr
    nlinarith
  have hgammapos : 0<gamma B tol := by dsimp [gamma]; positivity
  have hG := hgammapos.trans hgamma
  have hcert := full_gde_certificate g G hg' hLip' hC (center P) (delta B tol) (gamma B tol)
    hdelta hdelta1 hgammapos hgamma.le
  have hGupper : ‖G (center P)‖≤B+1 :=
    (PaperBallOptChart.chart_gradient_norm_le grad p L _).trans
      (PaperCentroid.gradient_norm_bound f grad hg hLip xstar _ hmin hstar B hxK)
  intro y hy
  refine ⟨hTP hy,?_⟩
  have htarget : g y≤g zm+tol/2 := by simpa [g,objective,hzm] using hy.2
  have hcut := PaperCentroid.ballopt_cut_retains_target g G hg' hc' (center P) y zm _ B (B+1) tol
    (by linarith) (by linarith) htol hbad' htarget
    (PaperBallOptChart.body_diameter p L B hy.1 hxK) hG hGupper hcert.2.1
  exact hcut.le.trans (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))

end
end PaperBallOpt

end SnapshotModule_045
/- END ballopt_core -/

/- BEGIN ballopt_complete -/
section SnapshotModule_046

namespace PaperBallOpt
open Set MeasureTheory PaperGDE PaperCentroidProgram
open scoped RealInnerProductSpace
noncomputable section

lemma volume_threshold {n d : ℕ} (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d)
    (f : Space d→ℝ) (m : Space d) (B tol : ℝ) (hB : 1≤B) (hpB : ‖p‖≤B-1)
    (htol : 0<tol) (z0 : Space n)
    (hball : Metric.closedBall z0 (radius B tol)⊆target p L f m B tol) :
    (1-Real.exp (-1))^(roundsBeforeLast n B tol+1)*
      (volume (PaperBallOptChart.body p L B)).toReal < (volume (target p L f m B tol)).toReal := by
  have hr : 0<radius B tol := by dsimp [radius]; positivity
  have hKfin : volume (PaperBallOptChart.body p L B)≠⊤ := (PaperBallOptChart.body_compact p L B hB hpB).measure_ne_top
  have hTfin : volume (target p L f m B tol)≠⊤ := ne_top_of_le_ne_top hKfin (measure_mono inter_subset_left)
  have hlower := ENNReal.toReal_mono hTfin (measure_mono hball)
  have hupper : (volume (PaperBallOptChart.body p L B)).toReal≤(volume (Metric.closedBall (0 : Space n) (4*B))).toReal := ENNReal.toReal_mono (isCompact_closedBall (0 : Space n) (4*B)).measure_ne_top
    (measure_mono (PaperBallOptChart.body_subset_enclosing_ball p L B hB hpB))
  have hunitpos : 0 < (volume (Metric.closedBall (0 : Space n) 1)).toReal := by
    apply ENNReal.toReal_pos
    · have hp : 0<volume (Metric.ball (0 : Space n) 1) :=
        Metric.isOpen_ball.measure_pos volume ⟨0,Metric.mem_ball_self (by norm_num)⟩
      exact (hp.trans_le (measure_mono Metric.ball_subset_closedBall)).ne'
    · exact (isCompact_closedBall (0 : Space n) 1).measure_ne_top
  have hs := mul_lt_mul_of_pos_right
    (PaperVolumeBudget.public_horizon (n+1) (1-Real.exp (-1)) (4*B) (radius B tol)
      PaperVolumeBudget.grunbaum_ratio_pos PaperVolumeBudget.grunbaum_ratio_lt_one (by positivity) hr)
    hunitpos
  have hd : Module.finrank ℝ (Space n)=n+1 := by simp [Space,PaperGDE.Vec]
  have hbig := Measure.addHaar_real_closedBall' (volume : Measure (Space n)) (0 : Space n)
    (by positivity : (0:ℝ)≤4*B)
  have hsmall := Measure.addHaar_real_closedBall' (volume : Measure (Space n)) z0 hr.le
  change (volume (Metric.closedBall (0 : Space n) (4*B))).toReal = _ at hbig
  change (volume (Metric.closedBall z0 (radius B tol))).toReal = _ at hsmall
  rw [hd] at hbig hsmall
  rw [hsmall] at hlower
  rw [hbig] at hupper
  have hqnonneg : 0≤(1-Real.exp (-1))^(roundsBeforeLast n B tol+1) :=
    pow_nonneg PaperVolumeBudget.grunbaum_ratio_pos.le _
  have hh := mul_le_mul_of_nonneg_left hupper hqnonneg
  unfold roundsBeforeLast at hh ⊢
  simp only [measureReal_def] at hlower hupper hh ⊢
  nlinarith

/-- The actual finite comparison program on an arbitrary orthonormal affine chart.
The chart has full range in A; neither its correctness nor its volume loss is assumed. -/
theorem chart_complete {n d : ℕ} (C : Oracle n)
    (f : Space d→ℝ) (grad : Space d→Space d)
    (hg : ∀x,HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f) (hLip : LipschitzWith 1 grad)
    (xstar : Space d) (hmin : ∀y,f xstar≤f y) (hstar : ‖xstar‖≤1)
    (A : AffineSubspace ℝ (Space d)) (p : Space d) (hp : p∈A)
    (L : Space n →ₗᵢ[ℝ] Space d) (hL : ∀x,x∈A ↔∃z,PaperBallOptChart.chart p L z=x)
    (B tol : ℝ) (hpB : ‖p‖≤B-1) (htol : 0<tol) (htol1 : tol≤1)
    (hC : OracleCorrect C (objective p L f)) :
    (PaperBallOptChart.chart p L (Program.eval C (algorithm p L B tol)).best)∈PaperCentroid.affineBall A B ∧
    (∀y∈PaperCentroid.affineBall A B,
      f (PaperBallOptChart.chart p L (Program.eval C (algorithm p L B tol)).best)-f y≤tol) ∧
    Program.height (algorithm p L B tol) ≤
      (roundsBeforeLast n B tol+1)*(2*(n+1)-1+n*rounds n (delta B tol)+1)-1 := by
  have hB : 1≤B := by linarith [norm_nonneg p]
  obtain ⟨m,hm,hminimum,z0,hball,hTi⟩ := target_data f grad hg hLip xstar hmin hstar A p hp L hL
    B tol hpB htol htol1
  obtain ⟨zm,hzm⟩ := (hL m).mp hm.1
  have haccuracy := firstProgram_accuracy_from_geometry C (objective p L f) hC (delta B tol) (gamma B tol)
    (f m+tol) (1-Real.exp (-1)) PaperVolumeBudget.grunbaum_ratio_pos.le
    (PaperBallOptChart.body p L B) (target p L f m B tol)
    (PaperBallOptChart.body_compact p L B hB hpB) (PaperBallOptChart.body_convex p L B)
    inter_subset_left hTi
    (fun P hPc hPv hPK hTP hbad=>actual_gde_retains_target C f grad hg hc hLip p L xstar hmin hstar
      hC m B tol zm hzm hm.2 hB htol htol1 P hPc hPv hPK hTP hTi hbad)
    (fun P hPc hPv _ hPi v hv=>actual_centroid_shrink hPc hPv hPi v hv)
    (roundsBeforeLast n B tol) (volume_threshold p L f m B tol hB hpB htol z0 hball)
  have hfeasible : (Program.eval C (algorithm p L B tol)).best∈PaperBallOptChart.body p L B := by
    dsimp [algorithm,firstProgram]
    rw [Program.eval_bind]
    exact loop_best_feasible C (delta B tol) (gamma B tol) (roundsBeforeLast n B tol) _
      (PaperBallOptChart.body p L B)
      (cut_compact (PaperBallOptChart.body_compact p L B hB hpB) _ _)
      (cut_convex (PaperBallOptChart.body_convex p L B) _ _)
      (cut_subset _ _ _)
      (center_mem (PaperBallOptChart.body_compact p L B hB hpB)
        (PaperBallOptChart.body_convex p L B) (PaperBallOptChart.body_interior p L B hpB))
  refine ⟨⟨(hL _).mpr ⟨_,rfl⟩,hfeasible⟩,?_,first_public_height _ _ _ _⟩
  intro y hy
  have hmle := hminimum y hy
  change f (PaperBallOptChart.chart p L (Program.eval C (firstProgram _ _ _ _)).best)≤f m+tol at haccuracy
  dsimp [algorithm]
  linarith

end
end PaperBallOpt

end SnapshotModule_046
/- END ballopt_complete -/

/- BEGIN ballopt_ambient -/
section SnapshotModule_047

namespace PaperBallOpt
open Set PaperGDE PaperCentroidProgram
open scoped RealInnerProductSpace
noncomputable section

lemma positive_dimension_eq {d : ℕ} (A : AffineSubspace ℝ (Space d))
    (h : Module.finrank ℝ A.direction≠0) :
    Module.finrank ℝ A.direction=(Module.finrank ℝ A.direction-1)+1 := by omega

def ambientCap {d : ℕ} (A : AffineSubspace ℝ (Space d)) (B tol : ℝ) : ℕ :=
  if Module.finrank ℝ A.direction=0 then 0 else
    let n := Module.finrank ℝ A.direction-1
    (roundsBeforeLast n B tol+1)*(2*(n+1)-1+n*rounds n (delta B tol)+1)-1

/-- Public affine chart, a dimension-zero branch, and literal lifted comparison queries.
No gradient, objective value, or minimizer is used in the construction. -/
def ambientProgram {d : ℕ} (A : AffineSubspace ℝ (Space d)) (p : Space d) (B tol : ℝ) :
    Program d (Space d) := by
  classical
  exact if h : Module.finrank ℝ A.direction=0 then .pure p else
    let L := PaperBallOptChart.directionChart A (positive_dimension_eq A h)
    Program.bind (Program.mapQueries (PaperBallOptChart.chart p L) (algorithm p L B tol))
      (fun s=>.pure (PaperBallOptChart.chart p L s.best))

lemma ambient_public_height {d : ℕ} (A : AffineSubspace ℝ (Space d))
    (p : Space d) (B tol : ℝ) : Program.height (ambientProgram A p B tol)≤ambientCap A B tol := by
  classical
  unfold ambientProgram ambientCap
  split_ifs with h
  · rfl
  · dsimp only
    have hh := Program.height_bind_le
      (Program.mapQueries (PaperBallOptChart.chart p (PaperBallOptChart.directionChart A (positive_dimension_eq A h)))
        (algorithm p (PaperBallOptChart.directionChart A (positive_dimension_eq A h)) B tol))
      (fun s=>Program.pure (PaperBallOptChart.chart p (PaperBallOptChart.directionChart A (positive_dimension_eq A h)) s.best))
      ((roundsBeforeLast (Module.finrank ℝ A.direction-1) B tol+1)*
        (2*((Module.finrank ℝ A.direction-1)+1)-1+
          (Module.finrank ℝ A.direction-1)*rounds (Module.finrank ℝ A.direction-1) (delta B tol)+1)-1)
      0 (by rw [Program.height_mapQueries]; exact first_public_height _ _ _ _) (by intro s; rfl)
    simpa using hh

lemma chart_algorithm_feasible {n d : ℕ} (C : Oracle n)
    (p : Space d) (L : Space n →ₗᵢ[ℝ] Space d) (B tol : ℝ) (hpB : ‖p‖≤B-1) :
    (Program.eval C (algorithm p L B tol)).best∈PaperBallOptChart.body p L B := by
  have hB : 1≤B := by linarith [norm_nonneg p]
  dsimp [algorithm,firstProgram]
  rw [Program.eval_bind]
  exact loop_best_feasible C (delta B tol) (gamma B tol) (roundsBeforeLast n B tol) _
    (PaperBallOptChart.body p L B)
    (cut_compact (PaperBallOptChart.body_compact p L B hB hpB) _ _)
    (cut_convex (PaperBallOptChart.body_convex p L B) _ _) (cut_subset _ _ _)
    (center_mem (PaperBallOptChart.body_compact p L B hB hpB)
      (PaperBallOptChart.body_convex p L B) (PaperBallOptChart.body_interior p L B hpB))

lemma ambient_feasible {d : ℕ} (C : Oracle d) (A : AffineSubspace ℝ (Space d))
    (p : Space d) (hp : p∈A) (B tol : ℝ) (hpB : ‖p‖≤B-1) :
    Program.eval C (ambientProgram A p B tol)∈PaperCentroid.affineBall A B := by
  classical
  unfold ambientProgram
  split_ifs with h
  · exact ⟨hp,by change ‖p‖≤B; linarith⟩
  · let L := PaperBallOptChart.directionChart A (positive_dimension_eq A h)
    rw [Program.eval_bind,Program.eval_mapQueries]
    simp only [Program.eval]
    refine ⟨(PaperBallOptChart.directionChart_range A (positive_dimension_eq A h) p hp _).mpr ⟨_,rfl⟩,?_⟩
    exact chart_algorithm_feasible (fun y x=>C (PaperBallOptChart.chart p L y) (PaperBallOptChart.chart p L x)) p L B tol hpB

/-- Complete BALL-OPT proposition with the actual ambient comparison program,
all-reply-tree cap, feasibility even for inconsistent replies, and accuracy. -/
theorem ambient_complete {d : ℕ} (C : Oracle d)
    (f : Space d→ℝ) (grad : Space d→Space d)
    (hg : ∀x,HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f) (hLip : LipschitzWith 1 grad)
    (xstar : Space d) (hmin : ∀y,f xstar≤f y) (hstar : ‖xstar‖≤1) (hC : OracleCorrect C f)
    (A : AffineSubspace ℝ (Space d)) (p : Space d) (hp : p∈A)
    (B tol : ℝ) (hpB : ‖p‖≤B-1) (htol : 0<tol) (htol1 : tol≤1) :
    Program.eval C (ambientProgram A p B tol)∈PaperCentroid.affineBall A B ∧
      (∀y∈PaperCentroid.affineBall A B,f (Program.eval C (ambientProgram A p B tol))-f y≤tol) ∧
      Program.height (ambientProgram A p B tol)≤ambientCap A B tol := by
  refine ⟨ambient_feasible C A p hp B tol hpB,?_,ambient_public_height A p B tol⟩
  classical
  unfold ambientProgram
  split_ifs with h
  · intro y hy
    have hyEq := PaperBallOptChart.direction_zero_singleton A h p hp y hy.1
    simp only [Program.eval,hyEq,sub_self]
    exact htol.le
  · let L := PaperBallOptChart.directionChart A (positive_dimension_eq A h)
    let Cs : Oracle (Module.finrank ℝ A.direction-1) :=
      fun y x=>C (PaperBallOptChart.chart p L y) (PaperBallOptChart.chart p L x)
    have hCs : OracleCorrect Cs (objective p L f) := by intro y x; exact hC _ _
    have hh := (chart_complete Cs f grad hg hc hLip xstar hmin hstar A p hp L
      (PaperBallOptChart.directionChart_range A (positive_dimension_eq A h) p hp)
      B tol hpB htol htol1 hCs).2.1
    rw [Program.eval_bind,Program.eval_mapQueries]
    simp only [Program.eval]
    exact hh

end
end PaperBallOpt

end SnapshotModule_047
/- END ballopt_ambient -/

/- BEGIN ballopt_submodule -/
section SnapshotModule_048

namespace PaperBallOpt
open Set PaperGDE
noncomputable section

def subspaceProgram {d : ℕ} (U : Submodule ℝ (Space d)) (p : Space d) (B tol : ℝ) :
    PaperTrinary.Program d (Space d) :=
  PaperTrinary.liftGDE (ambientProgram U.toAffineSubspace p B tol)

def subspaceCap {d : ℕ} (U : Submodule ℝ (Space d)) (B tol : ℝ) : ℕ :=
  ambientCap U.toAffineSubspace B tol

lemma subspace_public_cap {d : ℕ} (U : Submodule ℝ (Space d)) (p : Space d) (B tol : ℝ) :
    PaperOracle.Program.Cap (subspaceCap U B tol) (subspaceProgram U p B tol) := by
  exact PaperOracle.Program.cap_mono _ (PaperTrinary.liftGDE_cap _)
    (ambient_public_height U.toAffineSubspace p B tol)

lemma subspace_feasible {d : ℕ} (C : PaperTrinary.Oracle d) (U : Submodule ℝ (Space d))
    (p : Space d) (hp : p∈U) (B tol : ℝ) (hpB : ‖p‖≤B-1) :
    PaperOracle.Program.run C (subspaceProgram U p B tol)∈U ∧
      ‖PaperOracle.Program.run C (subspaceProgram U p B tol)‖≤B := by
  unfold subspaceProgram
  rw [PaperTrinary.liftGDE_run]
  exact ambient_feasible _ U.toAffineSubspace p hp B tol hpB

lemma subspace_accurate {d : ℕ} (f : Space d→ℝ) (grad : Space d→Space d)
    (hg : ∀x,HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f) (hLip : LipschitzWith 1 grad)
    (xstar : Space d) (hmin : ∀y,f xstar≤f y) (hstar : ‖xstar‖≤1)
    (U : Submodule ℝ (Space d)) (p : Space d) (hp : p∈U)
    (B tol : ℝ) (hpB : ‖p‖≤B-1) (htol : 0<tol) (htol1 : tol≤1) :
    ∀y∈U, ‖y‖≤B →
      f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (subspaceProgram U p B tol))≤f y+tol := by
  intro y hy hyn
  unfold subspaceProgram
  rw [PaperTrinary.liftGDE_run]
  have hh := (ambient_complete _ f grad hg hc hLip xstar hmin hstar (PaperTrinary.comparison_correct f)
    U.toAffineSubspace p hp B tol hpB htol htol1).2.1 y ⟨hy,hyn⟩
  linarith

lemma subspaceCap_zero {d : ℕ} (U : Submodule ℝ (Space d)) (hU : Module.finrank ℝ U=0)
    (B tol : ℝ) : subspaceCap U B tol=0 := by
  have hdir : U.toAffineSubspace.direction=U := by
    convert Submodule.toAffineSubspace_direction U using 1 <;> rfl
  simp only [subspaceCap,ambientCap]
  rw [hdir,hU]
  rfl

lemma subspaceCap_positive {d : ℕ} (U : Submodule ℝ (Space d)) (hU : Module.finrank ℝ U≠0)
    (B tol : ℝ) :
    subspaceCap U B tol =
      (roundsBeforeLast (Module.finrank ℝ U-1) B tol+1)*
        (2*(Module.finrank ℝ U)-1+(Module.finrank ℝ U-1)*
          rounds (Module.finrank ℝ U-1) (delta B tol)+1)-1 := by
  have hdim : Module.finrank ℝ U=(Module.finrank ℝ U-1)+1 := by omega
  have hdir : U.toAffineSubspace.direction=U := by
    convert Submodule.toAffineSubspace_direction U using 1 <;> rfl
  simp only [subspaceCap,ambientCap]
  rw [hdir,if_neg hU,←hdim]

end
end PaperBallOpt

end SnapshotModule_048
/- END ballopt_submodule -/

/- BEGIN full_history_complete -/
section SnapshotModule_049

namespace PaperFullHistoryComplete
open Set PaperGDE PaperTrinary PaperFullHistory PaperFullHistoryProgram
open scoped RealInnerProductSpace
noncomputable section

def rankCost (rank : ℕ) (B tol : ℝ) : ℕ :=
  if rank=0 then 0 else
    (PaperBallOpt.roundsBeforeLast (rank-1) B tol+1)*
      (2*rank-1+(rank-1)*rounds (rank-1) (PaperBallOpt.delta B tol)+1)-1

def innerCap (n k : ℕ) : ℕ :=
  (Finset.range (min (n+1) (k+2)+1)).sup
    (fun rank => rankCost rank (radius (k+1)) (xi k))

def innerProgram {n : ℕ} : InnerProgram n := fun k x vs =>
  PaperBallOpt.subspaceProgram (stateSpace x vs k) x (radius (k+1)) (xi k)

lemma state_dimension_bound {n : ℕ} (x : Vec n) (vs : ℕ → Vec n) (k : ℕ) :
    Module.finrank ℝ (stateSpace x vs k) ≤ min (n+1) (k+2) := by
  have h := history_dimension_bound (fun _ => x) vs k
  simpa [stateSpace,historySpace,PaperGDE.Vec] using! h

lemma subspace_rankCost {n : ℕ} (U : Submodule ℝ (Vec n)) (B tol : ℝ) :
    PaperBallOpt.subspaceCap U B tol=rankCost (Module.finrank ℝ U) B tol := by
  classical
  unfold rankCost
  split_ifs with h
  · exact PaperBallOpt.subspaceCap_zero U h B tol
  · exact PaperBallOpt.subspaceCap_positive U h B tol

lemma inner_public_cap (n k : ℕ) (x : Vec n) (vs : ℕ → Vec n) :
    PaperOracle.Program.Cap (innerCap n k) (innerProgram k x vs) := by
  apply PaperOracle.Program.cap_mono _ (PaperBallOpt.subspace_public_cap _ _ _ _)
  rw [subspace_rankCost]
  exact Finset.le_sup (f := fun rank => rankCost rank (radius (k+1)) (xi k))
    (Finset.mem_range.mpr (by have h := state_dimension_bound x vs k; omega))

lemma inner_feasible {n : ℕ} (C : PaperTrinary.Oracle n) : InnerFeasible C (@innerProgram n) := by
  intro k x vs hx
  apply PaperBallOpt.subspace_feasible C (stateSpace x vs k) x
    (Submodule.subset_span (Or.inl rfl)) (radius (k+1)) (xi k)
  rw [radius_succ]
  linarith

lemma inner_accurate {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (xstar : Vec n)
    (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1) : InnerAccurate f (@innerProgram n) := by
  intro k x vs hx u hu hun
  apply PaperBallOpt.subspace_accurate f grad hg hc hLip xstar hmin hstar
    (stateSpace x vs k) x (Submodule.subset_span (Or.inl rfl)) (radius (k+1)) (xi k)
    (by rw [radius_succ]; linarith) (xi_pos k) ((xi_le_nu k).trans (by norm_num [nu])) u hu hun

def program {n : ℕ} (Q : ℝ) : PaperTrinary.Program n (Vec n) :=
  PaperFullHistoryProgram.algorithm innerProgram Q

def cap (n : ℕ) (Q : ℝ) : ℕ :=
  ∑ k ∈ Finset.range (PaperFullHistoryProgram.iterationCount Q),stepBudget n (innerCap n) k

lemma program_public_cap (n : ℕ) (Q : ℝ) :
    PaperOracle.Program.Cap (cap n Q) (program (n := n) Q) :=
  algorithm_public_cap innerProgram (innerCap n) (inner_public_cap n) Q

/-- The full normalized acceleration program. There are no subroutine accuracy,
convergence, KKT, volume, perturbation or path-cap assumptions in this theorem. -/
theorem normalized_fullhistory_complete {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (hLip : LipschitzWith 1 grad) (xstar : Vec n)
    (hmin : ∀ y, f xstar ≤ f y) (hstar : ‖xstar‖ ≤ 1) (Q : ℝ) (hQ : 0<Q) :
    f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (program Q))-f xstar ≤ 1/Q ∧
      PaperOracle.Program.Cap (cap n Q) (program (n := n) Q) := by
  exact ⟨accuracy_from_actual_inner f grad hg hc hLip xstar hmin hstar innerProgram
    (inner_feasible _) (inner_accurate f grad hg hc hLip xstar hmin hstar) Q hQ,program_public_cap n Q⟩

def originalProgram {n : ℕ} (R Q : ℝ) : PaperTrinary.Program n (Vec n) :=
  PaperOracle.Program.bind
    (PaperOracle.Program.mapQueries (fun q : Vec n×Vec n => (R • q.1,R • q.2)) (program Q))
    (fun x => .done (R • x))

lemma original_public_cap (n : ℕ) (R Q : ℝ) :
    PaperOracle.Program.Cap (cap n Q) (originalProgram (n := n) R Q) := by
  have h := PaperOracle.Program.cap_bind _ (fun x => PaperOracle.Program.done (R • x))
    (PaperOracle.Program.cap_mapQueries (fun q : Vec n×Vec n => (R • q.1,R • q.2)) (cap n Q) (program Q) (program_public_cap n Q))
    (b := 0) (by intro x; trivial)
  simpa [originalProgram] using h

/-- Original beta,R,epsilon correctness and fixed cap for the concrete accelerated
comparison program. Its geometry and arithmetic depend only on public inputs. -/
theorem original_fullhistory_complete {n : ℕ} (f : Vec n → ℝ) (grad : Vec n → Vec n)
    (hg : ∀ x, HasGradientAt f (grad x) x) (hc : ConvexOn ℝ univ f)
    (beta : NNReal) (hb : 0<beta) (hLip : LipschitzWith beta grad)
    (xstar : Vec n) (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon)
    (hmin : ∀ y, f xstar≤f y) (hstar : ‖xstar‖≤R)
    (hQ : 0<Q) (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    f (PaperOracle.Program.run (PaperOracle.comparisonOracle f) (originalProgram R Q))-f xstar≤epsilon ∧
      PaperOracle.Program.Cap (cap n Q) (originalProgram (n := n) R Q) := by
  have hbR : (0:ℝ)<beta := hb
  have hscale : 0<(beta:ℝ)*R^2 := by positivity
  let g := PaperNormalization.objective f beta R
  let gg := PaperNormalization.scaledGradient grad beta R
  let a := R⁻¹ • xstar
  have hnorm := PaperNormalization.localized_minimizer f beta R xstar hbR hR hstar hmin
  have hgap := (normalized_fullhistory_complete g gg (PaperNormalization.hasGradient f grad hg beta R)
    (PaperNormalization.convex_objective f hc beta R hscale)
    (PaperNormalization.gradient_lipschitz grad beta R hb hR hLip) a hnorm.2 hnorm.1 Q hQ).1
  have hrecip : 1/Q=epsilon/((beta:ℝ)*R^2) := by rw [hQdef]; field_simp
  have horig := PaperNormalization.original_gap f beta R epsilon
    (PaperOracle.Program.run (PaperOracle.comparisonOracle g) (program Q)) a hbR hR heps
    (by rw [←hrecip]; exact hgap)
  have ha : R • a=xstar := by dsimp [a]; rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  rw [ha] at horig
  have hOracle : (fun q : Vec n×Vec n => PaperOracle.comparisonOracle f (R • q.1,R • q.2))=
      PaperOracle.comparisonOracle g := by
    funext q
    exact (PaperOracle.realOrder_positive_division (f (R • q.1)) (f (R • q.2))
      ((beta:ℝ)*R^2) hscale).symm
  constructor
  · simpa only [originalProgram,PaperOracle.Program.run_bind,PaperOracle.Program.run,
      PaperOracle.Program.run_mapQueries,hOracle] using horig
  · exact original_public_cap n R Q

end
end PaperFullHistoryComplete

end SnapshotModule_049
/- END full_history_complete -/

/- BEGIN full_history_rate_costs -/
section SnapshotModule_050

namespace PaperFullHistoryRates
open PaperGDE PaperFullHistory PaperAdaNGD
noncomputable section
set_option maxHeartbeats 2000000

lemma inner_volume_arg_formula (k : ℕ) :
    innerVolumeArg k=(32/(9/20000:ℝ))*((k:ℝ)+5)*((k:ℝ)+6)^2*((k:ℝ)+1)^8 := by
  unfold innerVolumeArg xi nu
  field_simp
  <;> ring

lemma inner_volume_arg_ge_one (k : ℕ) : 1 ≤ innerVolumeArg k := by
  rw [inner_volume_arg_formula]
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have hp : (1:ℝ)≤((k:ℝ)+1)^8 := one_le_pow₀ (by linarith)
  have hb : (1:ℝ)≤((k:ℝ)+6)^2 := by nlinarith
  have hm := mul_le_mul hb hp (by norm_num) (by positivity)
  have hm2 := mul_le_mul (show (1:ℝ)≤(k:ℝ)+5 by linarith) hm (by norm_num) (by positivity)
  nlinarith

lemma inner_volume_arg_upper (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) : innerVolumeArg k≤(10:ℝ)^20*Q^6 := by
  have hp : 0<Q := by linarith
  have hb := small_iteration_bounds Q hQ k hk
  have hs := Real.sq_sqrt hp.le
  have h5 : (k:ℝ)+5≤7*Real.sqrt Q := by linarith [hb.1]
  have h6 : (k:ℝ)+6≤7*Real.sqrt Q := hb.1
  have h1 : (k:ℝ)+1≤7*Real.sqrt Q := hb.2.1
  have hpow : (7*Real.sqrt Q)^11≤(7*Real.sqrt Q)^12 :=
    pow_le_pow_right₀ (by nlinarith [Real.sqrt_nonneg Q,horizon_sqrt_bound Q hQ]) (by norm_num)
  have hsqpow : (Real.sqrt Q)^12=Q^6 := by rw [show (12:ℕ)=2*6 by norm_num,pow_mul,hs]
  have h12 : (7*Real.sqrt Q)^12=(7:ℝ)^12*Q^6 := by rw [mul_pow,hsqpow]
  calc
    innerVolumeArg k=(32/(9/20000:ℝ))*((k:ℝ)+5)*((k:ℝ)+6)^2*((k:ℝ)+1)^8 := inner_volume_arg_formula k
    _ ≤ (32/(9/20000:ℝ))*(7*Real.sqrt Q)^11 := by
      calc
        _ ≤ (32/(9/20000:ℝ))*(7*Real.sqrt Q)*(7*Real.sqrt Q)^2*(7*Real.sqrt Q)^8 := by gcongr
        _ = _ := by ring
    _ ≤ (32/(9/20000:ℝ))*(7*Real.sqrt Q)^12 := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = (32/(9/20000:ℝ))*(7:ℝ)^12*Q^6 := by rw [h12]; ring
    _ ≤ _ := by nlinarith [pow_nonneg hp.le 6]

lemma inner_volume_log_bound (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) : Real.log (innerVolumeArg k)≤206*Real.log Q := by
  have hp : 0<Q := by linarith
  have harg := inner_volume_arg_ge_one k
  have hh := Real.log_le_log (show 0 < innerVolumeArg k by linarith) (inner_volume_arg_upper Q hQ k hk)
  rw [Real.log_mul (by norm_num : (10:ℝ)^20≠0) (pow_ne_zero 6 hp.ne'),Real.log_pow,Real.log_pow] at hh
  have h10 : Real.log (10:ℝ)≤10 := Real.log_le_self (by norm_num)
  have hL := PaperCentroidRates.logQ_lower Q hQ
  norm_num at hh
  linarith

lemma large_accuracy_log_bound (rank : ℕ) (Q : ℝ) (hQ : 32≤Q)
    (hrank : 1≤rank) (hrankQ : (rank:ℝ)≤2*Q) :
    Real.log ((rank:ℝ)*largeAccuracyParameter Q)≤312*Real.log Q := by
  have hp : 0<Q := by linarith
  have hr : (0:ℝ)<rank := by exact_mod_cast (show 0<rank by omega)
  have hu : (rank:ℝ)*largeAccuracyParameter Q≤2*(10:ℝ)^30*Q^11 := by
    have hm := mul_le_mul_of_nonneg_right hrankQ (show 0≤largeAccuracyParameter Q by unfold largeAccuracyParameter; positivity)
    convert hm using 1 <;> (first | rfl | (unfold largeAccuracyParameter; ring))
  have hh := Real.log_le_log (mul_pos hr (by unfold largeAccuracyParameter; positivity)) hu
  rw [Real.log_mul (mul_ne_zero (by norm_num : (2:ℝ)≠0) (by norm_num : (10:ℝ)^30≠0)) (pow_ne_zero 11 hp.ne'),
    Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (10:ℝ)^30≠0),Real.log_pow,Real.log_pow] at hh
  have h2 : Real.log (2:ℝ)≤1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have h10 : Real.log (10:ℝ)≤10 := Real.log_le_self (by norm_num)
  have hL := PaperCentroidRates.logQ_lower Q hQ
  norm_num at hh
  linarith

lemma inner_direction_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) (hrank : (n+1:ℝ)≤2*Q) :
    ((directionCost n (innerDelta k)+1:ℕ):ℝ)≤400000*(n+1:ℝ)*Real.log Q := by
  have hp : 0<Q := by linarith
  have hbig : 32≤largeAccuracyParameter Q := by
    unfold largeAccuracyParameter
    have hpow : (1:ℝ)≤Q^10 := one_le_pow₀ (by linarith)
    nlinarith
  have hsmall : 0<angularTolerance (largeAccuracyParameter Q) := by unfold angularTolerance largeAccuracyParameter; positivity
  have hmono := direction_cost_antitone n hsmall (inner_delta_comparison Q hQ k hk)
  have hcast : ((directionCost n (innerDelta k)+1:ℕ):ℝ)≤
      ((directionCost n (angularTolerance (largeAccuracyParameter Q))+1:ℕ):ℝ) := by exact_mod_cast Nat.add_le_add_right hmono 1
  have hcost := PaperRates.directionCost_uniform n (largeAccuracyParameter Q) hbig
  have hlog := large_accuracy_log_bound (n+1) Q hQ (by omega) (by simpa using hrank)
  push_cast at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0≤1003*(n+1:ℝ) by positivity)
  have hbase : 0≤(n+1:ℝ)*Real.log Q := by
    have hL := PaperCentroidRates.logQ_lower Q hQ
    positivity
  simp only [Nat.cast_add,Nat.cast_one] at hcast ⊢
  nlinarith

end
end PaperFullHistoryRates

end SnapshotModule_050
/- END full_history_rate_costs -/

/- BEGIN full_history_inner_rate -/
section SnapshotModule_051

namespace PaperFullHistoryRates
open PaperGDE PaperFullHistory PaperAdaNGD
noncomputable section
set_option maxHeartbeats 2000000

lemma inner_B (k : ℕ) : radius (k+1)=(k:ℝ)+5 := by simp [radius]; ring

lemma ball_delta_eq (k : ℕ) : PaperBallOpt.delta (radius (k+1)) (xi k)=innerDelta k := by
  rw [inner_B]
  unfold PaperBallOpt.delta innerDelta
  congr 1
  ring

lemma ball_volume_arg_eq (k : ℕ) :
    (4*radius (k+1))/PaperBallOpt.radius (radius (k+1)) (xi k)=innerVolumeArg k := by
  rw [inner_B]
  unfold PaperBallOpt.radius innerVolumeArg
  congr 2
  ring

lemma inner_centroid_count (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) :
    ((PaperBallOpt.roundsBeforeLast n (radius (k+1)) (xi k)+1:ℕ):ℝ)≤
      620*(n+1:ℝ)*Real.log Q := by
  have hL := PaperCentroidRates.logQ_lower Q hQ
  have harg := inner_volume_arg_ge_one k
  have hlog0 : 0≤Real.log (innerVolumeArg k) := Real.log_nonneg harg
  have hlambda := PaperVolumeBudget.grunbaum_lambda_pos
  have hn : 1≤(n+1:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hfloor := Nat.floor_le (show 0≤(n+1:ℝ)*Real.log (innerVolumeArg k)/
    (-Real.log (1-Real.exp (-1))) by positivity)
  have hf : ((PaperBallOpt.roundsBeforeLast n (radius (k+1)) (xi k)+1:ℕ):ℝ)≤
      (n+1:ℝ)*Real.log (innerVolumeArg k)/(-Real.log (1-Real.exp (-1)))+1 := by
    unfold PaperBallOpt.roundsBeforeLast
    rw [ball_volume_arg_eq]
    push_cast
    linarith [hfloor]
  have hdiv : (n+1:ℝ)*Real.log (innerVolumeArg k)/(-Real.log (1-Real.exp (-1)))≤
      618*(n+1:ℝ)*Real.log Q := by
    apply (div_le_iff₀ hlambda).mpr
    have hm := mul_le_mul_of_nonneg_left (inner_volume_log_bound Q hQ k hk)
      (show 0≤(n+1:ℝ) by positivity)
    have hc := mul_le_mul_of_nonneg_left PaperCentroidRates.lambda_lower
      (show 0≤618*(n+1:ℝ)*Real.log Q by positivity)
    nlinarith
  have hDL : 1≤(n+1:ℝ)*Real.log Q := by nlinarith
  linarith

lemma rank_cost_bound (rank : ℕ) (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) (hRank : (rank:ℝ)≤2*Q) :
    (PaperFullHistoryComplete.rankCost rank (radius (k+1)) (xi k):ℝ)≤
      (10:ℝ)^12*(rank:ℝ)^2*(Real.log Q)^2 := by
  classical
  by_cases hz : rank=0
  · simp [hz,PaperFullHistoryComplete.rankCost]
  · have hrank : 1≤rank := by omega
    have hdim : ((rank-1:ℕ):ℝ)+1=(rank:ℝ) := by exact_mod_cast Nat.sub_add_cancel hrank
    have hM := inner_centroid_count (rank-1) Q hQ k hk
    have hG := inner_direction_bound (rank-1) Q hQ k hk (by rw [hdim]; exact hRank)
    rw [hdim] at hM hG
    have hfactor : 2*rank-1+(rank-1)*rounds (rank-1)
        (PaperBallOpt.delta (radius (k+1)) (xi k))+1 =
        directionCost (rank-1) (PaperBallOpt.delta (radius (k+1)) (xi k))+1 := by
      unfold directionCost
      rw [Nat.sub_add_cancel hrank]
    have hnat : PaperFullHistoryComplete.rankCost rank (radius (k+1)) (xi k)≤
        (PaperBallOpt.roundsBeforeLast (rank-1) (radius (k+1)) (xi k)+1)*
          (directionCost (rank-1) (innerDelta k)+1) := by
      unfold PaperFullHistoryComplete.rankCost
      rw [if_neg hz,hfactor,ball_delta_eq]
      exact Nat.sub_le _ _
    have hc : (PaperFullHistoryComplete.rankCost rank (radius (k+1)) (xi k):ℝ)≤
        ((PaperBallOpt.roundsBeforeLast (rank-1) (radius (k+1)) (xi k)+1:ℕ):ℝ)*
          ((directionCost (rank-1) (innerDelta k)+1:ℕ):ℝ) := by exact_mod_cast hnat
    have hL := PaperCentroidRates.logQ_lower Q hQ
    have hp : 0≤620*(rank:ℝ)*Real.log Q := by positivity
    have hm := mul_le_mul hM hG (Nat.cast_nonneg _) hp
    have hbase : 0≤(rank:ℝ)^2*(Real.log Q)^2 := by positivity
    nlinarith

lemma public_inner_cap_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) :
    (PaperFullHistoryComplete.innerCap n k:ℝ)≤
      (10:ℝ)^12*((PaperFullHistoryProgram.iterationCount Q:ℝ)+1)^2*(Real.log Q)^2 := by
  classical
  let s := Finset.range (min (n+1) (k+2)+1)
  have hne : s.Nonempty := ⟨0,Finset.mem_range.mpr (by omega)⟩
  obtain ⟨rank,hrank,heq⟩ := Finset.exists_mem_eq_sup s hne
    (fun rank => PaperFullHistoryComplete.rankCost rank (radius (k+1)) (xi k))
  have hr : rank≤PaperFullHistoryProgram.iterationCount Q+1 := by
    have hmem := Finset.mem_range.mp hrank
    omega
  have hrreal : (rank:ℝ)≤(PaperFullHistoryProgram.iterationCount Q:ℝ)+1 := by exact_mod_cast hr
  have hb := small_iteration_bounds Q hQ k hk
  have hbound := rank_cost_bound rank Q hQ k hk (hrreal.trans (hb.2.2.1.trans hb.2.2.2))
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) rank) hrreal 2
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log Q))
  change ((s.sup (fun rank => PaperFullHistoryComplete.rankCost rank (radius (k+1)) (xi k)):ℕ):ℝ)≤_
  rw [heq]
  nlinarith

end
end PaperFullHistoryRates

end SnapshotModule_051
/- END full_history_inner_rate -/

/- BEGIN full_history_outer_rate -/
section SnapshotModule_052

namespace PaperFullHistoryRates
open PaperGDE PaperFullHistory PaperAdaNGD
noncomputable section
set_option maxHeartbeats 2000000

lemma outer_delta_comparison (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) :
    angularTolerance (128*Q)≤delta k := by
  have hp : 0<Q := by linarith
  have hb := small_iteration_bounds Q hQ k hk
  have hs : Real.sqrt (2*(128*Q))=16*Real.sqrt Q := by
    rw [show 2*(128*Q)=(16:ℝ)^2*Q by ring,Real.sqrt_mul (by norm_num),Real.sqrt_sq (by norm_num)]
  rw [angularTolerance,delta,hs]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Real.sqrt_nonneg Q]

lemma outer_direction_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) :
    (directionCost n (delta k):ℝ)≤1000000*(n+1:ℝ)*Real.log ((n+1:ℝ)*Q) := by
  have hp : 0<Q := by linarith
  have hsmall : 0<angularTolerance (128*Q) := by unfold angularTolerance; positivity
  have hn : 0<(n+1:ℝ) := by positivity
  have hmono := direction_cost_antitone n hsmall (outer_delta_comparison Q hQ k hk)
  have hcast : (directionCost n (delta k):ℝ)≤(directionCost n (angularTolerance (128*Q)):ℝ) := by exact_mod_cast hmono
  have hc := PaperRates.directionCost_uniform n (128*Q) (by linarith)
  have hL := PaperRates.dimension_log_lower n Q hQ
  have hlog : Real.log ((n+1:ℝ)*(128*Q))≤130*Real.log ((n+1:ℝ)*Q) := by
    rw [show (n+1:ℝ)*(128*Q)=128*((n+1:ℝ)*Q) by ring,
      Real.log_mul (by norm_num : (128:ℝ)≠0) (mul_ne_zero hn.ne' hp.ne')]
    have h128 : Real.log (128:ℝ)≤128 := Real.log_le_self (by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (show 0≤1003*(n+1:ℝ) by positivity)
  have hbase : 0≤(n+1:ℝ)*Real.log ((n+1:ℝ)*Q) := by positivity
  nlinarith

lemma line_ratio_le_inner_volume (k : ℕ) : (radius k+2)/(xi k)≤ innerVolumeArg k := by
  have hxi := xi_pos k
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have heq : innerVolumeArg k=32*((k:ℝ)+5)*((k:ℝ)+6)^2/(xi k) := by
    unfold innerVolumeArg
    field_simp
    <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hxi.le
  unfold radius
  have hh : (1:ℝ)≤32*((k:ℝ)+5)*((k:ℝ)+6) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hh (show 0≤(k:ℝ)+6 by positivity)
  nlinarith

lemma outer_line_bound (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) :
    (PaperLineSearchComplete.horizon (radius k+2) (xi k):ℝ)≤1000*Real.log Q := by
  have hxi := xi_pos k
  have hxile := xi_le_nu k
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hD : xi k≤radius k+2 := by unfold nu radius at *; linarith
  have hratio : 1≤(radius k+2)/(xi k) := (one_le_div hxi).mpr hD
  have hratio0 : 0<(radius k+2)/(xi k) := by linarith
  have hlog0 : 0≤Real.log ((radius k+2)/(xi k)) := Real.log_nonneg hratio
  have hbase : (1/3:ℝ)≤Real.log (3/2:ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2)
    norm_num at hh
    exact hh
  have hbasepos : 0<Real.log (3/2:ℝ) := by linarith
  have hlog := (Real.log_le_log hratio0 (line_ratio_le_inner_volume k)).trans
    (inner_volume_log_bound Q hQ k hk)
  have hL := PaperCentroidRates.logQ_lower Q hQ
  have hc := Nat.ceil_lt_add_one (show 0≤Real.log ((radius k+2)/(xi k))/Real.log (3/2:ℝ) by positivity)
  change (PaperLineSearchComplete.horizon (radius k+2) (xi k):ℝ)<
    Real.log ((radius k+2)/(xi k))/Real.log (3/2:ℝ)+1 at hc
  have hdiv : Real.log ((radius k+2)/(xi k))/Real.log (3/2:ℝ)≤618*Real.log Q := by
    apply (div_le_iff₀ hbasepos).mpr
    have hm := mul_le_mul_of_nonneg_left hbase (show 0≤618*Real.log Q by positivity)
    nlinarith
  linarith

lemma step_budget_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (k : ℕ)
    (hk : k < PaperFullHistoryProgram.iterationCount Q) :
    (PaperFullHistoryProgram.stepBudget n (PaperFullHistoryComplete.innerCap n) k:ℝ)≤
      1000000*(n+1:ℝ)*Real.log ((n+1:ℝ)*Q)+
      2*(10:ℝ)^12*((PaperFullHistoryProgram.iterationCount Q:ℝ)+1)^2*(Real.log Q)^2 := by
  have hG := outer_direction_bound n Q hQ k hk
  have hI := public_inner_cap_bound n Q hQ k hk
  have hline := outer_line_bound Q hQ k hk
  have hL := PaperCentroidRates.logQ_lower Q hQ
  have hN : (1:ℝ)≤(PaperFullHistoryProgram.iterationCount Q:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) (PaperFullHistoryProgram.iterationCount Q)]
  have hN2 : (1:ℝ)≤((PaperFullHistoryProgram.iterationCount Q:ℝ)+1)^2 := by nlinarith
  have hL2 : Real.log Q≤(Real.log Q)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hN2 (sq_nonneg (Real.log Q))
  have heq : (PaperFullHistoryProgram.stepBudget n (PaperFullHistoryComplete.innerCap n) k:ℝ)=
      (directionCost n (delta k):ℝ)+(PaperFullHistoryComplete.innerCap n k:ℝ)+
      (PaperLineSearchComplete.horizon (radius k+2) (xi k):ℝ)+2 := by
    simp only [PaperFullHistoryProgram.stepBudget,directionCost,Nat.cast_add,Nat.cast_ofNat]
  rw [heq]
  nlinarith

/-- One absolute numerical constant proves the full-history rate uniformly.
The cap is the actual public reply-tree cap of the implemented algorithm. -/
theorem fullhistory_cap_uniform (n : ℕ) (Q : ℝ) (hQ : 32≤Q) :
    (PaperFullHistoryComplete.cap n Q:ℝ)≤(10:ℝ)^16*
      ((n+1:ℝ)*Real.sqrt Q*Real.log ((n+1:ℝ)*Q)+Q*Real.sqrt Q*(Real.log Q)^2) := by
  let N := PaperFullHistoryProgram.iterationCount Q
  let L := Real.log Q
  let H := Real.log ((n+1:ℝ)*Q)
  have hp : 0<Q := by linarith
  have hL : 1≤L := PaperCentroidRates.logQ_lower Q hQ
  have hH : 1≤H := PaperRates.dimension_log_lower n Q hQ
  have hs := horizon_sqrt_bound Q hQ
  have hN : (N:ℝ)≤6*Real.sqrt Q := hs.1
  have hNp : (N:ℝ)+1≤7*Real.sqrt Q := by linarith [hs.2]
  have hsq := Real.sq_sqrt hp.le
  have hNp2 : ((N:ℝ)+1)^2≤49*Q := by
    have hh := pow_le_pow_left₀ (show 0≤(N:ℝ)+1 by positivity) hNp 2
    nlinarith
  have hsum : (PaperFullHistoryComplete.cap n Q:ℝ)≤(N:ℝ)*
      (1000000*(n+1:ℝ)*H+2*(10:ℝ)^12*((N:ℝ)+1)^2*L^2) := by
    unfold PaperFullHistoryComplete.cap
    push_cast
    calc
      _ ≤ ∑ _k ∈ Finset.range N,
          (1000000*(n+1:ℝ)*H+2*(10:ℝ)^12*((N:ℝ)+1)^2*L^2) :=
        Finset.sum_le_sum (fun k hk => step_budget_bound n Q hQ k (Finset.mem_range.mp hk))
      _ = _ := by simp; ring
  have hC : 1000000*(n+1:ℝ)*H+2*(10:ℝ)^12*((N:ℝ)+1)^2*L^2 ≤
      1000000*(n+1:ℝ)*H+98*(10:ℝ)^12*Q*L^2 := by
    have hm := mul_le_mul_of_nonneg_right hNp2 (show 0≤2*(10:ℝ)^12*L^2 by positivity)
    nlinarith
  have hm := mul_le_mul hN hC (show 0≤1000000*(n+1:ℝ)*H+
    2*(10:ℝ)^12*((N:ℝ)+1)^2*L^2 by positivity) (by positivity)
  have hpos1 : 0≤(n+1:ℝ)*Real.sqrt Q*H := by positivity
  have hpos2 : 0≤Q*Real.sqrt Q*L^2 := by positivity
  change (PaperFullHistoryComplete.cap n Q:ℝ)≤(10:ℝ)^16*((n+1:ℝ)*Real.sqrt Q*H+Q*Real.sqrt Q*L^2)
  nlinarith

end
end PaperFullHistoryRates

end SnapshotModule_052
/- END full_history_outer_rate -/

/- BEGIN adangd_public_cap -/
section SnapshotModule_053

namespace PaperAdaNGD
open PaperGDE
noncomputable section

lemma adangdProgram_public_height {n : ℕ} (delta gamma : ℝ) (T : ℕ) :
    Program.height (adangdProgram (d := n) delta gamma T)≤T*(directionCost n delta+1) := by
  induction T with
  | zero => simp [adangdProgram,Program.height]
  | succ T ih =>
    unfold adangdProgram
    apply (Program.height_bind_le _ _ (T*(directionCost n delta+1)) (directionCost n delta+1) ih ?_).trans_eq
      (by ring)
    intro state
    apply Program.height_bind_le _ _ (directionCost n delta) 1 (gdeProgram_public_height _ _ _)
    intro v
    simp [Program.height]

lemma adangdOutput_public_height {n : ℕ} (delta gamma : ℝ) (T : ℕ) :
    Program.height (adangdOutput (d := n) delta gamma T)≤T*(directionCost n delta+1) := by
  have h := Program.height_bind_le (adangdProgram delta gamma T) (fun s => Program.pure s.2)
    (T*(directionCost n delta+1)) 0 (adangdProgram_public_height delta gamma T) (by intro s; rfl)
  simpa [adangdOutput] using h

lemma originalAdangd_public_height {n : ℕ} (R Q : ℝ) :
    Program.height (originalAdangd (d := n) R Q)≤
      iterationCount Q*(directionCost n (angularTolerance Q)+1) :=
  (Program.height_scaleProgram R _).trans (adangdOutput_public_height _ _ _)

end
end PaperAdaNGD

end SnapshotModule_053
/- END adangd_public_cap -/

/- BEGIN optimization_model -/
section SnapshotModule_054

namespace PaperOptimizationModel
open Set MeasureTheory PaperGDE PaperTrinary
open scoped ENNReal
noncomputable section

def admissible (n : ℕ) (beta : NNReal) (R : ℝ) : Set (Vec n → ℝ) :=
  {f | ∃ grad : Vec n → Vec n, (∀ x, HasGradientAt f (grad x) x) ∧
    ConvexOn ℝ univ f ∧ LipschitzWith beta grad ∧
      ∃ a : Vec n, ‖a‖≤R ∧ ∀ y, f a≤f y}

def minimum {V : Type*} (f : V → ℝ) : ℝ := sInf (Set.range f)
def success {V : Type*} (epsilon : ℝ) (f : V → ℝ) (x : V) : Prop := f x-minimum f≤epsilon

lemma attained_minimum {V : Type*} (f : V → ℝ) (a : V) (hmin : ∀ y, f a≤f y) :
    minimum f=f a := by
  exact IsLeast.csInf_eq ⟨⟨a,rfl⟩,by rintro b ⟨y,rfl⟩; exact hmin y⟩

lemma comparison_measurable {V : Type*} [MeasurableSpace V] (f : V → ℝ) (hf : Measurable f) :
    Measurable (PaperOracle.comparisonOracle f) := by
  unfold PaperOracle.comparisonOracle PaperOracle.realOrder
  exact Measurable.ite (measurableSet_lt (hf.comp measurable_fst) (hf.comp measurable_snd))
    measurable_const (Measurable.ite
      (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd)) measurable_const measurable_const)

def centroidProgram {n : ℕ} (R Q : ℝ) : PaperTrinary.Program n (Vec n) :=
  liftGDE (PaperCentroidComplete.originalProgram R Q)

def adangdProgram {n : ℕ} (R Q : ℝ) : PaperTrinary.Program n (Vec n) :=
  liftGDE (PaperAdaNGD.originalAdangd R Q)

/-- A uniform original-scale witness, fixed before f is chosen. -/
theorem centroid_uniform_budget (n : ℕ) (beta : NNReal) (hb : 0<beta)
    (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon) (hQ : 32≤Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    PaperUniformBudget.DeterministicBudget (admissible n beta R) (success epsilon)
      (PaperCentroidComplete.cap n (1/Q)) := by
  refine ⟨centroidProgram R Q,?_,?_⟩
  · exact PaperOracle.Program.cap_mono _ (liftGDE_cap _) (PaperCentroidComplete.original_height R Q)
  · intro f hf
    obtain ⟨grad,hg,hc,hLip,a,ha,hmin⟩ := hf
    rw [success,attained_minimum f a hmin,centroidProgram,liftGDE_run]
    exact (PaperCentroidComplete.original_centroid_complete _ f grad hg hc beta hb hLip a R epsilon Q
      hR heps hmin ha hQ hQdef (PaperTrinary.comparison_correct f)).1

theorem fullhistory_uniform_budget (n : ℕ) (beta : NNReal) (hb : 0<beta)
    (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon) (hQ : 32≤Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    PaperUniformBudget.DeterministicBudget (admissible n beta R) (success epsilon)
      (PaperFullHistoryComplete.cap n Q) := by
  refine ⟨PaperFullHistoryComplete.originalProgram R Q,PaperFullHistoryComplete.original_public_cap n R Q,?_⟩
  intro f hf
  obtain ⟨grad,hg,hc,hLip,a,ha,hmin⟩ := hf
  rw [success,attained_minimum f a hmin]
  exact (PaperFullHistoryComplete.original_fullhistory_complete f grad hg hc beta hb hLip a R epsilon Q
    hR heps hmin ha (by linarith) hQdef).1

theorem adangd_uniform_budget (n : ℕ) (beta : NNReal) (hb : 0<beta)
    (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon) (hQ : 32≤Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    PaperUniformBudget.DeterministicBudget (admissible n beta R) (success epsilon)
      (PaperAdaNGD.iterationCount Q*(PaperAdaNGD.directionCost n (PaperAdaNGD.angularTolerance Q)+1)) := by
  refine ⟨adangdProgram R Q,?_,?_⟩
  · exact PaperOracle.Program.cap_mono _ (liftGDE_cap _) (PaperAdaNGD.originalAdangd_public_height R Q)
  · intro f hf
    obtain ⟨grad,hg,hc,hLip,a,ha,hmin⟩ := hf
    rw [success,attained_minimum f a hmin,adangdProgram,liftGDE_run]
    exact (PaperAdaNGD.original_adangd_complete f grad hg hc beta hb hLip a R epsilon Q
      hR heps ha hmin hQ hQdef _ (PaperTrinary.comparison_correct f)).1

/-- The paper's deterministic inclusion holds for the full admissible class and
actual total Borel policies, since a concrete uniform witness exists. -/
theorem randomized_complexity_le_deterministic (n : ℕ) (beta : NNReal) (hb : 0<beta)
    (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon) (hQ : 32≤Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    PaperUniformBudget.randomizedComplexity (admissible n beta R) (success epsilon)≤
      PaperUniformBudget.deterministicComplexity (admissible n beta R) (success epsilon) := by
  apply PaperUniformBudget.randomized_le_deterministic
  exact ⟨_,centroid_uniform_budget n beta hb R epsilon Q hR heps hQ hQdef⟩

end
end PaperOptimizationModel

end SnapshotModule_054
/- END optimization_model -/

/- BEGIN joint_upper_envelope -/
section SnapshotModule_055

namespace PaperJointUpper
open PaperGDE PaperOptimizationModel
noncomputable section
set_option maxHeartbeats 1000000

def logEnvelope (n : ℕ) (Q : ℝ) : ℝ := 2+Real.log (n+1:ℝ)+Real.log Q

lemma logEnvelope_source (n : ℕ) (Q : ℝ) (hQ : 0<Q) :
    logEnvelope n Q=Real.log (Real.exp 1*(n+1:ℝ))+Real.log (Real.exp 1*Q) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity : (n+1:ℝ)≠0),
    Real.log_mul (Real.exp_pos 1).ne' hQ.ne',Real.log_exp]
  unfold logEnvelope
  ring

lemma logEnvelope_ge_one (n : ℕ) (Q : ℝ) (hQ : 32≤Q) : 1≤logEnvelope n Q := by
  have hL := PaperCentroidRates.logQ_lower Q hQ
  have hn : 0≤Real.log (n+1:ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  unfold logEnvelope
  linarith

lemma logQ_le_envelope (n : ℕ) (Q : ℝ) : Real.log Q≤logEnvelope n Q := by
  have hn : 0≤Real.log (n+1:ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  unfold logEnvelope
  linarith

lemma logdQ_le_envelope (n : ℕ) (Q : ℝ) (hQ : 0<Q) :
    Real.log ((n+1:ℝ)*Q)≤logEnvelope n Q := by
  rw [Real.log_mul (by positivity : (n+1:ℝ)≠0) hQ.ne']
  unfold logEnvelope
  linarith

lemma logdroot_le_envelope (n : ℕ) (Q : ℝ) (hQ : 32≤Q) :
    Real.log ((n+1:ℝ)*Real.sqrt Q)≤logEnvelope n Q := by
  have hp : 0<Q := by linarith
  rw [Real.log_mul (by positivity : (n+1:ℝ)≠0) (Real.sqrt_pos.mpr hp).ne',Real.log_sqrt hp.le]
  have hL := PaperCentroidRates.logQ_lower Q hQ
  unfold logEnvelope
  linarith

lemma fullhistory_log_envelope (n : ℕ) (Q : ℝ) (hQ : 32≤Q) :
    (PaperFullHistoryComplete.cap n Q:ℝ)≤(10:ℝ)^16*
      ((n+1:ℝ)*Real.sqrt Q+Q*Real.sqrt Q)*(logEnvelope n Q)^2 := by
  have hp : 0<Q := by linarith
  have hL := logEnvelope_ge_one n Q hQ
  have hQlog := PaperCentroidRates.logQ_lower Q hQ
  have hDQlog := PaperRates.dimension_log_lower n Q hQ
  have hL2 : logEnvelope n Q≤(logEnvelope n Q)^2 := by nlinarith
  have h1 := (logdQ_le_envelope n Q hp).trans hL2
  have h2 := (sq_le_sq₀ (show 0≤Real.log Q by linarith) (show 0≤logEnvelope n Q by linarith)).mpr
    (logQ_le_envelope n Q)
  have hm1 := mul_le_mul_of_nonneg_left h1 (show 0≤(n+1:ℝ)*Real.sqrt Q by positivity)
  have hm2 := mul_le_mul_of_nonneg_left h2 (show 0≤Q*Real.sqrt Q by positivity)
  have h := PaperFullHistoryRates.fullhistory_cap_uniform n Q hQ
  nlinarith

lemma low_cap_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (hwindow : Q≤(n+1:ℝ)) :
    (PaperFullHistoryComplete.cap n Q:ℝ)≤(10:ℝ)^18*(n+1:ℝ)*Real.sqrt Q*(logEnvelope n Q)^3 := by
  have h := fullhistory_log_envelope n Q hQ
  have hL := logEnvelope_ge_one n Q hQ
  have hdom := mul_le_mul_of_nonneg_right hwindow (Real.sqrt_nonneg Q)
  have h1 := mul_le_mul_of_nonneg_right hdom (sq_nonneg (logEnvelope n Q))
  have h2 := mul_nonneg (show 0≤(n+1:ℝ)*Real.sqrt Q by positivity)
    (mul_nonneg (show 0≤logEnvelope n Q-1 by linarith) (sq_nonneg (logEnvelope n Q)))
  have hpos : 0≤(n+1:ℝ)*Real.sqrt Q*(logEnvelope n Q)^3 := by positivity
  nlinarith

lemma middle_full_cap_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (hwindow : (n+1:ℝ)≤Q) :
    (PaperFullHistoryComplete.cap n Q:ℝ)≤(10:ℝ)^18*Q*Real.sqrt Q*(logEnvelope n Q)^3 := by
  have h := fullhistory_log_envelope n Q hQ
  have hp : 0<Q := by linarith
  have hL := logEnvelope_ge_one n Q hQ
  have hdom := mul_le_mul_of_nonneg_right hwindow (Real.sqrt_nonneg Q)
  have h1 := mul_le_mul_of_nonneg_right hdom (sq_nonneg (logEnvelope n Q))
  have h2 := mul_nonneg (show 0≤Q*Real.sqrt Q by positivity)
    (mul_nonneg (show 0≤logEnvelope n Q-1 by linarith) (sq_nonneg (logEnvelope n Q)))
  have hpos : 0≤Q*Real.sqrt Q*(logEnvelope n Q)^3 := by positivity
  nlinarith

lemma centroid_log_envelope (n : ℕ) (Q : ℝ) (hQ : 32≤Q) :
    (PaperCentroidComplete.cap n (1/Q):ℝ)≤(10:ℝ)^18*(n+1:ℝ)^2*(logEnvelope n Q)^3 := by
  have hL := logEnvelope_ge_one n Q hQ
  have hQlog := PaperCentroidRates.logQ_lower Q hQ
  have hdlog : 0≤Real.log ((n+1:ℝ)*Real.sqrt Q) := by
    have h := PaperCentroidRates.centroid_direction_bound n Q hQ
    have hmul : 0≤10000*(n+1:ℝ)*Real.log ((n+1:ℝ)*Real.sqrt Q) :=
      (Nat.cast_nonneg _).trans h
    have hn : 0<(n+1:ℝ) := by positivity
    nlinarith
  have hm := mul_le_mul (logQ_le_envelope n Q) (logdroot_le_envelope n Q hQ) hdlog (by linarith)
  have hm2 := mul_le_mul_of_nonneg_left hm (show 0≤(n+1:ℝ)^2 by positivity)
  have h3 := mul_nonneg (sq_nonneg (n+1:ℝ))
    (mul_nonneg (show 0≤logEnvelope n Q-1 by linarith) (sq_nonneg (logEnvelope n Q)))
  have hpos : 0≤(n+1:ℝ)^2*(logEnvelope n Q)^3 := by positivity
  have h := PaperCentroidRates.centroid_cap_uniform n Q hQ
  nlinarith

lemma middle_cap_bound (n : ℕ) (Q : ℝ) (hQ : 32≤Q) (hwindow : (n+1:ℝ)≤Q) :
    ((min (PaperFullHistoryComplete.cap n Q) (PaperCentroidComplete.cap n (1/Q)):ℕ):ℝ)≤
      (10:ℝ)^18*min (Q*Real.sqrt Q) ((n+1:ℝ)^2)*(logEnvelope n Q)^3 := by
  have hF := middle_full_cap_bound n Q hQ hwindow
  have hC := centroid_log_envelope n Q hQ
  have hminF : ((min (PaperFullHistoryComplete.cap n Q) (PaperCentroidComplete.cap n (1/Q)):ℕ):ℝ)≤
      (PaperFullHistoryComplete.cap n Q:ℝ) := by exact_mod_cast min_le_left _ _
  have hminC : ((min (PaperFullHistoryComplete.cap n Q) (PaperCentroidComplete.cap n (1/Q)):ℕ):ℝ)≤
      (PaperCentroidComplete.cap n (1/Q):ℝ) := by exact_mod_cast min_le_right _ _
  rcases le_total (Q*Real.sqrt Q) ((n+1:ℝ)^2) with h | h
  · rw [min_eq_left h]
    simpa only [mul_assoc] using hminF.trans hF
  · rw [min_eq_right h]
    exact hminC.trans hC

def jointCap (n : ℕ) (Q : ℝ) : ℕ := by
  classical
  exact if Q≤(n+1:ℝ) then PaperFullHistoryComplete.cap n Q else
    if Q≤(n+1:ℝ)^2 then min (PaperFullHistoryComplete.cap n Q) (PaperCentroidComplete.cap n (1/Q)) else
      PaperCentroidComplete.cap n (1/Q)

def upperProfile (n : ℕ) (Q : ℝ) : ℝ := by
  classical
  exact if Q≤(n+1:ℝ) then (10:ℝ)^18*(n+1:ℝ)*Real.sqrt Q*(logEnvelope n Q)^3 else
    if Q≤(n+1:ℝ)^2 then (10:ℝ)^18*min (Q*Real.sqrt Q) ((n+1:ℝ)^2)*(logEnvelope n Q)^3 else
      100000000*(n+1:ℝ)^2*Real.log Q*Real.log ((n+1:ℝ)*Real.sqrt Q)

lemma joint_cap_rate (n : ℕ) (Q : ℝ) (hQ : 32≤Q) : (jointCap n Q:ℝ)≤upperProfile n Q := by
  classical
  unfold jointCap upperProfile
  split_ifs with hlo hmid
  · exact low_cap_bound n Q hQ hlo
  · exact middle_cap_bound n Q hQ (le_of_not_ge hlo)
  · exact PaperCentroidRates.centroid_cap_uniform n Q hQ

/-- The complete piecewise deterministic upper witness on the manuscript class.
The selection depends only on public caps and parameters, before choosing f. -/
theorem piecewise_uniform_upper (n : ℕ) (beta : NNReal) (hb : 0<beta)
    (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon) (hQ : 32≤Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    PaperUniformBudget.DeterministicBudget (admissible n beta R) (success epsilon) (jointCap n Q) ∧
      (jointCap n Q:ℝ)≤upperProfile n Q := by
  refine ⟨?_,joint_cap_rate n Q hQ⟩
  classical
  unfold jointCap
  split_ifs
  · exact fullhistory_uniform_budget n beta hb R epsilon Q hR heps hQ hQdef
  · exact PaperUniformBudget.select_smaller_public_cap _ _ _ _
      (fullhistory_uniform_budget n beta hb R epsilon Q hR heps hQ hQdef)
      (centroid_uniform_budget n beta hb R epsilon Q hR heps hQ hQdef)
  · exact centroid_uniform_budget n beta hb R epsilon Q hR heps hQ hQdef

end
end PaperJointUpper

end SnapshotModule_055
/- END joint_upper_envelope -/

/- BEGIN probability_one_upper -/
section SnapshotModule_056

namespace PaperUniformBudget
open Set MeasureTheory PaperOracle PaperBorelPolicy
noncomputable section
variable {V : Type} [MeasurableSpace V] [Inhabited V]

/-- A deterministic uniform witness has an objective-independent unit seed,
a total Borel policy, the same public cap, and exact probability one. -/
theorem deterministic_probability_one_policy (objectives : Set (V → ℝ))
    (success : (V → ℝ) → V → Prop) (T : ℕ) (hT : DeterministicBudget objectives success T) :
    ∃ P : Policy Unit (V×V) Ordering V,
      (∀ seed, Program.Cap T (P.fromSeed T seed)) ∧
      ∀ f ∈ objectives,
        MeasurableSet {seed : Unit | success f (Program.run (comparisonOracle f) (P.fromSeed T seed))} ∧
        Measure.dirac () {seed : Unit | success f (Program.run (comparisonOracle f) (P.fromSeed T seed))}=1 := by
  obtain ⟨p,hcap,hgood⟩ := hT
  refine ⟨PaperProgramBorel.policy p,(fun seed => (PaperProgramBorel.policy p).fromSeed_cap T seed),?_⟩
  intro f hf
  have heq := PaperProgramBorel.finite_program_borel_realization p T hcap
  have hs : ∀ seed : Unit, success f (Program.run (comparisonOracle f)
      ((PaperProgramBorel.policy p).fromSeed T seed)) := by
    intro seed
    cases seed
    rw [heq]
    exact hgood f hf
  have hset : {seed : Unit | success f (Program.run (comparisonOracle f)
      ((PaperProgramBorel.policy p).fromSeed T seed))}=univ := Set.eq_univ_of_forall hs
  rw [hset]
  exact ⟨MeasurableSet.univ,by simp⟩

end
end PaperUniformBudget

namespace PaperJointUpper
open Set MeasureTheory PaperGDE PaperOracle PaperBorelPolicy PaperOptimizationModel
noncomputable section

/-- The same piecewise public budgets give the paper's probability-one
randomized upper witness, with every seed/history operation Borel. -/
theorem piecewise_probability_one (n : ℕ) (beta : NNReal) (hb : 0<beta)
    (R epsilon Q : ℝ) (hR : 0<R) (heps : 0<epsilon) (hQ : 32≤Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    ∃ P : Policy Unit (Vec n×Vec n) Ordering (Vec n),
      (∀ seed, Program.Cap (jointCap n Q) (P.fromSeed (jointCap n Q) seed)) ∧
      (∀ f ∈ admissible n beta R,
        Measure.dirac () {seed : Unit | success epsilon f
          (Program.run (comparisonOracle f) (P.fromSeed (jointCap n Q) seed))}=1) ∧
      (jointCap n Q:ℝ)≤upperProfile n Q := by
  have h := piecewise_uniform_upper n beta hb R epsilon Q hR heps hQ hQdef
  obtain ⟨P,hcap,hprob⟩ := PaperUniformBudget.deterministic_probability_one_policy _ _ _ h.1
  exact ⟨P,hcap,(fun f hf => (hprob f hf).2),h.2⟩

end
end PaperJointUpper

end SnapshotModule_056
/- END probability_one_upper -/

/- BEGIN joint_ratio_algebra -/
section SnapshotModule_057

namespace PaperJointRatios
noncomputable section

def residual (d Q : ℝ) : ℝ := min (Q/d) (d/Real.sqrt Q)

lemma residual_ratio_identity (d Q : ℝ) (hd : 0<d) (hQ : 0<Q) :
    min (Q*Real.sqrt Q) (d^2)/(d*Real.sqrt Q)=residual d Q := by
  have hs : 0<Real.sqrt Q := Real.sqrt_pos.mpr hQ
  rw [← min_div_div_right (mul_pos hd hs).le]
  unfold residual
  congr 1 <;> field_simp <;> ring

lemma residual_left (d Q r : ℝ) (hd : 0<d) (hQ : 0≤Q) (hr : 0<r)
    (hcube : r^3=d) (hcross : Q≤r^4) : residual d Q=Q/d := by
  have hs := Real.sq_sqrt hQ
  have hs0 := Real.sqrt_nonneg Q
  have hroot : Real.sqrt Q≤r^2 := by nlinarith [sq_nonneg (Real.sqrt Q-r^2)]
  have hprod := mul_le_mul hcross hroot hs0 (pow_nonneg hr.le 4)
  have hcube2 : r^4*r^2=d^2 := by rw [← hcube]; ring
  rw [hcube2] at hprod
  unfold residual
  by_cases hz : Q=0
  · simp [hz,hd.ne']
  · have hspos : 0<Real.sqrt Q := Real.sqrt_pos.mpr (lt_of_le_of_ne hQ (Ne.symm hz))
    apply min_eq_left
    apply (div_le_div_iff₀ hd hspos).mpr
    nlinarith

lemma residual_right (d Q r : ℝ) (hd : 0<d) (hQ : 0≤Q) (hr : 0<r)
    (hcube : r^3=d) (hcross : r^4≤Q) : residual d Q=d/Real.sqrt Q := by
  have hs := Real.sq_sqrt hQ
  have hs0 := Real.sqrt_nonneg Q
  have hroot : r^2≤Real.sqrt Q := by nlinarith [sq_nonneg (Real.sqrt Q-r^2)]
  have hQpos : 0<Q := (pow_pos hr 4).trans_le hcross
  have hspos : 0<Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hprod := mul_le_mul hcross hroot (sq_nonneg r) hQ
  have hcube2 : r^4*r^2=d^2 := by rw [← hcube]; ring
  rw [hcube2] at hprod
  unfold residual
  apply min_eq_right
  apply (div_le_div_iff₀ hspos hd).mpr
  nlinarith

lemma real_cube_root_spec (d : ℝ) (hd : 0<d) :
    0<d^(1/3:ℝ) ∧ (d^(1/3:ℝ))^3=d := by
  refine ⟨Real.rpow_pos_of_pos hd _,?_⟩
  calc
    (d^(1/3:ℝ))^3=(d^(1/3:ℝ))^(3:ℝ) := (Real.rpow_natCast _ 3).symm
    _=d^((1/3:ℝ)*3) := (Real.rpow_mul hd.le (1/3:ℝ) 3).symm
    _=d := by norm_num

lemma cube_root_fourth (d : ℝ) (hd : 0<d) : (d^(1/3:ℝ))^4=d^(4/3:ℝ) := by
  calc
    (d^(1/3:ℝ))^4=(d^(1/3:ℝ))^(4:ℝ) := (Real.rpow_natCast _ 4).symm
    _=d^((1/3:ℝ)*4) := (Real.rpow_mul hd.le (1/3:ℝ) 4).symm
    _=d^(4/3:ℝ) := by norm_num

/-- The manuscript's worst middle-window polynomial loss is at most d^(1/3). -/
theorem residual_worst_factor (d Q : ℝ) (hd : 0<d) (hQ : 0≤Q) :
    residual d Q≤d^(1/3:ℝ) :=
  middle_residual_cubic_bound d Q _ hd hQ (real_cube_root_spec d hd).1 (real_cube_root_spec d hd).2

lemma residual_at_crossover (d : ℝ) (hd : 0<d) : residual d (d^(4/3:ℝ))=d^(1/3:ℝ) := by
  have hr := real_cube_root_spec d hd
  have h4 := cube_root_fourth d hd
  have hQ : 0≤d^(4/3:ℝ) := (Real.rpow_pos_of_pos hd _).le
  rw [residual_left d (d^(4/3:ℝ)) (d^(1/3:ℝ)) hd hQ hr.1 hr.2 h4.ge]
  apply (div_eq_iff hd.ne').mpr
  calc
    d^(4/3:ℝ)=(d^(1/3:ℝ))^4 := h4.symm
    _=d^(1/3:ℝ)*(d^(1/3:ℝ))^3 := by ring
    _=d^(1/3:ℝ)*d := by rw [hr.2]

lemma residual_at_upper_endpoint (d : ℝ) (hd : 1≤d) : residual d (d^2)=1 := by
  have hp : 0<d := by linarith
  unfold residual
  rw [Real.sqrt_sq hp.le,div_self hp.ne']
  have hdiv : d^2/d=d := by field_simp
  rw [hdiv,min_eq_right hd]

/-- Divide any certified middle upper envelope by any applicable certified lower
bound; the lower-bound theorem itself remains a separate explicit dependency. -/
theorem middle_ratio_bound (d Q U L C Lambda : ℝ) (hd : 0<d) (hQ : 0<Q)
    (hC : 0≤C) (hLambda : 0≤Lambda)
    (hLower : d*Real.sqrt Q/8192≤L)
    (hUpper : U≤C*min (Q*Real.sqrt Q) (d^2)*Lambda^3) :
    U/L≤8192*C*residual d Q*Lambda^3 := by
  have hs : 0<Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hL : 0<L := (div_pos (mul_pos hd hs) (by norm_num)).trans_le hLower
  have hmin : 0 ≤ min (Q*Real.sqrt Q) (d^2) := le_min (by positivity) (sq_nonneg d)
  have hright : 0≤C*min (Q*Real.sqrt Q) (d^2)*Lambda^3 := by positivity
  have hden : U/L≤(C*min (Q*Real.sqrt Q) (d^2)*Lambda^3)/(d*Real.sqrt Q/8192) :=
    (div_le_div_of_nonneg_right hUpper hL.le).trans
      (div_le_div_of_nonneg_left hright (by positivity) hLower)
  have heq : (C*min (Q*Real.sqrt Q) (d^2)*Lambda^3)/(d*Real.sqrt Q/8192)=
      8192*C*(min (Q*Real.sqrt Q) (d^2)/(d*Real.sqrt Q))*Lambda^3 := by field_simp
  rw [heq,residual_ratio_identity d Q hd hQ] at hden
  exact hden

end
end PaperJointRatios

end SnapshotModule_057
/- END joint_ratio_algebra -/

/- BEGIN lower_bound_contracts -/
section SnapshotModule_058

/- Explicit external assumptions for the manuscript's two cited exact-value
   lower bounds. These structures are contracts, not axioms or proved Dorn theorems. -/
namespace PaperLowerBounds
noncomputable section
open Set MeasureTheory PaperBorelPolicy PaperOptimizationModel
open scoped ENNReal

def ValueBudget {V : Type} [MeasurableSpace V]
    (objectives : Set (V → ℝ)) (success : (V → ℝ) → V → Prop) (T : ℕ) : Prop :=
  ∃ Seed : Type, ∃ m : MeasurableSpace Seed, letI := m
    ∃ _ : StandardBorelSpace Seed, ∃ law : Measure Seed, IsProbabilityMeasure law ∧
      ∃ policy : Policy Seed V ℝ V,
        ∀ f ∈ objectives,
          MeasurableSet {s | success f (PaperOracle.Program.run f (policy.fromSeed T s))} ∧
          (2/3:ℝ≥0∞) ≤ law {s | success f (PaperOracle.Program.run f (policy.fromSeed T s))}

theorem valueBudget_restrict {V : Type} [MeasurableSpace V]
    {objectives contained : Set (V → ℝ)} {success : (V → ℝ) → V → Prop} {T : ℕ}
    (hsub : contained ⊆ objectives) (h : ValueBudget objectives success T) :
    ValueBudget contained success T := by
  rcases h with ⟨Seed, m, h⟩
  letI := m
  rcases h with ⟨hstandard, law, hprob, policy, hgood⟩
  exact ⟨Seed, m, hstandard, law, hprob, policy, fun f hf => hgood f (hsub hf)⟩

theorem admissible_continuous (n : ℕ) (beta : NNReal) (R : ℝ)
    (f : PaperGDE.Vec n → ℝ) (hf : f ∈ admissible n beta R) : Continuous f := by
  obtain ⟨grad, hg, hc, hLip, a, ha, hmin⟩ := hf
  exact continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)

theorem admissible_success_set_measurable (n : ℕ) (beta : NNReal) (R epsilon : ℝ)
    (f : PaperGDE.Vec n → ℝ) (hf : f ∈ admissible n beta R) :
    MeasurableSet {x | success epsilon f x} := by
  change MeasurableSet {x | f x - minimum f ≤ epsilon}
  exact measurableSet_le ((admissible_continuous n beta R f hf).measurable.sub measurable_const)
    measurable_const

/-- The source's globally strongly convex smooth localization class, with the
same ambient space, gradient, Lipschitz constant, and localized global minimum. -/
def strongLocalization (n : ℕ) (beta : NNReal) (mu R : ℝ) : Set (PaperGDE.Vec n → ℝ) :=
  {f | ∃ grad : PaperGDE.Vec n → PaperGDE.Vec n,
    (∀ x, HasGradientAt f (grad x) x) ∧ StrongConvexOn univ mu f ∧
      LipschitzWith beta grad ∧
        ∃ a : PaperGDE.Vec n, ‖a‖ ≤ R ∧ ∀ y, f a ≤ f y}

theorem strongLocalization_subset (n : ℕ) (beta : NNReal) (mu R : ℝ) (hmu : 0 ≤ mu) :
    strongLocalization n beta mu R ⊆ admissible n beta R := by
  intro f hf
  obtain ⟨grad, hg, hc, hLip, a, ha, hmin⟩ := hf
  refine ⟨grad, hg, ?_, hLip, a, ha, hmin⟩
  exact strongConvexOn_zero.mp (hc.mono hmu)

def valueDimensionLower (n : ℕ) (Q : ℝ) : ℝ :=
  max (5 * (n + 1 : ℝ) / 16)
    ((n + 1 : ℝ) / 4096 * min (n + 1 : ℝ) (Real.sqrt Q))

def comparisonLower (n : ℕ) (Q : ℝ) : ℝ :=
  max (5 * (n + 1 : ℝ) / 32)
    ((n + 1 : ℝ) / 8192 * min (n + 1 : ℝ) (Real.sqrt Q))

def comparisonLogLower (n : ℕ) (Q : ℝ) : ℝ :=
  (3 * (n + 1 : ℝ) / 8000) * (1 + Real.log Q / Real.log 3)

/-- External premise: Dorn et al., Theorem 2.1, stated on exactly the
manuscript's smooth convex localization class and total Borel value policies. -/
structure DornDimensionAccuracyPremise : Prop where
  lower_bound : ∀ (n : ℕ) (beta : NNReal), 0 < beta →
    ∀ (R epsilon : ℝ), 0 < R → 0 < epsilon → epsilon ≤ (beta : ℝ) * R ^ 2 / 32 →
      ∀ T : ℕ, ValueBudget (admissible n beta R) (success epsilon) T →
        valueDimensionLower n ((beta : ℝ) * R ^ 2 / epsilon) ≤ (T : ℝ)

/-- External premise: the lower half of Dorn et al., Theorem 2.5, restricted
to mu < beta. The manuscript uses only mu=beta/2, so no endpoint convention
at mu=beta is needed or claimed here. -/
structure DornLogarithmicPremise : Prop where
  lower_bound : ∀ (n : ℕ) (beta : NNReal), 0 < beta →
    ∀ (R epsilon mu : ℝ), 0 < R → 0 < epsilon →
      mu / (beta : ℝ) ∈ Icc (1 / 2 : ℝ) 1 → mu < (beta : ℝ) →
      epsilon ≤ (beta : ℝ) * R ^ 2 / (128 : ℝ) ^ 2 →
      ∀ T : ℕ, ValueBudget (strongLocalization n beta mu R) (success epsilon) T →
        (3 * (n + 1 : ℝ) / 4000) *
          (1 + Real.log ((beta : ℝ) * R ^ 2 / epsilon) /
            Real.log (((beta : ℝ) + mu) / ((beta : ℝ) - mu))) ≤ (T : ℝ)

theorem epsilon_le_scale_div (beta : NNReal) (R epsilon Q c : ℝ)
    (heps : 0 < epsilon) (hc : 0 < c) (hQ : c ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) :
    epsilon ≤ (beta : ℝ) * R ^ 2 / c := by
  have hscale : Q * epsilon = (beta : ℝ) * R ^ 2 := (eq_div_iff heps.ne').mp hQdef
  apply (le_div_iff₀ hc).mpr
  nlinarith

theorem half_strong_parameter (beta : NNReal) (hb : 0 < beta) :
    0 ≤ (beta : ℝ) / 2 ∧
      ((beta : ℝ) / 2) / (beta : ℝ) ∈ Icc (1 / 2 : ℝ) 1 ∧
      (beta : ℝ) / 2 < (beta : ℝ) ∧
      ((beta : ℝ) + (beta : ℝ) / 2) / ((beta : ℝ) - (beta : ℝ) / 2) = 3 := by
  have hbR : (0 : ℝ) < beta := hb
  have hratio : ((beta : ℝ) / 2) / (beta : ℝ) = 1 / 2 := by field_simp
  refine ⟨by positivity, ?_, by linarith, ?_⟩
  · rw [hratio]
    norm_num
  · field_simp
    <;> ring

end
end PaperLowerBounds

end SnapshotModule_058
/- END lower_bound_contracts -/

/- BEGIN cg_exact -/
section SnapshotModule_059

/- Exact conjugate-gradient realization by complete A-reorthogonalization.
   Only stored p and Ap vectors enter orthogonalization; one new matvec is used per step.
   Complete reorthogonalization is free arithmetic in the appendix's exact oracle model. -/
namespace PaperCGExact

open Set Submodule
open scoped RealInnerProductSpace

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def PositiveDefinite (A : Module.End ℝ V) : Prop :=
  ∀ x : V, x ≠ 0 → 0 < inner ℝ x (A x)

theorem energy_symmetry (A : Module.End ℝ V) (hA : A.IsSymmetric) (x y : V) :
    inner ℝ x (A y)=inner ℝ y (A x) := by
  rw [← hA x y, real_inner_comm]

noncomputable def orthogonalize {k : ℕ} (r : V) (p ap : Fin k → V) : V :=
  r-∑ i, (inner ℝ r (ap i)/inner ℝ (p i) (ap i)) • p i

theorem orthogonalize_zero {k : ℕ} (p ap : Fin k → V) : orthogonalize (0:V) p ap=0 := by
  simp [orthogonalize]

theorem orthogonalize_residual_inner {k : ℕ} (r : V) (p ap : Fin k → V)
    (horth : ∀ i, inner ℝ r (p i)=0) : inner ℝ r (orthogonalize r p ap)=‖r‖^2 := by
  simp [orthogonalize, inner_sub_right, inner_sum, real_inner_smul_right, horth]

theorem orthogonalize_eq_zero_iff {k : ℕ} (r : V) (p ap : Fin k → V)
    (horth : ∀ i, inner ℝ r (p i)=0) : orthogonalize r p ap=0 ↔ r=0 := by
  constructor
  · intro hp
    have h := orthogonalize_residual_inner r p ap horth
    rw [hp, inner_zero_right] at h
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp h.symm)
  · intro hr
    rw [hr, orthogonalize_zero]

theorem orthogonalize_conjugate {k : ℕ}
    (A : Module.End ℝ V) (hpositive : PositiveDefinite A)
    (r : V) (p ap : Fin k → V) (hap : ∀ i, ap i=A (p i))
    (hconjugate : ∀ i j, i ≠ j → inner ℝ (p i) (ap j)=0) :
    ∀ j, inner ℝ (orthogonalize r p ap) (ap j)=0 := by
  intro j
  by_cases hpj : p j=0
  · rw [hap, hpj, map_zero, inner_zero_right]
  · have hden : inner ℝ (p j) (ap j) ≠ 0 := by
      rw [hap]
      exact ne_of_gt (hpositive _ hpj)
    have hsum : (∑ i : Fin k, (inner ℝ r (ap i)/inner ℝ (p i) (ap i))*inner ℝ (p i) (ap j)) =
        inner ℝ r (ap j) := by
      rw [Finset.sum_eq_single j]
      · exact div_mul_cancel₀ _ hden
      · intro i hi hij
        rw [hconjugate i j hij, mul_zero]
      · simp
    simp only [orthogonalize, inner_sub_left, sum_inner, real_inner_smul_left, hsum, sub_self]

structure State (V : Type*) (k : ℕ) where
  x : V
  r : V
  p : Fin k → V
  ap : Fin k → V

noncomputable def newDirection {k : ℕ} (state : State V k) : V := orthogonalize state.r state.p state.ap

noncomputable def stepLength {k : ℕ} (state : State V k) (image : V) : ℝ :=
  inner ℝ state.r (newDirection state)/inner ℝ (newDirection state) image

noncomputable def advance {k : ℕ} (state : State V k) (image : V) : State V (k+1) :=
  let p := newDirection state
  let alpha := stepLength state image
  ⟨state.x+alpha • p, state.r-alpha • image, Fin.snoc state.p p, Fin.snoc state.ap image⟩

noncomputable def initialState (b : V) : State V 0 := ⟨0,b,Fin.elim0,Fin.elim0⟩

noncomputable def stateSequence (A : Module.End ℝ V) (b : V) : (k : ℕ) → State V k
  | 0 => initialState b
  | k+1 => let previous := stateSequence A b k
      advance previous (A (newDirection previous))

def Invariant {k : ℕ} (A : Module.End ℝ V) (b : V) (state : State V k) : Prop :=
  state.r=b-A state.x ∧
  (∀ i, state.ap i=A (state.p i)) ∧
  (∀ i j, i ≠ j → inner ℝ (state.p i) (state.ap j)=0) ∧
  (∀ i, inner ℝ state.r (state.p i)=0) ∧
  (state.r ≠ 0 → ∀ i, state.p i ≠ 0)

theorem initialState_invariant (A : Module.End ℝ V) (b : V) : Invariant A b (initialState b) := by
  simp [Invariant, initialState]

theorem newDirection_ne_zero {k : ℕ} (A : Module.End ℝ V) (b : V) (state : State V k)
    (hstate : Invariant A b state) (hr : state.r ≠ 0) : newDirection state ≠ 0 := by
  exact (orthogonalize_eq_zero_iff state.r state.p state.ap hstate.2.2.2.1).not.mpr hr

theorem advance_residual_identity {k : ℕ} (A : Module.End ℝ V) (b : V) (state : State V k)
    (hr : state.r=b-A state.x) :
    (advance state (A (newDirection state))).r=b-A (advance state (A (newDirection state))).x := by
  simp only [advance, map_add, map_smul]
  rw [hr]
  module

theorem advance_preserves_old_orthogonality {k : ℕ}
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b : V) (state : State V k) (hstate : Invariant A b state) :
    ∀ i, inner ℝ (advance state (A (newDirection state))).r (state.p i)=0 := by
  intro i
  have hp := orthogonalize_conjugate A hpositive state.r state.p state.ap hstate.2.1 hstate.2.2.1 i
  simp only [advance, inner_sub_left, real_inner_smul_left]
  rw [hstate.2.2.2.1 i, hA]
  change 0-stepLength state (A (newDirection state))*inner ℝ (newDirection state) (A (state.p i))=0
  rw [← hstate.2.1 i]
  simp only [newDirection, hp, mul_zero, sub_zero]

theorem advance_new_orthogonality {k : ℕ}
    (A : Module.End ℝ V) (hpositive : PositiveDefinite A)
    (state : State V k) :
    inner ℝ (advance state (A (newDirection state))).r (newDirection state)=0 := by
  by_cases hp : newDirection state=0
  · rw [hp, inner_zero_right]
  · have hden : inner ℝ (newDirection state) (A (newDirection state)) ≠ 0 := ne_of_gt (hpositive _ hp)
    simp only [advance, inner_sub_left, real_inner_smul_left, stepLength]
    rw [real_inner_comm (newDirection state) (A (newDirection state)), div_mul_cancel₀ _ hden, sub_self]

theorem advance_zero_residual {k : ℕ} (A : Module.End ℝ V) (state : State V k)
    (hr : state.r=0) :
    (advance state (A (newDirection state))).r=0 ∧ newDirection state=0 := by
  have hp : newDirection state=0 := by simp only [newDirection, hr, orthogonalize_zero]
  simp [advance, hp, stepLength, hr]

theorem advance_invariant {k : ℕ}
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b : V) (state : State V k) (hstate : Invariant A b state) :
    Invariant A b (advance state (A (newDirection state))) := by
  have hstate0 := hstate
  rcases hstate with ⟨hr,hap,hconj,horth,hnonzero⟩
  have hnew := orthogonalize_conjugate A hpositive state.r state.p state.ap hap hconj
  have holdnew : ∀ i : Fin k, inner ℝ (state.p i) (A (newDirection state))=0 := by
    intro i
    rw [energy_symmetry A hA, ← hap i]
    exact hnew i
  refine ⟨advance_residual_identity A b state hr, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [advance, Fin.snoc_last]
    · simpa only [advance, Fin.snoc_castSucc] using hap j
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro hne
        exact (hne rfl).elim
      · intro hne
        simpa only [advance, Fin.snoc_last, Fin.snoc_castSucc, newDirection] using hnew j'
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro hne
        simpa only [advance, Fin.snoc_last, Fin.snoc_castSucc] using holdnew i'
      · intro hne
        have hij : i' ≠ j' := by intro h; exact hne (congrArg Fin.castSucc h)
        simpa only [advance, Fin.snoc_castSucc] using hconj i' j' hij
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [advance, Fin.snoc_last] using advance_new_orthogonality A hpositive state
    · simpa only [advance, Fin.snoc_castSucc] using advance_preserves_old_orthogonality A hA hpositive b state hstate0 j
  · intro hnewr i
    have hrnonzero : state.r ≠ 0 := by
      intro hz
      exact hnewr (advance_zero_residual A state hz).1
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [advance, Fin.snoc_last] using newDirection_ne_zero A b state hstate0 hrnonzero
    · simpa only [advance, Fin.snoc_castSucc] using hnonzero hrnonzero j

theorem stateSequence_invariant
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A) (b : V) :
    ∀ k, Invariant A b (stateSequence A b k) := by
  intro k
  induction k with
  | zero => exact initialState_invariant A b
  | succ k ih => exact advance_invariant A hA hpositive b (stateSequence A b k) ih

noncomputable def historySpan {k : ℕ} (state : State V k) : Submodule ℝ V := span ℝ (range state.p)

theorem advance_historySpan_le {k : ℕ} (state : State V k) (image : V) :
    historySpan state ≤ historySpan (advance state image) := by
  apply Submodule.span_mono
  rintro x ⟨i,rfl⟩
  exact ⟨i.castSucc,by simp only [advance, Fin.snoc_castSucc]⟩

theorem advance_newDirection_mem {k : ℕ} (state : State V k) (image : V) :
    newDirection state ∈ historySpan (advance state image) := by
  apply Submodule.subset_span
  exact ⟨Fin.last k,by simp only [advance, Fin.snoc_last]⟩

theorem stateSequence_x_mem_historySpan (A : Module.End ℝ V) (b : V) :
    ∀ k, (stateSequence A b k).x ∈ historySpan (stateSequence A b k) := by
  intro k
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    apply Submodule.add_mem
    · exact advance_historySpan_le (stateSequence A b k) _ ih
    · exact Submodule.smul_mem _ _ (advance_newDirection_mem (stateSequence A b k) _)

theorem residual_orthogonal_historySpan {k : ℕ} (r : V) (state : State V k)
    (horth : ∀ i, inner ℝ r (state.p i)=0) :
    ∀ v ∈ historySpan state, inner ℝ r v=0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    exact horth i
  | zero => simp
  | add x y hx hy ihx ihy => simp only [inner_add_right, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [real_inner_smul_right, ih, mul_zero]

theorem conjugate_linearIndependent {k : ℕ}
    (A : Module.End ℝ V) (hpositive : PositiveDefinite A)
    (p : Fin k → V) (hp : ∀ i, p i ≠ 0)
    (hconj : ∀ i j, i ≠ j → inner ℝ (p i) (A (p j))=0) :
    LinearIndependent ℝ p := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hsum := congrArg (fun v : V => inner ℝ v (A (p j))) hc
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at hsum
  have heq : ∑ i, c i * inner ℝ (p i) (A (p j)) = c j * inner ℝ (p j) (A (p j)) := by
    apply Finset.sum_eq_single j
    · intro i hi hij
      rw [hconj i j hij, mul_zero]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [heq] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right (ne_of_gt (hpositive _ (hp j)))

theorem finite_termination [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b : V) : (stateSequence A b (Module.finrank ℝ V)).r=0 := by
  classical
  by_contra hr
  let state := stateSequence A b (Module.finrank ℝ V)
  have hinv : Invariant A b state := stateSequence_invariant A hA hpositive b _
  have hli : LinearIndependent ℝ state.p :=
    conjugate_linearIndependent A hpositive state.p (hinv.2.2.2.2 hr)
      (by intro i j hij; simpa [hinv.2.1 j] using hinv.2.2.1 i j hij)
  have hspan : historySpan state=⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    change Module.finrank ℝ (⊤ : Submodule ℝ V) ≤ Module.finrank ℝ (span ℝ (range state.p))
    rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_top]
  have hzero := residual_orthogonal_historySpan state.r state hinv.2.2.2.1 state.r
    (by rw [hspan]; trivial)
  have : state.r=0 := inner_self_eq_zero.mp hzero
  exact hr this

theorem finite_termination_solves [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b : V) : A (stateSequence A b (Module.finrank ℝ V)).x=b := by
  have h := (stateSequence_invariant A hA hpositive b (Module.finrank ℝ V)).1
  rw [finite_termination A hA hpositive b] at h
  exact (sub_eq_zero.mp h.symm).symm

noncomputable def krylovSpace (A : Module.End ℝ V) (b : V) (k : ℕ) : Submodule ℝ V :=
  span ℝ (range (fun i : Fin k => (A^i.val) b))

theorem krylovSpace_mono (A : Module.End ℝ V) (b : V) {k l : ℕ} (hkl : k ≤ l) :
    krylovSpace A b k ≤ krylovSpace A b l := by
  apply Submodule.span_mono
  rintro v ⟨i,rfl⟩
  exact ⟨i.castLE hkl,rfl⟩

theorem b_mem_krylovSpace (A : Module.End ℝ V) (b : V) (k : ℕ) :
    b ∈ krylovSpace A b (k+1) := by
  apply Submodule.subset_span
  exact ⟨⟨0,by omega⟩,by simp⟩

theorem apply_mem_krylovSpace (A : Module.End ℝ V) (b : V) {k : ℕ}
    (v : V) (hv : v ∈ krylovSpace A b k) : A v ∈ krylovSpace A b (k+1) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨⟨i.val+1,by omega⟩,?_⟩
    simp [pow_succ', Module.End.mul_apply]
  | zero => simpa only [map_zero] using (Submodule.zero_mem (krylovSpace A b (k+1)))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem stateSequence_mem_krylovSpace
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A) (b : V) :
    ∀ k, (stateSequence A b k).x ∈ krylovSpace A b k ∧
      (∀ i, (stateSequence A b k).p i ∈ krylovSpace A b k) := by
  intro k
  induction k with
  | zero => exact ⟨Submodule.zero_mem _,fun i => Fin.elim0 i⟩
  | succ k ih =>
    let state := stateSequence A b k
    let K := krylovSpace A b (k+1)
    have hres : state.r ∈ K := by
      rw [(stateSequence_invariant A hA hpositive b k).1]
      exact Submodule.sub_mem _ (b_mem_krylovSpace A b k)
        (apply_mem_krylovSpace A b state.x ih.1)
    have hold : ∀ i, state.p i ∈ K := fun i =>
      krylovSpace_mono A b (Nat.le_succ k) (ih.2 i)
    have hnew : newDirection state ∈ K := by
      apply Submodule.sub_mem _ hres
      exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (hold i))
    refine ⟨?_,?_⟩
    · exact Submodule.add_mem _ (krylovSpace_mono A b (Nat.le_succ k) ih.1)
        (Submodule.smul_mem _ _ hnew)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [stateSequence, advance, Fin.snoc_last] using hnew
      · simpa only [stateSequence, advance, Fin.snoc_castSucc] using hold j

theorem historySpan_le_krylovSpace
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A) (b : V) (k : ℕ) :
    historySpan (stateSequence A b k) ≤ krylovSpace A b k := by
  apply Submodule.span_le.mpr
  rintro v ⟨i,rfl⟩
  exact (stateSequence_mem_krylovSpace A hA hpositive b k).2 i

theorem historySpan_eq_krylovSpace_of_residual_ne_zero [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A) (b : V) (k : ℕ)
    (hr : (stateSequence A b k).r≠0) :
    historySpan (stateSequence A b k)=krylovSpace A b k := by
  have hinv := stateSequence_invariant A hA hpositive b k
  have hli : LinearIndependent ℝ (stateSequence A b k).p :=
    conjugate_linearIndependent A hpositive _ (hinv.2.2.2.2 hr)
      (by intro i j hij; simpa [hinv.2.1 j] using hinv.2.2.1 i j hij)
  apply Submodule.eq_of_le_of_finrank_le (historySpan_le_krylovSpace A hA hpositive b k)
  have hdim := finrank_range_le_card (R:=ℝ) (fun i : Fin k => (A^i.val) b)
  change Module.finrank ℝ (krylovSpace A b k) ≤ Module.finrank ℝ (span ℝ (range (stateSequence A b k).p))
  rw [finrank_span_eq_card hli, Fintype.card_fin]
  simpa only [krylovSpace, Set.finrank, Fintype.card_fin] using! hdim

theorem residual_orthogonal_krylovSpace [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A) (b : V) (k : ℕ) :
    ∀ v ∈ krylovSpace A b k, inner ℝ (stateSequence A b k).r v=0 := by
  by_cases hr : (stateSequence A b k).r=0
  · simp [hr]
  · rw [← historySpan_eq_krylovSpace_of_residual_ne_zero A hA hpositive b k hr]
    exact residual_orthogonal_historySpan _ _
      (stateSequence_invariant A hA hpositive b k).2.2.2.1

noncomputable def energy (A : Module.End ℝ V) (v : V) : ℝ := inner ℝ v (A v)

theorem energy_nonnegative (A : Module.End ℝ V) (hpositive : PositiveDefinite A) (v : V) :
    0 ≤ energy A v := by
  by_cases hv : v=0
  · simp [energy,hv]
  · exact le_of_lt (hpositive v hv)

theorem energy_difference (A : Module.End ℝ V) (hA : A.IsSymmetric)
    (b z x y r : V) (hz : A z=b) (hr : r=b-A x) :
    energy A (y-z)-energy A (x-z)=energy A (y-x)-2*inner ℝ r (y-x) := by
  have hxy := energy_symmetry A hA x y
  have hxz := energy_symmetry A hA x z
  have hyz := energy_symmetry A hA y z
  simp only [energy, map_sub, inner_sub_left, inner_sub_right] at *
  rw [hr, ← hz]
  simp only [inner_sub_left]
  have hzy := real_inner_comm (A z) y
  have hzx := real_inner_comm (A z) x
  have hxx := real_inner_comm (A x) x
  have hyx := real_inner_comm (A x) y
  ring_nf
  linarith

theorem krylov_energy_minimal [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b z : V) (hz : A z=b) (k : ℕ) (y : V) (hy : y ∈ krylovSpace A b k) :
    energy A ((stateSequence A b k).x-z) ≤ energy A (y-z) := by
  have hx := (stateSequence_mem_krylovSpace A hA hpositive b k).1
  have horth := residual_orthogonal_krylovSpace A hA hpositive b k (y-(stateSequence A b k).x)
    (Submodule.sub_mem _ hy hx)
  have hid := energy_difference A hA b z (stateSequence A b k).x y (stateSequence A b k).r hz
    (stateSequence_invariant A hA hpositive b k).1
  have hnonneg := energy_nonnegative A hpositive (y-(stateSequence A b k).x)
  rw [horth, mul_zero, sub_zero] at hid
  linarith

theorem advance_x_of_zero_residual {k : ℕ} (state : State V k) (image : V)
    (hr : state.r=0) : (advance state image).x=state.x := by
  have hp : newDirection state=0 := by simp only [newDirection,hr,orthogonalize_zero]
  simp [advance,hp]

theorem stateSequence_stable_after_zero (A : Module.End ℝ V) (b : V) (k : ℕ)
    (hr : (stateSequence A b k).r=0) :
    ∀ j, (stateSequence A b (k+j)).r=0 ∧
      (stateSequence A b (k+j)).x=(stateSequence A b k).x := by
  intro j
  induction j with
  | zero => simpa only [Nat.add_zero] using (And.intro hr (rfl : (stateSequence A b k).x=(stateSequence A b k).x))
  | succ j ih =>
    change (advance (stateSequence A b (k+j)) (A (newDirection (stateSequence A b (k+j))))).r=0 ∧ _
    exact ⟨(advance_zero_residual A _ ih.1).1,
      (advance_x_of_zero_residual _ _ ih.1).trans ih.2⟩

end PaperCGExact



end SnapshotModule_059
/- END cg_exact -/

/- BEGIN cg_gaussian -/
section SnapshotModule_060

/- Objective-independent standard-Gaussian nondegeneracy for exact-line calibration. -/
namespace PaperCGGaussian

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_linear_ae_ne_zero (L : StrongDual ℝ E) (hL : L ≠ 0) :
    ∀ᵐ g ∂stdGaussian E, L g ≠ 0 := by
  have hnorm : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hvariance : (‖L‖^2).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (pow_pos hnorm 2))
  have hmap : (stdGaussian E).map L=gaussianReal 0 ((‖L‖^2).toNNReal) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  letI := nullSingletonClass_gaussianReal (μ:=0) hvariance
  have hreal : ∀ᵐ y ∂(stdGaussian E).map L, y ≠ (0:ℝ) := by
    rw [hmap]
    simp [ae_iff]
  exact ae_of_ae_map L.continuous.aemeasurable hreal

theorem stdGaussian_finite_linear_family_ae_ne_zero
    {ι : Type*} [Fintype ι] (L : ι → StrongDual ℝ E) (hL : ∀ i, L i ≠ 0) :
    ∀ᵐ g ∂stdGaussian E, ∀ i, L i g ≠ 0 := by
  exact ae_all_iff.mpr (fun i => stdGaussian_linear_ae_ne_zero (L i) (hL i))

theorem normalized_gaussian_finite_family_good
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → StrongDual ℝ E) (hL : ∀ i, L i ≠ 0) :
    ∀ᵐ g ∂stdGaussian E, g ≠ 0 ∧ ‖NormedSpace.normalize g‖=1 ∧
      ∀ i, L i (NormedSpace.normalize g) ≠ 0 := by
  filter_upwards [stdGaussian_finite_linear_family_ae_ne_zero L hL] with g hg
  let i0 : ι := Classical.choice inferInstance
  have hgzero : g ≠ 0 := by
    intro hz
    exact hg i0 (by simp only [hz, map_zero])
  refine ⟨hgzero,NormedSpace.norm_normalize hgzero,?_⟩
  intro i
  simp only [NormedSpace.normalize, map_smul, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hgzero)) (hg i)

theorem measurable_normalize : Measurable (NormedSpace.normalize : E → E) := by
  unfold NormedSpace.normalize
  fun_prop

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def axis {d : ℕ} (i : Fin d) : Vec d := PiLp.single 2 i (1:ℝ)

noncomputable def coordinateRow {d : ℕ} (A : Vec d →L[ℝ] Vec d) (i : Fin d) : StrongDual ℝ (Vec d) :=
  (InnerProductSpace.toDual ℝ (Vec d) (axis i)).comp A

theorem coordinateRow_ne_zero {d : ℕ} (A : Vec d →L[ℝ] Vec d)
    (hpositive : ∀ x : Vec d, x ≠ 0 → 0 < inner ℝ x (A x)) (i : Fin d) :
    coordinateRow A i ≠ 0 := by
  intro hz
  have hai : axis i ≠ (0:Vec d) := by simp [axis]
  have hp := hpositive (axis i) hai
  have heq := congrArg (fun L : StrongDual ℝ (Vec d) => L (axis i)) hz
  simp only [coordinateRow, ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
    zero_apply] at heq
  linarith

/-- The probability-one event is per fixed SPD operator; the Gaussian law itself is fixed. -/
theorem spd_normalized_gaussian_calibration_good (d : ℕ) (hd : 0 < d)
    (A : Vec d →L[ℝ] Vec d)
    (hpositive : ∀ x : Vec d, x ≠ 0 → 0 < inner ℝ x (A x)) :
    ∀ᵐ g ∂stdGaussian (Vec d), g ≠ 0 ∧ ‖NormedSpace.normalize g‖=1 ∧
      ∀ i : Fin d, (A (NormedSpace.normalize g)) i ≠ 0 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have h := normalized_gaussian_finite_family_good (coordinateRow A) (coordinateRow_ne_zero A hpositive)
  filter_upwards [h] with g hg
  refine ⟨hg.1,hg.2.1,?_⟩
  intro i
  have hi := hg.2.2 i
  simpa [coordinateRow, axis, InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_single_left] using hi

def GoodCalibrationSeed {d : ℕ} (A : Vec d →L[ℝ] Vec d) (g : Vec d) : Prop :=
  g ≠ 0 ∧ ‖NormedSpace.normalize g‖=1 ∧ ∀ i : Fin d, (A (NormedSpace.normalize g)) i ≠ 0

theorem goodCalibrationSeed_measurable (d : ℕ) (A : Vec d →L[ℝ] Vec d) :
    MeasurableSet {g : Vec d | GoodCalibrationSeed A g} := by
  have hn : Measurable (NormedSpace.normalize : Vec d → Vec d) := measurable_normalize
  have hzero : MeasurableSet {g : Vec d | g=0} := measurableSet_eq_fun measurable_id measurable_const
  have hnorm : MeasurableSet {g : Vec d | ‖NormedSpace.normalize g‖=1} :=
    measurableSet_eq_fun hn.norm measurable_const
  have hrows : MeasurableSet {g : Vec d | ∀ i : Fin d, (A (NormedSpace.normalize g)) i ≠ 0} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun g : Vec d => (A (NormedSpace.normalize g)) i) := by fun_prop
    exact (measurableSet_eq_fun hm measurable_const).compl
  exact hzero.compl.inter (hnorm.inter hrows)

theorem goodCalibrationSeed_probability_one (d : ℕ) (hd : 0 < d)
    (A : Vec d →L[ℝ] Vec d)
    (hpositive : ∀ x : Vec d, x ≠ 0 → 0 < inner ℝ x (A x)) :
    stdGaussian (Vec d) {g | GoodCalibrationSeed A g}=1 := by
  have h := spd_normalized_gaussian_calibration_good d hd A hpositive
  have heq : {g : Vec d | GoodCalibrationSeed A g} =ᵐ[stdGaussian (Vec d)] univ := by
    filter_upwards [h] with g hg
    apply propext
    exact ⟨fun _ => mem_univ g, fun _ => hg⟩
  rw [measure_congr heq, measure_univ]

end PaperCGGaussian


end SnapshotModule_060
/- END cg_gaussian -/

/- BEGIN cg_line_program -/
section SnapshotModule_061

namespace PaperCGLine
open PaperCGExact
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev LineOracle (d : ℕ) := Vec d → Vec d → ℝ
noncomputable abbrev axis {d : ℕ} (i : Fin d) : Vec d := PaperCGGaussian.axis i

inductive Program (d : ℕ) (α : Type) where
  | pure : α → Program d α
  | query : Vec d → Vec d → (ℝ → Program d α) → Program d α

namespace Program

def bind {d : ℕ} {α β : Type} (P : Program d α) (f : α → Program d β) : Program d β :=
  match P with
  | .pure a => f a
  | .query x v next => .query x v (fun t => bind (next t) f)

def eval {d : ℕ} {α : Type} (L : LineOracle d) : Program d α → α
  | .pure a => a
  | .query x v next => eval L (next (L x v))

def count {d : ℕ} {α : Type} (L : LineOracle d) : Program d α → ℕ
  | .pure _ => 0
  | .query x v next => 1+count L (next (L x v))

theorem eval_bind {d : ℕ} {α β : Type} (L : LineOracle d) (P : Program d α) (f : α → Program d β) :
    eval L (bind P f)=eval L (f (eval L P)) := by
  induction P with
  | pure a => rfl
  | query x v next ih => simp [bind,eval,ih]

theorem count_bind {d : ℕ} {α β : Type} (L : LineOracle d) (P : Program d α) (f : α → Program d β) :
    count L (bind P f)=count L P+count L (f (eval L P)) := by
  induction P with
  | pure a => simp [bind,count,eval]
  | query x v next ih => simp [bind,count,eval,ih,Nat.add_assoc]

def collect {d : ℕ} {α : Type} : (m : ℕ) → (Fin m → Program d α) → Program d (Fin m → α)
  | 0,_ => .pure Fin.elim0
  | m+1,f => bind (f 0) (fun first =>
      bind (collect m (fun i => f i.succ)) (fun rest => .pure (Fin.cons first rest)))

theorem eval_collect {d : ℕ} {α : Type} (L : LineOracle d) (m : ℕ) (f : Fin m → Program d α) :
    eval L (collect m f)=fun i => eval L (f i) := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    simp only [collect,eval_bind,eval]
    rw [ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem count_collect {d : ℕ} {α : Type} (L : LineOracle d) (m : ℕ) (f : Fin m → Program d α) :
    count L (collect m f)=∑ i, count L (f i) := by
  induction m with
  | zero => simp [collect,count]
  | succ m ih => simp [collect,count_bind,count,ih,Fin.sum_univ_succ]

/-- Every query direction on the evaluated path is nonzero. -/
def Valid {d : ℕ} {α : Type} (L : LineOracle d) : Program d α → Prop
  | .pure _ => True
  | .query x v next => v≠0 ∧ Valid L (next (L x v))

theorem valid_bind {d : ℕ} {α β : Type} (L : LineOracle d) (P : Program d α) (f : α → Program d β)
    (hp : Valid L P) (hf : Valid L (f (eval L P))) : Valid L (bind P f) := by
  induction P with
  | pure a => exact hf
  | query x v next ih => exact ⟨hp.1,ih _ hp.2 hf⟩

theorem valid_collect {d : ℕ} {α : Type} (L : LineOracle d) (m : ℕ) (f : Fin m → Program d α)
    (hf : ∀ i, Valid L (f i)) : Valid L (collect m f) := by
  induction m with
  | zero => trivial
  | succ m ih =>
    apply valid_bind _ _ _ (hf 0)
    apply valid_bind _ _ _ (ih (fun i => f i.succ) (fun i => hf i.succ))
    trivial

end Program

noncomputable def lineRoot {d : ℕ} (A : Module.End ℝ (Vec d)) (b x v : Vec d) : ℝ :=
  inner ℝ v (b-A x)/inner ℝ v (A v)

def ExactLineOracle {d : ℕ} (A : Module.End ℝ (Vec d)) (b : Vec d) (L : LineOracle d) : Prop :=
  ∀ x v, v≠0 → L x v=lineRoot A b x v

noncomputable def matvecProgram {d : ℕ} (h r : Fin d → ℝ) (v : Vec d) : Program d (Vec d) :=
  Program.bind (Program.collect d (fun i => .query v (axis i) (fun t => .pure t)))
    (fun tau => .pure (WithLp.toLp 2 (fun i => h i*(r i-tau i))))

theorem matvecProgram_count {d : ℕ} (L : LineOracle d) (h r : Fin d → ℝ) (v : Vec d) :
    Program.count L (matvecProgram h r v)=d := by
  simp [matvecProgram,Program.count_bind,Program.count_collect,Program.count]

theorem matvecProgram_valid {d : ℕ} (L : LineOracle d) (h r : Fin d → ℝ) (v : Vec d) :
    Program.Valid L (matvecProgram h r v) := by
  apply Program.valid_bind
  · apply Program.valid_collect
    intro i
    exact ⟨by simp [axis,PaperCGGaussian.axis],trivial⟩
  · trivial

noncomputable def cgLoop {d : ℕ} (h r : Fin d → ℝ) :
    (fuel k : ℕ) → State (Vec d) k → Program d (Vec d)
  | 0,_,state => .pure state.x
  | fuel+1,k,state =>
    if state.r=0 then .pure state.x else
      Program.bind (matvecProgram h r (newDirection state)) (fun image =>
        cgLoop h r fuel (k+1) (advance state image))

theorem cgLoop_count {d : ℕ} (L : LineOracle d) (h r : Fin d → ℝ) :
    ∀ fuel k (state : State (Vec d) k), Program.count L (cgLoop h r fuel k state) ≤ d*fuel := by
  intro fuel
  induction fuel with
  | zero => intro k state; simp [cgLoop,Program.count]
  | succ fuel ih =>
    intro k state
    simp only [cgLoop]
    split_ifs
    · simp [Program.count]
    · rw [Program.count_bind,matvecProgram_count]
      have hstep := ih (k+1) (advance state (Program.eval L (matvecProgram h r (newDirection state))))
      nlinarith

theorem cgLoop_valid {d : ℕ} (L : LineOracle d) (h r : Fin d → ℝ) :
    ∀ fuel k (state : State (Vec d) k), Program.Valid L (cgLoop h r fuel k state) := by
  intro fuel
  induction fuel with
  | zero => intro k state; trivial
  | succ fuel ih =>
    intro k state
    simp only [cgLoop]
    split_ifs
    · trivial
    · exact Program.valid_bind _ _ _ (matvecProgram_valid L h r _) (ih _ _)

/-- Returned triples are r_i, P_i, S_i. No matrix or right-hand side is an input. -/
noncomputable def calibrationProgram {d : ℕ} (u : Vec d) : Program d (Fin d → ℝ×ℝ×ℝ) :=
  Program.collect d (fun i => .query 0 (axis i) (fun r =>
    .query (axis i) u (fun p => .query u (axis i) (fun s => .pure (r,p,s)))))

noncomputable def algorithm {d : ℕ} (g : Vec d) (N : ℕ) : Program d (Vec d) :=
  if g=0 then .pure 0 else
    let u := NormedSpace.normalize g
    .query 0 u (fun P => Program.bind (calibrationProgram u) (fun data =>
      if ∃ i, (data i).1-(data i).2.2=0 then .pure 0 else
        let h := fun i => (P-(data i).2.1)/((data i).1-(data i).2.2)
        let r := fun i => (data i).1
        cgLoop h r N 0 (initialState (WithLp.toLp 2 (fun i => h i*r i)))))

theorem calibrationProgram_count {d : ℕ} (L : LineOracle d) (u : Vec d) :
    Program.count L (calibrationProgram u)=3*d := by
  simp [calibrationProgram,Program.count_collect,Program.count,Nat.mul_comm]

theorem algorithm_pathwise_cap {d : ℕ} (L : LineOracle d) (g : Vec d) (N : ℕ) :
    Program.count L (algorithm g N) ≤ 3*d+1+d*N := by
  unfold algorithm
  split_ifs
  · simp [Program.count]
  · simp only [Program.count,Program.count_bind,calibrationProgram_count]
    split_ifs
    · simp only [Program.count]
      omega
    · rw [← Nat.add_assoc]
      exact Nat.add_le_add (by omega) (cgLoop_count L _ _ N 0 _)

theorem algorithm_valid {d : ℕ} (L : LineOracle d) (g : Vec d) (N : ℕ) :
    Program.Valid L (algorithm g N) := by
  unfold algorithm
  split_ifs with hg
  · trivial
  · refine ⟨(by intro h; exact hg ((NormedSpace.normalize_eq_zero_iff g).mp h)),?_⟩
    apply Program.valid_bind
    · apply Program.valid_collect
      intro i
      exact ⟨by simp [axis,PaperCGGaussian.axis],(by intro h; exact hg ((NormedSpace.normalize_eq_zero_iff g).mp h)),
        by simp [axis,PaperCGGaussian.axis],trivial⟩
    · split_ifs
      · trivial
      · exact cgLoop_valid L _ _ _ _ _

namespace Program
lemma eval_congr_exact {d : ℕ} {α : Type} (L K : LineOracle d) (P : Program d α)
    (hvalid : Valid L P) (hLK : ∀ x v, v≠0 → L x v=K x v) :
    eval L P=eval K P := by
  induction P with
  | pure a => rfl
  | query x v next ih =>
    simp only [eval]
    rw [← hLK x v hvalid.1]
    exact ih _ hvalid.2
end Program

end PaperCGLine

end SnapshotModule_061
/- END cg_line_program -/

/- BEGIN real_borel_program -/
section SnapshotModule_062

/- A finite adaptive real-response syntax with Borel state transformations.
   Unlike an unrestricted real continuation, every continuation carries a Borel
   parameter-state interface. All reply values, including exceptional ones, are total. -/
namespace PaperRealBorel
open MeasureTheory PaperCGLine
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

structure Space where
  carrier : Type
  inst : MeasurableSpace carrier
instance : CoeSort Space Type := ⟨Space.carrier⟩
instance (S : Space) : MeasurableSpace S := S.inst

abbrev space (S : Type) [MeasurableSpace S] : Space := ⟨S,inferInstance⟩
abbrev Space.prod (S T : Space) : Space := space (S × T)

inductive Code (d : ℕ) (A : Type) [MeasurableSpace A] : Space → Type 1 where
  | pure {S : Space} (out : S → A) (ho : Measurable out) : Code d A S
  | ask {S : Space} (q : S → Vec d × Vec d)
      (hq : Measurable q) (next : Code d A (S.prod (space ℝ))) : Code d A S
  | branch {S : Space} (E : Set S) (hE : MeasurableSet E)
      (yes no : Code d A S) : Code d A S

namespace Code
variable {d : ℕ} {A : Type} [MeasurableSpace A] {S : Space}

noncomputable def denote : {S : Space} → Code d A S → S → Program d A
  | _,.pure out _,s => .pure (out s)
  | _,.ask q _ next,s => .query (q s).1 (q s).2 (fun r => denote next (s,r))
  | _,.branch E _ yes no,s => by
    classical
    exact if s ∈ E then denote yes s else denote no s

noncomputable def comap : {S T : Space} →
    (f : T → S) → Measurable f → Code d A S → Code d A T
  | _,_,f,hf,.pure out ho => .pure (out ∘ f) (ho.comp hf)
  | S,T,f,hf,.ask q hq next => .ask (q ∘ f) (hq.comp hf)
      (comap (S:=S.prod (space ℝ)) (T:=T.prod (space ℝ))
        (fun tr : T × ℝ => (f tr.1,tr.2)) ((hf.comp measurable_fst).prodMk measurable_snd) next)
  | _,_,f,hf,.branch E hE yes no => .branch (f ⁻¹' E) (hE.preimage hf)
      (comap f hf yes) (comap f hf no)

theorem denote_comap {T : Space}
    (f : T → S) (hf : Measurable f) (P : Code d A S) (t : T) :
    denote (comap f hf P) t=denote P (f t) := by
  classical
  induction P generalizing T with
  | pure out ho => rfl
  | ask q hq next ih =>
    simp only [comap,denote]
    congr 1
    funext r
    exact ih _ _ _
  | branch E hE yes no ihy ihn =>
    simp only [comap,denote,Set.mem_preimage]
    split_ifs <;> [exact ihy _ _ _; exact ihn _ _ _]

noncomputable def bind {B : Type} [MeasurableSpace B] :
    {S : Space} → Code d A S → Code d B (S.prod (space A)) → Code d B S
  | _,.pure out ho,next => comap (fun s => (s,out s)) (measurable_id.prodMk ho) next
  | _,.ask q hq cont,next => .ask q hq
      (bind cont (comap (fun sra => (sra.1.1,sra.2)) (by fun_prop) next))
  | _,.branch E hE yes no,next => .branch E hE (bind yes next) (bind no next)

theorem denote_bind {B : Type} [MeasurableSpace B]
    (P : Code d A S) (next : Code d B (S.prod (space A))) (s : S) :
    denote (bind P next) s=Program.bind (denote P s) (fun a => denote next (s,a)) := by
  classical
  induction P with
  | pure out ho => exact denote_comap _ _ next s
  | ask q hq cont ih =>
    simp only [bind,denote,Program.bind]
    congr 1
    funext r
    rw [ih]
    congr 1
    funext a
    exact denote_comap _ _ next _
  | branch E hE yes no ihy ihn =>
    simp only [bind,denote]
    split_ifs <;> [exact ihy _ _;exact ihn _ _]

noncomputable def height : {S : Space} → Code d A S → ℕ
  | _,.pure _ _ => 0
  | _,.ask _ _ next => height next+1
  | _,.branch _ _ yes no => max (height yes) (height no)

/-- Syntactic cap quantifies over arbitrary real feedback, not merely consistent oracles. -/
def Cap : ℕ → Program d A → Prop
  | _, .pure _ => True
  | 0, .query _ _ _ => False
  | n+1, .query _ _ next => ∀ r : ℝ, Cap n (next r)

theorem cap_mono {n m : ℕ} (hnm : n ≤ m) {P : Program d A} (hP : Cap n P) : Cap m P := by
  classical
  induction n generalizing m P with
  | zero => cases P <;> simp_all [Cap]
  | succ n ih =>
    cases P with
    | pure a => cases m <;> trivial
    | query x v next =>
      cases m with
      | zero => omega
      | succ m => exact fun r => ih (by omega) (hP r)

theorem denote_cap (P : Code d A S) (s : S) : Cap (height P) (denote P s) := by
  classical
  induction P with
  | pure out ho => trivial
  | ask q hq next ih => exact fun r => ih (s,r)
  | branch E hE yes no ihy ihn =>
    simp only [height,denote]
    split_ifs
    · exact cap_mono (Nat.le_max_left _ _) (ihy s)
    · exact cap_mono (Nat.le_max_right _ _) (ihn s)

theorem eval_measurable (P : Code d A S) (L : LineOracle d)
    (hL : Measurable (fun q : Vec d × Vec d => L q.1 q.2)) :
    Measurable (fun s => Program.eval L (denote P s)) := by
  classical
  induction P with
  | pure out ho => exact ho
  | ask q hq next ih =>
    exact ih.comp (measurable_id.prodMk (hL.comp hq))
  | branch E hE yes no ihy ihn =>
    simpa only [denote,apply_ite] using! Measurable.ite hE ihy ihn

/-- Read a fixed chronological finite reply tape. Already-stopped programs ignore surplus replies. -/
noncomputable def front : {S : Space} → Code d A S →
    (t : ℕ) → S × (Fin t → ℝ) → (Vec d × Vec d) ⊕ A
  | _,.pure out _,_,st => .inr (out st.1)
  | _,.ask q _ _,0,st => .inl (q st.1)
  | _,.ask _ _ next,t+1,st => front next t ((st.1,st.2 0),fun i => st.2 i.succ)
  | _,.branch E _ yes no,t,st => by
    classical
    exact if st.1 ∈ E then front yes t st else front no t st

theorem front_measurable (P : Code d A S) : ∀ t, Measurable (front P t) := by
  classical
  induction P with
  | pure out ho => intro t; exact measurable_inr.comp (ho.comp measurable_fst)
  | ask q hq next ih =>
    intro t
    cases t with
    | zero => exact measurable_inl.comp (hq.comp measurable_fst)
    | succ t =>
      apply (ih t).comp
      apply Measurable.prodMk
      · exact measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
      · apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i.succ).comp measurable_snd
  | branch E hE yes no ihy ihn =>
    intro t
    exact Measurable.ite (hE.preimage measurable_fst) (ihy t) (ihn t)

noncomputable def query (q : S → Vec d × Vec d) (hq : Measurable q) : Code d ℝ S :=
  .ask q hq (.pure Prod.snd measurable_snd)

theorem denote_query (q : S → Vec d × Vec d) (hq : Measurable q) (s : S) :
    denote (query q hq) s=.query (q s).1 (q s).2 (fun r => .pure r) := rfl

lemma measurable_cons {m : ℕ} :
    Measurable (fun ar : A × (Fin m → A) => (Fin.cons ar.1 ar.2 : Fin (m+1) → A)) := by
  classical
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

noncomputable def collect : (m : ℕ) → (Fin m → Code d A S) → Code d (Fin m → A) S
  | 0,_ => .pure (fun _ => Fin.elim0) measurable_const
  | m+1,f => bind (f 0)
      (bind (comap Prod.fst measurable_fst (collect m (fun i => f i.succ)))
        (.pure (fun st => Fin.cons st.1.2 st.2)
          (measurable_cons.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))

theorem denote_collect (m : ℕ) (f : Fin m → Code d A S) (s : S) :
    denote (collect m f) s=Program.collect m (fun i => denote (f i) s) := by
  classical
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [collect,denote_bind,denote_comap,denote,Program.collect]
    congr 1
    funext first
    rw [ih]

theorem height_comap {T : Space} (f : T → S) (hf : Measurable f) (P : Code d A S) :
    height (comap f hf P)=height P := by
  classical
  induction P generalizing T with
  | pure out ho => rfl
  | ask q hq next ih => simp only [comap,height,ih]
  | branch E hE yes no ihy ihn => simp only [comap,height,ihy,ihn]

theorem height_bind {B : Type} [MeasurableSpace B]
    (P : Code d A S) (next : Code d B (S.prod (space A))) :
    height (bind P next)=height P+height next := by
  classical
  induction P with
  | pure out ho => simp only [bind,height_comap,height,Nat.zero_add]
  | ask q hq cont ih => simp only [bind,height,ih,height_comap]; omega
  | branch E hE yes no ihy ihn =>
    simp only [bind,height,ihy,ihn]
    omega

theorem height_collect (m : ℕ) (f : Fin m → Code d A S) :
    height (collect m f)=∑ i, height (f i) := by
  classical
  induction m with
  | zero => simp [collect,height]
  | succ m ih =>
    simp only [collect,height_bind,height_comap,height,Nat.add_zero,ih,Fin.sum_univ_succ]

end Code
end PaperRealBorel

namespace PaperCGLine.Program
noncomputable def replayFront {d : ℕ} {A : Type} : Program d A →
    (t : ℕ) → (Fin t → ℝ) → (Vec d × Vec d) ⊕ A
  | .pure a,_,_ => .inr a
  | .query x v _,0,_ => .inl (x,v)
  | .query _ _ next,t+1,h => replayFront (next (h 0)) t (fun i => h i.succ)
end PaperCGLine.Program

namespace PaperRealBorel.Code
open MeasureTheory PaperCGLine
variable {d : ℕ} {A : Type} [MeasurableSpace A] {S : Space}

theorem front_eq_replay (P : Code d A S) (t : ℕ) (s : S) (h : Fin t → ℝ) :
    front P t (s,h)=Program.replayFront (denote P s) t h := by
  classical
  induction P generalizing t with
  | pure out ho => rfl
  | ask q hq next ih =>
    cases t with
    | zero => rfl
    | succ t => exact ih t (s,h 0) (fun i => h i.succ)
  | branch E hE yes no ihy ihn =>
    simp only [front,denote]
    split_ifs <;> [exact ihy _ _ _;exact ihn _ _ _]

noncomputable def request (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) : Vec d × Vec d :=
  (front P t st).elim id (fun _ => (0,0))
noncomputable def stopped (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) : Bool :=
  (front P t st).elim (fun _ => false) (fun _ => true)
noncomputable def result [Zero A] (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) : A :=
  (front P t st).elim (fun _ => 0) id

theorem request_measurable (P : Code d A S) (t : ℕ) : Measurable (request P t) :=
  (measurable_id.sumElim measurable_const).comp (front_measurable P t)
theorem stopped_measurable (P : Code d A S) (t : ℕ) : Measurable (stopped P t) :=
  (measurable_const.sumElim measurable_const).comp (front_measurable P t)
theorem result_measurable [Zero A] (P : Code d A S) (t : ℕ) : Measurable (result P t) :=
  (measurable_const.sumElim measurable_id).comp (front_measurable P t)

end PaperRealBorel.Code

end SnapshotModule_062
/- END real_borel_program -/

/- BEGIN real_borel_policy -/
section SnapshotModule_063

namespace PaperCGLine.Program
open MeasureTheory
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def observe {d : ℕ} {A : Type} : Program d A → (Vec d × Vec d) ⊕ A
  | .pure a => .inr a
  | .query x v _ => .inl (x,v)

def resumeList {d : ℕ} {A : Type} : Program d A → List ℝ → Program d A
  | P,[] => P
  | .pure a,_::_ => .pure a
  | .query _ _ next,r::rs => resumeList (next r) rs

lemma resumeList_append {d : ℕ} {A : Type} (P : Program d A) (l r : List ℝ) :
    resumeList P (l++r)=resumeList (resumeList P l) r := by
  induction l generalizing P with
  | nil => simp only [List.nil_append,resumeList]
  | cons a l ih =>
    cases P with
    | pure b => cases r <;> rfl
    | query x v next => exact ih (next a)

noncomputable def toOracle {d : ℕ} {A : Type} : Program d A → PaperOracle.Program (Vec d × Vec d) ℝ A
  | .pure a => .done a
  | .query x v next => .ask (x,v) (fun r => toOracle (next r))

noncomputable def truncate {d : ℕ} {A : Type} [Zero A] :
    ℕ → Program d A → PaperOracle.Program (Vec d × Vec d) ℝ A
  | 0,P => .done (P.observe.elim (fun _ => 0) id)
  | _+1,.pure a => .done a
  | n+1,.query x v next => .ask (x,v) (fun r => truncate n (next r))

lemma truncate_of_cap {d : ℕ} {A : Type} [MeasurableSpace A] [Zero A]
    (n : ℕ) (P : Program d A) (hP : PaperRealBorel.Code.Cap n P) :
    truncate n P=toOracle P := by
  induction n generalizing P with
  | zero => cases P <;> simp_all [PaperRealBorel.Code.Cap,truncate,toOracle,observe]
  | succ n ih =>
    cases P with
    | pure a => rfl
    | query x v next =>
      simp only [truncate,toOracle]
      congr 1
      funext r
      exact ih (next r) (hP r)

lemma run_toOracle {d : ℕ} {A : Type} (L : LineOracle d) (P : Program d A) :
    PaperOracle.Program.run (fun q => L q.1 q.2) (toOracle P)=eval L P := by
  induction P with
  | pure a => rfl
  | query x v next ih => exact ih _

lemma count_toOracle {d : ℕ} {A : Type} (L : LineOracle d) (P : Program d A) :
    (PaperOracle.Program.trace (fun q => L q.1 q.2) (toOracle P)).length=count L P := by
  induction P with
  | pure a => rfl
  | query x v next ih =>
    simp only [toOracle,PaperOracle.Program.trace,List.length_cons,count,ih]
    omega

end PaperCGLine.Program

namespace PaperRealBorel.Code
open MeasureTheory PaperCGLine
variable {d : ℕ} {A : Type} [MeasurableSpace A] {S : Space}
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-- The same replay in the policy convention: newest response first. -/
noncomputable def reverseFront (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) :
    (Vec d × Vec d) ⊕ A :=
  Program.observe (Program.resumeList (denote P st.1) (List.ofFn st.2).reverse)

theorem reverseFront_measurable (P : Code d A S) : ∀ t, Measurable (reverseFront P t) := by
  classical
  induction P with
  | pure out ho =>
    intro t
    have heq : reverseFront (d:=d) (.pure out ho) t=fun st => Sum.inr (out st.1) := by
      funext st
      unfold reverseFront
      cases (List.ofFn st.2).reverse <;> rfl
    rw [heq]
    exact measurable_inr.comp (ho.comp measurable_fst)
  | ask q hq next ih =>
    intro t
    cases t with
    | zero => exact measurable_inl.comp (hq.comp measurable_fst)
    | succ t =>
      have heq : reverseFront (.ask q hq next) (t+1)=fun st =>
          reverseFront next t ((st.1,st.2 (Fin.last t)),fun i => st.2 i.castSucc) := by
        funext st
        simp only [reverseFront,denote,List.ofFn_succ',List.concat_eq_append,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,Program.resumeList]
      rw [heq]
      apply (ih t).comp
      apply Measurable.prodMk
      · exact measurable_fst.prodMk ((measurable_pi_apply (Fin.last t)).comp measurable_snd)
      · apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i.castSucc).comp measurable_snd
  | branch E hE yes no ihy ihn =>
    intro t
    have heq : reverseFront (.branch E hE yes no) t=fun st =>
        if st.1 ∈ E then reverseFront yes t st else reverseFront no t st := by
      funext st
      simp only [reverseFront,denote]
      split_ifs <;> rfl
    rw [heq]
    exact Measurable.ite (hE.preimage measurable_fst) (ihy t) (ihn t)

noncomputable def policy [Zero A] (P : Code d A S) :
    PaperBorelPolicy.Policy S (Vec d × Vec d) ℝ A where
  query t st := (reverseFront P t st).elim id (fun _ => (0,0))
  output t st := (reverseFront P t st).elim (fun _ => 0) id
  stop t st := (reverseFront P t st).elim (fun _ => false) (fun _ => true)
  query_measurable t := (measurable_id.sumElim measurable_const).comp (reverseFront_measurable P t)
  output_measurable t := (measurable_const.sumElim measurable_id).comp (reverseFront_measurable P t)
  stop_measurable t := measurableSet_eq_fun
    ((measurable_const.sumElim measurable_const).comp (reverseFront_measurable P t)) measurable_const

lemma policy_query_eq [Zero A] (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) :
    P.policy.query t st=(reverseFront P t st).elim id (fun _ => (0,0)) := rfl
lemma policy_output_eq [Zero A] (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) :
    P.policy.output t st=(reverseFront P t st).elim (fun _ => 0) id := rfl
lemma policy_stop_eq [Zero A] (P : Code d A S) (t : ℕ) (st : S × (Fin t → ℝ)) :
    P.policy.stop t st=(reverseFront P t st).elim (fun _ => false) (fun _ => true) := rfl

theorem policy_unroll_eq_truncate [Zero A] (P : Code d A S)
    (budget t : ℕ) (st : S × (Fin t → ℝ)) :
    P.policy.unroll budget t st =
      Program.truncate budget (Program.resumeList (denote P st.1) (List.ofFn st.2).reverse) := by
  classical
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    let rest := Program.resumeList (denote P st.1) (List.ofFn st.2).reverse
    have hrest : Program.resumeList (denote P st.1) (List.ofFn st.2).reverse=rest := rfl
    cases hr : rest with
    | pure a =>
      simp only [PaperBorelPolicy.Policy.unroll,policy_query_eq,policy_output_eq,policy_stop_eq,reverseFront,hrest,hr,Program.observe,
        Sum.elim_inr,if_true,Program.truncate,id_eq]
    | query x v next =>
      simp only [PaperBorelPolicy.Policy.unroll,policy_query_eq,policy_output_eq,policy_stop_eq,reverseFront,hrest,hr,Program.observe,
        Sum.elim_inl,Bool.false_eq_true,if_false,Program.truncate]
      congr 1
      funext r
      rw [ih]
      simp only [List.ofFn_cons,List.reverse_cons,Program.resumeList_append,hrest,hr,Program.resumeList]

theorem policy_fromSeed_eq [Zero A] (P : Code d A S) (budget : ℕ)
    (hbudget : height P ≤ budget) (s : S) :
    P.policy.fromSeed budget s=Program.toOracle (denote P s) := by
  rw [PaperBorelPolicy.Policy.fromSeed,policy_unroll_eq_truncate]
  simp only [List.ofFn_zero,List.reverse_nil,Program.resumeList]
  exact Program.truncate_of_cap budget _ (cap_mono hbudget (denote_cap P s))

theorem policy_run_eq [Zero A] (P : Code d A S) (budget : ℕ)
    (hbudget : height P ≤ budget) (L : LineOracle d) (s : S) :
    PaperOracle.Program.run (fun q => L q.1 q.2) (P.policy.fromSeed budget s)=
      Program.eval L (denote P s) := by
  rw [policy_fromSeed_eq P budget hbudget s]
  exact Program.run_toOracle L _

theorem policy_count_eq [Zero A] (P : Code d A S) (budget : ℕ)
    (hbudget : height P ≤ budget) (L : LineOracle d) (s : S) :
    (PaperOracle.Program.trace (fun q => L q.1 q.2) (P.policy.fromSeed budget s)).length=
      Program.count L (denote P s) := by
  rw [policy_fromSeed_eq P budget hbudget s]
  exact Program.count_toOracle L _

end PaperRealBorel.Code

end SnapshotModule_063
/- END real_borel_policy -/

/- BEGIN borel_comparison_transfer -/
section SnapshotModule_064

namespace PaperBorelPolicy
noncomputable section
open MeasureTheory PaperOracle

theorem realOrder_measurable [MeasurableSpace Ordering] :
    Measurable (fun x : ℝ × ℝ => PaperOracle.realOrder x.1 x.2) := by
  unfold PaperOracle.realOrder
  exact Measurable.ite (isOpen_lt continuous_fst continuous_snd).measurableSet measurable_const
    (Measurable.ite (isClosed_eq continuous_fst continuous_snd).measurableSet measurable_const measurable_const)

theorem comparisonOracle_measurable {X : Type} [MeasurableSpace X] [MeasurableSpace Ordering]
    (f : X → ℝ) (hf : Measurable f) : Measurable (PaperOracle.comparisonOracle f) :=
  realOrder_measurable.comp ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd))

theorem simulated_policy_measurable {Seed X A : Type}
    [MeasurableSpace Seed] [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Ordering]
    (P : Policy Seed (X × X) Ordering A) (f : X → ℝ) (hf : Measurable f) (budget : ℕ) :
    Measurable (fun seed => PaperOracle.Program.run f (PaperOracle.simulate (P.fromSeed budget seed))) := by
  exact PaperOracle.measurable_output_preserved f (P.fromSeed budget)
    (P.fixed_oracle_output_measurable (PaperOracle.comparisonOracle f) (comparisonOracle_measurable f hf) budget)

theorem simulated_policy_cap {Seed X A : Type}
    [MeasurableSpace Seed] [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Ordering]
    (P : Policy Seed (X × X) Ordering A) (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.Cap (2 * budget) (PaperOracle.simulate (P.fromSeed budget seed)) :=
  PaperOracle.simulate_cap _ (P.fromSeed_cap budget seed)

theorem comparison_factory_measurable {Theta X : Type}
    [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Ordering]
    (F : Theta → X → ℝ) (hF : Measurable (fun x : Theta × X => F x.1 x.2)) :
    Measurable (fun x : Theta × (X × X) => PaperOracle.comparisonOracle (F x.1) x.2) := by
  exact realOrder_measurable.comp
    ((hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (hF.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))

theorem joint_simulated_policy_measurable {Theta Seed X A : Type}
    [MeasurableSpace Theta] [MeasurableSpace Seed] [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace Ordering]
    (P : Policy Seed (X × X) Ordering A)
    (F : Theta → X → ℝ) (hF : Measurable (fun x : Theta × X => F x.1 x.2)) (budget : ℕ) :
    Measurable (fun st : Theta × Seed =>
      PaperOracle.Program.run (F st.1) (PaperOracle.simulate (P.fromSeed budget st.2))) := by
  have hm := P.joint_output_measurable (fun theta => PaperOracle.comparisonOracle (F theta))
    (comparison_factory_measurable F hF) budget
  simpa only [PaperOracle.simulate_output] using hm

end
end PaperBorelPolicy

end SnapshotModule_064
/- END borel_comparison_transfer -/

/- BEGIN two_value_borel_policy -/
section SnapshotModule_065

namespace PaperTwoValuePolicy
open MeasureTheory PaperBorelPolicy PaperRealBorel
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
variable {Seed Q Q' R A : Type} [MeasurableSpace Seed] [MeasurableSpace Q]
  [MeasurableSpace Q'] [MeasurableSpace R] [MeasurableSpace A]

def projectQueries (P : Policy Seed Q R A) (F : Q → Q') (hF : Measurable F) : Policy Seed Q' R A where
  query t st := F (P.query t st)
  output := P.output
  stop := P.stop
  query_measurable t := hF.comp (P.query_measurable t)
  output_measurable := P.output_measurable
  stop_measurable := P.stop_measurable

lemma project_unroll (P : Policy Seed Q R A) (F : Q → Q') (hF : Measurable F)
    (budget t : ℕ) (st : Seed×(Fin t → R)) :
    (projectQueries P F hF).unroll budget t st=
      PaperOracle.Program.mapQueries F (P.unroll budget t st) := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    simp only [Policy.unroll,projectQueries]
    cases hs : P.stop t st
    · simp only [Bool.false_eq_true,↓reduceIte,PaperOracle.Program.mapQueries]
      congr 1
      funext r
      exact ih (t+1) (st.1,Fin.cons r st.2)
    · simp [PaperOracle.Program.mapQueries]

abbrev V (d : ℕ) := PaperCGLine.Vec d
abbrev Param (Seed : Type) [MeasurableSpace Seed] (t : ℕ) := space (Seed×(Fin t → Ordering))

def advance {t : ℕ} (st : ((Seed×(Fin t → Ordering))×ℝ)×ℝ) : Seed×(Fin (t+1) → Ordering) :=
  (st.1.1.1,Fin.cons (PaperOracle.realOrder st.1.2 st.2) st.1.1.2)

lemma advance_measurable (t : ℕ) : Measurable (@advance Seed t) := by
  apply Measurable.prodMk
  · fun_prop
  · apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hfirst : Measurable (fun st : ((Seed×(Fin t → Ordering))×ℝ)×ℝ => st.1.2) := by fun_prop
      exact PaperBorelPolicy.realOrder_measurable.comp (hfirst.prodMk measurable_snd)
    · simpa only [Fin.cons_succ] using
        (show Measurable (fun st : ((Seed×(Fin t → Ordering))×ℝ)×ℝ => st.1.1.2 j) from by fun_prop)

/-- Two legal value requests per original trinary comparison, with every
continuation explicitly Borel on arbitrary real reply histories. -/
def code {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d)) :
    (budget t : ℕ) → Code d (V d) (Param Seed t)
  | 0,t => .pure (P.output t) (P.output_measurable t)
  | budget+1,t => .branch {st | P.stop t st=true} (P.stop_measurable t)
      (.pure (P.output t) (P.output_measurable t))
      (.ask (fun st => ((P.query t st).1,0)) ((P.query_measurable t).fst.prodMk measurable_const)
        (.ask (fun st => ((P.query t st.1).2,0))
          (((P.query_measurable t).comp measurable_fst).snd.prodMk measurable_const)
          (Code.comap advance (advance_measurable t) (code P budget (t+1)))))

lemma code_height {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d)) (budget t : ℕ) :
    Code.height (code P budget t)≤2*budget := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    simp only [code,Code.height,Code.height_comap]
    have hh := ih (t+1)
    omega

lemma code_denote {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d))
    (budget t : ℕ) (st : Seed×(Fin t → Ordering)) :
    PaperOracle.Program.mapQueries Prod.fst (PaperCGLine.Program.toOracle (Code.denote (code P budget t) st))=
      PaperOracle.simulate (P.unroll budget t st) := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    simp only [code,Code.denote,Policy.unroll,Set.mem_setOf_eq]
    split_ifs
    · rfl
    · simp only [PaperCGLine.Program.toOracle,PaperOracle.Program.mapQueries,PaperOracle.simulate]
      congr 1
      funext first
      congr 1
      funext second
      rw [Code.denote_comap]
      exact ih (t+1) (advance ((st,first),second))

def seededCode {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d)) (budget : ℕ) :
    Code d (V d) (space Seed) :=
  Code.comap (fun seed => (seed,Fin.elim0)) (measurable_id.prodMk measurable_const) (code P budget 0)

lemma seededCode_height {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d)) (budget : ℕ) :
    Code.height (seededCode P budget)≤2*budget := by rw [seededCode,Code.height_comap]; exact code_height P budget 0

/-- The actual total Borel exact-value policy, fixed before the objective. -/
def policy {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d)) (budget : ℕ) :
    Policy Seed (V d) ℝ (V d) :=
  projectQueries (seededCode P budget).policy Prod.fst measurable_fst

/-- Equality of entire finite adaptive trees, rather than only final outputs. -/
theorem policy_fromSeed_eq {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d))
    (budget : ℕ) (seed : Seed) :
    (policy P budget).fromSeed (2*budget) seed=PaperOracle.simulate (P.fromSeed budget seed) := by
  unfold policy Policy.fromSeed
  rw [project_unroll]
  change PaperOracle.Program.mapQueries Prod.fst ((seededCode P budget).policy.fromSeed (2*budget) seed)=_
  rw [Code.policy_fromSeed_eq _ _ (seededCode_height P budget)]
  rw [seededCode,Code.denote_comap]
  exact code_denote P budget 0 (seed,Fin.elim0)

theorem output_exact {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d))
    (budget : ℕ) (seed : Seed) (f : V d → ℝ) :
    PaperOracle.Program.run f ((policy P budget).fromSeed (2*budget) seed)=
      PaperOracle.Program.run (PaperOracle.comparisonOracle f) (P.fromSeed budget seed) := by
  rw [policy_fromSeed_eq,PaperOracle.simulate_output]

theorem all_reply_cap {d : ℕ} (P : Policy Seed (V d×V d) Ordering (V d))
    (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.Cap (2*budget) ((policy P budget).fromSeed (2*budget) seed) :=
  (policy P budget).fromSeed_cap (2*budget) seed

end
end PaperTwoValuePolicy

end SnapshotModule_065
/- END two_value_borel_policy -/

/- BEGIN comparison_seed_compression -/
section SnapshotModule_066

/- A comparison policy has only countably many finite trinary histories.
   Its entire seed-dependent decision table is a standard Borel replacement
   seed. This preserves the full tree simultaneously for every objective. -/
namespace PaperSeedCompression
noncomputable section
open MeasureTheory PaperBorelPolicy Set

abbrev History := (t : ℕ) × (Fin t → Ordering)
abbrev Decision (V : Type) := Bool × (V × V) × V
abbrev CompressedSeed (V : Type) := History → Decision V

instance history_countable : Countable History := inferInstance

instance compressedSeed_standardBorel {V : Type} [MeasurableSpace V] [StandardBorelSpace V] :
    StandardBorelSpace (CompressedSeed V) := inferInstance

variable {Seed V : Type} [MeasurableSpace Seed] [MeasurableSpace V]

def encode (P : Policy Seed (V × V) Ordering V) (seed : Seed) : CompressedSeed V :=
  fun i => (P.stop i.1 (seed, i.2), P.query i.1 (seed, i.2), P.output i.1 (seed, i.2))

theorem encode_measurable (P : Policy Seed (V × V) Ordering V) : Measurable (encode P) := by
  apply measurable_pi_lambda
  intro i
  have hs : Measurable (P.stop i.1) := measurable_to_bool (P.stop_measurable i.1)
  exact (hs.comp (measurable_id.prodMk measurable_const)).prodMk
    (((P.query_measurable i.1).comp (measurable_id.prodMk measurable_const)).prodMk
      ((P.output_measurable i.1).comp (measurable_id.prodMk measurable_const)))

def policy : Policy (CompressedSeed V) (V × V) Ordering V where
  query t st := (st.1 ⟨t, st.2⟩).2.1
  output t st := (st.1 ⟨t, st.2⟩).2.2
  stop t st := (st.1 ⟨t, st.2⟩).1
  query_measurable t := measurable_from_prod_countable_left
    (fun h => (measurable_pi_apply (X := fun _ : History => Decision V) ⟨t, h⟩).snd.fst)
  output_measurable t := measurable_from_prod_countable_left
    (fun h => (measurable_pi_apply (X := fun _ : History => Decision V) ⟨t, h⟩).snd.snd)
  stop_measurable t := by
    have hs : Measurable (fun st : CompressedSeed V × (Fin t → Ordering) => (st.1 ⟨t, st.2⟩).1) :=
      measurable_from_prod_countable_left
        (fun h => (measurable_pi_apply (X := fun _ : History => Decision V) ⟨t, h⟩).fst)
    exact hs (measurableSet_singleton true)

theorem unroll_encode (P : Policy Seed (V × V) Ordering V)
    (budget t : ℕ) (seed : Seed) (history : Fin t → Ordering) :
    (policy (V := V)).unroll budget t (encode P seed, history) =
      P.unroll budget t (seed, history) := by
  induction budget generalizing t with
  | zero => rfl
  | succ budget ih =>
    simp only [Policy.unroll, policy, encode]
    split_ifs
    · rfl
    · congr 1
      funext reply
      exact ih (t + 1) (Fin.cons reply history)

theorem fromSeed_encode (P : Policy Seed (V × V) Ordering V) (budget : ℕ) (seed : Seed) :
    (policy (V := V)).fromSeed budget (encode P seed) = P.fromSeed budget seed :=
  unroll_encode P budget 0 seed Fin.elim0

theorem all_reply_cap (budget : ℕ) (seed : CompressedSeed V) :
    PaperOracle.Program.Cap budget ((policy (V := V)).fromSeed budget seed) :=
  (policy (V := V)).fromSeed_cap budget seed

theorem output_exact (P : Policy Seed (V × V) Ordering V)
    (budget : ℕ) (seed : Seed) (f : V → ℝ) :
    PaperOracle.Program.run (PaperOracle.comparisonOracle f)
      ((policy (V := V)).fromSeed budget (encode P seed)) =
      PaperOracle.Program.run (PaperOracle.comparisonOracle f) (P.fromSeed budget seed) := by
  rw [fromSeed_encode]

end
end PaperSeedCompression

end SnapshotModule_066
/- END comparison_seed_compression -/

/- BEGIN lower_bound_transfer -/
section SnapshotModule_067

/- The manuscript's internal lower-bound transfer and uniform joint bracket.
   The two named Dorn contracts below are explicit external premises. -/
namespace PaperLowerBounds
noncomputable section
open Set MeasureTheory PaperBorelPolicy PaperOptimizationModel PaperUniformBudget
open scoped ENNReal

theorem randomized_comparison_to_value (n : ℕ) (beta : NNReal) (R epsilon : ℝ) (T : ℕ)
    (h : RandomizedBudget (admissible n beta R) (success epsilon) T) :
    ValueBudget (admissible n beta R) (success epsilon) (2 * T) := by
  rcases h with ⟨Seed, m, h⟩
  letI := m
  rcases h with ⟨law, hprob, policy, hgood⟩
  letI : IsProbabilityMeasure law := hprob
  let newPolicy := PaperTwoValuePolicy.policy (d := n + 1)
    (PaperSeedCompression.policy (V := PaperGDE.Vec n)) T
  let mappedLaw := law.map (PaperSeedCompression.encode policy)
  have hmapped : IsProbabilityMeasure mappedLaw :=
    Measure.isProbabilityMeasure_map (PaperSeedCompression.encode_measurable policy).aemeasurable
  refine ⟨PaperSeedCompression.CompressedSeed (PaperGDE.Vec n), inferInstance,
    inferInstance, mappedLaw, hmapped, newPolicy, ?_⟩
  intro f hf
  have hcont := admissible_continuous n beta R f hf
  have hout := newPolicy.fixed_oracle_output_measurable f hcont.measurable (2 * T)
  have hmeas : MeasurableSet {seed | success epsilon f
      (PaperOracle.Program.run f (newPolicy.fromSeed (2 * T) seed))} :=
    (admissible_success_set_measurable n beta R epsilon f hf).preimage hout
  refine ⟨hmeas, ?_⟩
  rw [show mappedLaw = law.map (PaperSeedCompression.encode policy) from rfl,
    Measure.map_apply (PaperSeedCompression.encode_measurable policy) hmeas]
  have heq : (PaperSeedCompression.encode policy) ⁻¹'
      {seed | success epsilon f (PaperOracle.Program.run f (newPolicy.fromSeed (2 * T) seed))} =
      {seed | success epsilon f (PaperOracle.Program.run (PaperOracle.comparisonOracle f)
        (policy.fromSeed T seed))} := by
    ext seed
    simp only [Set.mem_preimage, Set.mem_setOf_eq, newPolicy, PaperTwoValuePolicy.output_exact,
      PaperSeedCompression.fromSeed_encode]
  rw [heq]
  exact (hgood f hf).2

theorem randomized_comparison_lower (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) (T : ℕ)
    (hT : RandomizedBudget (admissible n beta R) (success epsilon) T) :
    comparisonLower n Q ≤ (T : ℝ) := by
  have he : epsilon ≤ (beta : ℝ) * R ^ 2 / 32 :=
    epsilon_le_scale_div beta R epsilon Q 32 heps (by norm_num) hQ hQdef
  have hv := randomized_comparison_to_value n beta R epsilon T hT
  have hd := external.lower_bound n beta hb R epsilon hR heps he (2 * T) hv
  rw [← hQdef] at hd
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hd
  have hfirst := (le_max_left _ _).trans hd
  have hsecond := (le_max_right _ _).trans hd
  apply max_le
  · linarith
  · linarith

theorem randomized_comparison_log_lower (external : DornLogarithmicPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : (128 : ℝ) ^ 2 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) (T : ℕ)
    (hT : RandomizedBudget (admissible n beta R) (success epsilon) T) :
    comparisonLogLower n Q ≤ (T : ℝ) := by
  have he : epsilon ≤ (beta : ℝ) * R ^ 2 / (128 : ℝ) ^ 2 :=
    epsilon_le_scale_div beta R epsilon Q ((128 : ℝ) ^ 2) heps (by norm_num) hQ hQdef
  obtain ⟨hmu_nonneg, hratio, hmu_lt, hden⟩ := half_strong_parameter beta hb
  have hv := randomized_comparison_to_value n beta R epsilon T hT
  have hs := valueBudget_restrict (strongLocalization_subset n beta ((beta : ℝ) / 2) R hmu_nonneg) hv
  have hl := external.lower_bound n beta hb R epsilon ((beta : ℝ) / 2)
    hR heps hratio hmu_lt he (2 * T) hs
  rw [← hQdef, hden] at hl
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hl
  dsimp [comparisonLogLower]
  linarith

theorem deterministic_comparison_lower (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) (T : ℕ)
    (hT : DeterministicBudget (admissible n beta R) (success epsilon) T) :
    comparisonLower n Q ≤ (T : ℝ) :=
  randomized_comparison_lower external n beta hb R epsilon Q hR heps hQ hQdef T
    (deterministic_is_randomized _ _ T hT)

theorem randomized_complexity_is_budget
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) :
    RandomizedBudget (admissible n beta R) (success epsilon)
      (randomizedComplexity (admissible n beta R) (success epsilon)) := by
  have hu := (PaperJointUpper.piecewise_uniform_upper n beta hb R epsilon Q hR heps hQ hQdef).1
  change sInf {T : ℕ | RandomizedBudget (admissible n beta R) (success epsilon) T} ∈
    {T : ℕ | RandomizedBudget (admissible n beta R) (success epsilon) T}
  apply Nat.sInf_mem
  exact ⟨PaperJointUpper.jointCap n Q, deterministic_is_randomized _ _ _ hu⟩

theorem randomized_complexity_lower (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) :
    comparisonLower n Q ≤
      (randomizedComplexity (admissible n beta R) (success epsilon) : ℝ) :=
  randomized_comparison_lower external n beta hb R epsilon Q hR heps hQ hQdef _
    (randomized_complexity_is_budget n beta hb R epsilon Q hR heps hQ hQdef)

theorem randomized_complexity_log_lower (external : DornLogarithmicPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : (128 : ℝ) ^ 2 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) :
    comparisonLogLower n Q ≤
      (randomizedComplexity (admissible n beta R) (success epsilon) : ℝ) := by
  have h32 : (32 : ℝ) ≤ Q := by nlinarith
  exact randomized_comparison_log_lower external n beta hb R epsilon Q hR heps hQ hQdef _
    (randomized_complexity_is_budget n beta hb R epsilon Q hR heps h32 hQdef)

/-- Internal joint bracket, conditional on exactly the two explicitly named
external exact-value hardness contracts. The upper witness and all transfers
are proved here; no external lower theorem is counted as proved. -/
theorem conditional_joint_bracket
    (dimensionPremise : DornDimensionAccuracyPremise) (logPremise : DornLogarithmicPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) :
    comparisonLower n Q ≤
        (randomizedComplexity (admissible n beta R) (success epsilon) : ℝ) ∧
      (((128 : ℝ) ^ 2 ≤ Q) → comparisonLogLower n Q ≤
        (randomizedComplexity (admissible n beta R) (success epsilon) : ℝ)) ∧
      randomizedComplexity (admissible n beta R) (success epsilon) ≤
        deterministicComplexity (admissible n beta R) (success epsilon) ∧
      deterministicComplexity (admissible n beta R) (success epsilon) ≤ PaperJointUpper.jointCap n Q ∧
      (PaperJointUpper.jointCap n Q : ℝ) ≤ PaperJointUpper.upperProfile n Q := by
  obtain ⟨hu, hrate⟩ := PaperJointUpper.piecewise_uniform_upper n beta hb R epsilon Q hR heps hQ hQdef
  exact ⟨randomized_complexity_lower dimensionPremise n beta hb R epsilon Q hR heps hQ hQdef,
    fun hlog => randomized_complexity_log_lower logPremise n beta hb R epsilon Q hR heps hlog hQdef,
    PaperOptimizationModel.randomized_complexity_le_deterministic n beta hb R epsilon Q hR heps hQ hQdef,
    deterministic_upper _ _ _ hu, hrate⟩

theorem admissible_success_event_measurable
    {Seed : Type} [MeasurableSpace Seed] (n : ℕ) (beta : NNReal) (R epsilon : ℝ)
    (policy : Policy Seed (PaperGDE.Vec n × PaperGDE.Vec n) Ordering (PaperGDE.Vec n))
    (T : ℕ) (f : PaperGDE.Vec n → ℝ) (hf : f ∈ admissible n beta R) :
    MeasurableSet {seed | success epsilon f (PaperOracle.Program.run
      (PaperOracle.comparisonOracle f) (policy.fromSeed T seed))} := by
  obtain ⟨grad, hg, hc, hLip, a, ha, hmin⟩ := hf
  have hcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x => (hg x).hasFDerivAt.continuousAt)
  have hout := policy.fixed_oracle_output_measurable (PaperOracle.comparisonOracle f)
    (comparison_measurable f hcont.measurable) T
  change MeasurableSet {seed | f (PaperOracle.Program.run
    (PaperOracle.comparisonOracle f) (policy.fromSeed T seed)) - minimum f ≤ epsilon}
  exact measurableSet_le ((hcont.measurable.comp hout).sub measurable_const) measurable_const

/-- For each fixed algorithm below the threshold there is one fixed hard
objective. It is selected before the private seed is realized. -/
theorem fixed_policy_hard_instance (external : DornDimensionAccuracyPremise)
    {Seed : Type} [MeasurableSpace Seed] (law : Measure Seed) (hprob : IsProbabilityMeasure law)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) (T : ℕ)
    (policy : Policy Seed (PaperGDE.Vec n × PaperGDE.Vec n) Ordering (PaperGDE.Vec n))
    (hT : (T : ℝ) < comparisonLower n Q) :
    ∃ f ∈ admissible n beta R,
      law {seed | success epsilon f (PaperOracle.Program.run
        (PaperOracle.comparisonOracle f) (policy.fromSeed T seed))} < (2 / 3 : ℝ≥0∞) := by
  by_contra hnone
  have hgood : ∀ f ∈ admissible n beta R,
      (2 / 3 : ℝ≥0∞) ≤ law {seed | success epsilon f (PaperOracle.Program.run
        (PaperOracle.comparisonOracle f) (policy.fromSeed T seed))} := by
    intro f hf
    by_contra hlt
    exact hnone ⟨f, hf, lt_of_not_ge hlt⟩
  have hbudget : RandomizedBudget (admissible n beta R) (success epsilon) T :=
    ⟨Seed, inferInstance, law, hprob, policy, fun f hf =>
      ⟨admissible_success_event_measurable n beta R epsilon policy T f hf, hgood f hf⟩⟩
  exact (not_le_of_gt hT) (randomized_comparison_lower external n beta hb R epsilon Q
    hR heps hQ hQdef T hbudget)

theorem fixed_policy_log_hard_instance (external : DornLogarithmicPremise)
    {Seed : Type} [MeasurableSpace Seed] (law : Measure Seed) (hprob : IsProbabilityMeasure law)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : (128 : ℝ) ^ 2 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) (T : ℕ)
    (policy : Policy Seed (PaperGDE.Vec n × PaperGDE.Vec n) Ordering (PaperGDE.Vec n))
    (hT : (T : ℝ) < comparisonLogLower n Q) :
    ∃ f ∈ admissible n beta R,
      law {seed | success epsilon f (PaperOracle.Program.run
        (PaperOracle.comparisonOracle f) (policy.fromSeed T seed))} < (2 / 3 : ℝ≥0∞) := by
  by_contra hnone
  have hgood : ∀ f ∈ admissible n beta R,
      (2 / 3 : ℝ≥0∞) ≤ law {seed | success epsilon f (PaperOracle.Program.run
        (PaperOracle.comparisonOracle f) (policy.fromSeed T seed))} := by
    intro f hf
    by_contra hlt
    exact hnone ⟨f, hf, lt_of_not_ge hlt⟩
  have hbudget : RandomizedBudget (admissible n beta R) (success epsilon) T :=
    ⟨Seed, inferInstance, law, hprob, policy, fun f hf =>
      ⟨admissible_success_event_measurable n beta R epsilon policy T f hf, hgood f hf⟩⟩
  exact (not_le_of_gt hT) (randomized_comparison_log_lower external n beta hb R epsilon Q
    hR heps hQ hQdef T hbudget)

theorem unsaturated_accuracy_lower (n : ℕ) (Q : ℝ) (hQ : Q ≤ (n + 1 : ℝ) ^ 2) :
    (n + 1 : ℝ) * Real.sqrt Q / 8192 ≤ comparisonLower n Q := by
  have hsqrt : Real.sqrt Q ≤ (n + 1 : ℝ) :=
    (Real.sqrt_le_left (by positivity : 0 ≤ (n + 1 : ℝ))).mpr hQ
  unfold comparisonLower
  rw [min_eq_right hsqrt]
  simpa only [div_mul_eq_mul_div] using
    (le_max_right (5 * (n + 1 : ℝ) / 32) ((n + 1 : ℝ) / 8192 * Real.sqrt Q))

theorem saturated_accuracy_lower (n : ℕ) (Q : ℝ) (hQ : (n + 1 : ℝ) ^ 2 ≤ Q) :
    (n + 1 : ℝ) ^ 2 / 8192 ≤ comparisonLower n Q := by
  have hsqrt : (n + 1 : ℝ) ≤ Real.sqrt Q :=
    (Real.le_sqrt (by positivity) ((sq_nonneg _).trans hQ)).mpr hQ
  unfold comparisonLower
  rw [min_eq_left hsqrt]
  have heq : (n + 1 : ℝ) ^ 2 / 8192 = (n + 1 : ℝ) / 8192 * (n + 1 : ℝ) := by ring
  rw [heq]
  exact le_max_right _ _

theorem log_accuracy_lower (n : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) :
    (n + 1 : ℝ) * Real.log Q / 8192 ≤ comparisonLogLower n Q := by
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog3two : Real.log (3 : ℝ) ≤ 2 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) using 1 <;> norm_num
  have hfrac : Real.log Q / 2 ≤ Real.log Q / Real.log 3 :=
    div_le_div_of_nonneg_left hlog hlog3 hlog3two
  have hmul := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 3 * (n + 1 : ℝ) / 8000 by positivity)
  have hprod : 0 ≤ (n + 1 : ℝ) * Real.log Q := mul_nonneg (by positivity) hlog
  unfold comparisonLogLower
  nlinarith

theorem high_window_max_lower
    (dimensionPremise : DornDimensionAccuracyPremise) (logPremise : DornLogarithmicPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : (128 : ℝ) ^ 2 ≤ Q)
    (hQdef : Q = (beta : ℝ) * R ^ 2 / epsilon) (hwindow : (n + 1 : ℝ) ^ 2 ≤ Q) :
    max ((n + 1 : ℝ) ^ 2) ((n + 1 : ℝ) * Real.log Q) / 8192 ≤
      (randomizedComplexity (admissible n beta R) (success epsilon) : ℝ) := by
  have h32 : (32 : ℝ) ≤ Q := by nlinarith
  have hpoly := (saturated_accuracy_lower n Q hwindow).trans
    (randomized_complexity_lower dimensionPremise n beta hb R epsilon Q hR heps h32 hQdef)
  have hlog := (log_accuracy_lower n Q (by nlinarith)).trans
    (randomized_complexity_log_lower logPremise n beta hb R epsilon Q hR heps hQ hQdef)
  rcases le_total ((n + 1 : ℝ) ^ 2) ((n + 1 : ℝ) * Real.log Q) with h | h
  · simpa only [max_eq_right h] using hlog
  · simpa only [max_eq_left h] using hpoly

end
end PaperLowerBounds

end SnapshotModule_067
/- END lower_bound_transfer -/

/- BEGIN joint_window_ratios -/
section SnapshotModule_068

namespace PaperJointWindowRatios
open PaperOptimizationModel PaperUniformBudget PaperLowerBounds PaperJointUpper
noncomputable section
set_option maxHeartbeats 1000000

lemma scaled_ratio (s U L F : ℝ) (hs : 0 < s) (hF : 0 ≤ F)
    (hlo : s/8192 ≤ L) (hup : U ≤ F*s) : U/L ≤ 8192*F := by
  have hL : 0 < L := (div_pos hs (by norm_num)).trans_le hlo
  apply (div_le_iff₀ hL).mpr
  have hm:=mul_le_mul_of_nonneg_left hlo (show 0 ≤ 8192*F by positivity)
  nlinarith

lemma deterministic_upper (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) :
    (deterministicComplexity (admissible n beta R) (success epsilon):ℝ) ≤ upperProfile n Q := by
  have hu:=piecewise_uniform_upper n beta hb R epsilon Q hR heps hQ hQdef
  exact (Nat.cast_le.mpr (PaperUniformBudget.deterministic_upper _ _ _ hu.1)).trans hu.2

/-- Actual minimax ratio in the low window, relative only to the named
external dimension/accuracy lower theorem. -/
theorem low_window_ratio (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) (hwindow : Q ≤ (n+1:ℝ)) :
    (deterministicComplexity (admissible n beta R) (success epsilon):ℝ)/
      (randomizedComplexity (admissible n beta R) (success epsilon):ℝ) ≤
        8192*(10:ℝ)^18*(logEnvelope n Q)^3 := by
  have hd1 : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hQ2 : Q ≤ (n+1:ℝ)^2 := by nlinarith
  have hlo:=(unsaturated_accuracy_lower n Q hQ2).trans
    (randomized_complexity_lower external n beta hb R epsilon Q hR heps hQ hQdef)
  have hup:=deterministic_upper n beta hb R epsilon Q hR heps hQ hQdef
  rw [upperProfile,if_pos hwindow] at hup
  have hs : 0 < (n+1:ℝ)*Real.sqrt Q := by positivity
  have hL:=logEnvelope_ge_one n Q hQ
  have hh:=scaled_ratio ((n+1:ℝ)*Real.sqrt Q) _ _ ((10:ℝ)^18*(logEnvelope n Q)^3) hs (by positivity) hlo
    (by convert hup using 1 <;> ring)
  convert hh using 1 <;> ring

/-- The two actually certified complexities leave precisely the paper's middle
residual factor up to the displayed uniform logarithmic power. -/
theorem middle_window_ratio (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) (hloWindow : (n+1:ℝ) < Q) (hhiWindow : Q ≤ (n+1:ℝ)^2) :
    (deterministicComplexity (admissible n beta R) (success epsilon):ℝ)/
      (randomizedComplexity (admissible n beta R) (success epsilon):ℝ) ≤
        8192*(10:ℝ)^18*PaperJointRatios.residual (n+1:ℝ) Q*(logEnvelope n Q)^3 := by
  have hlo:=(unsaturated_accuracy_lower n Q hhiWindow).trans
    (randomized_complexity_lower external n beta hb R epsilon Q hR heps hQ hQdef)
  have hup:=deterministic_upper n beta hb R epsilon Q hR heps hQ hQdef
  rw [upperProfile,if_neg (not_le.mpr hloWindow),if_pos hhiWindow] at hup
  exact PaperJointRatios.middle_ratio_bound (n+1:ℝ) Q _ _ ((10:ℝ)^18) (logEnvelope n Q)
    (by positivity) (by linarith) (by positivity) (by linarith [logEnvelope_ge_one n Q hQ]) hlo hup

/-- The sharp high-window ratio uses only the saturated dimension lower bound;
it does not require the separate logarithmic external premise. -/
theorem high_window_ratio (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) (hwindow : (n+1:ℝ)^2 < Q) :
    (deterministicComplexity (admissible n beta R) (success epsilon):ℝ)/
      (randomizedComplexity (admissible n beta R) (success epsilon):ℝ) ≤
        8192*100000000*Real.log Q*Real.log ((n+1:ℝ)*Real.sqrt Q) := by
  have hd1 : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnQ : (n+1:ℝ) < Q := by nlinarith
  have hlo:=(saturated_accuracy_lower n Q hwindow.le).trans
    (randomized_complexity_lower external n beta hb R epsilon Q hR heps hQ hQdef)
  have hup:=deterministic_upper n beta hb R epsilon Q hR heps hQ hQdef
  rw [upperProfile,if_neg (not_le.mpr hnQ),if_neg (not_le.mpr hwindow)] at hup
  have hroot : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr (by linarith)
  have hlog : 0 ≤ Real.log ((n+1:ℝ)*Real.sqrt Q) := Real.log_nonneg (by nlinarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hh:=scaled_ratio ((n+1:ℝ)^2) _ _ (100000000*Real.log Q*Real.log ((n+1:ℝ)*Real.sqrt Q))
    (by positivity) (by positivity) hlo (by convert hup using 1 <;> ring)
  convert hh using 1 <;> ring

 theorem high_window_log_envelope (external : DornDimensionAccuracyPremise)
    (n : ℕ) (beta : NNReal) (hb : 0 < beta) (R epsilon Q : ℝ)
    (hR : 0 < R) (heps : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q=(beta:ℝ)*R^2/epsilon) (hwindow : (n+1:ℝ)^2 < Q) :
    (deterministicComplexity (admissible n beta R) (success epsilon):ℝ)/
      (randomizedComplexity (admissible n beta R) (success epsilon):ℝ) ≤
        8192*100000000*(logEnvelope n Q)^2 := by
  have hh:=high_window_ratio external n beta hb R epsilon Q hR heps hQ hQdef hwindow
  have hroot : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr (by linarith)
  have hd1 : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hlog : 0 ≤ Real.log ((n+1:ℝ)*Real.sqrt Q) := Real.log_nonneg (by nlinarith)
  have hL:=logEnvelope_ge_one n Q hQ
  have hm:=mul_le_mul (logQ_le_envelope n Q) (logdroot_le_envelope n Q hQ) hlog (by linarith)
  have hm2:=mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 8192*100000000)
  nlinarith

end
end PaperJointWindowRatios

end SnapshotModule_068
/- END joint_window_ratios -/

/- BEGIN kernel_randomization -/
section SnapshotModule_069

namespace PaperKernelRandomization
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory unitInterval
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def randomizedKernel (f : X→I→Y) (hf : Measurable (Function.uncurry f)) : Kernel X Y :=
  (Kernel.id.prod (Kernel.const X (volume : Measure I))).map (Function.uncurry f)

lemma randomizedKernel_apply (f : X→I→Y) (hf : Measurable (Function.uncurry f)) (x : X) :
    randomizedKernel f hf x=(volume : Measure I).map (f x) := by
  rw [randomizedKernel,Kernel.map_apply _ hf,Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,
    Measure.dirac_prod,Measure.map_map hf (by fun_prop)]
  rfl

/-- The standard-Borel randomization lemma is imported as a proved Mathlib
result, with a jointly measurable sampler, not as an external paper premise. -/
theorem conditional_randomization [Nonempty Y] [StandardBorelSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] :
    ∃ f : X→I→Y, ∃ hf : Measurable (Function.uncurry f), randomizedKernel f hf=K := by
  obtain ⟨f,hf,heq⟩:=K.exists_measurable_map_eq_unitInterval
  refine ⟨f,hf,?_⟩
  ext x s hs
  rw [randomizedKernel_apply,heq]

variable {S : Type*} [MeasurableSpace S]
def finiteLaw (K : ℕ→Kernel S S) : ℕ→Kernel S S
  | 0=>Kernel.id
  | n+1=>(K n) ∘ₖ finiteLaw K n

lemma finiteLaw_congr (K L : ℕ→Kernel S S) (heq : ∀n,K n=L n) (n : ℕ) :
    finiteLaw K n=finiteLaw L n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [finiteLaw,finiteLaw,heq n,ih]

/-- Replacing each conditional next-state law by fresh private uniform
randomization preserves every finite transcript-state law. The state may store
all queries, exact replies, stopping flags and outputs for a fixed objective. -/
theorem finite_conditional_randomization [Nonempty S] [StandardBorelSpace S]
    (K : ℕ→Kernel S S) (hK : ∀n,IsMarkovKernel (K n)) :
    ∃ f : ℕ→S→I→S, ∃ hf : ∀n,Measurable (Function.uncurry (f n)),
      (∀n,randomizedKernel (f n) (hf n)=K n) ∧
      ∀n x,finiteLaw (fun j=>randomizedKernel (f j) (hf j)) n x=finiteLaw K n x := by
  have h : ∀n,∃ f : S→I→S,∃hf : Measurable (Function.uncurry f),randomizedKernel f hf=K n := by
    intro n
    letI:=hK n
    exact conditional_randomization (K n)
  choose f hf heq using h
  refine ⟨f,hf,heq,?_⟩
  intro n x
  rw [finiteLaw_congr _ K heq n]

end
end PaperKernelRandomization

end SnapshotModule_069
/- END kernel_randomization -/

/- BEGIN cg_chebyshev -/
section SnapshotModule_070

/- Actual Chebyshev residual polynomials for the exact-line Krylov/CG proof. -/
namespace PaperCGChebyshev

open Polynomial Polynomial.Chebyshev Set

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def theta (Q : ℝ) : ℝ := (Real.sqrt Q-1)/(Real.sqrt Q+1)

noncomputable def spectralCenter (Q : ℝ) : ℝ := (Q+1)/(Q-1)

noncomputable def spectralSlope (Q : ℝ) : ℝ := 2*Q/(Q-1)

theorem sqrt_gt_one (Q : ℝ) (hQ : 1 < Q) : 1 < Real.sqrt Q := by
  have hsq := Real.sq_sqrt (show 0 ≤ Q by linarith)
  nlinarith [Real.sqrt_nonneg Q]

theorem cosh_log_ratio (r : ℝ) (hr : 1 < r) :
    Real.cosh (Real.log ((r+1)/(r-1)))=(r^2+1)/(r^2-1) := by
  have hratio : 0 < (r+1)/(r-1) := by positivity
  have hminus : r-1 ≠ 0 := ne_of_gt (by linarith)
  have hplus : r+1 ≠ 0 := ne_of_gt (by linarith)
  have hsquare : r^2-1 ≠ 0 := ne_of_gt (by nlinarith)
  rw [Real.cosh_log hratio]
  field_simp
  ring

theorem chebyshev_center_lower (Q : ℝ) (hQ : 1 < Q) (n : ℕ) :
    (((Real.sqrt Q+1)/(Real.sqrt Q-1))^n)/2 ≤ (T ℝ (n:ℤ)).eval (spectralCenter Q) := by
  have hr := sqrt_gt_one Q hQ
  have hratio : 0 < (Real.sqrt Q+1)/(Real.sqrt Q-1) := by positivity
  have hcenter : spectralCenter Q=Real.cosh (Real.log ((Real.sqrt Q+1)/(Real.sqrt Q-1))) := by
    rw [cosh_log_ratio _ hr, Real.sq_sqrt (show 0 ≤ Q by linarith)]
    rfl
  rw [hcenter, T_real_cosh]
  have hexp : Real.exp ((n:ℝ)*Real.log ((Real.sqrt Q+1)/(Real.sqrt Q-1))) =
      ((Real.sqrt Q+1)/(Real.sqrt Q-1))^n := by
    rw [Real.exp_nat_mul, Real.exp_log hratio]
  simp only [Int.cast_natCast]
  rw [Real.cosh_eq, hexp]
  linarith [Real.exp_pos (-((n:ℝ)*Real.log ((Real.sqrt Q+1)/(Real.sqrt Q-1))))]

theorem chebyshev_center_pos (Q : ℝ) (hQ : 1 < Q) (n : ℕ) :
    0 < (T ℝ (n:ℤ)).eval (spectralCenter Q) := by
  have hr := sqrt_gt_one Q hQ
  have hlower := chebyshev_center_lower Q hQ n
  have hpos : 0 < (((Real.sqrt Q+1)/(Real.sqrt Q-1))^n)/2 := by positivity
  linarith

theorem chebyshev_center_reciprocal (Q : ℝ) (hQ : 1 < Q) (n : ℕ) :
    1/(T ℝ (n:ℤ)).eval (spectralCenter Q) ≤ 2*(theta Q)^n := by
  have hr := sqrt_gt_one Q hQ
  have hratio : 0 < (Real.sqrt Q+1)/(Real.sqrt Q-1) := by positivity
  have h := one_div_le_one_div_of_le
    (show 0 < (((Real.sqrt Q+1)/(Real.sqrt Q-1))^n)/2 by positivity)
    (chebyshev_center_lower Q hQ n)
  have heq : 1/((((Real.sqrt Q+1)/(Real.sqrt Q-1))^n)/2)=2*(theta Q)^n := by
    have hinverse : ((Real.sqrt Q+1)/(Real.sqrt Q-1))⁻¹=theta Q := by
      unfold theta
      rw [inv_div]
    rw [← hinverse, inv_pow]
    field_simp
  rw [heq] at h
  exact h

noncomputable def residualPolynomial (Q : ℝ) (n : ℕ) : ℝ[X] :=
  C (((T ℝ (n:ℤ)).eval (spectralCenter Q))⁻¹) *
    (T ℝ (n:ℤ)).comp (C (spectralCenter Q)-C (spectralSlope Q)*X)

theorem residual_at_zero (Q : ℝ) (hQ : 1 < Q) (n : ℕ) :
    (residualPolynomial Q n).eval 0=1 := by
  simp only [residualPolynomial, eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero,
    sub_zero]
  exact inv_mul_cancel₀ (ne_of_gt (chebyshev_center_pos Q hQ n))

theorem spectral_affine_interval (Q t : ℝ) (hQ : 1 < Q) (htlow : 1/Q ≤ t) (hthigh : t ≤ 1) :
    |spectralCenter Q-spectralSlope Q*t| ≤ 1 := by
  have hQpos : 0 < Q := by linarith
  have hminus : 0 < Q-1 := by linarith
  have hlower := (div_le_iff₀ hQpos).mp htlow
  have heq : spectralCenter Q-spectralSlope Q*t=(Q+1-2*Q*t)/(Q-1) := by
    unfold spectralCenter spectralSlope
    ring
  rw [heq]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀' hminus).mpr
    nlinarith
  · apply (div_le_iff₀ hminus).mpr
    nlinarith

theorem residual_uniform_bound (Q : ℝ) (hQ : 1 < Q) (n : ℕ) (t : ℝ)
    (htlow : 1/Q ≤ t) (hthigh : t ≤ 1) :
    |(residualPolynomial Q n).eval t| ≤ 2*(theta Q)^n := by
  have hnum := abs_eval_T_real_le_one (n:ℤ) (spectral_affine_interval Q t hQ htlow hthigh)
  have hden := chebyshev_center_pos Q hQ n
  have hreciprocal := chebyshev_center_reciprocal Q hQ n
  simp only [residualPolynomial, eval_mul, eval_C, eval_comp, eval_sub, eval_X, abs_mul,
    abs_inv, abs_of_pos hden]
  have hmul := mul_le_mul_of_nonneg_left hnum (le_of_lt (inv_pos.mpr hden))
  simp only [mul_one] at hmul
  exact hmul.trans (by simpa only [one_div] using hreciprocal)

theorem residual_degree_le (Q : ℝ) (n : ℕ) : (residualPolynomial Q n).natDegree ≤ n := by
  have haffine : (C (spectralCenter Q)-C (spectralSlope Q)*X : ℝ[X]).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  unfold residualPolynomial
  apply (natDegree_C_mul_le _ _).trans
  have hcomp := natDegree_comp_le (p:=T ℝ (n:ℤ)) (q:=C (spectralCenter Q)-C (spectralSlope Q)*X)
  rw [natDegree_T] at hcomp
  simpa only [Int.natAbs_natCast, mul_one] using hcomp.trans (Nat.mul_le_mul_left n haffine)

theorem theta_nonneg (Q : ℝ) (hQ : 1 < Q) : 0 ≤ theta Q := by
  have hr := sqrt_gt_one Q hQ
  unfold theta
  positivity

theorem theta_lt_one (Q : ℝ) (hQ : 1 < Q) : theta Q < 1 := by
  have hr := sqrt_gt_one Q hQ
  unfold theta
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem theta_exp_bound (Q : ℝ) (hQ : 1 < Q) : theta Q ≤ Real.exp (-1/Real.sqrt Q) := by
  have hr := sqrt_gt_one Q hQ
  have hpos : 0 < Real.sqrt Q := by linarith
  have hdiv : (Real.sqrt Q-1)/(Real.sqrt Q+1) ≤ (Real.sqrt Q-1)/Real.sqrt Q :=
    div_le_div_of_nonneg_left (by linarith) hpos (by linarith)
  have heq : (Real.sqrt Q-1)/Real.sqrt Q=1-1/Real.sqrt Q := by field_simp
  have hexp := Real.add_one_le_exp (-1/Real.sqrt Q)
  have hexp' : 1-1/Real.sqrt Q ≤ Real.exp (-1/Real.sqrt Q) := by
    rw [show (-1:ℝ)/Real.sqrt Q+1=1-1/Real.sqrt Q by ring] at hexp
    exact hexp
  rw [heq] at hdiv
  unfold theta
  exact hdiv.trans hexp'

theorem theta_power_decay (Q : ℝ) (hQ : 1 < Q) (n : ℕ) :
    (theta Q)^(2*n) ≤ Real.exp (-(2*(n:ℝ))/Real.sqrt Q) := by
  have h := pow_le_pow_left₀ (theta_nonneg Q hQ) (theta_exp_bound Q hQ) (2*n)
  rw [← Real.exp_nat_mul] at h
  have heq : ((2*n:ℕ):ℝ)*(-1/Real.sqrt Q)= -(2*(n:ℝ))/Real.sqrt Q := by
    push_cast
    ring
  rw [heq] at h
  exact h

noncomputable def acceleratedIterations (Q : ℝ) : ℕ := ⌈Real.sqrt Q*Real.log (2*Q)⌉₊

theorem acceleratedIterations_accuracy (Q : ℝ) (hQ : 1 < Q) :
    2*Real.exp (-(2*(acceleratedIterations Q:ℝ))/Real.sqrt Q) ≤ 1/(2*Q^2) := by
  have hQpos : 0 < Q := by linarith
  have hr : 0 < Real.sqrt Q := by positivity
  have hceil := Nat.le_ceil (Real.sqrt Q*Real.log (2*Q))
  change Real.sqrt Q*Real.log (2*Q) ≤ (acceleratedIterations Q:ℝ) at hceil
  have hexponent : -(2*(acceleratedIterations Q:ℝ))/Real.sqrt Q ≤ -2*Real.log (2*Q) := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hexp2 : Real.exp ((2:ℝ)*Real.log (2*Q))=(2*Q)^2 := by
    simpa [Real.exp_log (by positivity : 0 < 2*Q)] using! Real.exp_nat_mul (Real.log (2*Q)) 2
  have hidentity : 2*Real.exp (-2*Real.log (2*Q))=1/(2*Q^2) := by
    rw [show -2*Real.log (2*Q)= -((2:ℝ)*Real.log (2*Q)) by ring,
      Real.exp_neg, hexp2]
    field_simp
  linarith

end PaperCGChebyshev


end SnapshotModule_070
/- END cg_chebyshev -/

/- BEGIN cg_spectral -/
section SnapshotModule_071

namespace PaperCGSpectral
open Polynomial PaperCGExact
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma aeval_apply_sum (A : Module.End ℝ V) (p : Polynomial ℝ) (k : ℕ)
    (hk : p.natDegree < k) (z : V) :
    (aeval A p) z = ∑ i ∈ Finset.range k, p.coeff i • (A^i) z := by
  rw [aeval_eq_sum_range' hk A]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

lemma aeval_residual_candidate_mem (A : Module.End ℝ V) (b z : V) (hz : A z=b)
    (p : Polynomial ℝ) (k : ℕ) (hdegree : p.natDegree ≤ k) (hzero : p.eval 0=1) :
    z-(aeval A p) z ∈ krylovSpace A b k := by
  have hcoeff : p.coeff 0=1 := by rw [coeff_zero_eq_eval_zero]; exact hzero
  have heval := aeval_apply_sum A p (k+1) (by omega) z
  rw [Finset.sum_range_succ'] at heval
  simp only [hcoeff, pow_zero, Module.End.one_apply, one_smul] at heval
  have hsum : (∑ i ∈ Finset.range k, p.coeff (i+1) • (A^(i+1)) z) ∈ krylovSpace A b k := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨⟨i,Finset.mem_range.mp hi⟩,?_⟩
    simp only [pow_succ, Module.End.mul_apply, hz]
  rw [heval]
  have hid : z - ((∑ i ∈ Finset.range k, p.coeff (i+1) • (A^(i+1)) z)+z) =
      -(∑ i ∈ Finset.range k, p.coeff (i+1) • (A^(i+1)) z) := by abel
  rw [hid]
  exact Submodule.neg_mem _ hsum

lemma repr_aeval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (A : Module.End ℝ V) (lambda : ι → ℝ)
    (heigen : ∀ i, A (basis i)=lambda i • basis i)
    (p : Polynomial ℝ) (z : V) (i : ι) :
    basis.repr ((aeval A p) z) i = p.eval (lambda i) * basis.repr z i := by
  nth_rw 1 [← basis.sum_repr z]
  simp only [map_sum, map_smul]
  simp_rw [Module.End.aeval_apply_of_mem_apply_eq_smul (heigen _)]
  simp only [map_smul, smul_smul]
  simp [basis.repr_self, Pi.single_apply, mul_comm]

lemma energy_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (A : Module.End ℝ V) (lambda : ι → ℝ)
    (heigen : ∀ i, A (basis i)=lambda i • basis i) (z : V) :
    energy A z = ∑ i, lambda i * (basis.repr z i)^2 := by
  have hdiag : ∀ i, basis.repr (A z) i=lambda i * basis.repr z i := by
    intro i
    have h := repr_aeval basis A lambda heigen X z i
    simpa only [aeval_X, eval_X] using h
  rw [energy, ← basis.repr.inner_map_map z (A z), PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hdiag]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma polynomial_energy_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (A : Module.End ℝ V) (lambda : ι → ℝ)
    (heigen : ∀ i, A (basis i)=lambda i • basis i)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (p : Polynomial ℝ) (rho : ℝ) (hbound : ∀ i, |p.eval (lambda i)| ≤ rho) (z : V) :
    energy A ((aeval A p) z) ≤ rho^2 * energy A z := by
  rw [energy_diagonal basis A lambda heigen, energy_diagonal basis A lambda heigen,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [repr_aeval basis A lambda heigen]
  have hsq : (p.eval (lambda i))^2 ≤ rho^2 := by
    nlinarith [sq_nonneg (rho-|p.eval (lambda i)|), abs_nonneg (p.eval (lambda i)),
      sq_abs (p.eval (lambda i)), hbound i]
  have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg (hlambda i) (sq_nonneg (basis.repr z i)))
  nlinarith

open PaperCGChebyshev

noncomputable def scaledResidual (Q M : ℝ) (k : ℕ) : Polynomial ℝ :=
  (residualPolynomial Q k).comp (C M⁻¹*X)

lemma scaledResidual_zero (Q M : ℝ) (hQ : 1 < Q) (k : ℕ) :
    (scaledResidual Q M k).eval 0=1 := by
  simpa [scaledResidual] using residual_at_zero Q hQ k

lemma scaledResidual_degree (Q M : ℝ) (k : ℕ) :
    (scaledResidual Q M k).natDegree ≤ k := by
  have ha : (C M⁻¹*X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have hc := natDegree_comp_le (p:=residualPolynomial Q k) (q:=C M⁻¹*X)
  have hc' := Nat.mul_le_mul (residual_degree_le Q k) ha
  exact hc.trans (by simpa only [mul_one] using hc')

lemma scaledResidual_bound (Q M : ℝ) (hQ : 1 < Q) (hM : 0 < M) (k : ℕ)
    (t : ℝ) (ht : M/Q ≤ t ∧ t ≤ M) :
    |(scaledResidual Q M k).eval t| ≤ 2*(theta Q)^k := by
  simp only [scaledResidual, eval_comp, eval_mul, eval_C, eval_X]
  apply residual_uniform_bound Q hQ k
  · have hh : 1/Q ≤ t/M := by
      apply (le_div_iff₀ hM).mpr
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using ht.1
    simpa only [div_eq_mul_inv, mul_comm] using hh
  · have hh : t/M ≤ 1 := (div_le_one hM).mpr ht.2
    simpa only [div_eq_mul_inv, mul_comm] using hh

lemma energy_neg (A : Module.End ℝ V) (v : V) : energy A (-v)=energy A v := by
  simp [energy]

theorem cg_chebyshev_energy [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b z : V) (hz : A z=b) (Q M : ℝ) (hQ : 1 < Q) (hM : 0 < M)
    (hspectrum : ∀ v, M/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ M*‖v‖^2)
    (k : ℕ) :
    energy A ((stateSequence A b k).x-z) ≤ 4*(theta Q)^(2*k)*energy A z := by
  classical
  let basis := hA.eigenvectorBasis (rfl : Module.finrank ℝ V=Module.finrank ℝ V)
  let lambda := hA.eigenvalues (rfl : Module.finrank ℝ V=Module.finrank ℝ V)
  have heigen : ∀ i, A (basis i)=lambda i • basis i := hA.apply_eigenvectorBasis rfl
  have hevalue : ∀ i, energy A (basis i)=lambda i := by
    intro i
    simp only [energy, heigen i, real_inner_smul_right, real_inner_self_eq_norm_sq,
      basis.orthonormal.norm_eq_one i, one_pow, mul_one]
  have hbnds : ∀ i, M/Q ≤ lambda i ∧ lambda i ≤ M := by
    intro i
    have h := hspectrum (basis i)
    simpa only [hevalue i, basis.orthonormal.norm_eq_one i, one_pow, mul_one] using h
  have hlambda : ∀ i, 0 ≤ lambda i := by
    intro i
    exact (le_of_lt (div_pos hM (by linarith))).trans (hbnds i).1
  let p := scaledResidual Q M k
  let y := z-(aeval A p) z
  have hy : y ∈ krylovSpace A b k :=
    aeval_residual_candidate_mem A b z hz p k (scaledResidual_degree Q M k)
      (scaledResidual_zero Q M hQ k)
  have hmin := krylov_energy_minimal A hA hpositive b z hz k y hy
  have hspec := polynomial_energy_bound basis A lambda heigen hlambda p (2*(theta Q)^k)
    (fun i => scaledResidual_bound Q M hQ hM k (lambda i) (hbnds i)) z
  have hyz : y-z = -(aeval A p) z := by dsimp [y]; abel
  rw [hyz, energy_neg] at hmin
  apply hmin.trans
  convert! hspec using 1
  ring

theorem cg_exponential_energy [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (hA : A.IsSymmetric) (hpositive : PositiveDefinite A)
    (b z : V) (hz : A z=b) (Q M : ℝ) (hQ : 1 < Q) (hM : 0 < M)
    (hspectrum : ∀ v, M/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ M*‖v‖^2)
    (k : ℕ) :
    energy A ((stateSequence A b k).x-z) ≤
      4*Real.exp (-2*(k:ℝ)/Real.sqrt Q)*energy A z := by
  apply (cg_chebyshev_energy A hA hpositive b z hz Q M hQ hM hspectrum k).trans
  have hh : theta Q^(2*k) ≤ Real.exp (-2*(k:ℝ)/Real.sqrt Q) := by
    simpa only [neg_mul] using theta_power_decay Q hQ k
  have hnn := energy_nonnegative A hpositive z
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num)) hnn

end PaperCGSpectral


end SnapshotModule_071
/- END cg_spectral -/

/- BEGIN cg_calibration -/
section SnapshotModule_072

namespace PaperCGLine
open PaperCGExact
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

lemma axis_inner {d : ℕ} (i : Fin d) (v : Vec d) : inner ℝ (axis i) v=v i := by
  simp [axis,PaperCGGaussian.axis,EuclideanSpace.inner_single_left]

lemma axis_ne_zero {d : ℕ} (i : Fin d) : axis i ≠ (0:Vec d) := by
  simp [axis,PaperCGGaussian.axis]

noncomputable def diagonal {d : ℕ} (A : Module.End ℝ (Vec d)) (i : Fin d) : ℝ := (A (axis i)) i

lemma diagonal_pos {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A) (i : Fin d) :
    0 < diagonal A i := by
  simpa only [diagonal,axis_inner] using hpos (axis i) (axis_ne_zero i)

lemma lineRoot_zero_axis {d : ℕ} (A : Module.End ℝ (Vec d)) (b : Vec d) (i : Fin d) :
    lineRoot A b 0 (axis i)=b i/diagonal A i := by
  simp [lineRoot,map_zero,axis_inner,diagonal]

lemma lineRoot_axis {d : ℕ} (A : Module.End ℝ (Vec d)) (b v : Vec d) (i : Fin d) :
    lineRoot A b v (axis i)=(b i-(A v) i)/diagonal A i := by
  simp [lineRoot,axis_inner,diagonal]

lemma calibration_numerator {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (b u : Vec d) (i : Fin d) :
    lineRoot A b 0 u-lineRoot A b (axis i) u=(A u) i/inner ℝ u (A u) := by
  have hs := energy_symmetry A hA u (axis i)
  rw [axis_inner] at hs
  simp only [lineRoot,map_zero,sub_zero,inner_sub_right]
  rw [hs]
  ring

lemma calibration_denominator {d : ℕ} (A : Module.End ℝ (Vec d)) (b u : Vec d) (i : Fin d) :
    lineRoot A b 0 (axis i)-lineRoot A b u (axis i)=(A u) i/diagonal A i := by
  rw [lineRoot_zero_axis,lineRoot_axis]
  ring

lemma calibration_denominator_ne_zero {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A)
    (b u : Vec d) (hrows : ∀ i, (A u) i≠0) (i : Fin d) :
    lineRoot A b 0 (axis i)-lineRoot A b u (axis i)≠0 := by
  rw [calibration_denominator]
  exact div_ne_zero (hrows i) (ne_of_gt (diagonal_pos A hpos i))

lemma calibration_ratio {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b u : Vec d) (hu : u≠0) (hrows : ∀ i, (A u) i≠0) (i : Fin d) :
    (lineRoot A b 0 u-lineRoot A b (axis i) u)/
      (lineRoot A b 0 (axis i)-lineRoot A b u (axis i))=
      diagonal A i/inner ℝ u (A u) := by
  rw [calibration_numerator A hA,calibration_denominator]
  have hd := ne_of_gt (diagonal_pos A hpos i)
  have hU := ne_of_gt (hpos u hu)
  field_simp [hrows i,hd,hU]

lemma scaled_rhs_coordinate {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A)
    (b u : Vec d) (i : Fin d) :
    (diagonal A i/inner ℝ u (A u))*lineRoot A b 0 (axis i)=
      (inner ℝ u (A u))⁻¹*b i := by
  rw [lineRoot_zero_axis]
  have hd := ne_of_gt (diagonal_pos A hpos i)
  field_simp

lemma matvec_coordinate {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A)
    (b u v : Vec d) (i : Fin d) :
    (diagonal A i/inner ℝ u (A u))*(lineRoot A b 0 (axis i)-lineRoot A b v (axis i))=
      (inner ℝ u (A u))⁻¹*(A v) i := by
  rw [calibration_denominator]
  have hd := ne_of_gt (diagonal_pos A hpos i)
  field_simp

lemma matvecProgram_eval {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A)
    (b u v : Vec d) :
    Program.eval (lineRoot A b)
      (matvecProgram (fun i => diagonal A i/inner ℝ u (A u))
        (fun i => lineRoot A b 0 (axis i)) v)=
        ((inner ℝ u (A u))⁻¹ • A) v := by
  simp only [matvecProgram,Program.eval_bind,Program.eval_collect,Program.eval,
    LinearMap.smul_apply]
  ext i
  exact matvec_coordinate A hpos b u v i

lemma calibrationProgram_eval {d : ℕ} (A : Module.End ℝ (Vec d)) (b u : Vec d) :
    Program.eval (lineRoot A b) (calibrationProgram u)=
      fun i => (lineRoot A b 0 (axis i),lineRoot A b (axis i) u,lineRoot A b u (axis i)) := by
  simp only [calibrationProgram,Program.eval_collect,Program.eval]

lemma cgLoop_eval {d : ℕ} (A : Module.End ℝ (Vec d))
    (b : Vec d) (h r : Fin d → ℝ) (L : LineOracle d)
    (hmatvec : ∀ v, Program.eval L (matvecProgram h r v)=A v) :
    ∀ fuel k, Program.eval L (cgLoop h r fuel k (stateSequence A b k))=
      (stateSequence A b (k+fuel)).x := by
  intro fuel
  induction fuel with
  | zero => intro k; simp [cgLoop,Program.eval]
  | succ fuel ih =>
    intro k
    simp only [cgLoop]
    split_ifs with hr
    · exact (stateSequence_stable_after_zero A b k hr (fuel+1)).2.symm
    · rw [Program.eval_bind,hmatvec]
      change Program.eval L (cgLoop h r fuel (k+1) (stateSequence A b (k+1)))=_
      rw [ih]
      rw [show k+1+fuel=k+(fuel+1) by omega]

lemma scaled_symmetric {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (c : ℝ) :
    (c • A).IsSymmetric := by
  intro x y
  simp only [LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right]
  rw [hA x y]

lemma scaled_positive {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A)
    (c : ℝ) (hc : 0 < c) : PositiveDefinite (c • A) := by
  intro v hv
  simp only [LinearMap.smul_apply,real_inner_smul_right]
  exact mul_pos hc (hpos v hv)

lemma algorithm_canonical_eval {d : ℕ}
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b g : Vec d) (hg : g≠0)
    (hrows : ∀ i, (A (NormedSpace.normalize g)) i≠0) (N : ℕ) :
    Program.eval (lineRoot A b) (algorithm g N)=
      (stateSequence ((inner ℝ (NormedSpace.normalize g) (A (NormedSpace.normalize g)))⁻¹ • A)
        ((inner ℝ (NormedSpace.normalize g) (A (NormedSpace.normalize g)))⁻¹ • b) N).x := by
  let u := NormedSpace.normalize g
  have hu : u≠0 := by intro h; exact hg ((NormedSpace.normalize_eq_zero_iff g).mp h)
  have hden : ¬∃ i, lineRoot A b 0 (axis i)-lineRoot A b u (axis i)=0 := by
    push Not
    exact calibration_denominator_ne_zero A hpos b u hrows
  simp only [algorithm,if_neg hg,Program.eval,Program.eval_bind,calibrationProgram_eval]
  change Program.eval (lineRoot A b)
    (if ∃ i, lineRoot A b 0 (axis i)-lineRoot A b u (axis i)=0 then .pure 0 else _) = _
  rw [if_neg hden]
  simp_rw [calibration_ratio A hA hpos b (NormedSpace.normalize g) hu hrows]
  have hrhs : (WithLp.toLp 2 (fun i => diagonal A i/inner ℝ u (A u)*lineRoot A b 0 (axis i)) : Vec d)=
      (inner ℝ u (A u))⁻¹ • b := by
    ext i
    exact scaled_rhs_coordinate A hpos b u i
  rw [hrhs]
  have hcg := cgLoop_eval ((inner ℝ u (A u))⁻¹ • A) ((inner ℝ u (A u))⁻¹ • b)
      (fun i => diagonal A i/inner ℝ u (A u)) (fun i => lineRoot A b 0 (axis i))
      (lineRoot A b) (matvecProgram_eval A hpos b u) N 0
  have hzadd := congrArg (fun j => (stateSequence ((inner ℝ u (A u))⁻¹ • A)
    ((inner ℝ u (A u))⁻¹ • b) j).x) (Nat.zero_add N)
  exact hcg.trans hzadd

lemma algorithm_exact_eval {d : ℕ}
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b : Vec d) (L : LineOracle d) (hL : ExactLineOracle A b L)
    (g : Vec d) (hg : g≠0) (hrows : ∀ i, (A (NormedSpace.normalize g)) i≠0) (N : ℕ) :
    Program.eval L (algorithm g N)=
      (stateSequence ((inner ℝ (NormedSpace.normalize g) (A (NormedSpace.normalize g)))⁻¹ • A)
        ((inner ℝ (NormedSpace.normalize g) (A (NormedSpace.normalize g)))⁻¹ • b) N).x := by
  rw [Program.eval_congr_exact L (lineRoot A b) (algorithm g N) (algorithm_valid L g N) hL]
  exact algorithm_canonical_eval A hA hpos b g hg hrows N

end PaperCGLine

end SnapshotModule_072
/- END cg_calibration -/

/- BEGIN cg_complete -/
section SnapshotModule_073

namespace PaperCGLine
open PaperCGExact PaperCGChebyshev PaperCGSpectral
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

noncomputable def quadratic {d : ℕ} (A : Module.End ℝ (Vec d)) (b x : Vec d) : ℝ :=
  energy A x/2-inner ℝ b x

lemma quadratic_gap {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (b z x : Vec d) (hz : A z=b) :
    quadratic A b x-quadratic A b z=energy A (x-z)/2 := by
  have hs := energy_symmetry A hA x z
  have hc1 := real_inner_comm (A z) x
  have hc2 := real_inner_comm (A z) z
  rw [← hz]
  simp only [quadratic,energy,map_sub,inner_sub_left,inner_sub_right]
  linarith

lemma energy_scaled {d : ℕ} (A : Module.End ℝ (Vec d)) (c : ℝ) (v : Vec d) :
    energy (c • A) v=c*energy A v := by
  simp only [energy,LinearMap.smul_apply,real_inner_smul_right]

lemma positive_injective {d : ℕ} (A : Module.End ℝ (Vec d)) (hpos : PositiveDefinite A) :
    Function.Injective A := by
  intro x y hxy
  by_contra hne
  have hsub : x-y≠0 := sub_ne_zero.mpr hne
  have h := hpos (x-y) hsub
  rw [map_sub,hxy,sub_self,inner_zero_right] at h
  linarith

noncomputable def cgBudget (d : ℕ) (Q : ℝ) : ℕ := min d (acceleratedIterations Q)

lemma cg_original_exponential_gap {d : ℕ}
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b z : Vec d) (hz : A z=b) (Q beta R : ℝ)
    (hQ : 1 < Q) (hbeta : 0 < beta) (hR : 0 ≤ R) (hzR : ‖z‖≤R)
    (hspec : ∀ v, beta/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ beta*‖v‖^2)
    (U : ℝ) (hU : 0 < U) (k : ℕ) :
    quadratic A b ((stateSequence (U⁻¹ • A) (U⁻¹ • b) k).x)-quadratic A b z ≤
      2*beta*R^2*Real.exp (-2*(k:ℝ)/Real.sqrt Q) := by
  let Abar := U⁻¹ • A
  have hbarpos : PositiveDefinite Abar := scaled_positive A hpos U⁻¹ (inv_pos.mpr hU)
  have hbarsym : Abar.IsSymmetric := scaled_symmetric A hA U⁻¹
  have hbarz : Abar z=U⁻¹ • b := by simp [Abar,hz]
  have hbarspec : ∀ v, (beta/U)/Q*‖v‖^2 ≤ energy Abar v ∧
      energy Abar v ≤ (beta/U)*‖v‖^2 := by
    intro v
    rw [show energy Abar v=U⁻¹*energy A v from energy_scaled A U⁻¹ v]
    constructor
    · simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using!
        mul_le_mul_of_nonneg_left (hspec v).1 (le_of_lt (inv_pos.mpr hU))
    · simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using!
        mul_le_mul_of_nonneg_left (hspec v).2 (le_of_lt (inv_pos.mpr hU))
  have hcg := cg_exponential_energy Abar hbarsym hbarpos (U⁻¹ • b) z hbarz Q (beta/U)
    hQ (div_pos hbeta hU) hbarspec k
  have he0 : energy Abar z ≤ (beta/U)*R^2 := by
    apply (hbarspec z).2.trans
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hbeta hU))
    nlinarith [norm_nonneg z]
  have he1 : energy Abar ((stateSequence Abar (U⁻¹ • b) k).x-z) ≤
      4*Real.exp (-2*(k:ℝ)/Real.sqrt Q)*((beta/U)*R^2) :=
    hcg.trans (mul_le_mul_of_nonneg_left he0 (by positivity))
  have hmul := mul_le_mul_of_nonneg_left he1 (le_of_lt (div_pos hU (by norm_num : (0:ℝ)<2)))
  have hcancel : U/2*(U⁻¹*energy A ((stateSequence Abar (U⁻¹ • b) k).x-z))=
      energy A ((stateSequence Abar (U⁻¹ • b) k).x-z)/2 := by field_simp
  have hright : U/2*(4*Real.exp (-2*(k:ℝ)/Real.sqrt Q)*((beta/U)*R^2))=
      2*beta*R^2*Real.exp (-2*(k:ℝ)/Real.sqrt Q) := by field_simp; ring
  rw [show energy Abar ((stateSequence Abar (U⁻¹ • b) k).x-z)=
      U⁻¹*energy A ((stateSequence Abar (U⁻¹ • b) k).x-z) from energy_scaled A U⁻¹ _,
    hcancel,hright] at hmul
  rw [quadratic_gap A hA b z _ hz]
  exact hmul

theorem cg_budget_accuracy {d : ℕ}
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b z : Vec d) (hz : A z=b) (Q beta R epsilon : ℝ)
    (hQ : 32 ≤ Q) (hbeta : 0 < beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQdef : Q=beta*R^2/epsilon) (hzR : ‖z‖≤R)
    (hspec : ∀ v, beta/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ beta*‖v‖^2)
    (U : ℝ) (hU : 0 < U) :
    quadratic A b ((stateSequence (U⁻¹ • A) (U⁻¹ • b) (cgBudget d Q)).x)-quadratic A b z ≤ epsilon/2 := by
  have hbarpos := scaled_positive A hpos U⁻¹ (inv_pos.mpr hU)
  have hbarsym := scaled_symmetric A hA U⁻¹
  have hbarz : (U⁻¹ • A) z=U⁻¹ • b := by simp [hz]
  by_cases hd : d ≤ acceleratedIterations Q
  · have hsolve := finite_termination_solves (U⁻¹ • A) hbarsym hbarpos (U⁻¹ • b)
    have hdim : Module.finrank ℝ (Vec d)=d := by simp [Vec]
    rw [hdim] at hsolve
    have hxz := positive_injective (U⁻¹ • A) hbarpos (hsolve.trans hbarz.symm)
    rw [cgBudget,min_eq_left hd,hxz,sub_self]
    positivity
  · have hn : cgBudget d Q=acceleratedIterations Q := min_eq_right (by omega)
    have hgap := cg_original_exponential_gap A hA hpos b z hz Q beta R
      (by linarith) hbeta (le_of_lt hR) hzR hspec U hU (acceleratedIterations Q)
    have hrate := acceleratedIterations_accuracy Q (by linarith)
    have hbr : 0 ≤ beta*R^2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hrate hbr
    have hrel : beta*R^2=Q*epsilon := by
      rw [hQdef]
      field_simp
    have hsmall : beta*R^2*(1/(2*Q^2))≤epsilon/2 := by
      rw [hrel]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < 2*Q^2)).mpr
      have hQpos : 0 < Q := by linarith
      nlinarith [mul_pos hQpos heps]
    rw [hn]
    apply hgap.trans
    have hmid : 2*beta*R^2*Real.exp (-2*(acceleratedIterations Q:ℝ)/Real.sqrt Q) ≤
        beta*R^2*(1/(2*Q^2)) := by
      simpa only [neg_mul,mul_assoc,mul_comm,mul_left_comm] using! hmul
    exact hmid.trans hsmall

/-- Full success statement on the actual objective-independent Gaussian seed event. -/
theorem exact_line_cg_on_good_seed {d : ℕ}
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b z : Vec d) (hz : A z=b) (Q beta R epsilon : ℝ)
    (hQ : 32 ≤ Q) (hbeta : 0 < beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQdef : Q=beta*R^2/epsilon) (hzR : ‖z‖≤R)
    (hspec : ∀ v, beta/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ beta*‖v‖^2)
    (L : LineOracle d) (hL : ExactLineOracle A b L)
    (g : Vec d) (hg : g≠0) (hrows : ∀ i, (A (NormedSpace.normalize g)) i≠0) :
    quadratic A b (Program.eval L (algorithm g (cgBudget d Q)))-quadratic A b z ≤ epsilon/2 := by
  rw [algorithm_exact_eval A hA hpos b L hL g hg hrows]
  apply cg_budget_accuracy A hA hpos b z hz Q beta R epsilon hQ hbeta hR heps hQdef hzR hspec
  apply hpos
  intro h
  exact hg ((NormedSpace.normalize_eq_zero_iff g).mp h)

/-- The random law does not depend on A or b; for each fixed instance success is almost sure. -/
theorem exact_line_cg_almost_sure (d : ℕ) (hd : 0 < d)
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b z : Vec d) (hz : A z=b) (Q beta R epsilon : ℝ)
    (hQ : 32 ≤ Q) (hbeta : 0 < beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQdef : Q=beta*R^2/epsilon) (hzR : ‖z‖≤R)
    (hspec : ∀ v, beta/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ beta*‖v‖^2)
    (L : LineOracle d) (hL : ExactLineOracle A b L) :
    (∀ᵐ g ∂stdGaussian (Vec d),
      quadratic A b (Program.eval L (algorithm g (cgBudget d Q)))-quadratic A b z ≤ epsilon/2) ∧
    (∀ g, Program.count L (algorithm g (cgBudget d Q)) ≤ 3*d+1+d*cgBudget d Q) ∧
    (∀ g, Program.Valid L (algorithm g (cgBudget d Q))) := by
  refine ⟨?_,fun g => algorithm_pathwise_cap L g _,fun g => algorithm_valid L g _⟩
  have hgauss := PaperCGGaussian.spd_normalized_gaussian_calibration_good d hd
    (LinearMap.toContinuousLinearMap A) hpos
  filter_upwards [hgauss] with g hg
  exact exact_line_cg_on_good_seed A hA hpos b z hz Q beta R epsilon hQ hbeta hR heps
    hQdef hzR hspec L hL g hg.1 hg.2.2

end PaperCGLine


end SnapshotModule_073
/- END cg_complete -/

/- BEGIN cg_line_semantics -/
section SnapshotModule_074

namespace PaperCGLine
open PaperCGExact
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

lemma quadratic_line_expansion {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (b x v : Vec d) (t : ℝ) :
    quadratic A b (x+t • v)=quadratic A b x+
      t*(inner ℝ v (A x)-inner ℝ b v)+t^2*energy A v/2 := by
  simp only [quadratic,energy,map_add,map_smul,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right]
  rw [energy_symmetry A hA x v]
  ring

lemma quadratic_line_completed_square {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b x v : Vec d) (hv : v≠0) (t : ℝ) :
    quadratic A b (x+t • v)-quadratic A b (x+lineRoot A b x v • v)=
      energy A v/2*(t-lineRoot A b x v)^2 := by
  rw [quadratic_line_expansion A hA,quadratic_line_expansion A hA]
  have hd : inner ℝ v (A v)≠0 := ne_of_gt (hpos v hv)
  have hcomm : inner ℝ b v=inner ℝ v b := real_inner_comm _ _
  rw [hcomm]
  unfold lineRoot energy
  rw [inner_sub_right]
  field_simp
  ring

lemma lineRoot_unique_minimizer {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b x v : Vec d) (hv : v≠0) :
    (∀ t : ℝ, quadratic A b (x+lineRoot A b x v • v) ≤ quadratic A b (x+t • v)) ∧
    (∀ t : ℝ, quadratic A b (x+t • v)=quadratic A b (x+lineRoot A b x v • v) ↔
      t=lineRoot A b x v) := by
  have hE : 0 < energy A v := hpos v hv
  constructor
  · intro t
    have h := quadratic_line_completed_square A hA hpos b x v hv t
    nlinarith [sq_nonneg (t-lineRoot A b x v)]
  · intro t
    constructor
    · intro heq
      have h := quadratic_line_completed_square A hA hpos b x v hv t
      rw [heq,sub_self] at h
      have hs : (t-lineRoot A b x v)^2=0 := by nlinarith [sq_nonneg (t-lineRoot A b x v)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · intro ht
      rw [ht]

def MinimizingLineOracle {d : ℕ} (A : Module.End ℝ (Vec d)) (b : Vec d) (L : LineOracle d) : Prop :=
  ∀ x v, v≠0 → ∀ t : ℝ, quadratic A b (x+L x v • v) ≤ quadratic A b (x+t • v)

theorem exactLineOracle_iff_minimizing {d : ℕ} (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b : Vec d) (L : LineOracle d) :
    ExactLineOracle A b L ↔ MinimizingLineOracle A b L := by
  constructor
  · intro hL x v hv t
    rw [hL x v hv]
    exact (lineRoot_unique_minimizer A hA hpos b x v hv).1 t
  · intro hL x v hv
    have hle := hL x v hv (lineRoot A b x v)
    have hge := (lineRoot_unique_minimizer A hA hpos b x v hv).1 (L x v)
    exact (lineRoot_unique_minimizer A hA hpos b x v hv).2 (L x v) |>.mp (le_antisymm hle hge)

/-- Strictly increasing objective postcomposition preserves the exact scalar response. -/
theorem strictly_increasing_same_line_minimizer {d : ℕ}
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b x v : Vec d) (hv : v≠0) (h : ℝ → ℝ) (hh : StrictMono h) (s : ℝ) :
    (∀ t : ℝ, h (quadratic A b (x+s • v)) ≤ h (quadratic A b (x+t • v))) ↔ s=lineRoot A b x v := by
  constructor
  · intro hs
    have hle : quadratic A b (x+s • v)≤quadratic A b (x+lineRoot A b x v • v) :=
      hh.le_iff_le.mp (hs (lineRoot A b x v))
    have hge := (lineRoot_unique_minimizer A hA hpos b x v hv).1 s
    exact (lineRoot_unique_minimizer A hA hpos b x v hv).2 s |>.mp (le_antisymm hle hge)
  · intro hs t
    rw [hs]
    exact hh.monotone ((lineRoot_unique_minimizer A hA hpos b x v hv).1 t)

end PaperCGLine

end SnapshotModule_074
/- END cg_line_semantics -/

/- BEGIN one_query_reduction_policy -/
section SnapshotModule_075

namespace PaperOneQueryReduction
open MeasureTheory PaperOracle PaperBorelPolicy
noncomputable section
variable {Seed Q Q' R A : Type}
  [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace Q']
  [MeasurableSpace R] [MeasurableSpace A]

def mappedHistory (P : Policy Seed Q Ordering A) (reply : Q×R → Ordering) :
    (t : ℕ) → Seed×(Fin t → R) → (Fin t → Ordering)
  | 0,_ => Fin.elim0
  | t+1,st =>
    let prev : Seed×(Fin t → R) := (st.1,fun i => st.2 i.succ)
    let old := mappedHistory P reply t prev
    Fin.cons (reply (P.query t (st.1,old),st.2 0)) old

lemma mappedHistory_cons (P : Policy Seed Q Ordering A) (reply : Q×R → Ordering)
    (t : ℕ) (seed : Seed) (history : Fin t → R) (r : R) :
    mappedHistory P reply (t+1) (seed,Fin.cons r history)=
      Fin.cons (reply (P.query t (seed,mappedHistory P reply t (seed,history)),r))
        (mappedHistory P reply t (seed,history)) := by
  simp only [mappedHistory,Fin.cons_succ,Fin.cons_zero]

lemma mappedHistory_measurable (P : Policy Seed Q Ordering A) (reply : Q×R → Ordering)
    (hr : Measurable reply) (t : ℕ) : Measurable (mappedHistory P reply t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hprev : Measurable (fun st : Seed×(Fin (t+1) → R) =>
        (st.1,(fun i : Fin t => st.2 i.succ))) := by
      apply measurable_fst.prodMk
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply i.succ).comp measurable_snd
    have hold := ih.comp hprev
    have hquery := (P.query_measurable t).comp (measurable_fst.prodMk hold)
    have hreply := hr.comp (hquery.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hreply
    · exact (measurable_pi_apply j).comp hold

def policy (P : Policy Seed Q Ordering A) (query : Q → Q') (reply : Q×R → Ordering)
    (hq : Measurable query) (hr : Measurable reply) : Policy Seed Q' R A where
  query t st := query (P.query t (st.1,mappedHistory P reply t st))
  output t st := P.output t (st.1,mappedHistory P reply t st)
  stop t st := P.stop t (st.1,mappedHistory P reply t st)
  query_measurable t := hq.comp ((P.query_measurable t).comp
    (measurable_fst.prodMk (mappedHistory_measurable P reply hr t)))
  output_measurable t := (P.output_measurable t).comp
    (measurable_fst.prodMk (mappedHistory_measurable P reply hr t))
  stop_measurable t := (P.stop_measurable t).preimage
    (measurable_fst.prodMk (mappedHistory_measurable P reply hr t))

def tree (query : Q → Q') (reply : Q×R → Ordering) :
    Program Q Ordering A → Program Q' R A
  | .done a => .done a
  | .ask q next => .ask (query q) (fun r => tree query reply (next (reply (q,r))))

lemma tree_cap (query : Q → Q') (reply : Q×R → Ordering) (k : ℕ)
    (p : Program Q Ordering A) (hp : Program.Cap k p) : Program.Cap k (tree query reply p) := by
  induction k generalizing p with
  | zero => cases p <;> trivial
  | succ k ih =>
    cases p with
    | done a => trivial
    | ask q next => exact fun r => ih (next (reply (q,r))) (hp _)

lemma tree_run (query : Q → Q') (reply : Q×R → Ordering) (oracle : Q' → R)
    (p : Program Q Ordering A) :
    Program.run oracle (tree query reply p)=
      Program.run (fun q => reply (q,oracle (query q))) p := by
  induction p with
  | done a => rfl
  | ask q next ih => exact ih (reply (q,oracle (query q)))

/-- Exact program-level coupling, including every adaptive query and stop,
for arbitrary real or vector feedback histories. -/
lemma policy_unroll (P : Policy Seed Q Ordering A) (query : Q → Q') (reply : Q×R → Ordering)
    (hq : Measurable query) (hr : Measurable reply) (k t : ℕ) (seed : Seed) (history : Fin t → R) :
    (policy P query reply hq hr).unroll k t (seed,history)=
      tree query reply (P.unroll k t (seed,mappedHistory P reply t (seed,history))) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [Policy.unroll,policy]
    cases hs : P.stop t (seed,mappedHistory P reply t (seed,history))
    · simp only [Bool.false_eq_true,↓reduceIte,tree]
      congr 1
      funext r
      change (policy P query reply hq hr).unroll k (t+1) (seed,Fin.cons r history)=_
      rw [ih,mappedHistory_cons]
    · simp [tree]

lemma fromSeed_eq_tree (P : Policy Seed Q Ordering A) (query : Q → Q') (reply : Q×R → Ordering)
    (hq : Measurable query) (hr : Measurable reply) (budget : ℕ) (seed : Seed) :
    (policy P query reply hq hr).fromSeed budget seed=tree query reply (P.fromSeed budget seed) := by
  rw [Policy.fromSeed,policy_unroll]
  rfl

theorem run_reduced_policy (P : Policy Seed Q Ordering A) (query : Q → Q') (reply : Q×R → Ordering)
    (hq : Measurable query) (hr : Measurable reply) (budget : ℕ) (seed : Seed) (oracle : Q' → R) :
    Program.run oracle ((policy P query reply hq hr).fromSeed budget seed)=
      Program.run (fun q => reply (q,oracle (query q))) (P.fromSeed budget seed) := by
  rw [fromSeed_eq_tree,tree_run]

end
end PaperOneQueryReduction

end SnapshotModule_075
/- END one_query_reduction_policy -/

/- BEGIN quadratic_oracle_reductions -/
section SnapshotModule_076

namespace PaperQuadraticReductions
open Set MeasureTheory PaperCGLine PaperCGExact
open scoped RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000

abbrev V (d : ℕ) := PaperCGLine.Vec d

def mid {d : ℕ} (x y : V d) : V d := (1/2:ℝ) • (x+y)
def halfDifference {d : ℕ} (x y : V d) : V d := (1/2:ℝ) • (x-y)

lemma line_points {d : ℕ} (x y : V d) :
    mid x y+(1:ℝ) • halfDifference x y=x ∧
      mid x y+(-1:ℝ) • halfDifference x y=y := by
  constructor <;> dsimp [mid,halfDifference] <;> module

lemma polarization {d : ℕ} (A : Module.End ℝ (V d)) (hA : A.IsSymmetric) (b x y : V d) :
    quadratic A b x-quadratic A b y=inner ℝ (x-y) (A (mid x y)-b) := by
  have hp := quadratic_line_expansion A hA b (mid x y) (halfDifference x y) 1
  have hm := quadratic_line_expansion A hA b (mid x y) (halfDifference x y) (-1)
  rw [(line_points x y).1] at hp
  rw [(line_points x y).2] at hm
  norm_num at hp hm
  have hi : inner ℝ (x-y) (A (mid x y)-b)=
      2*(inner ℝ (halfDifference x y) (A (mid x y))-inner ℝ b (halfDifference x y)) := by
    simp only [halfDifference,real_inner_smul_left,real_inner_smul_right,inner_sub_right]
    rw [real_inner_comm b (x-y)]
    simp only [inner_sub_right]
    ring
  linarith

lemma realOrder_sub (a b : ℝ) : PaperOracle.realOrder a b=PaperOracle.realOrder (a-b) 0 := by
  unfold PaperOracle.realOrder
  simp only [sub_lt_zero,sub_eq_zero]

lemma realOrder_positive_mul (a b c : ℝ) (hc : 0<c) :
    PaperOracle.realOrder (c*a) (c*b)=PaperOracle.realOrder a b := by
  have h := PaperOracle.realOrder_positive_division (c*a) (c*b) c hc
  simpa [mul_div_cancel_left₀ _ hc.ne'] using h.symm

lemma comparison_from_direction {d : ℕ} (A : Module.End ℝ (V d)) (hA : A.IsSymmetric)
    (b x y : V d) :
    PaperOracle.realOrder (inner ℝ (x-y) (NormedSpace.normalize (A (mid x y)-b))) 0=
      PaperOracle.comparisonOracle (quadratic A b) (x,y) := by
  change PaperOracle.realOrder (inner ℝ (x-y) (NormedSpace.normalize (A (mid x y)-b))) 0=
    PaperOracle.realOrder (quadratic A b x) (quadratic A b y)
  rw [realOrder_sub (quadratic A b x) (quadratic A b y),polarization A hA b x y]
  by_cases hz : A (mid x y)-b=0
  · simp [hz,NormedSpace.normalize]
  · have hn : 0<‖A (mid x y)-b‖ := norm_pos_iff.mpr hz
    have hh := PaperOracle.realOrder_positive_division
      (inner ℝ (x-y) (A (mid x y)-b)) 0 ‖A (mid x y)-b‖ hn
    simpa only [NormedSpace.normalize,real_inner_smul_right,zero_div,div_eq_mul_inv,mul_comm,zero_mul,mul_zero] using hh

lemma line_polarization {d : ℕ} (A : Module.End ℝ (V d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b x y : V d) (hxy : x≠y) :
    quadratic A b x-quadratic A b y=
      (2*inner ℝ (halfDifference x y) (A (halfDifference x y)))*(-lineRoot A b (mid x y) (halfDifference x y)) := by
  have hv : halfDifference x y≠0 := smul_ne_zero (by norm_num) (sub_ne_zero.mpr hxy)
  have hp : 0 < inner ℝ (halfDifference x y) (A (halfDifference x y)) := hpos _ hv
  rw [polarization A hA b x y]
  unfold lineRoot
  have hi : inner ℝ (x-y) (A (mid x y)-b)=2*inner ℝ (halfDifference x y) (A (mid x y)-b) := by
    simp only [halfDifference,real_inner_smul_left]
    ring
  rw [hi,inner_sub_right,inner_sub_right]
  field_simp [hp.ne']
  <;> ring

lemma comparison_from_line {d : ℕ} (A : Module.End ℝ (V d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b x y : V d) (hxy : x≠y) :
    PaperOracle.realOrder (-lineRoot A b (mid x y) (halfDifference x y)) 0=
      PaperOracle.comparisonOracle (quadratic A b) (x,y) := by
  change PaperOracle.realOrder (-lineRoot A b (mid x y) (halfDifference x y)) 0=
    PaperOracle.realOrder (quadratic A b x) (quadratic A b y)
  rw [realOrder_sub (quadratic A b x) (quadratic A b y),line_polarization A hA hpos b x y hxy]
  have hv : halfDifference x y≠0 := smul_ne_zero (by norm_num) (sub_ne_zero.mpr hxy)
  have hc : 0<2*inner ℝ (halfDifference x y) (A (halfDifference x y)) := by
    have hh := hpos (halfDifference x y) hv
    linarith
  have hh := realOrder_positive_mul (-lineRoot A b (mid x y) (halfDifference x y)) 0
    (2*inner ℝ (halfDifference x y) (A (halfDifference x y))) hc
  simpa only [mul_zero] using hh.symm

def directionQuery {d : ℕ} (q : V d×V d) : V d := mid q.1 q.2
def directionReply {d : ℕ} (qr : (V d×V d)×V d) : Ordering :=
  PaperOracle.realOrder (inner ℝ (qr.1.1-qr.1.2) qr.2) 0

def lineQuery {d : ℕ} (fallback : V d) (q : V d×V d) : V d×V d := by
  classical
  exact (mid q.1 q.2,if q.1=q.2 then fallback else halfDifference q.1 q.2)

def lineReply {d : ℕ} (qr : (V d×V d)×ℝ) : Ordering := by
  classical
  exact if qr.1.1=qr.1.2 then .eq else PaperOracle.realOrder (-qr.2) 0

lemma directionQuery_measurable (d : ℕ) : Measurable (@directionQuery d) := by
  unfold directionQuery mid
  fun_prop

lemma directionReply_measurable (d : ℕ) : Measurable (@directionReply d) := by
  unfold directionReply
  have hm : Measurable (fun qr : (V d×V d)×V d => inner ℝ (qr.1.1-qr.1.2) qr.2) := by fun_prop
  exact PaperBorelPolicy.realOrder_measurable.comp (hm.prodMk measurable_const)

lemma lineQuery_measurable {d : ℕ} (fallback : V d) : Measurable (lineQuery fallback) := by
  classical
  unfold lineQuery mid halfDifference
  apply Measurable.prodMk
  · fun_prop
  · exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const (by fun_prop)

lemma lineReply_measurable (d : ℕ) : Measurable (@lineReply d) := by
  classical
  unfold lineReply
  have he : MeasurableSet {qr : (V d×V d)×ℝ | qr.1.1=qr.1.2} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hm : Measurable (fun qr : (V d×V d)×ℝ => -qr.2) := by fun_prop
  exact Measurable.ite he measurable_const
    (PaperBorelPolicy.realOrder_measurable.comp (hm.prodMk measurable_const))

lemma lineQuery_nonzero {d : ℕ} (fallback : V d) (hf : fallback≠0) (q : V d×V d) :
    (lineQuery fallback q).2≠0 := by
  classical
  simp only [lineQuery]
  split_ifs with hxy
  · exact hf
  · exact smul_ne_zero (by norm_num) (sub_ne_zero.mpr hxy)

lemma induced_direction_oracle {d : ℕ} (A : Module.End ℝ (V d)) (hA : A.IsSymmetric) (b : V d) :
    (fun q : V d×V d => directionReply (q,NormedSpace.normalize (A (directionQuery q)-b)))=
      PaperOracle.comparisonOracle (quadratic A b) := by
  funext q
  exact comparison_from_direction A hA b q.1 q.2

lemma induced_line_oracle {d : ℕ} (A : Module.End ℝ (V d)) (hA : A.IsSymmetric)
    (hpos : PositiveDefinite A) (b fallback : V d) (hf : fallback≠0)
    (L : LineOracle d) (hL : ExactLineOracle A b L) :
    (fun q : V d×V d => lineReply (q,L (lineQuery fallback q).1 (lineQuery fallback q).2))=
      PaperOracle.comparisonOracle (quadratic A b) := by
  classical
  funext q
  by_cases hxy : q.1=q.2
  · simp [lineReply,hxy,PaperOracle.comparisonOracle,PaperOracle.realOrder]
  · simp only [lineQuery,lineReply,if_neg hxy]
    have hv : halfDifference q.1 q.2≠0 := by
      unfold halfDifference
      exact smul_ne_zero (by norm_num : (1/2:ℝ)≠0) (sub_ne_zero.mpr hxy)
    rw [hL (mid q.1 q.2) (halfDifference q.1 q.2) hv]
    exact comparison_from_line A hA hpos b q.1 q.2 hxy

lemma strictly_increasing_comparisons {d : ℕ} (f : V d → ℝ) (phi : ℝ → ℝ) (hphi : StrictMono phi) :
    PaperOracle.comparisonOracle (phi ∘ f)=PaperOracle.comparisonOracle f := by
  funext q
  unfold PaperOracle.comparisonOracle PaperOracle.realOrder
  simp only [Function.comp_apply,hphi.lt_iff_lt,hphi.injective.eq_iff]

end
end PaperQuadraticReductions

end SnapshotModule_076
/- END quadratic_oracle_reductions -/

/- BEGIN quadratic_policy_simulations -/
section SnapshotModule_077

namespace PaperOracle.Program
variable {Q R A : Type}
def AllQueries (valid : Q → Prop) : Program Q R A → Prop
  | .done _ => True
  | .ask q next => valid q ∧ ∀ r, AllQueries valid (next r)

lemma trace_valid (valid : Q → Prop) (p : Program Q R A) (hp : AllQueries valid p)
    (C : Q → R) : ∀ q ∈ trace C p, valid q := by
  induction p with
  | done a => simp [trace]
  | ask q next ih =>
    intro q' hq'
    rcases List.mem_cons.mp hq' with heq | hmem
    · simpa only [heq] using hp.1
    · exact ih (C q) (hp.2 _) q' hmem
end PaperOracle.Program

namespace PaperQuadraticReductions
open Set MeasureTheory PaperCGLine PaperCGExact PaperBorelPolicy
noncomputable section
variable {Seed A : Type} [MeasurableSpace Seed] [MeasurableSpace A]

def directionPolicy {d : ℕ} (P : Policy Seed (V d×V d) Ordering A) : Policy Seed (V d) (V d) A :=
  PaperOneQueryReduction.policy P directionQuery directionReply
    (directionQuery_measurable d) (directionReply_measurable d)

def linePolicy {d : ℕ} (P : Policy Seed (V d×V d) Ordering A) (fallback : V d) :
    Policy Seed (V d×V d) ℝ A :=
  PaperOneQueryReduction.policy P (lineQuery fallback) lineReply
    (lineQuery_measurable fallback) (lineReply_measurable d)

/-- One exact oriented direction response simulates one comparison, online with
the same seed. A stationary gradient has the canonical zero-vector response. -/
theorem direction_simulation_output {d : ℕ} (P : Policy Seed (V d×V d) Ordering A)
    (M : Module.End ℝ (V d)) (hM : M.IsSymmetric) (b : V d) (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.run (fun x => NormedSpace.normalize (M x-b))
      ((directionPolicy P).fromSeed budget seed)=
      PaperOracle.Program.run (PaperOracle.comparisonOracle (quadratic M b)) (P.fromSeed budget seed) := by
  rw [directionPolicy,PaperOneQueryReduction.run_reduced_policy,induced_direction_oracle M hM b]

/-- The exact-line simulation uses a fixed public nonzero fallback on x=y;
no zero direction is ever queried, and one original node costs one line query. -/
theorem line_simulation_output {d : ℕ} (P : Policy Seed (V d×V d) Ordering A)
    (M : Module.End ℝ (V d)) (hM : M.IsSymmetric) (hpos : PositiveDefinite M)
    (b fallback : V d) (hf : fallback≠0) (L : LineOracle d) (hL : ExactLineOracle M b L)
    (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.run (fun q : V d×V d => L q.1 q.2) ((linePolicy P fallback).fromSeed budget seed)=
      PaperOracle.Program.run (PaperOracle.comparisonOracle (quadratic M b)) (P.fromSeed budget seed) := by
  rw [linePolicy,PaperOneQueryReduction.run_reduced_policy,induced_line_oracle M hM hpos b fallback hf L hL]

lemma line_tree_all_queries {d : ℕ} (fallback : V d) (hf : fallback≠0)
    (p : PaperOracle.Program (V d×V d) Ordering A) :
    PaperOracle.Program.AllQueries (fun q : V d×V d => q.2≠0)
      (PaperOneQueryReduction.tree (lineQuery fallback) lineReply p) := by
  induction p with
  | done a => trivial
  | ask q next ih => exact ⟨lineQuery_nonzero fallback hf q,fun r => ih _⟩

theorem line_policy_all_queries {d : ℕ} (P : Policy Seed (V d×V d) Ordering A)
    (fallback : V d) (hf : fallback≠0) (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.AllQueries (fun q : V d×V d => q.2≠0)
      ((linePolicy P fallback).fromSeed budget seed) := by
  rw [linePolicy,PaperOneQueryReduction.fromSeed_eq_tree]
  exact line_tree_all_queries fallback hf _

theorem line_policy_public_cap {d : ℕ} (P : Policy Seed (V d×V d) Ordering A)
    (fallback : V d) (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.Cap budget ((linePolicy P fallback).fromSeed budget seed) :=
  (linePolicy P fallback).fromSeed_cap budget seed

theorem direction_policy_public_cap {d : ℕ} (P : Policy Seed (V d×V d) Ordering A)
    (budget : ℕ) (seed : Seed) :
    PaperOracle.Program.Cap budget ((directionPolicy P).fromSeed budget seed) :=
  (directionPolicy P).fromSeed_cap budget seed

lemma line_success_event {d : ℕ} (P : Policy Seed (V d×V d) Ordering A)
    (M : Module.End ℝ (V d)) (hM : M.IsSymmetric) (hpos : PositiveDefinite M)
    (b fallback : V d) (hf : fallback≠0) (L : LineOracle d) (hL : ExactLineOracle M b L)
    (budget : ℕ) (success : A → Prop) :
    {seed | success (PaperOracle.Program.run (fun q : V d×V d => L q.1 q.2)
      ((linePolicy P fallback).fromSeed budget seed))}=
    {seed | success (PaperOracle.Program.run (PaperOracle.comparisonOracle (quadratic M b))
      (P.fromSeed budget seed))} := by
  ext seed
  simp only [Set.mem_setOf_eq,line_simulation_output P M hM hpos b fallback hf L hL budget seed]

end
end PaperQuadraticReductions

end SnapshotModule_077
/- END quadratic_policy_simulations -/

/- BEGIN cg_rates -/
section SnapshotModule_078

namespace PaperCGLine
open PaperCGChebyshev
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

lemma logQ_lower (Q : ℝ) (hQ : 32 ≤ Q) : 1 ≤ Real.log Q := by
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
  have hf := Real.log_le_log (show (0:ℝ)<4 by norm_num) (show 4≤Q by linarith)
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow] at hf
  norm_num at hf
  linarith

lemma acceleratedIterations_uniform (Q : ℝ) (hQ : 32 ≤ Q) :
    (acceleratedIterations Q:ℝ) ≤ 3*Real.sqrt Q*Real.log Q := by
  have hQpos : 0 < Q := by linarith
  have hs : 1 ≤ Real.sqrt Q := by
    nlinarith [Real.sq_sqrt (le_of_lt hQpos),Real.sqrt_nonneg Q]
  have hlog := logQ_lower Q hQ
  have hlog2 : Real.log (2:ℝ) ≤ Real.log Q := Real.log_le_log (by norm_num) (by linarith)
  have hlogprod : Real.log (2*Q)=Real.log 2+Real.log Q :=
    Real.log_mul (by norm_num) (ne_of_gt hQpos)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt Q*Real.log (2*Q) by
    apply mul_nonneg (Real.sqrt_nonneg Q)
    exact le_of_lt (Real.log_pos (by linarith)))
  change (acceleratedIterations Q:ℝ)<Real.sqrt Q*Real.log (2*Q)+1 at hc
  rw [hlogprod] at hc
  have h1 := mul_le_mul_of_nonneg_left hlog2 (Real.sqrt_nonneg Q)
  have h2 : 1 ≤ Real.sqrt Q*Real.log Q := by nlinarith
  nlinarith

lemma cgBudget_uniform (d : ℕ) (Q : ℝ) (hQ : 32 ≤ Q) :
    (cgBudget d Q:ℝ) ≤ 3*min (d:ℝ) (Real.sqrt Q*Real.log Q) := by
  have hleft : (cgBudget d Q:ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.min_le_left d (acceleratedIterations Q)
  have hright : (cgBudget d Q:ℝ) ≤ (acceleratedIterations Q:ℝ) := by
    exact_mod_cast Nat.min_le_right d (acceleratedIterations Q)
  have hnn : 0 ≤ (d:ℝ) := by positivity
  by_cases hd : (d:ℝ) ≤ Real.sqrt Q*Real.log Q
  · rw [min_eq_left hd]
    linarith
  · rw [min_eq_right (by linarith : Real.sqrt Q*Real.log Q ≤ (d:ℝ))]
    exact hright.trans (by nlinarith [acceleratedIterations_uniform Q hQ])

/-- A single absolute constant bounds the exact cap for every positive d and Q>=32. -/
theorem conditioned_cg_cap_uniform (d : ℕ) (hd : 0 < d) (Q : ℝ) (hQ : 32 ≤ Q) :
    ((3*d+1+d*cgBudget d Q:ℕ):ℝ) ≤
      7*(d:ℝ)*min (d:ℝ) (Real.sqrt Q*Real.log Q) := by
  have hd1 : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt Q := by
    nlinarith [Real.sq_sqrt (show 0≤Q by linarith),Real.sqrt_nonneg Q]
  have hlog := logQ_lower Q hQ
  have hmin : 1 ≤ min (d:ℝ) (Real.sqrt Q*Real.log Q) := by
    apply le_min hd1
    nlinarith
  have hN := cgBudget_uniform d Q hQ
  have hprod := mul_le_mul_of_nonneg_left hN (show 0 ≤ (d:ℝ) by positivity)
  have hbase := mul_le_mul_of_nonneg_left hmin (show 0 ≤ (d:ℝ) by positivity)
  push_cast
  nlinarith

theorem conditioned_cg_program_uniform {d : ℕ} (hd : 0 < d) (L : LineOracle d)
    (g : Vec d) (Q : ℝ) (hQ : 32 ≤ Q) :
    (Program.count L (algorithm g (cgBudget d Q)):ℝ) ≤
      7*(d:ℝ)*min (d:ℝ) (Real.sqrt Q*Real.log Q) := by
  exact (show (Program.count L (algorithm g (cgBudget d Q)):ℝ) ≤
    ((3*d+1+d*cgBudget d Q:ℕ):ℝ) by exact_mod_cast algorithm_pathwise_cap L g _).trans
      (conditioned_cg_cap_uniform d hd Q hQ)

theorem dimension_one_cap (L : LineOracle 1) (g : Vec 1) (Q : ℝ) :
    Program.count L (algorithm g (cgBudget 1 Q)) ≤ 5 := by
  have h := algorithm_pathwise_cap L g (cgBudget 1 Q)
  have hn : cgBudget 1 Q ≤ 1 := Nat.min_le_left _ _
  omega

end PaperCGLine

end SnapshotModule_078
/- END cg_rates -/

/- BEGIN cg_measurable -/
section SnapshotModule_079

namespace PaperCGLine
open PaperCGExact MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

theorem measurable_stateSequence_scaled {d : ℕ} (A : Module.End ℝ (Vec d)) (b : Vec d) :
    ∀ k, Measurable (fun c : ℝ => (stateSequence (c • A) (c • b) k).x) ∧
      Measurable (fun c : ℝ => (stateSequence (c • A) (c • b) k).r) ∧
      (∀ i, Measurable (fun c : ℝ => (stateSequence (c • A) (c • b) k).p i)) ∧
      (∀ i, Measurable (fun c : ℝ => (stateSequence (c • A) (c • b) k).ap i)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨measurable_const,?_,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
    change Measurable (fun c : ℝ => c • b)
    fun_prop
  | succ k ih =>
    rcases ih with ⟨hx,hr,hp,hap⟩
    let state := fun c : ℝ => stateSequence (c • A) (c • b) k
    have hnew : Measurable (fun c : ℝ => newDirection (state c)) := by
      unfold newDirection orthogonalize
      apply hr.sub
      apply Finset.measurable_sum
      intro i hi
      exact ((hr.inner (𝕜:=ℝ) (hap i)).div ((hp i).inner (𝕜:=ℝ) (hap i))).smul (hp i)
    have himage : Measurable (fun c : ℝ => (c • A) (newDirection (state c))) := by
      simp only [LinearMap.smul_apply]
      exact measurable_id.smul ((LinearMap.toContinuousLinearMap A).continuous.measurable.comp hnew)
    have halpha : Measurable (fun c : ℝ => stepLength (state c) ((c • A) (newDirection (state c)))) :=
      (hr.inner (𝕜:=ℝ) hnew).div (hnew.inner (𝕜:=ℝ) himage)
    refine ⟨?_,?_,?_,?_⟩
    · exact hx.add (halpha.smul hnew)
    · exact hr.sub (halpha.smul himage)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [stateSequence,advance,Fin.snoc_last] using hnew
      · simpa only [stateSequence,advance,Fin.snoc_castSucc] using hp j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [stateSequence,advance,Fin.snoc_last] using himage
      · simpa only [stateSequence,advance,Fin.snoc_castSucc] using hap j

theorem measurable_ideal_seed_output {d : ℕ} (A : Module.End ℝ (Vec d)) (b : Vec d) (N : ℕ) :
    Measurable (fun g : Vec d =>
      (stateSequence ((inner ℝ (NormedSpace.normalize g) (A (NormedSpace.normalize g)))⁻¹ • A)
        ((inner ℝ (NormedSpace.normalize g) (A (NormedSpace.normalize g)))⁻¹ • b) N).x) := by
  apply (measurable_stateSequence_scaled A b N).1.comp
  have hn : Measurable (NormedSpace.normalize : Vec d → Vec d) := PaperCGGaussian.measurable_normalize
  exact (hn.inner (𝕜:=ℝ) ((LinearMap.toContinuousLinearMap A).continuous.measurable.comp hn)).inv

theorem algorithm_aemeasurable (d : ℕ) (hd : 0 < d)
    (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric) (hpos : PositiveDefinite A)
    (b : Vec d) (L : LineOracle d) (hL : ExactLineOracle A b L) (N : ℕ) :
    AEMeasurable (fun g : Vec d => Program.eval L (algorithm g N)) (stdGaussian (Vec d)) := by
  apply (measurable_ideal_seed_output A b N).aemeasurable.congr
  have hgauss := PaperCGGaussian.spd_normalized_gaussian_calibration_good d hd (LinearMap.toContinuousLinearMap A) hpos
  filter_upwards [hgauss] with g hg
  exact (algorithm_exact_eval A hA hpos b L hL g hg.1 hg.2.2 N).symm

end PaperCGLine

end SnapshotModule_079
/- END cg_measurable -/

/- BEGIN cg_public_theorem -/
section SnapshotModule_080

namespace PaperCGLine
open PaperCGExact PaperCGChebyshev
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-- Literal conditioned exact-line CG theorem. The oracle premise is a genuine line
    minimum, not an assumed root formula, matrix-vector product or convergence estimate.
    Complete A-reorthogonalization implements the exact Krylov-minimizing CG iterate;
    only one new matvec is queried at each nonterminal iteration. -/
theorem conditioned_exact_line_cg
    (d : ℕ) (hd : 0 < d) (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (b z : Vec d) (hz : A z=b) (Q beta R epsilon : ℝ)
    (hQ : 32 ≤ Q) (hbeta : 0 < beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQdef : Q=beta*R^2/epsilon) (hzR : ‖z‖≤R)
    (hspec : ∀ v, beta/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ beta*‖v‖^2)
    (L : LineOracle d) (hL : MinimizingLineOracle A b L) :
    (∃ event : Set (Vec d), MeasurableSet event ∧ stdGaussian (Vec d) event=1 ∧
      ∀ g ∈ event, quadratic A b (Program.eval L (algorithm g (cgBudget d Q)))-quadratic A b z ≤ epsilon/2) ∧
    AEMeasurable (fun g : Vec d => Program.eval L (algorithm g (cgBudget d Q))) (stdGaussian (Vec d)) ∧
    (∀ g, Program.Valid L (algorithm g (cgBudget d Q))) ∧
    (∀ g, Program.count L (algorithm g (cgBudget d Q)) ≤ 3*d+1+d*cgBudget d Q) ∧
    (∀ g, (Program.count L (algorithm g (cgBudget d Q)):ℝ) ≤
      7*(d:ℝ)*min (d:ℝ) (Real.sqrt Q*Real.log Q)) := by
  have hpos : PositiveDefinite A := by
    intro v hv
    have hp : 0 < beta/Q*‖v‖^2 :=
      mul_pos (div_pos hbeta (by linarith)) (sq_pos_of_pos (norm_pos_iff.mpr hv))
    exact lt_of_lt_of_le hp (hspec v).1
  have hroot : ExactLineOracle A b L := (exactLineOracle_iff_minimizing A hA hpos b L).mpr hL
  refine ⟨?_,algorithm_aemeasurable d hd A hA hpos b L hroot _,
    fun g => algorithm_valid L g _,fun g => algorithm_pathwise_cap L g _,
    fun g => conditioned_cg_program_uniform hd L g Q hQ⟩
  let Ac : Vec d →L[ℝ] Vec d := LinearMap.toContinuousLinearMap A
  refine ⟨{g | PaperCGGaussian.GoodCalibrationSeed Ac g},
    PaperCGGaussian.goodCalibrationSeed_measurable d Ac,
    PaperCGGaussian.goodCalibrationSeed_probability_one d hd Ac hpos,?_⟩
  intro g hg
  exact exact_line_cg_on_good_seed A hA hpos b z hz Q beta R epsilon hQ hbeta hR heps
    hQdef hzR hspec L hroot g hg.1 hg.2.2

end PaperCGLine

end SnapshotModule_080
/- END cg_public_theorem -/

/- BEGIN cg_borel_state -/
section SnapshotModule_081

namespace PaperCGBorel
open MeasureTheory PaperCGLine PaperCGExact PaperRealBorel
open scoped RealInnerProductSpace
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev Packed (d k : ℕ) := Vec d × Vec d × (Fin k → Vec d) × (Fin k → Vec d)
def pack {d k : ℕ} (s : State (Vec d) k) : Packed d k := (s.x,s.r,s.p,s.ap)
instance stateMeasurableSpace (d k : ℕ) : MeasurableSpace (State (Vec d) k) :=
  MeasurableSpace.comap pack inferInstance

lemma measurable_pack (d k : ℕ) : Measurable (pack : State (Vec d) k → Packed d k) := comap_measurable _
lemma measurable_x (d k : ℕ) : Measurable (fun s : State (Vec d) k => s.x) :=
  measurable_fst.comp (measurable_pack d k)
lemma measurable_r (d k : ℕ) : Measurable (fun s : State (Vec d) k => s.r) :=
  measurable_fst.comp (measurable_snd.comp (measurable_pack d k))
lemma measurable_p (d k : ℕ) : Measurable (fun s : State (Vec d) k => s.p) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_pack d k)))
lemma measurable_ap (d k : ℕ) : Measurable (fun s : State (Vec d) k => s.ap) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_pack d k)))

lemma measurable_newDirection (d k : ℕ) : Measurable (newDirection : State (Vec d) k → Vec d) := by
  unfold newDirection orthogonalize
  apply (measurable_r d k).sub
  apply Finset.measurable_sum
  intro i hi
  have hp := (measurable_pi_apply i).comp (measurable_p d k)
  have hap := (measurable_pi_apply i).comp (measurable_ap d k)
  exact (((measurable_r d k).inner (𝕜:=ℝ) hap).div (hp.inner (𝕜:=ℝ) hap)).smul hp

lemma measurable_initial (d : ℕ) : Measurable (initialState : Vec d → State (Vec d) 0) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun b : Vec d => ((0:Vec d),b,(Fin.elim0 : Fin 0 → Vec d),(Fin.elim0 : Fin 0 → Vec d)))
  fun_prop

lemma measurable_advance (d k : ℕ) :
    Measurable (fun si : State (Vec d) k × Vec d => advance si.1 si.2) := by
  have hx : Measurable (fun si : State (Vec d) k × Vec d => si.1.x) := (measurable_x d k).comp measurable_fst
  have hr : Measurable (fun si : State (Vec d) k × Vec d => si.1.r) := (measurable_r d k).comp measurable_fst
  have hp : Measurable (fun si : State (Vec d) k × Vec d => newDirection si.1) := (measurable_newDirection d k).comp measurable_fst
  have ha : Measurable (fun si : State (Vec d) k × Vec d => stepLength si.1 si.2) :=
    (hr.inner (𝕜:=ℝ) hp).div (hp.inner (𝕜:=ℝ) measurable_snd)
  apply measurable_comap_iff.mpr
  change Measurable (fun si : State (Vec d) k × Vec d =>
    (si.1.x+stepLength si.1 si.2 • newDirection si.1,
     si.1.r-stepLength si.1 si.2 • si.2,
     (Fin.snoc si.1.p (newDirection si.1) : Fin (k+1) → Vec d),
     (Fin.snoc si.1.ap si.2 : Fin (k+1) → Vec d)))
  apply Measurable.prodMk (hx.add (ha.smul hp))
  apply Measurable.prodMk (hr.sub (ha.smul measurable_snd))
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hp
    · simpa only [Fin.snoc_castSucc] using!
        ((measurable_pi_apply j).comp ((measurable_p d k).comp measurable_fst))
  · apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd : State (Vec d) k × Vec d → Vec d))
    · simpa only [Fin.snoc_castSucc] using!
        ((measurable_pi_apply j).comp ((measurable_ap d k).comp measurable_fst))

lemma residual_zero_measurable (d k : ℕ) : MeasurableSet {s : State (Vec d) k | s.r=0} :=
  measurableSet_eq_fun (measurable_r d k) measurable_const

end PaperCGBorel

end SnapshotModule_081
/- END cg_borel_state -/

/- BEGIN cg_borel_code -/
section SnapshotModule_082

namespace PaperCGBorel
open MeasureTheory PaperCGLine PaperCGExact PaperRealBorel
open scoped RealInnerProductSpace
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

abbrev Params (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ)
abbrev MatState (d : ℕ) := Params d × Vec d
abbrev LoopState (d k : ℕ) := Params d × State (Vec d) k
abbrev CalState (d : ℕ) := (Vec d × ℝ) × (Fin d → ℝ × ℝ × ℝ)

noncomputable def matvecCode (d : ℕ) : Code d (Vec d) (space (MatState d)) :=
  Code.bind (Code.collect d (fun i => Code.query
    (fun st : MatState d => (st.2,axis i)) (measurable_snd.prodMk measurable_const)))
    (.pure (fun st : MatState d × (Fin d → ℝ) =>
      WithLp.toLp 2 (fun i => st.1.1.1 i*(st.1.1.2 i-st.2 i))) (by
      apply (WithLp.measurable_toLp 2 _).comp
      apply measurable_pi_lambda
      intro i
      fun_prop))

theorem denote_matvecCode (d : ℕ) (st : MatState d) :
    Code.denote (matvecCode d) st=matvecProgram st.1.1 st.1.2 st.2 := by
  simp only [matvecCode,Code.denote_bind,Code.denote_collect,Code.denote_query,Code.denote,matvecProgram]

noncomputable def calibrationCode (d : ℕ) : Code d (Fin d → ℝ×ℝ×ℝ) (space (Vec d)) :=
  Code.collect d (fun i => .ask (fun _ : Vec d => (0,axis i)) measurable_const
    (.ask (fun ur : Vec d × ℝ => (axis i,ur.1)) (measurable_const.prodMk measurable_fst)
      (.ask (fun urp : (Vec d × ℝ) × ℝ => (urp.1.1,axis i))
        ((measurable_fst.comp measurable_fst).prodMk measurable_const)
        (.pure (fun urps : ((Vec d × ℝ) × ℝ) × ℝ => (urps.1.1.2,urps.1.2,urps.2))
          (by fun_prop)))))

theorem denote_calibrationCode (d : ℕ) (u : Vec d) :
    Code.denote (calibrationCode d) u=calibrationProgram u := by
  simp only [calibrationCode,Code.denote_collect,Code.denote,calibrationProgram]

noncomputable def loopCode (d : ℕ) : (fuel k : ℕ) → Code d (Vec d) (space (LoopState d k))
  | 0,k => .pure (fun st => st.2.x) ((measurable_x d k).comp measurable_snd)
  | fuel+1,k => .branch {st | st.2.r=0}
      ((residual_zero_measurable d k).preimage measurable_snd)
      (.pure (fun st => st.2.x) ((measurable_x d k).comp measurable_snd))
      (Code.bind (Code.comap (fun st : LoopState d k => (st.1,newDirection st.2))
        (measurable_fst.prodMk ((measurable_newDirection d k).comp measurable_snd)) (matvecCode d))
        (Code.comap (fun st : LoopState d k × Vec d => (st.1.1,advance st.1.2 st.2))
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_advance d k).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
          (loopCode d fuel (k+1))))

theorem denote_loopCode (d fuel k : ℕ) (st : LoopState d k) :
    Code.denote (loopCode d fuel k) st=cgLoop st.1.1 st.1.2 fuel k st.2 := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    simp only [loopCode,Code.denote,Code.denote_bind,Code.denote_comap,denote_matvecCode,cgLoop,
      Set.mem_setOf_eq]
    split_ifs
    · rfl
    · congr 1
      funext image
      exact ih _ _

noncomputable def calibratedH {d : ℕ} (st : CalState d) (i : Fin d) : ℝ :=
  (st.1.2-(st.2 i).2.1)/((st.2 i).1-(st.2 i).2.2)
noncomputable def calibratedR {d : ℕ} (st : CalState d) (i : Fin d) : ℝ := (st.2 i).1
noncomputable def calibratedB {d : ℕ} (st : CalState d) : Vec d :=
  WithLp.toLp 2 (fun i => calibratedH st i*calibratedR st i)

lemma calibratedH_measurable (d : ℕ) : Measurable (calibratedH : CalState d → Fin d → ℝ) := by
  apply measurable_pi_lambda
  intro i
  unfold calibratedH
  fun_prop
lemma calibratedR_measurable (d : ℕ) : Measurable (calibratedR : CalState d → Fin d → ℝ) := by
  apply measurable_pi_lambda
  intro i
  unfold calibratedR
  fun_prop
lemma calibratedB_measurable (d : ℕ) : Measurable (calibratedB : CalState d → Vec d) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp (calibratedH_measurable d)).mul
    ((measurable_pi_apply i).comp (calibratedR_measurable d))
lemma bad_calibration_measurable (d : ℕ) :
    MeasurableSet {st : CalState d | ∃ i, (st.2 i).1-(st.2 i).2.2=0} := by
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  apply measurableSet_eq_fun _ measurable_const
  fun_prop

/-- Objective-independent, total real-response code for the frozen CG algorithm. -/
noncomputable def algorithmCode (d N : ℕ) : Code d (Vec d) (space (Vec d)) :=
  .branch {g | g=0} (measurableSet_eq_fun measurable_id measurable_const) (.pure (fun _ => 0) measurable_const)
    (.ask (fun g : Vec d => (0,NormedSpace.normalize g))
      (measurable_const.prodMk (PaperCGGaussian.measurable_normalize (E:=Vec d)))
      (Code.bind (Code.comap (S:=space (Vec d)) (T:=(space (Vec d)).prod (space ℝ))
        (fun gP : Vec d × ℝ => NormedSpace.normalize gP.1)
        ((PaperCGGaussian.measurable_normalize (E:=Vec d)).comp measurable_fst) (calibrationCode d))
        (.branch {st | ∃ i, (st.2 i).1-(st.2 i).2.2=0} (bad_calibration_measurable d)
          (.pure (fun _ => 0) measurable_const)
          (Code.comap (fun st : CalState d => ((calibratedH st,calibratedR st),initialState (calibratedB st)))
            (((calibratedH_measurable d).prodMk (calibratedR_measurable d)).prodMk
              ((measurable_initial d).comp (calibratedB_measurable d))) (loopCode d N 0)))))

theorem denote_algorithmCode (d N : ℕ) (g : Vec d) :
    Code.denote (algorithmCode d N) g=algorithm g N := by
  simp only [algorithmCode,Code.denote,Code.denote_bind,Code.denote_comap,denote_calibrationCode,
    denote_loopCode,algorithm,Set.mem_setOf_eq]
  split_ifs
  · rfl
  · congr 1

theorem height_matvecCode (d : ℕ) : Code.height (matvecCode d)=d := by
  simp [matvecCode,Code.height_bind,Code.height_collect,Code.query,Code.height]

theorem height_calibrationCode (d : ℕ) : Code.height (calibrationCode d)=3*d := by
  simp [calibrationCode,Code.height_collect,Code.height,Nat.mul_comm]

theorem height_loopCode (d fuel k : ℕ) : Code.height (loopCode d fuel k)=d*fuel := by
  induction fuel generalizing k with
  | zero => simp [loopCode,Code.height]
  | succ fuel ih =>
    simp only [loopCode,Code.height,Code.height_bind,Code.height_comap,height_matvecCode,ih,
      Nat.max_eq_right (Nat.zero_le _)]
    simp only [Nat.mul_succ]
    omega

theorem height_algorithmCode (d N : ℕ) : Code.height (algorithmCode d N)=3*d+1+d*N := by
  simp only [algorithmCode,Code.height,Code.height_bind,Code.height_comap,height_calibrationCode,
    height_loopCode,Nat.max_eq_right (Nat.zero_le _)]
  omega

theorem algorithm_syntactic_cap (d N : ℕ) (g : Vec d) :
    Code.Cap (3*d+1+d*N) (algorithm g N) := by
  rw [← denote_algorithmCode d N g,← height_algorithmCode d N]
  exact Code.denote_cap _ _

end PaperCGBorel

end SnapshotModule_082
/- END cg_borel_code -/

/- BEGIN cg_borel_public -/
section SnapshotModule_083

namespace PaperCGBorel
open MeasureTheory ProbabilityTheory PaperCGLine PaperCGExact PaperRealBorel
open scoped RealInnerProductSpace
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-- Fixed before the objective, with total Borel maps on every real history. -/
noncomputable def algorithmPolicy (d N : ℕ) :
    PaperBorelPolicy.Policy (Vec d) (Vec d × Vec d) ℝ (Vec d) := (algorithmCode d N).policy

theorem algorithmPolicy_realizes (d N : ℕ) (g : Vec d) :
    (algorithmPolicy d N).fromSeed (3*d+1+d*N) g=Program.toOracle (algorithm g N) := by
  rw [algorithmPolicy,Code.policy_fromSeed_eq _ _ (le_of_eq (height_algorithmCode d N)) g,
    denote_algorithmCode]

theorem algorithmPolicy_run (d N : ℕ) (L : LineOracle d) (g : Vec d) :
    PaperOracle.Program.run (fun q => L q.1 q.2) ((algorithmPolicy d N).fromSeed (3*d+1+d*N) g)=
      Program.eval L (algorithm g N) := by
  rw [algorithmPolicy_realizes]
  exact Program.run_toOracle L _

theorem algorithmPolicy_count (d N : ℕ) (L : LineOracle d) (g : Vec d) :
    (PaperOracle.Program.trace (fun q => L q.1 q.2)
      ((algorithmPolicy d N).fromSeed (3*d+1+d*N) g)).length=Program.count L (algorithm g N) := by
  rw [algorithmPolicy_realizes]
  exact Program.count_toOracle L _

/-- Exact next-query, stop, and output identification for arbitrary real histories,
    including histories inconsistent with any objective. Newest response is first. -/
theorem algorithmPolicy_history (d N t : ℕ) (g : Vec d) (h : Fin t → ℝ) :
    let f := Program.observe (Program.resumeList (algorithm g N) (List.ofFn h).reverse)
    (algorithmPolicy d N).query t (g,h)=f.elim id (fun _ => (0,0)) ∧
    (algorithmPolicy d N).stop t (g,h)=f.elim (fun _ => false) (fun _ => true) ∧
    (algorithmPolicy d N).output t (g,h)=f.elim (fun _ => 0) id := by
  simp only [algorithmPolicy,Code.policy_query_eq,Code.policy_output_eq,Code.policy_stop_eq,
    Code.reverseFront,denote_algorithmCode]
  simp

lemma lineRoot_measurable (d : ℕ) (A : Module.End ℝ (Vec d)) (b : Vec d) :
    Measurable (fun q : Vec d × Vec d => lineRoot A b q.1 q.2) := by
  have hAx : Measurable (fun q : Vec d × Vec d => A q.1) :=
    (LinearMap.toContinuousLinearMap A).continuous.measurable.comp measurable_fst
  have hAv : Measurable (fun q : Vec d × Vec d => A q.2) :=
    (LinearMap.toContinuousLinearMap A).continuous.measurable.comp measurable_snd
  exact (measurable_snd.inner (𝕜:=ℝ) (measurable_const.sub hAx)).div
    (measurable_snd.inner (𝕜:=ℝ) hAv)

theorem algorithm_measurable (d N : ℕ) (A : Module.End ℝ (Vec d)) (b : Vec d)
    (L : LineOracle d) (hL : ExactLineOracle A b L) :
    Measurable (fun g : Vec d => Program.eval L (algorithm g N)) := by
  have heq : (fun g : Vec d => Program.eval L (algorithm g N))=
      (fun g : Vec d => Program.eval (lineRoot A b) (algorithm g N)) := by
    funext g
    exact Program.eval_congr_exact L (lineRoot A b) _ (algorithm_valid L g N) hL
  rw [heq]
  simpa only [denote_algorithmCode] using!
    Code.eval_measurable (algorithmCode d N) (lineRoot A b) (lineRoot_measurable d A b)

/-- Replaces the earlier AE-only output certificate by a total Borel history policy.
    The policy is the named objective-independent algorithmPolicy above; its complete
    unrolled request tree equals the frozen actual CG program, before any oracle is chosen. -/
theorem conditioned_exact_line_cg_borel
    (d : ℕ) (hd : 0 < d) (A : Module.End ℝ (Vec d)) (hA : A.IsSymmetric)
    (b z : Vec d) (hz : A z=b) (Q beta R epsilon : ℝ)
    (hQ : 32 ≤ Q) (hbeta : 0 < beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQdef : Q=beta*R^2/epsilon) (hzR : ‖z‖≤R)
    (hspec : ∀ v, beta/Q*‖v‖^2 ≤ energy A v ∧ energy A v ≤ beta*‖v‖^2)
    (L : LineOracle d) (hL : MinimizingLineOracle A b L) :
    let N := cgBudget d Q
    let cap := 3*d+1+d*N
    let P := algorithmPolicy d N
    (∀ g, P.fromSeed cap g=Program.toOracle (algorithm g N)) ∧
    Measurable (fun g : Vec d => PaperOracle.Program.run (fun q => L q.1 q.2) (P.fromSeed cap g)) ∧
    (∃ event : Set (Vec d), MeasurableSet event ∧ stdGaussian (Vec d) event=1 ∧
      ∀ g ∈ event, quadratic A b
        (PaperOracle.Program.run (fun q => L q.1 q.2) (P.fromSeed cap g))-quadratic A b z ≤ epsilon/2) ∧
    (∀ g, PaperOracle.Program.Cap cap (P.fromSeed cap g)) ∧
    (∀ g, (PaperOracle.Program.trace (fun q => L q.1 q.2) (P.fromSeed cap g)).length ≤ cap) ∧
    (∀ g, ((PaperOracle.Program.trace (fun q => L q.1 q.2) (P.fromSeed cap g)).length:ℝ) ≤
      7*(d:ℝ)*min (d:ℝ) (Real.sqrt Q*Real.log Q)) ∧
    (∀ g, Program.Valid L (algorithm g N)) := by
  dsimp only
  have hpos : PositiveDefinite A := by
    intro v hv
    exact lt_of_lt_of_le
      (mul_pos (div_pos hbeta (by linarith)) (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hspec v).1
  have hroot : ExactLineOracle A b L := (exactLineOracle_iff_minimizing A hA hpos b L).mpr hL
  have hold := conditioned_exact_line_cg d hd A hA b z hz Q beta R epsilon hQ hbeta hR heps hQdef hzR hspec L hL
  refine ⟨algorithmPolicy_realizes d _,?_,?_,?_,?_,?_,hold.2.2.1⟩
  · simpa only [algorithmPolicy_run] using! algorithm_measurable d (cgBudget d Q) A b L hroot
  · obtain ⟨event,hmeas,hprob,hsuccess⟩ := hold.1
    refine ⟨event,hmeas,hprob,?_⟩
    intro g hg
    rw [algorithmPolicy_run]
    exact hsuccess g hg
  · exact fun g => (algorithmPolicy d _).fromSeed_cap _ g
  · intro g
    rw [algorithmPolicy_count]
    exact algorithm_pathwise_cap L g _
  · intro g
    rw [algorithmPolicy_count]
    exact conditioned_cg_program_uniform hd L g Q hQ

end PaperCGBorel

end SnapshotModule_083
/- END cg_borel_public -/

/- BEGIN reflection_complete -/
section SnapshotModule_084

/-!
Phase 2: reflection geometry and the executed comparison-only endpoint search.
All statements below use the actual branch recursion and its query counter.
The comparison reply contract specifies exact comparisons, including ties.
-/

namespace PaperReflection

open Set

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem strict_reflection_return_interval
    {phi : ℝ → ℝ} {b t : ℝ}
    (hphi : StrictConvexOn ℝ univ phi)
    (hsym : ∀ x, phi (b - x) = phi x) :
    phi t ≤ phi 0 ↔ t ∈ Icc (min 0 b) (max 0 b) := by
  have hb : phi b = phi 0 := by simpa using hsym 0
  constructor
  · intro ht
    by_contra hout
    have hout' : t < min 0 b ∨ max 0 b < t := by
      simpa only [mem_Icc, not_and_or, not_le] using hout
    rcases hout' with hleft | hright
    · have ht0 : t < 0 := lt_of_lt_of_le hleft (min_le_left _ _)
      have htb : t < b := lt_of_lt_of_le hleft (min_le_right _ _)
      have hstrict := hphi.lt_on_openSegment (mem_univ t) (mem_univ (b-t))
        (show t ≠ b-t by linarith)
        (Ioo_subset_openSegment (show 0 ∈ Ioo t (b-t) by constructor <;> linarith))
      have : phi 0 < phi t := by simpa only [hsym t, max_self] using hstrict
      exact (not_lt_of_ge ht) this
    · have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) hright
      have hbt : b < t := lt_of_le_of_lt (le_max_right _ _) hright
      have hstrict := hphi.lt_on_openSegment (mem_univ (b-t)) (mem_univ t)
        (show b-t ≠ t by linarith)
        (Ioo_subset_openSegment (show 0 ∈ Ioo (b-t) t by constructor <;> linarith))
      have : phi 0 < phi t := by simpa only [hsym t, max_self] using hstrict
      exact (not_lt_of_ge ht) this
  · intro ht
    have hseg : t ∈ segment ℝ 0 b := by
      rw [segment_eq_Icc']
      exact ht
    have := hphi.convexOn.le_on_segment (mem_univ 0) (mem_univ b) hseg
    simpa only [hb, max_self] using this

theorem strict_mono_reflection_return
    {phi Phi : ℝ → ℝ} {b t : ℝ}
    (hphi : StrictConvexOn ℝ univ phi)
    (hsym : ∀ x, phi (b-x) = phi x) (hPhi : StrictMono Phi) :
    Phi (phi t) ≤ Phi (phi 0) ↔ t ∈ Icc (min 0 b) (max 0 b) := by
  rw [hPhi.le_iff_le]
  exact strict_reflection_return_interval hphi hsym

theorem positive_return_threshold
    {phi Phi : ℝ → ℝ} {b s : ℝ}
    (hphi : StrictConvexOn ℝ univ phi)
    (hsym : ∀ x, phi (b-x) = phi x) (hPhi : StrictMono Phi) (hs : 0 ≤ s) :
    Phi (phi s) ≤ Phi (phi 0) ↔ s ≤ max b 0 := by
  rw [strict_mono_reflection_return hphi hsym hPhi]
  constructor
  · intro h
    simpa only [max_comm] using h.2
  · intro h
    exact ⟨(min_le_left 0 b).trans hs, by simpa only [max_comm] using h⟩

theorem negative_return_threshold
    {phi Phi : ℝ → ℝ} {b s : ℝ}
    (hphi : StrictConvexOn ℝ univ phi)
    (hsym : ∀ x, phi (b-x) = phi x) (hPhi : StrictMono Phi) (hs : 0 ≤ s) :
    Phi (phi (-s)) ≤ Phi (phi 0) ↔ s ≤ max (-b) 0 := by
  rw [strict_mono_reflection_return hphi hsym hPhi]
  by_cases hb : 0 ≤ b
  · rw [min_eq_left hb, max_eq_right hb, max_eq_right (by linarith : -b ≤ 0)]
    constructor
    · intro h; linarith [h.1]
    · intro h; constructor <;> linarith
  · have hb' : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
    rw [min_eq_right hb', max_eq_left hb', max_eq_left (by linarith : 0 ≤ -b)]
    constructor
    · intro h; linarith [h.1]
    · intro h; constructor <;> linarith

structure BracketResult where
  low : ℝ
  high : ℝ
  queries : ℕ

structure EndpointResult where
  estimate : ℝ
  queries : ℕ

/-- Each recursive step consumes exactly one weak-comparison reply at its midpoint. -/
noncomputable def bisect (oracle : ℝ → Bool) : ℕ → ℝ → ℝ → BracketResult
  | 0, l, u => ⟨l, u, 0⟩
  | n+1, l, u =>
    let mid := (l+u)/2
    let next := if oracle mid = true then bisect oracle n mid u else bisect oracle n l mid
    ⟨next.low, next.high, next.queries+1⟩

theorem bisect_queries (oracle : ℝ → Bool) (n : ℕ) (l u : ℝ) :
    (bisect oracle n l u).queries = n := by
  induction n generalizing l u with
  | zero => rfl
  | succ n ih =>
    simp only [bisect]
    split_ifs <;> simp only [ih]

theorem bisect_bracket
    (oracle : ℝ → Bool) (endpoint : ℝ)
    (hcontract : ∀ s, 0 ≤ s → (oracle s = true ↔ s ≤ endpoint))
    (n : ℕ) (l u : ℝ) (hl : 0 ≤ l) (hle : l ≤ endpoint) (heu : endpoint ≤ u) :
    let out := bisect oracle n l u
    0 ≤ out.low ∧ out.low ≤ endpoint ∧ endpoint ≤ out.high ∧
      out.high-out.low = (u-l)/(2:ℝ)^n := by
  induction n generalizing l u with
  | zero => simp [bisect, hl, hle, heu]
  | succ n ih =>
    have hlu : l ≤ u := hle.trans heu
    have hmid : 0 ≤ (l+u)/2 := by linarith
    simp only [bisect]
    split_ifs with hreply
    · have hme := (hcontract _ hmid).mp hreply
      have hsub := ih ((l+u)/2) u hmid hme heu
      dsimp at hsub ⊢
      refine ⟨hsub.1, hsub.2.1, hsub.2.2.1, ?_⟩
      rw [hsub.2.2.2, pow_succ]
      field_simp
      ring
    · have hem : endpoint ≤ (l+u)/2 :=
        le_of_lt (lt_of_not_ge (fun h => hreply ((hcontract _ hmid).mpr h)))
      have hsub := ih l ((l+u)/2) hl hle hem
      dsimp at hsub ⊢
      refine ⟨hsub.1, hsub.2.1, hsub.2.2.1, ?_⟩
      rw [hsub.2.2.2, pow_succ]
      field_simp
      ring

/-- One public endpoint probe, then exactly n midpoint probes if that endpoint was false. -/
noncomputable def endpointSearch (oracle : ℝ → Bool) (R : ℝ) (n : ℕ) : EndpointResult :=
  if oracle (2*R) = true then ⟨2*R, 1⟩ else
    let bracket := bisect oracle n 0 (2*R)
    ⟨(bracket.low+bracket.high)/2, bracket.queries+1⟩

theorem endpointSearch_queries (oracle : ℝ → Bool) (R : ℝ) (n : ℕ) :
    (endpointSearch oracle R n).queries ≤ n+1 := by
  simp only [endpointSearch]
  split_ifs
  · simp
  · simp [bisect_queries]

theorem endpointSearch_correct
    (oracle : ℝ → Bool) (R endpoint : ℝ) (n : ℕ)
    (hR : 0 < R) (he : 0 ≤ endpoint) (heR : endpoint ≤ 2*R)
    (hcontract : ∀ s, 0 ≤ s → (oracle s = true ↔ s ≤ endpoint)) :
    |(endpointSearch oracle R n).estimate-endpoint| ≤ R/(2:ℝ)^n := by
  have hp : 0 < (2:ℝ)^n := by positivity
  simp only [endpointSearch]
  split_ifs with hreply
  · have hRe : 2*R ≤ endpoint := (hcontract _ (by positivity)).mp hreply
    have hEq : 2*R = endpoint := le_antisymm hRe heR
    simp only [hEq, sub_self, abs_zero]
    positivity
  · have hb := bisect_bracket oracle endpoint hcontract n 0 (2*R) (by norm_num) he heR
    dsimp at hb ⊢
    have hw : (bisect oracle n 0 (2*R)).high - (bisect oracle n 0 (2*R)).low =
        2*(R/(2:ℝ)^n) := by
      rw [hb.2.2.2]
      ring
    apply abs_le.mpr
    constructor <;> linarith [hb.2.1, hb.2.2.1, hw]

theorem executed_signed_scalar_search
    {phi Phi : ℝ → ℝ} (positive negative : ℝ → Bool) (b R : ℝ) (n : ℕ)
    (hphi : StrictConvexOn ℝ univ phi)
    (hsym : ∀ x, phi (b-x) = phi x) (hPhi : StrictMono Phi)
    (hR : 0 < R) (hb : |b| ≤ 2*R)
    (hpos : ∀ s, positive s = true ↔ Phi (phi s) ≤ Phi (phi 0))
    (hneg : ∀ s, negative s = true ↔ Phi (phi (-s)) ≤ Phi (phi 0)) :
    |((endpointSearch positive R n).estimate -
      (endpointSearch negative R n).estimate)/2 - b/2| ≤ R/(2:ℝ)^n ∧
      (endpointSearch positive R n).queries +
      (endpointSearch negative R n).queries ≤ 2*(n+1) := by
  have hbpos : max b 0 ≤ 2*R := max_le (le_trans (le_abs_self b) hb) (by positivity)
  have hbneg : max (-b) 0 ≤ 2*R := max_le (by simpa only [abs_neg] using (le_abs_self (-b)).trans (by simpa using hb)) (by positivity)
  have hp := endpointSearch_correct positive R (max b 0) n hR (le_max_right _ _) hbpos
    (fun s hs => (hpos s).trans (positive_return_threshold hphi hsym hPhi hs))
  have hm := endpointSearch_correct negative R (max (-b) 0) n hR (le_max_right _ _) hbneg
    (fun s hs => (hneg s).trans (negative_return_threshold hphi hsym hPhi hs))
  have hdifference : max b 0 - max (-b) 0 = b := by
    by_cases h : 0 ≤ b
    · rw [max_eq_left h, max_eq_right (by linarith : -b ≤ 0)]; ring
    · rw [max_eq_right (le_of_lt (lt_of_not_ge h)), max_eq_left (by linarith : 0 ≤ -b)]; ring
  constructor
  · rcases abs_le.mp hp with ⟨hpl,hpu⟩
    rcases abs_le.mp hm with ⟨hml,hmu⟩
    apply abs_le.mpr
    constructor <;> linarith
  · have hpc := endpointSearch_queries positive R n
    have hmc := endpointSearch_queries negative R n
    omega

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Vector (ι : Type*) := EuclideanSpace ℝ ι

noncomputable def axis (i : ι) : Vector ι := PiLp.single 2 i (1:ℝ)

noncomputable def signedCoordinates (S : Finset ι) (x : Vector ι) : Vector ι :=
  WithLp.toLp 2 (fun j => if j ∈ S then -x j else x j)

noncomputable def coordinateFlip (i : ι) (x : Vector ι) : Vector ι :=
  signedCoordinates {i} x

omit [Fintype ι] in
theorem signedCoordinates_insert (i : ι) (S : Finset ι) (hi : i ∉ S) (x : Vector ι) :
    signedCoordinates (insert i S) x = coordinateFlip i (signedCoordinates S x) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [signedCoordinates, coordinateFlip, hi, PiLp.toLp_apply]
  · by_cases hj : j ∈ S <;>
      simp [signedCoordinates, coordinateFlip, hji, hj, PiLp.toLp_apply]

theorem coordinate_symmetry_implies_even (q : Vector ι → ℝ)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) : ∀ x, q (-x) = q x := by
  intro x
  have hmask : ∀ S : Finset ι, q (signedCoordinates S x) = q x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hzero : signedCoordinates ∅ x = x := by ext j; simp [signedCoordinates]
      rw [hzero]
    | @insert i S hi ih => rw [signedCoordinates_insert i S hi, hflip, ih]
  have hall : signedCoordinates Finset.univ x = -x := by
    ext j
    simp [signedCoordinates, PiLp.toLp_apply]
  simpa only [hall] using hmask Finset.univ

omit [Fintype ι] in
theorem coordinate_line_strict_convex (q : Vector ι → ℝ)
    (hq : StrictConvexOn ℝ univ q) (a : Vector ι) (i : ι) :
    StrictConvexOn ℝ univ (fun t : ℝ => q (a-t • axis i)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy alpha beta halpha hbeta hab
  have hxy' : a-x • axis i ≠ a-y • axis i := by
    intro heq
    have hc := congrArg (fun z : Vector ι => z i) heq
    simp [axis] at hc
    exact hxy (by linarith)
  have hcomb : a-(alpha*x+beta*y) • axis i =
      alpha • (a-x • axis i) + beta • (a-y • axis i) := by
    ext j
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t * a j) hab]
  have h := hq.2 (mem_univ _) (mem_univ _) hxy' halpha hbeta hab
  simpa only [smul_eq_mul, hcomb] using h

omit [Fintype ι] in
theorem coordinate_line_symmetry (q : Vector ι → ℝ)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (a : Vector ι) (i : ι) (t : ℝ) :
    q (a-(2*a i-t) • axis i) = q (a-t • axis i) := by
  have heq : a-(2*a i-t) • axis i = coordinateFlip i (a-t • axis i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [coordinateFlip, signedCoordinates, axis, PiLp.single_apply, PiLp.toLp_apply]
      ring
    · simp [coordinateFlip, signedCoordinates, axis, PiLp.single_apply, PiLp.toLp_apply, hji]
  rw [heq, hflip]

noncomputable def translatedObjective (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (a x : Vector ι) : ℝ := Phi (q (x-a))

theorem translated_axis_value (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (a : Vector ι) (i : ι) (t : ℝ) :
    translatedObjective q Phi a (t • axis i) = Phi (q (a-t • axis i)) := by
  have heq : t • axis i-a = -(a-t • axis i) := by abel
  simp only [translatedObjective, heq, coordinate_symmetry_implies_even q hflip]

theorem translated_return_interval (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (i : ι) (t : ℝ) :
    translatedObjective q Phi a (t • axis i) ≤ translatedObjective q Phi a 0 ↔
      t ∈ Icc (min 0 (2*a i)) (max 0 (2*a i)) := by
  have hzero : translatedObjective q Phi a 0 = Phi (q (a-(0:ℝ) • axis i)) := by
    simpa using translated_axis_value q Phi hflip a i 0
  rw [translated_axis_value q Phi hflip, hzero]
  exact strict_mono_reflection_return (coordinate_line_strict_convex q hq a i)
    (coordinate_line_symmetry q hflip a i) hPhi

theorem reflection_gauge_minimum (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a x : Vector ι) : translatedObjective q Phi a a ≤ translatedObjective q Phi a x := by
  have heven := coordinate_symmetry_implies_even q hflip
  have hmin : ∀ y : Vector ι, q 0 ≤ q y := by
    intro y
    have h := hq.convexOn.2 (mem_univ y) (mem_univ (-y))
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    have hmid : (1/2:ℝ) • y + (1/2:ℝ) • (-y) = 0 := by module
    simpa only [hmid, heven y, smul_eq_mul, ← add_mul, add_halves, one_mul] using h
  simp only [translatedObjective, sub_self]
  exact hPhi.monotone (hmin (x-a))

noncomputable def signedQuery (i : ι) (positive : Bool) (s : ℝ) : Vector ι :=
  if positive then s • axis i else (-s) • axis i

structure ReflectionResult (ι : Type*) [Fintype ι] where
  estimate : Vector ι
  queries : ℕ

/-- The deterministic program depends on replies, R and n; q, Phi and a are absent. -/
noncomputable def reflectionSearch (oracle : ι → Bool → ℝ → Bool) (R : ℝ) (n : ℕ) :
    ReflectionResult ι :=
  let positive := fun i => endpointSearch (oracle i true) R n
  let negative := fun i => endpointSearch (oracle i false) R n
  ⟨WithLp.toLp 2 (fun i => ((positive i).estimate-(negative i).estimate)/2),
    ∑ i, ((positive i).queries+(negative i).queries)⟩

omit [DecidableEq ι] in
theorem reflectionSearch_query_cap (oracle : ι → Bool → ℝ → Bool) (R : ℝ) (n : ℕ) :
    (reflectionSearch oracle R n).queries ≤ 2*Fintype.card ι*(n+1) := by
  simp only [reflectionSearch]
  calc
    (∑ i, ((endpointSearch (oracle i true) R n).queries +
      (endpointSearch (oracle i false) R n).queries)) ≤ ∑ _i : ι, 2*(n+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := endpointSearch_queries (oracle i true) R n
      have hm := endpointSearch_queries (oracle i false) R n
      omega
    _ = 2*Fintype.card ι*(n+1) := by simp; ring

theorem reflectionSearch_coordinate_correct
    (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (R : ℝ) (n : ℕ) (hR : 0 < R) (ha : ‖a‖ ≤ R)
    (oracle : ι → Bool → ℝ → Bool)
    (hcontract : ∀ i sign s, oracle i sign s = true ↔
      translatedObjective q Phi a (signedQuery i sign s) ≤ translatedObjective q Phi a 0) :
    ∀ i, |(reflectionSearch oracle R n).estimate i-a i| ≤ R/(2:ℝ)^n := by
  intro i
  have hainorm : |a i| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
  have hai : |a i| ≤ R := hainorm.trans ha
  have hbase : translatedObjective q Phi a 0 = Phi (q (a-(0:ℝ) • axis i)) := by
    simpa using translated_axis_value q Phi hflip a i 0
  have hpos : ∀ s, oracle i true s = true ↔
      Phi (q (a-s • axis i)) ≤ Phi (q (a-(0:ℝ) • axis i)) := by
    intro s
    rw [hcontract]
    simp [signedQuery, translated_axis_value q Phi hflip, hbase]
  have hneg : ∀ s, oracle i false s = true ↔
      Phi (q (a-(-s) • axis i)) ≤ Phi (q (a-(0:ℝ) • axis i)) := by
    intro s
    rw [hcontract]
    change translatedObjective q Phi a ((-s) • axis i) ≤ translatedObjective q Phi a 0 ↔ _
    rw [translated_axis_value q Phi hflip, hbase]
  have h := executed_signed_scalar_search (oracle i true) (oracle i false) (2*a i) R n
    (coordinate_line_strict_convex q hq a i) (coordinate_line_symmetry q hflip a i)
    hPhi hR (by rw [abs_mul]; norm_num; linarith) hpos hneg
  have hhalf : 2*a i/2 = a i := by ring
  simpa only [reflectionSearch, PiLp.toLp_apply, hhalf] using h.1

theorem reflectionSearch_distance_correct
    (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (R : ℝ) (n : ℕ) (hR : 0 < R) (ha : ‖a‖ ≤ R)
    (oracle : ι → Bool → ℝ → Bool)
    (hcontract : ∀ i sign s, oracle i sign s = true ↔
      translatedObjective q Phi a (signedQuery i sign s) ≤ translatedObjective q Phi a 0) :
    ‖(reflectionSearch oracle R n).estimate-a‖^2 ≤
      (Fintype.card ι:ℝ)*R^2/(2:ℝ)^(2*n) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ i, (((reflectionSearch oracle R n).estimate-a) i)^2) ≤
        ∑ _i : ι, (R/(2:ℝ)^n)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := reflectionSearch_coordinate_correct q Phi hq hflip hPhi a R n hR ha oracle hcontract i
      simpa only [PiLp.sub_apply] using sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    _ = (Fintype.card ι:ℝ)*R^2/(2:ℝ)^(2*n) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [div_pow, show 2*n = n*2 by omega, pow_mul]
      ring

/-- Public precision; natural ceiling already clips negative values to zero. -/
noncomputable def publicSteps (d : ℕ) (Q : ℝ) : ℕ :=
  ⌈Real.log ((d:ℝ)*Q)/(2*Real.log 2)⌉₊

theorem publicSteps_matches_paper (d : ℕ) (Q : ℝ) :
    (publicSteps d Q:ℤ) = max 0 ⌈(1/2:ℝ)*Real.logb 2 ((d:ℝ)*Q)⌉ := by
  have hlog : Real.log ((d:ℝ)*Q)/(2*Real.log 2) =
      (1/2:ℝ)*Real.logb 2 ((d:ℝ)*Q) := by
    rw [Real.logb]
    ring
  unfold publicSteps
  rw [hlog, ← Int.ceil_toNat]
  omega

theorem publicSteps_precision (d : ℕ) (Q : ℝ) (hd : 0 < d) (hQ : 0 < Q) :
    (d:ℝ)*Q ≤ (2:ℝ)^(2*publicSteps d Q) := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil (Real.log ((d:ℝ)*Q)/(2*Real.log 2))
  change Real.log ((d:ℝ)*Q)/(2*Real.log 2) ≤ (publicSteps d Q:ℝ) at hceil
  have hlogbound := (div_le_iff₀ (show 0 < 2*Real.log (2:ℝ) by positivity)).mp hceil
  have hlog : Real.log ((d:ℝ)*Q) ≤ Real.log ((2:ℝ)^(2*publicSteps d Q)) := by
    rw [Real.log_pow]
    push_cast
    nlinarith
  exact (Real.log_le_log_iff (mul_pos (Nat.cast_pos.mpr hd) hQ) (by positivity)).mp hlog

theorem reflectionSearch_gap_at_precision
    (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (R epsilon Q : ℝ) (beta : NNReal) (n : ℕ)
    (hR : 0 < R) (hepsilon : 0 < epsilon) (ha : ‖a‖ ≤ R)
    (hQdef : Q = (beta:ℝ)*R^2/epsilon)
    (hprecision : (Fintype.card ι:ℝ)*Q ≤ (2:ℝ)^(2*n))
    (grad : Vector ι → Vector ι)
    (hg : ∀ x, HasGradientAt (translatedObjective q Phi a) (grad x) x)
    (hLip : LipschitzWith beta grad)
    (oracle : ι → Bool → ℝ → Bool)
    (hcontract : ∀ i sign s, oracle i sign s = true ↔
      translatedObjective q Phi a (signedQuery i sign s) ≤ translatedObjective q Phi a 0) :
    translatedObjective q Phi a (reflectionSearch oracle R n).estimate -
      translatedObjective q Phi a a ≤ epsilon/2 ∧
      (reflectionSearch oracle R n).queries ≤ 2*Fintype.card ι*(n+1) := by
  have hdist := reflectionSearch_distance_correct q Phi hq hflip hPhi a R n hR ha oracle hcontract
  have hgap := PaperSmooth.gap_at_min (translatedObjective q Phi a) grad hg beta hLip a
    (reflectionSearch oracle R n).estimate (reflection_gauge_minimum q Phi hq hflip hPhi a)
  have hscaled := mul_le_mul_of_nonneg_left hdist (show 0 ≤ (beta:ℝ)/2 by positivity)
  have hden : 0 < (2:ℝ)^(2*n) := by positivity
  have hbudget := mul_le_mul_of_nonneg_left hprecision (le_of_lt hepsilon)
  have hidentity : epsilon*((Fintype.card ι:ℝ)*Q) = (beta:ℝ)*(Fintype.card ι:ℝ)*R^2 := by
    rw [hQdef]
    field_simp
  rw [hidentity] at hbudget
  have hquotient : (beta:ℝ)*(Fintype.card ι:ℝ)*R^2/(2:ℝ)^(2*n) ≤ epsilon :=
    (div_le_iff₀ hden).mpr hbudget
  have htarget : (beta:ℝ)/2*((Fintype.card ι:ℝ)*R^2/(2:ℝ)^(2*n)) ≤ epsilon/2 := by
    have hhalf := div_le_div_of_nonneg_right hquotient (show (0:ℝ) ≤ 2 by norm_num)
    calc
      (beta:ℝ)/2*((Fintype.card ι:ℝ)*R^2/(2:ℝ)^(2*n)) =
          ((beta:ℝ)*(Fintype.card ι:ℝ)*R^2/(2:ℝ)^(2*n))/2 := by ring
      _ ≤ epsilon/2 := hhalf
  exact ⟨hgap.trans (hscaled.trans htarget), reflectionSearch_query_cap oracle R n⟩

theorem reflectionSearch_complete
    (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (R epsilon Q : ℝ) (beta : NNReal)
    (hcard : 0 < Fintype.card ι) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (ha : ‖a‖ ≤ R) (hQ : 32 ≤ Q) (hQdef : Q = (beta:ℝ)*R^2/epsilon)
    (grad : Vector ι → Vector ι)
    (hg : ∀ x, HasGradientAt (translatedObjective q Phi a) (grad x) x)
    (hLip : LipschitzWith beta grad)
    (oracle : ι → Bool → ℝ → Bool)
    (hcontract : ∀ i sign s, oracle i sign s = true ↔
      translatedObjective q Phi a (signedQuery i sign s) ≤ translatedObjective q Phi a 0) :
    let n := publicSteps (Fintype.card ι) Q
    translatedObjective q Phi a (reflectionSearch oracle R n).estimate -
      translatedObjective q Phi a a ≤ epsilon/2 ∧
      (reflectionSearch oracle R n).queries ≤ 2*Fintype.card ι*(n+1) := by
  exact reflectionSearch_gap_at_precision q Phi hq hflip hPhi a R epsilon Q beta
    (publicSteps (Fintype.card ι) Q) hR hepsilon ha hQdef
    (publicSteps_precision (Fintype.card ι) Q hcard (by linarith)) grad hg hLip oracle hcontract

/-- A trinary comparison is projected to the weak predicate; an exact tie is true. -/
def weakReply : Ordering → Bool
  | .lt => true
  | .eq => true
  | .gt => false

theorem weakReply_correct (r : Ordering) (x y : ℝ) (hgt : r = .gt ↔ y < x) :
    weakReply r = true ↔ x ≤ y := by
  calc
    weakReply r = true ↔ r ≠ .gt := by cases r <;> simp [weakReply]
    _ ↔ ¬ y < x := not_congr hgt
    _ ↔ x ≤ y := not_lt

/-- Exactly one original comparison is consumed per weak oracle invocation. -/
noncomputable def coordinateOracle (comparison : Vector ι → Vector ι → Ordering)
    (i : ι) (sign : Bool) (s : ℝ) : Bool :=
  weakReply (comparison (signedQuery i sign s) 0)

omit [Fintype ι] in
theorem coordinateOracle_contract
    (f : Vector ι → ℝ) (comparison : Vector ι → Vector ι → Ordering)
    (hcomparison : ∀ x y, comparison x y = .gt ↔ f y < f x) :
    ∀ i sign s, coordinateOracle comparison i sign s = true ↔
      f (signedQuery i sign s) ≤ f 0 := by
  intro i sign s
  exact weakReply_correct _ _ _ (hcomparison _ _)

/-- The complete deterministic reflection algorithm from exact comparison feedback. -/
theorem exact_comparison_reflection_complete
    (q : Vector ι → ℝ) (Phi : ℝ → ℝ)
    (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x) = q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (R epsilon Q : ℝ) (beta : NNReal)
    (hcard : 0 < Fintype.card ι) (hR : 0 < R) (hepsilon : 0 < epsilon)
    (ha : ‖a‖ ≤ R) (hQ : 32 ≤ Q) (hQdef : Q = (beta:ℝ)*R^2/epsilon)
    (grad : Vector ι → Vector ι)
    (hg : ∀ x, HasGradientAt (translatedObjective q Phi a) (grad x) x)
    (hLip : LipschitzWith beta grad)
    (comparison : Vector ι → Vector ι → Ordering)
    (hcomparison : ∀ x y, comparison x y = .gt ↔
      translatedObjective q Phi a y < translatedObjective q Phi a x) :
    let n := publicSteps (Fintype.card ι) Q
    let out := reflectionSearch (coordinateOracle comparison) R n
    translatedObjective q Phi a out.estimate-translatedObjective q Phi a a ≤ epsilon/2 ∧
      out.queries ≤ 2*Fintype.card ι*(n+1) := by
  exact reflectionSearch_complete q Phi hq hflip hPhi a R epsilon Q beta
    hcard hR hepsilon ha hQ hQdef grad hg hLip (coordinateOracle comparison)
    (coordinateOracle_contract (translatedObjective q Phi a) comparison hcomparison)

end Coordinates

end PaperReflection


end SnapshotModule_084
/- END reflection_complete -/

/- BEGIN reflection_query_program -/
section SnapshotModule_085

namespace PaperOracle.Program
variable {Q R A : Type}

def collectFin : (m : ℕ) → (Fin m → Program Q R A) → Program Q R (Fin m → A)
  | 0,_ => .done Fin.elim0
  | m+1,f => bind (f 0) (fun first =>
      bind (collectFin m (fun i => f i.succ)) (fun rest => .done (Fin.cons first rest)))

lemma run_collectFin (C : Q → R) (m : ℕ) (f : Fin m → Program Q R A) :
    run C (collectFin m f)=fun i => run C (f i) := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    simp only [collectFin,run_bind,run,ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

lemma collectFin_cap (m c : ℕ) (f : Fin m → Program Q R A) (hf : ∀ i,Cap c (f i)) :
    Cap (m*c) (collectFin m f) := by
  induction m with
  | zero => simp [collectFin,Cap]
  | succ m ih =>
    have h : Cap (c+m*c) (collectFin (m+1) f) := by
      unfold collectFin
      apply cap_bind _ _ (hf 0)
      intro first
      have ht := cap_bind _ (fun rest => Program.done (Q := Q) (A := Fin (m+1) → A) (Fin.cons first rest))
        (ih (fun i => f i.succ) (fun i => hf i.succ)) (b := 0) (by intro rest; trivial)
      simpa using ht
    convert h using 1 <;> (first | rfl | ring)

end PaperOracle.Program

namespace PaperReflectionProgram
open Set PaperReflection
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Program (ι : Type) := PaperOracle.Program (Vector ι×Vector ι) Ordering
abbrev Oracle (ι : Type) := (Vector ι×Vector ι) → Ordering

/-- Explicit query-tree lift of the instrumented scalar reflection bisection. -/
def bisectProgram (point : ℝ → Vector ι) : ℕ → ℝ → ℝ → Program ι BracketResult
  | 0,l,u => .done ⟨l,u,0⟩
  | k+1,l,u => .ask (point ((l+u)/2),0) (fun r =>
      let next := if weakReply r then bisectProgram point k ((l+u)/2) u else bisectProgram point k l ((l+u)/2)
      PaperOracle.Program.bind next (fun b => .done ⟨b.low,b.high,b.queries+1⟩))

lemma bisect_run (C : Oracle ι) (point : ℝ → Vector ι) (k : ℕ) (l u : ℝ) :
    PaperOracle.Program.run C (bisectProgram point k l u)=
      PaperReflection.bisect (fun t => weakReply (C (point t,0))) k l u := by
  induction k generalizing l u with
  | zero => rfl
  | succ k ih =>
    simp only [bisectProgram,PaperOracle.Program.run,PaperOracle.Program.run_bind,PaperReflection.bisect]
    split_ifs <;> simp only [ih,PaperOracle.Program.run]

lemma bisect_cap (point : ℝ → Vector ι) (k : ℕ) (l u : ℝ) :
    PaperOracle.Program.Cap k (bisectProgram point k l u) := by
  induction k generalizing l u with
  | zero => trivial
  | succ k ih =>
    intro r
    have hnext : PaperOracle.Program.Cap k
        (if weakReply r then bisectProgram point k ((l+u)/2) u else bisectProgram point k l ((l+u)/2)) := by
      split_ifs <;> apply ih
    have hh := PaperOracle.Program.cap_bind _ (fun b : BracketResult =>
      PaperOracle.Program.done (Q := Vector ι×Vector ι) (R := Ordering) (A := BracketResult) ⟨b.low,b.high,b.queries+1⟩)
      hnext (b := 0) (by intro b; trivial)
    simpa using hh

def endpointProgram (point : ℝ → Vector ι) (R : ℝ) (k : ℕ) : Program ι EndpointResult :=
  .ask (point (2*R),0) (fun r => if weakReply r then .done ⟨2*R,1⟩ else
    PaperOracle.Program.bind (bisectProgram point k 0 (2*R))
      (fun b => .done ⟨(b.low+b.high)/2,b.queries+1⟩))

lemma endpoint_run (C : Oracle ι) (point : ℝ → Vector ι) (R : ℝ) (k : ℕ) :
    PaperOracle.Program.run C (endpointProgram point R k)=
      endpointSearch (fun t => weakReply (C (point t,0))) R k := by
  simp only [endpointProgram,PaperOracle.Program.run,endpointSearch]
  split_ifs <;> simp only [PaperOracle.Program.run_bind,bisect_run,PaperOracle.Program.run]

lemma endpoint_cap (point : ℝ → Vector ι) (R : ℝ) (k : ℕ) :
    PaperOracle.Program.Cap (k+1) (endpointProgram point R k) := by
  intro r
  dsimp only
  split_ifs
  · cases k <;> trivial
  · have h := PaperOracle.Program.cap_bind _ (fun b : BracketResult =>
      PaperOracle.Program.done (Q := Vector ι×Vector ι) (R := Ordering)
        (A := EndpointResult) ⟨(b.low+b.high)/2,b.queries+1⟩)
      (bisect_cap point k 0 (2*R)) (b := 0) (by intro b; trivial)
    simpa using h

def coordinateProgram (i : ι) (R : ℝ) (k : ℕ) : Program ι ℝ :=
  PaperOracle.Program.bind (endpointProgram (signedQuery i true) R k) (fun p =>
    PaperOracle.Program.bind (endpointProgram (signedQuery i false) R k)
      (fun m => .done ((p.estimate-m.estimate)/2)))

lemma coordinate_run (C : Oracle ι) (i : ι) (R : ℝ) (k : ℕ) :
    PaperOracle.Program.run C (coordinateProgram i R k)=
      ((endpointSearch (coordinateOracle (fun x y => C (x,y)) i true) R k).estimate-
       (endpointSearch (coordinateOracle (fun x y => C (x,y)) i false) R k).estimate)/2 := by
  simp only [coordinateProgram,PaperOracle.Program.run_bind,endpoint_run,PaperOracle.Program.run,coordinateOracle]
  rfl

lemma coordinate_cap (i : ι) (R : ℝ) (k : ℕ) :
    PaperOracle.Program.Cap (2*(k+1)) (coordinateProgram i R k) := by
  have hh := PaperOracle.Program.cap_bind _ _ (endpoint_cap (signedQuery i true) R k)
    (fun p => PaperOracle.Program.cap_bind _ (fun m : EndpointResult =>
      PaperOracle.Program.done (Q := Vector ι×Vector ι) (R := Ordering) ((p.estimate-m.estimate)/2))
      (endpoint_cap (signedQuery i false) R k) (b := 0) (by intro m; trivial))
  convert hh using 1 <;> (first | rfl | ring)

def program (R : ℝ) (k : ℕ) : Program ι (Vector ι) :=
  let e := Fintype.equivFin ι
  PaperOracle.Program.bind
    (PaperOracle.Program.collectFin (Fintype.card ι) (fun j => coordinateProgram (e.symm j) R k))
    (fun values => .done (WithLp.toLp 2 (fun i => values (e i))))

lemma program_run (C : Oracle ι) (R : ℝ) (k : ℕ) :
    PaperOracle.Program.run C (program R k)=
      (reflectionSearch (coordinateOracle (fun x y => C (x,y))) R k).estimate := by
  simp only [program,PaperOracle.Program.run_bind,PaperOracle.Program.run_collectFin,
    PaperOracle.Program.run,coordinate_run]
  ext i
  simp [reflectionSearch]

lemma program_cap (R : ℝ) (k : ℕ) :
    PaperOracle.Program.Cap (2*Fintype.card ι*(k+1)) (program (ι := ι) R k) := by
  have hh := PaperOracle.Program.cap_bind _ _
    (PaperOracle.Program.collectFin_cap (Fintype.card ι) (2*(k+1))
      (fun j => coordinateProgram ((Fintype.equivFin ι).symm j) R k)
      (fun j => coordinate_cap _ R k)) (b := 0)
    (fun values => (show PaperOracle.Program.Cap 0
      (PaperOracle.Program.done (Q := Vector ι×Vector ι) (R := Ordering)
        (WithLp.toLp 2 (fun i => values ((Fintype.equivFin ι) i)))) from trivial))
  convert hh using 1 <;> (first | rfl | ring)

/-- Complete reflection localization with an explicit trinary comparison tree;
the cost counts actual query nodes, independently of the instrumented counter. -/
theorem reflection_public_complete
    (q : Vector ι → ℝ) (Phi : ℝ → ℝ) (hq : StrictConvexOn ℝ univ q)
    (hflip : ∀ i x, q (coordinateFlip i x)=q x) (hPhi : StrictMono Phi)
    (a : Vector ι) (R epsilon Q : ℝ) (beta : NNReal)
    (hcard : 0<Fintype.card ι) (hR : 0<R) (heps : 0<epsilon) (ha : ‖a‖≤R)
    (hQ : 32≤Q) (hQdef : Q=(beta:ℝ)*R^2/epsilon)
    (grad : Vector ι → Vector ι)
    (hg : ∀ x, HasGradientAt (translatedObjective q Phi a) (grad x) x)
    (hLip : LipschitzWith beta grad) :
    translatedObjective q Phi a
      (PaperOracle.Program.run (PaperOracle.comparisonOracle (translatedObjective q Phi a))
        (program R (publicSteps (Fintype.card ι) Q)))-translatedObjective q Phi a a≤epsilon/2 ∧
      PaperOracle.Program.Cap (2*Fintype.card ι*(publicSteps (Fintype.card ι) Q+1))
        (program (ι := ι) R (publicSteps (Fintype.card ι) Q)) := by
  constructor
  · rw [program_run]
    exact (exact_comparison_reflection_complete q Phi hq hflip hPhi a R epsilon Q beta hcard hR heps
      ha hQ hQdef grad hg hLip (fun x y => PaperOracle.comparisonOracle (translatedObjective q Phi a) (x,y))
      (fun x y => PaperOracle.realOrder_eq_gt_iff _ _)).1
  · exact program_cap _ _

end
end PaperReflectionProgram

end SnapshotModule_085
/- END reflection_query_program -/

/- BEGIN logcosh_example -/
section SnapshotModule_086

/- Local development of the appendix's actual log-cosh example. -/
namespace PaperLogCosh

open Set
open scoped RealInnerProductSpace

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable def logCosh (x : ℝ) : ℝ := Real.log (Real.cosh x)

theorem logCosh_zero : logCosh 0 = 0 := by simp [logCosh]

theorem logCosh_even (x : ℝ) : logCosh (-x) = logCosh x := by simp [logCosh]

theorem hasDerivAt_logCosh (x : ℝ) : HasDerivAt logCosh (Real.tanh x) x := by
  have h := (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))
  simpa only [logCosh, Real.tanh_eq_sinh_div_cosh] using! h

theorem deriv_logCosh (x : ℝ) : deriv logCosh x = Real.tanh x := (hasDerivAt_logCosh x).deriv

theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh x)^2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  have hfn : Real.tanh = Real.sinh/Real.cosh := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  have hder : (Real.cosh x*Real.cosh x-Real.sinh x*Real.sinh x)/(Real.cosh x)^2 =
      1/(Real.cosh x)^2 := by
    congr 1
    nlinarith [Real.cosh_sq (x:=x)]
  rw [hder] at h
  simpa only [hfn] using! h

theorem deriv_tanh (x : ℝ) : deriv Real.tanh x = 1/(Real.cosh x)^2 := (hasDerivAt_tanh x).deriv

theorem cosh_one_le (x : ℝ) : 1 ≤ Real.cosh x := by
  have hp := Real.cosh_pos x
  nlinarith [Real.cosh_sq (x:=x), sq_nonneg (Real.sinh x)]

theorem logCosh_nonneg (x : ℝ) : 0 ≤ logCosh x := Real.log_nonneg (cosh_one_le x)

theorem strictMono_tanh : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [deriv_tanh]
  positivity

theorem logCosh_strictConvex : StrictConvexOn ℝ univ logCosh := by
  have hc : Continuous logCosh := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_logCosh x).continuousAt)
  have hm : StrictMono (deriv logCosh) := by
    intro x y hxy
    rw [deriv_logCosh, deriv_logCosh]
    exact strictMono_tanh hxy
  exact StrictMono.strictConvexOn_univ_of_deriv hc hm

theorem tanh_deriv_norm_le_one (x : ℝ) : ‖deriv Real.tanh x‖ ≤ 1 := by
  rw [deriv_tanh, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1/(Real.cosh x)^2)]
  apply (div_le_one (by positivity : 0 < (Real.cosh x)^2)).mpr
  nlinarith [cosh_one_le x]

theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_tanh x).differentiableAt)
  intro x
  exact_mod_cast tanh_deriv_norm_le_one x

theorem logCosh_coercive_lower (x : ℝ) : |x|-Real.log 2 ≤ logCosh x := by
  have hbound : Real.exp |x|/2 ≤ Real.cosh x := by
    rw [← Real.cosh_abs x, Real.cosh_eq]
    linarith [Real.exp_pos (-|x|)]
  have h := Real.log_le_log (by positivity : 0 < Real.exp |x|/2) hbound
  rw [Real.log_div (ne_of_gt (Real.exp_pos |x|)) (by norm_num : (2:ℝ) ≠ 0), Real.log_exp] at h
  exact h

abbrev Signs (d : ℕ) := Fin d → Bool
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

def signScalar (b : Bool) : ℝ := if b then 1 else -1

theorem signScalar_sq (b : Bool) : (signScalar b)^2 = 1 := by cases b <;> norm_num [signScalar]

theorem signScalar_not (b : Bool) : signScalar (!b) = -signScalar b := by cases b <;> norm_num [signScalar]

noncomputable def signVector {d : ℕ} (s : Signs d) : Vec d :=
  WithLp.toLp 2 (fun i => signScalar (s i))

def flipSign {d : ℕ} (i : Fin d) : Signs d ≃ Signs d where
  toFun s j := if j=i then !(s j) else s j
  invFun s j := if j=i then !(s j) else s j
  left_inv s := by ext j; by_cases h : j=i <;> simp [h]
  right_inv s := by ext j; by_cases h : j=i <;> simp [h]

theorem signs_card (d : ℕ) : Fintype.card (Signs d) = 2^d := by simp [Signs]

theorem sign_covariance (d : ℕ) (i j : Fin d) :
    (∑ s : Signs d, signScalar (s i)*signScalar (s j)) =
      if i=j then (2:ℝ)^d else 0 := by
  by_cases hij : i=j
  · subst j
    simp only [← pow_two, signScalar_sq, if_true]
    simp
  · have hterm : ∀ s : Signs d,
        signScalar ((flipSign i s) i)*signScalar ((flipSign i s) j) =
          -(signScalar (s i)*signScalar (s j)) := by
      intro s
      simp [flipSign, signScalar_not, Ne.symm hij]
    have hreindex := Equiv.sum_comp (flipSign i)
      (fun s : Signs d => signScalar (s i)*signScalar (s j))
    simp_rw [hterm] at hreindex
    rw [Finset.sum_neg_distrib] at hreindex
    rw [if_neg hij]
    linarith

theorem signed_inner (d : ℕ) (s : Signs d) (x : Vec d) :
    inner ℝ (signVector s) x = ∑ i, signScalar (s i)*x i := by
  simp [PiLp.inner_apply, signVector, mul_comm]

theorem sign_isotropy (d : ℕ) (x : Vec d) :
    (∑ s : Signs d, (inner ℝ (signVector s) x)^2) = (2:ℝ)^d*‖x‖^2 := by
  simp_rw [signed_inner]
  calc
    (∑ s : Signs d, (∑ i, signScalar (s i)*x i)^2) =
        ∑ s : Signs d, ∑ i : Fin d, ∑ j : Fin d,
          signScalar (s i)*signScalar (s j)*x i*x j := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : Fin d, ∑ j : Fin d,
        (∑ s : Signs d, signScalar (s i)*signScalar (s j))*x i*x j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = (2:ℝ)^d*‖x‖^2 := by
      simp_rw [sign_covariance]
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Finset.mul_sum, pow_two, mul_assoc]

theorem exists_distinguishing_sign (d : ℕ) (x y : Vec d) (hxy : x ≠ y) :
    ∃ s : Signs d, inner ℝ (signVector s) x ≠ inner ℝ (signVector s) y := by
  by_contra hnone
  have hall : ∀ s : Signs d, inner ℝ (signVector s) (x-y) = 0 := by
    intro s
    rw [inner_sub_right]
    have heq : inner ℝ (signVector s) x = inner ℝ (signVector s) y := by
      by_contra hne
      exact hnone ⟨s,hne⟩
    rw [heq, sub_self]
  have hiso := sign_isotropy d (x-y)
  simp only [hall, zero_pow (by norm_num : (2:ℕ) ≠ 0), Finset.sum_const_zero] at hiso
  have hnormpos : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hpow : 0 < (2:ℝ)^d := by positivity
  have hpos := mul_pos hpow (pow_pos hnormpos 2)
  linarith

noncomputable def gauge (d : ℕ) (beta : ℝ) (x : Vec d) : ℝ :=
  beta/(2:ℝ)^d * ∑ s : Signs d, logCosh (inner ℝ (signVector s) x)

theorem gauge_zero (d : ℕ) (beta : ℝ) : gauge d beta 0 = 0 := by
  simp [gauge, logCosh_zero]

theorem gauge_strictConvex (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    StrictConvexOn ℝ univ (gauge d beta) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy alpha beta' halpha hbeta' hab
  obtain ⟨s0,hs0⟩ := exists_distinguishing_sign d x y hxy
  have hterms : ∀ s : Signs d,
      logCosh (inner ℝ (signVector s) (alpha • x+beta' • y)) ≤
        alpha*logCosh (inner ℝ (signVector s) x)+beta'*logCosh (inner ℝ (signVector s) y) := by
    intro s
    simpa only [inner_add_right, real_inner_smul_right, smul_eq_mul] using
      logCosh_strictConvex.convexOn.2 (mem_univ _) (mem_univ _)
        (le_of_lt halpha) (le_of_lt hbeta') hab
  have hstrict : logCosh (inner ℝ (signVector s0) (alpha • x+beta' • y)) <
        alpha*logCosh (inner ℝ (signVector s0) x)+beta'*logCosh (inner ℝ (signVector s0) y) := by
    simpa only [inner_add_right, real_inner_smul_right, smul_eq_mul] using
      logCosh_strictConvex.2 (mem_univ _) (mem_univ _) hs0 halpha hbeta' hab
  have hsum := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterms s)
    ⟨s0,Finset.mem_univ _,hstrict⟩
  have hscale := mul_lt_mul_of_pos_left hsum (show 0 < beta/(2:ℝ)^d by positivity)
  simpa only [gauge, Finset.sum_add_distrib, ← Finset.mul_sum, smul_eq_mul,
    mul_add, mul_assoc, mul_left_comm, mul_comm] using hscale

theorem signed_inner_coordinateFlip (d : ℕ) (i : Fin d) (s : Signs d) (x : Vec d) :
    inner ℝ (signVector s) (PaperReflection.coordinateFlip i x) =
      inner ℝ (signVector (flipSign i s)) x := by
  simp_rw [signed_inner]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j=i
  · subst j
    simp [PaperReflection.coordinateFlip, PaperReflection.signedCoordinates,
      PiLp.toLp_apply, flipSign, signScalar_not]
  · simp [PaperReflection.coordinateFlip, PaperReflection.signedCoordinates,
      PiLp.toLp_apply, flipSign, hji]

theorem gauge_coordinateFlip (d : ℕ) (beta : ℝ) (i : Fin d) (x : Vec d) :
    gauge d beta (PaperReflection.coordinateFlip i x) = gauge d beta x := by
  unfold gauge
  congr 1
  simp_rw [signed_inner_coordinateFlip]
  exact Equiv.sum_comp (flipSign i) (fun s : Signs d => logCosh (inner ℝ (signVector s) x))

theorem gauge_global_minimum (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x : Vec d) :
    gauge d beta 0 ≤ gauge d beta x := by
  have h := PaperReflection.reflection_gauge_minimum (gauge d beta) id
    (gauge_strictConvex d beta hbeta) (gauge_coordinateFlip d beta) strictMono_id 0 x
  simpa only [PaperReflection.translatedObjective, id_eq, sub_zero] using h

theorem sum_abs_signed_inner_ge_norm (d : ℕ) (x : Vec d) :
    ‖x‖ ≤ ∑ s : Signs d, |inner ℝ (signVector s) x| := by
  let S : ℝ := ∑ s : Signs d, |inner ℝ (signVector s) x|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun s hs => abs_nonneg _)
  have hsquare : (∑ s : Signs d, (inner ℝ (signVector s) x)^2) ≤ S^2 := by
    calc
      _ ≤ ∑ s : Signs d, S*|inner ℝ (signVector s) x| := by
        apply Finset.sum_le_sum
        intro s hs
        have hsingle : |inner ℝ (signVector s) x| ≤ S := by
          dsimp [S]
          exact Finset.single_le_sum (fun t _ => abs_nonneg (inner ℝ (signVector t) x)) (Finset.mem_univ s)
        have hm := mul_le_mul_of_nonneg_right hsingle (abs_nonneg (inner ℝ (signVector s) x))
        simpa only [← pow_two, sq_abs] using hm
      _ = S^2 := by rw [← Finset.mul_sum]; change S*S=S^2; ring
  rw [sign_isotropy] at hsquare
  have hN : 1 ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hN (sq_nonneg ‖x‖)
  change ‖x‖ ≤ S
  nlinarith [norm_nonneg x]

theorem gauge_coercive_lower (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x : Vec d) :
    beta/(2:ℝ)^d*‖x‖-beta*Real.log 2 ≤ gauge d beta x := by
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    logCosh_coercive_lower (inner ℝ (signVector s) x))
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ beta/(2:ℝ)^d by positivity)
  have hcard : (Fintype.card (Signs d):ℝ) = (2:ℝ)^d := by rw [signs_card]; norm_cast
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hscaled
  have hnorm := mul_le_mul_of_nonneg_left (sum_abs_signed_inner_ge_norm d x)
    (show 0 ≤ beta/(2:ℝ)^d by positivity)
  have hidentity : beta/(2:ℝ)^d*((2:ℝ)^d*Real.log 2) = beta*Real.log 2 := by
    field_simp
  unfold gauge
  nlinarith

theorem gauge_sublevel_norm_bound (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (c : ℝ) :
    ∃ B : ℝ, ∀ x : Vec d, gauge d beta x ≤ c → ‖x‖ ≤ B := by
  refine ⟨(c+beta*Real.log 2)/(beta/(2:ℝ)^d), ?_⟩
  intro x hx
  apply (le_div_iff₀ (show 0 < beta/(2:ℝ)^d by positivity)).mpr
  have h := gauge_coercive_lower d beta hbeta x
  nlinarith

theorem gauge_coercive (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    Filter.Tendsto (gauge d beta) (Filter.cocompact (Vec d)) Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro c
  have hcoef : 0 < beta/(2:ℝ)^d := by positivity
  have hevent := (tendsto_norm_cocompact_atTop (E:=Vec d)).eventually_ge_atTop
    ((c+beta*Real.log 2)/(beta/(2:ℝ)^d))
  filter_upwards [hevent] with x hx
  have hm := mul_le_mul_of_nonneg_left hx (le_of_lt hcoef)
  have hid : beta/(2:ℝ)^d*((c+beta*Real.log 2)/(beta/(2:ℝ)^d)) = c+beta*Real.log 2 := by
    field_simp
  rw [hid] at hm
  linarith [gauge_coercive_lower d beta hbeta x]

noncomputable def gaugeGradient (d : ℕ) (beta : ℝ) (x : Vec d) : Vec d :=
  (beta/(2:ℝ)^d) • ∑ s : Signs d, Real.tanh (inner ℝ (signVector s) x) • signVector s

theorem gauge_hasGradient (d : ℕ) (beta : ℝ) (x : Vec d) :
    HasGradientAt (gauge d beta) (gaugeGradient d beta x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hterm : ∀ s : Signs d,
      HasFDerivAt (fun z : Vec d => logCosh (inner ℝ (signVector s) z))
        (Real.tanh (inner ℝ (signVector s) x) • InnerProductSpace.toDual ℝ (Vec d) (signVector s)) x := by
    intro s
    have hlin := (InnerProductSpace.toDual ℝ (Vec d) (signVector s)).hasFDerivAt (x:=x)
    simpa using! (hasDerivAt_logCosh (inner ℝ (signVector s) x)).comp_hasFDerivAt x hlin
  have hsum := HasFDerivAt.sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  have hscaled := hsum.const_mul (beta/(2:ℝ)^d)
  convert! hscaled using 1
  · funext y
    simp [gauge, Finset.sum_apply]
  · ext v
    simp [gaugeGradient, InnerProductSpace.toDual_apply_apply, Finset.mul_sum]

theorem gaugeGradient_lipschitz (d : ℕ) (beta : NNReal) :
    LipschitzWith beta (gaugeGradient d beta) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  let N : ℝ := (2:ℝ)^d
  let z := x-y
  let v := gaugeGradient d beta x-gaugeGradient d beta y
  let A : Signs d → ℝ := fun s => Real.tanh (inner ℝ (signVector s) x)-Real.tanh (inner ℝ (signVector s) y)
  let B : Signs d → ℝ := fun s => inner ℝ (signVector s) v
  let S : ℝ := ∑ s : Signs d, A s*B s
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : (∑ s : Signs d, (A s)^2) ≤ N*‖z‖^2 := by
    calc
      _ ≤ ∑ s : Signs d, (inner ℝ (signVector s) z)^2 := by
        apply Finset.sum_le_sum
        intro s hs
        have h := tanh_lipschitz.norm_sub_le (inner ℝ (signVector s) x) (inner ℝ (signVector s) y)
        simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs, ← inner_sub_right] at h
        exact sq_le_sq.mpr h
      _ = _ := sign_isotropy d z
  have hB : (∑ s : Signs d, (B s)^2) = N*‖v‖^2 := sign_isotropy d v
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Signs d)) A B
  change S^2 ≤ (∑ s : Signs d, (A s)^2)*(∑ s : Signs d, (B s)^2) at hc
  rw [hB] at hc
  have hm := mul_le_mul_of_nonneg_right hA (show 0 ≤ N*‖v‖^2 by positivity)
  have hsquare : S^2 ≤ (N*‖z‖*‖v‖)^2 := by
    exact (hc.trans hm).trans_eq (by ring)
  have habs : |S| ≤ N*‖z‖*‖v‖ := by
    have h := sq_le_sq.mp hsquare
    simpa only [abs_of_nonneg (show 0 ≤ N*‖z‖*‖v‖ by positivity)] using h
  have hvector : v = ((beta:ℝ)/N) • ∑ s : Signs d, A s • signVector s := by
    dsimp [v, gaugeGradient, A, N]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [sub_smul]
  have hinner : ‖v‖^2 = ((beta:ℝ)/N)*S := by
    calc
      ‖v‖^2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
      _ = inner ℝ (((beta:ℝ)/N) • ∑ s : Signs d, A s • signVector s) v :=
        congrArg (fun w => inner ℝ w v) hvector
      _ = ((beta:ℝ)/N)*S := by simp [S, B, real_inner_smul_left, sum_inner]
  have hnorm : ‖v‖^2 ≤ (beta:ℝ)*‖z‖*‖v‖ := by
    calc
      ‖v‖^2 = ((beta:ℝ)/N)*S := hinner
      _ ≤ ((beta:ℝ)/N)*|S| := mul_le_mul_of_nonneg_left (le_abs_self S) (by positivity)
      _ ≤ ((beta:ℝ)/N)*(N*‖z‖*‖v‖) := mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (beta:ℝ)*‖z‖*‖v‖ := by field_simp
  change ‖v‖ ≤ (beta:ℝ)*‖z‖
  by_cases hvzero : ‖v‖=0
  · rw [hvzero]
    positivity
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hvzero)
    have hm' : ‖v‖*‖v‖ ≤ ‖v‖*((beta:ℝ)*‖z‖) := by convert hnorm using 1 <;> ring
    exact (mul_le_mul_iff_right₀ hvpos).mp hm'

theorem logCosh_upper (x : ℝ) : logCosh x ≤ |x| := by
  have hbound : Real.cosh x ≤ Real.exp |x| := by
    rw [← Real.cosh_abs x, Real.cosh_eq]
    have h := Real.exp_le_exp.mpr (show -|x| ≤ |x| by linarith [abs_nonneg x])
    linarith
  have h := Real.log_le_log (Real.cosh_pos x) hbound
  simpa only [logCosh, Real.log_exp] using! h

theorem signed_inner_axis (d : ℕ) (s : Signs d) (i : Fin d) (t : ℝ) :
    inner ℝ (signVector s) (t • PaperReflection.axis i) = t*signScalar (s i) := by
  simp [PaperReflection.axis, signVector, EuclideanSpace.inner_single_right, real_inner_smul_right]

theorem gauge_axis_value (d : ℕ) (beta t : ℝ) (i : Fin d) :
    gauge d beta (t • PaperReflection.axis i) = beta*logCosh t := by
  have hterms : ∀ s : Signs d,
      logCosh (inner ℝ (signVector s) (t • PaperReflection.axis i)) = logCosh t := by
    intro s
    rw [signed_inner_axis]
    cases hi : s i <;> simp [signScalar, logCosh_even]
  unfold gauge
  simp_rw [hterms]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, signs_card, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem gauge_not_stronglyConvex (d : ℕ) (hd : 0 < d) (beta mu : ℝ)
    (hbeta : 0 < beta) (hmu : 0 < mu) : ¬ StrongConvexOn univ mu (gauge d beta) := by
  intro hstrong
  let i : Fin d := ⟨0,hd⟩
  let t : ℝ := 1+2*beta/mu
  have ht : 0 < t := by dsimp [t]; positivity
  let x : Vec d := t • PaperReflection.axis i
  have hhalf := hstrong.2 (mem_univ x) (mem_univ (-x))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hmid : (1/2:ℝ) • x+(1/2:ℝ) • (-x) = 0 := by module
  have heven := PaperReflection.coordinate_symmetry_implies_even (gauge d beta) (gauge_coordinateFlip d beta) x
  have hdist : ‖x-(-x)‖^2 = 4*t^2 := by
    have heq : x-(-x) = (2*t) • PaperReflection.axis i := by dsimp [x]; module
    rw [heq, norm_smul, Real.norm_eq_abs]
    norm_num [PaperReflection.axis, mul_pow, sq_abs]
  simp only [hmid, gauge_zero, heven, smul_eq_mul, hdist] at hhalf
  have hupper : gauge d beta x ≤ beta*t := by
    dsimp [x]
    rw [gauge_axis_value]
    exact mul_le_mul_of_nonneg_left (by simpa only [abs_of_pos ht] using logCosh_upper t) (le_of_lt hbeta)
  have hrelation : mu*t=mu+2*beta := by dsimp [t]; field_simp
  have hm := mul_pos ht hmu
  nlinarith [congrArg (fun r : ℝ => r*t) hrelation]

theorem logCosh_twice_lt_four (t : ℝ) (ht : t ≠ 0) : logCosh (2*t) < 4*logCosh t := by
  have hc : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht
  have hsq : 0 < (Real.cosh t)^2-1 := by nlinarith
  have hcosh : Real.cosh (2*t) < (Real.cosh t)^4 := by
    rw [Real.cosh_two_mul]
    nlinarith [Real.cosh_sq (x:=t), sq_pos_of_pos hsq]
  have hl := (Real.log_lt_log_iff (Real.cosh_pos (2*t)) (pow_pos (Real.cosh_pos t) 4)).mpr hcosh
  rw [Real.log_pow] at hl
  simpa only [logCosh] using! hl

theorem scalar_sign_pair (a b : Bool) (t : ℝ) :
    logCosh (t*signScalar a+t*signScalar b)+
      logCosh (t*signScalar (!a)+t*signScalar b) = logCosh (2*t) := by
  cases a <;> cases b <;>
    simp [signScalar, ← two_mul, logCosh_even, logCosh_zero]

theorem gauge_diagonal_value (d : ℕ) (beta t : ℝ) (i j : Fin d) (hij : i ≠ j) :
    gauge d beta (t • PaperReflection.axis i+t • PaperReflection.axis j) = beta/2*logCosh (2*t) := by
  let x := t • PaperReflection.axis i+t • PaperReflection.axis j
  let F : Signs d → ℝ := fun s => logCosh (inner ℝ (signVector s) x)
  have hpair : ∀ s, F s+F (flipSign i s) = logCosh (2*t) := by
    intro s
    dsimp [F, x]
    simp only [inner_add_right, signed_inner_axis]
    have hflip_i : (flipSign i s) i = !(s i) := by simp [flipSign]
    have hflip_j : (flipSign i s) j = s j := by simp [flipSign, Ne.symm hij]
    rw [hflip_i, hflip_j]
    exact scalar_sign_pair (s i) (s j) t
  have hsum := congrArg (fun f : Signs d → ℝ => ∑ s, f s) (funext hpair)
  simp only [Finset.sum_add_distrib, Equiv.sum_comp, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, signs_card, Nat.cast_pow, Nat.cast_ofNat] at hsum
  change beta/(2:ℝ)^d*(∑ s, F s) = beta/2*logCosh (2*t)
  have hsum' : 2*(∑ s, F s) = (2:ℝ)^d*logCosh (2*t) := by linarith
  calc
    _ = beta/(2*(2:ℝ)^d)*(2*(∑ s, F s)) := by field_simp
    _ = beta/(2*(2:ℝ)^d)*((2:ℝ)^d*logCosh (2*t)) := by rw [hsum']
    _ = _ := by field_simp

def CoordinateSeparable {d : ℕ} (f : Vec d → ℝ) : Prop :=
  ∃ components : Fin d → ℝ → ℝ, ∀ x, f x = ∑ i, components i (x i)

theorem separable_axis_cross_identity {d : ℕ} (f : Vec d → ℝ)
    (hf : CoordinateSeparable f) (i j : Fin d) (hij : i ≠ j) :
    f (PaperReflection.axis i+PaperReflection.axis j)+f 0 =
      f (PaperReflection.axis i)+f (PaperReflection.axis j) := by
  obtain ⟨components,hcomponents⟩ := hf
  simp_rw [hcomponents]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k=i
  · subst k
    simp [PaperReflection.axis, hij]
  · by_cases hkj : k=j
    · subst k
      simp [PaperReflection.axis, Ne.symm hij, add_comm]
    · simp [PaperReflection.axis, hki, hkj]

theorem gauge_not_coordinate_separable (d : ℕ) (hd : 2 ≤ d) (beta : ℝ) (hbeta : 0 < beta) :
    ¬ CoordinateSeparable (gauge d beta) := by
  intro hsep
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i,j] at this; omega
  have hcross := separable_axis_cross_identity (gauge d beta) hsep i j hij
  have hdiag := gauge_diagonal_value d beta 1 i j hij
  have hi := gauge_axis_value d beta 1 i
  have hj := gauge_axis_value d beta 1 j
  simp only [one_smul, mul_one, gauge_zero] at hi hj hdiag hcross
  rw [hdiag, hi, hj] at hcross
  have hstrict := mul_lt_mul_of_pos_left (logCosh_twice_lt_four 1 (by norm_num)) hbeta
  norm_num at hstrict
  nlinarith

theorem diagonal_norm_sq (d : ℕ) (i j : Fin d) (hij : i ≠ j) (t : ℝ) :
    ‖t • PaperReflection.axis i+t • PaperReflection.axis j‖^2 = 2*t^2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  simp [PaperReflection.axis, EuclideanSpace.inner_single_left, hij, sq_abs]
  ring

theorem axis_norm_sq (d : ℕ) (i : Fin d) (t : ℝ) : ‖t • PaperReflection.axis i‖^2=t^2 := by
  rw [norm_smul]
  simp [PaperReflection.axis, sq_abs]

theorem gauge_not_radial (d : ℕ) (hd : 2 ≤ d) (beta : ℝ) (hbeta : 0 < beta) :
    ¬ (∀ x y : Vec d, ‖x‖=‖y‖ → gauge d beta x=gauge d beta y) := by
  intro hradial
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i,j] at this; omega
  have hs2 : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hnorm1 : ‖(1:ℝ) • PaperReflection.axis i+(1:ℝ) • PaperReflection.axis j‖ =
      ‖Real.sqrt 2 • PaperReflection.axis i‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [diagonal_norm_sq d i j hij, axis_norm_sq, hs2]
    norm_num
  have hnorm2 : ‖(Real.sqrt 2/2) • PaperReflection.axis i+(Real.sqrt 2/2) • PaperReflection.axis j‖ =
      ‖(1:ℝ) • PaperReflection.axis i‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [diagonal_norm_sq d i j hij, axis_norm_sq]
    nlinarith
  have h1 := hradial _ _ hnorm1
  have h2 := hradial _ _ hnorm2
  rw [gauge_diagonal_value d beta 1 i j hij, gauge_axis_value] at h1
  rw [gauge_diagonal_value d beta (Real.sqrt 2/2) i j hij, gauge_axis_value] at h2
  have ht : 2*(Real.sqrt (2:ℝ)/2) = Real.sqrt 2 := by ring
  rw [ht] at h2
  norm_num at h1
  have hstrict := mul_lt_mul_of_pos_left (logCosh_twice_lt_four 1 (by norm_num)) hbeta
  norm_num at hstrict
  nlinarith

theorem gauge_not_quadratic_homogeneous (d : ℕ) (hd : 0 < d) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ x : Vec d, gauge d beta ((2:ℝ) • x) ≠ 4*gauge d beta x := by
  let i : Fin d := ⟨0,hd⟩
  refine ⟨PaperReflection.axis i, ?_⟩
  have h1 := gauge_axis_value d beta 1 i
  have h2 := gauge_axis_value d beta 2 i
  simp only [one_smul] at h1
  rw [h1,h2]
  have hstrict := mul_lt_mul_of_pos_left (logCosh_twice_lt_four 1 (by norm_num)) hbeta
  norm_num at hstrict
  nlinarith

noncomputable def quadraticValue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Vec d) : ℝ :=
  ∑ i, ∑ j, A i j*x i*x j

theorem quadraticValue_axis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    quadraticValue A (PaperReflection.axis i) = A i i := by
  simp [quadraticValue, PaperReflection.axis, PiLp.single_apply, mul_ite]

theorem quadraticValue_two_axes {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) (u v : ℝ) :
    quadraticValue A (u • PaperReflection.axis i+v • PaperReflection.axis j) =
      u^2*A i i+u*v*(A i j+A j i)+v^2*A j j := by
  simp [quadraticValue, PaperReflection.axis, PiLp.single_apply, mul_add,
    Finset.sum_add_distrib, mul_ite, mul_comm, mul_left_comm]
  ring

theorem coordinateFlip_two_axes {d : ℕ} (i j : Fin d) (hij : i ≠ j) (u v : ℝ) :
    PaperReflection.coordinateFlip i (u • PaperReflection.axis i+v • PaperReflection.axis j) =
      (-u) • PaperReflection.axis i+v • PaperReflection.axis j := by
  ext k
  by_cases hki : k=i
  · subst k
    simp [PaperReflection.coordinateFlip, PaperReflection.signedCoordinates,
      PaperReflection.axis, PiLp.toLp_apply, hij]
  · by_cases hkj : k=j
    · subst k
      simp [PaperReflection.coordinateFlip, PaperReflection.signedCoordinates,
        PaperReflection.axis, PiLp.toLp_apply, Ne.symm hij]
    · simp [PaperReflection.coordinateFlip, PaperReflection.signedCoordinates,
        PaperReflection.axis, PiLp.toLp_apply, hki, hkj]

theorem gauge_no_ordered_quadratic_gauge (d : ℕ) (hd : 2 ≤ d) (beta : ℝ) (hbeta : 0 < beta)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose=A) :
    ¬ (∀ x y : Vec d, gauge d beta x ≤ gauge d beta y ↔ quadraticValue A x ≤ quadraticValue A y) := by
  intro horder
  have hQflip : ∀ i x, quadraticValue A (PaperReflection.coordinateFlip i x) = quadraticValue A x := by
    intro i x
    apply le_antisymm
    · exact (horder _ _).mp (by rw [gauge_coordinateFlip])
    · exact (horder _ _).mp (by rw [gauge_coordinateFlip])
  have hdiag : ∀ i j : Fin d, A i i=A j j := by
    intro i j
    have hi := gauge_axis_value d beta 1 i
    have hj := gauge_axis_value d beta 1 j
    simp only [one_smul] at hi hj
    have heq : gauge d beta (PaperReflection.axis i)=gauge d beta (PaperReflection.axis j) := hi.trans hj.symm
    have hQeq : quadraticValue A (PaperReflection.axis i)=quadraticValue A (PaperReflection.axis j) := by
      apply le_antisymm
      · exact (horder _ _).mp (le_of_eq heq)
      · exact (horder _ _).mp (le_of_eq heq.symm)
    simpa only [quadraticValue_axis] using hQeq
  have hoff : ∀ i j : Fin d, i ≠ j → A i j=0 := by
    intro i j hij
    have h := hQflip i ((1:ℝ) • PaperReflection.axis i+(1:ℝ) • PaperReflection.axis j)
    rw [coordinateFlip_two_axes i j hij, quadraticValue_two_axes, quadraticValue_two_axes] at h
    have hsym : A j i=A i j := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hA
    norm_num at h
    linarith
  let i0 : Fin d := ⟨0,by omega⟩
  let c := A i0 i0
  have hentry : ∀ i j : Fin d, A i j=if i=j then c else 0 := by
    intro i j
    by_cases hij : i=j
    · subst j
      simpa only [if_true] using hdiag i i0
    · rw [if_neg hij]
      exact hoff i j hij
  have hscalar : ∀ x : Vec d, quadraticValue A x=c*‖x‖^2 := by
    intro x
    unfold quadraticValue
    simp_rw [hentry]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Finset.mul_sum, pow_two, mul_assoc]
  apply gauge_not_radial d hd beta hbeta
  intro x y hnorm
  have hquadratic : quadraticValue A x=quadraticValue A y := by rw [hscalar, hscalar, hnorm]
  exact le_antisymm ((horder x y).mpr (le_of_eq hquadratic)) ((horder y x).mpr (le_of_eq hquadratic.symm))

theorem gauge_no_monotone_quadratic_representation (d : ℕ) (hd : 2 ≤ d) (beta : ℝ) (hbeta : 0 < beta) :
    ¬ (∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose=A ∧ ∃ Phi : ℝ → ℝ,
      StrictMono Phi ∧ ∀ x : Vec d, gauge d beta x=Phi (quadraticValue A x)) := by
  rintro ⟨A,hA,Phi,hPhi,hrepr⟩
  apply gauge_no_ordered_quadratic_gauge d hd beta hbeta A hA
  intro x y
  rw [hrepr,hrepr]
  exact hPhi.le_iff_le

theorem gauge_unique_minimum (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x : Vec d)
    (hx : gauge d beta x=gauge d beta 0) : x=0 := by
  apply (gauge_strictConvex d beta hbeta).eq_of_isMinOn
    (x:=x) (y:=0) ?_ ?_ (mem_univ _) (mem_univ _)
  · intro y hy
    rw [hx]
    exact gauge_global_minimum d beta hbeta y
  · intro y hy
    exact gauge_global_minimum d beta hbeta y

theorem translated_gauge_hasGradient (d : ℕ) (beta : ℝ) (a x : Vec d) :
    HasGradientAt (fun y => gauge d beta (y-a)) (gaugeGradient d beta (x-a)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (gauge_hasGradient d beta (x-a)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa using! h

theorem translated_gauge_lipschitz (d : ℕ) (beta : NNReal) (a : Vec d) :
    LipschitzWith beta (fun x => gaugeGradient d beta (x-a)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have h := (gaugeGradient_lipschitz d beta).norm_sub_le (x-a) (y-a)
  simpa only [show (x-a)-(y-a)=x-y by abel] using h

theorem translated_gauge_convex (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (a : Vec d) :
    ConvexOn ℝ univ (fun x => gauge d beta (x-a)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy alpha beta' halpha hbeta' hab
  have h := (gauge_strictConvex d beta hbeta).convexOn.2
    (mem_univ (x-a)) (mem_univ (y-a)) halpha hbeta' hab
  have hcombo : alpha • (x-a)+beta' • (y-a)=(alpha • x+beta' • y)-a := by
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun r : ℝ => r*a i) hab]
  simpa only [hcombo] using h

/-- The explicit example actually satisfies the complete reflection algorithm theorem. -/
theorem explicit_gauge_reflection_algorithm
    (d : ℕ) (hd : 0 < d) (beta : NNReal) (a : Vec d) (R epsilon Q : ℝ)
    (hR : 0 < R) (hepsilon : 0 < epsilon) (ha : ‖a‖ ≤ R)
    (hQ : 32 ≤ Q) (hQdef : Q=(beta:ℝ)*R^2/epsilon)
    (comparison : Vec d → Vec d → Ordering)
    (hcomparison : ∀ x y, comparison x y=.gt ↔ gauge d beta (y-a)<gauge d beta (x-a))
    (hbeta : 0 < beta) :
    let n := PaperReflection.publicSteps d Q
    let out := PaperReflection.reflectionSearch (PaperReflection.coordinateOracle comparison) R n
    gauge d beta (out.estimate-a)-gauge d beta 0 ≤ epsilon/2 ∧ out.queries ≤ 2*d*(n+1) := by
  have h := PaperReflection.exact_comparison_reflection_complete (gauge d beta) id
    (gauge_strictConvex d beta hbeta) (gauge_coordinateFlip d beta) strictMono_id
    a R epsilon Q beta (by simpa using hd) hR hepsilon ha hQ hQdef
    (fun x => gaugeGradient d beta (x-a))
    (fun x => by simpa only [PaperReflection.translatedObjective, id_eq] using! translated_gauge_hasGradient d beta a x)
    (translated_gauge_lipschitz d beta a) comparison
    (fun x y => by simpa only [PaperReflection.translatedObjective, id_eq] using hcomparison x y)
  simpa only [Fintype.card_fin, PaperReflection.translatedObjective, id_eq, sub_self] using h

end PaperLogCosh


end SnapshotModule_086
/- END logcosh_example -/

/- BEGIN logcosh_taylor -/
section SnapshotModule_087

/- Genuine Taylor remainder and finite sign moments for main.tex:595-597. -/
namespace PaperLogCoshTaylor

open PaperLogCosh Set Filter
open scoped Topology

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

noncomputable def derivativeFormula : ℕ → ℝ → ℝ
  | 0 => logCosh
  | 1 => Real.tanh
  | 2 => fun x => 1-(Real.tanh x)^2
  | 3 => fun x => -2*Real.tanh x+2*(Real.tanh x)^3
  | 4 => fun x => -2+8*(Real.tanh x)^2-6*(Real.tanh x)^4
  | 5 => fun x => 16*Real.tanh x-40*(Real.tanh x)^3+24*(Real.tanh x)^5
  | _ => fun x => 16-136*(Real.tanh x)^2+240*(Real.tanh x)^4-120*(Real.tanh x)^6

theorem tanh_derivative_polynomial (x : ℝ) :
    HasDerivAt Real.tanh (1-(Real.tanh x)^2) x := by
  have heq : 1/(Real.cosh x)^2 = 1-(Real.tanh x)^2 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
    nlinarith [Real.cosh_sq (x:=x)]
  rw [← heq]
  exact hasDerivAt_tanh x

theorem derivativeFormula_step (n : ℕ) (hn : n ≤ 5) (x : ℝ) :
    HasDerivAt (derivativeFormula n) (derivativeFormula (n+1) x) x := by
  have ht := tanh_derivative_polynomial x
  interval_cases n
  · exact hasDerivAt_logCosh x
  · exact ht
  · convert! ((hasDerivAt_const x (1:ℝ)).sub (ht.pow 2)) using 1
    simp only [derivativeFormula]
    ring
  · convert! ((ht.const_mul (-2:ℝ)).add ((ht.pow 3).const_mul 2)) using 1
    simp only [derivativeFormula]
    ring
  · convert! (((hasDerivAt_const x (-2:ℝ)).add ((ht.pow 2).const_mul 8)).sub
      ((ht.pow 4).const_mul 6)) using 1
    simp only [derivativeFormula]
    ring
  · convert! (((ht.const_mul (16:ℝ)).sub ((ht.pow 3).const_mul 40)).add
      ((ht.pow 5).const_mul 24)) using 1
    simp only [derivativeFormula]
    ring

theorem iterated_derivative_formula : ∀ n : ℕ, n ≤ 6 → iteratedDeriv n logCosh=derivativeFormula n := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
    intro hn
    rw [iteratedDeriv_succ, ih (by omega)]
    funext x
    exact (derivativeFormula_step n (by omega) x).deriv

theorem logCosh_contDiff : ContDiff ℝ ⊤ logCosh := by
  simpa only [logCosh] using! Real.contDiff_cosh.log (fun x => ne_of_gt (Real.cosh_pos x))

theorem scalar_taylor_polynomial (x : ℝ) :
    taylorWithinEval logCosh 5 (Icc 0 1) 0 x = x^2/2-x^4/12 := by
  have hwithin : ∀ k : ℕ, iteratedDerivWithin k logCosh (Icc 0 1) 0=iteratedDeriv k logCosh 0 := by
    intro k
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1))
      (logCosh_contDiff.contDiffAt.of_le le_top) (by norm_num)
  have hcoef : ∀ k : ℕ, k ≤ 5 → iteratedDerivWithin k logCosh (Icc 0 1) 0=derivativeFormula k 0 := by
    intro k hk
    rw [hwithin, iterated_derivative_formula k (by omega)]
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval,
    hcoef 0 (by omega), hcoef 1 (by omega), hcoef 2 (by omega), hcoef 3 (by omega),
    hcoef 4 (by omega), hcoef 5 (by omega), derivativeFormula, logCosh_zero]
  ring

theorem scalar_taylor_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |x| ≤ 1 →
    |logCosh x-(x^2/2-x^4/12)| ≤ C*|x|^6 := by
  obtain ⟨C,hC⟩ := exists_taylor_mean_remainder_bound (f:=logCosh) (a:=0) (b:=1) (n:=5)
    (by norm_num) ((logCosh_contDiff.of_le le_top).contDiffOn)
  refine ⟨|C|+1, by positivity, ?_⟩
  intro x hx
  have h := hC |x| ⟨abs_nonneg x,hx⟩
  rw [scalar_taylor_polynomial] at h
  have heven : logCosh |x|=logCosh x := by
    by_cases hpos : 0 ≤ x
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_neg (lt_of_not_ge hpos), logCosh_even]
  have hfour : |x|^4=x^4 := by
    calc
      |x|^4=(|x|^2)^2 := by ring
      _=(x^2)^2 := congrArg (fun r : ℝ => r^2) (sq_abs x)
      _=x^4 := by ring
  simp only [heven, sq_abs, hfour, sub_zero, Real.norm_eq_abs] at h
  have hm := mul_le_mul_of_nonneg_right (le_trans (le_abs_self C) (by linarith : |C| ≤ |C|+1))
    (show 0 ≤ |x|^6 by positivity)
  exact h.trans hm

theorem scalar_taylor_bigO :
    (fun x : ℝ => logCosh x-(x^2/2-x^4/12)) =O[𝓝 0] (fun x : ℝ => x^6) := by
  obtain ⟨C,hC,hbound⟩ := scalar_taylor_bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1)] with x hx
  have hx' : |x| ≤ 1 := le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx)
  simpa only [Real.norm_eq_abs, abs_pow] using hbound x hx'

def signSplit (d : ℕ) : Signs (d+1) ≃ Bool × Signs d where
  toFun s := (s 0, fun i => s i.succ)
  invFun bs := Fin.cons bs.1 bs.2
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv bs := by rcases bs with ⟨b,s⟩; rfl

noncomputable def tailVector {d : ℕ} (x : Vec (d+1)) : Vec d :=
  WithLp.toLp 2 (fun i => x i.succ)

theorem sign_sum_split (d : ℕ) (F : Signs (d+1) → ℝ) :
    (∑ s : Signs (d+1), F s) = ∑ b : Bool, ∑ s : Signs d, F (Fin.cons b s) := by
  have h := Equiv.sum_comp (signSplit d).symm F
  have h' : (∑ s : Signs (d+1), F s) =
      ∑ bs : Bool × Signs d, F (Fin.cons bs.1 bs.2) := h.symm
  exact h'.trans (Fintype.sum_prod_type _)

theorem signed_inner_split (d : ℕ) (x : Vec (d+1)) (b : Bool) (s : Signs d) :
    inner ℝ (signVector (Fin.cons b s)) x =
      signScalar b*x 0+inner ℝ (signVector s) (tailVector x) := by
  rw [signed_inner, Fin.sum_univ_succ, signed_inner]
  simp [tailVector, PiLp.toLp_apply]

theorem sign_fourth_moment : ∀ (d : ℕ) (x : Vec d),
    (∑ s : Signs d, (inner ℝ (signVector s) x)^4) =
      (2:ℝ)^d*(3*‖x‖^4-2*∑ i : Fin d, (x i)^4) := by
  intro d
  induction d with
  | zero =>
    intro x
    have hx : x=0 := by ext i; exact Fin.elim0 i
    rw [hx]
    simp
  | succ d ih =>
    intro x
    let a : ℝ := x 0
    let y := tailVector x
    have hnorm : ‖x‖^2=a^2+‖y‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq]
      rfl
    have hfour : (∑ i : Fin (d+1), (x i)^4)=a^4+∑ i : Fin d, (y i)^4 := by
      rw [Fin.sum_univ_succ]
      rfl
    have hpair : ∀ r : ℝ, (∑ b : Bool, (signScalar b*a+r)^4)=2*a^4+12*a^2*r^2+2*r^4 := by
      intro r
      rw [Fintype.sum_bool]
      norm_num [signScalar]
      ring
    have hrec : (∑ s : Signs (d+1), (inner ℝ (signVector s) x)^4) =
        2*(2:ℝ)^d*a^4+12*a^2*(∑ s : Signs d, (inner ℝ (signVector s) y)^2)+
          2*(∑ s : Signs d, (inner ℝ (signVector s) y)^4) := by
      rw [sign_sum_split, Finset.sum_comm]
      simp_rw [signed_inner_split]
      change (∑ s : Signs d, ∑ b : Bool, (signScalar b*a+inner ℝ (signVector s) y)^4)=_
      simp_rw [hpair]
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [hrec, sign_isotropy, ih, show ‖x‖^4=(‖x‖^2)^2 by ring, hnorm, hfour, pow_succ]
    ring

theorem signVector_norm (d : ℕ) (s : Signs d) : ‖signVector s‖=Real.sqrt (d:ℝ) := by
  have hsquare : ‖signVector s‖^2=(d:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [signVector, signScalar_sq]
  have hroot := Real.sq_sqrt (show (0:ℝ) ≤ d by positivity)
  nlinarith [norm_nonneg (signVector s), Real.sqrt_nonneg (d:ℝ)]

noncomputable def quarticPolynomial (d : ℕ) (beta : ℝ) (x : Vec d) : ℝ :=
  beta/2*‖x‖^2-beta/12*(3*‖x‖^4-2*∑ i : Fin d, (x i)^4)

theorem gauge_taylor_bound (d : ℕ) (hd : 0 < d) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ x : Vec d, ‖x‖ ≤ r →
      |gauge d beta x-quarticPolynomial d beta x| ≤ C*‖x‖^6 := by
  obtain ⟨C,hC,hscalar⟩ := scalar_taylor_bound
  let D : ℝ := Real.sqrt (d:ℝ)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hD2 : D^2=(d:ℝ) := Real.sq_sqrt (by positivity)
  refine ⟨beta*C*(d:ℝ)^3, by positivity, 1/(D+1), by positivity, ?_⟩
  intro x hx
  let remainder : Signs d → ℝ := fun s => logCosh (inner ℝ (signVector s) x)-
    ((inner ℝ (signVector s) x)^2/2-(inner ℝ (signVector s) x)^4/12)
  have hinner : ∀ s : Signs d, |inner ℝ (signVector s) x| ≤ D*‖x‖ := by
    intro s
    simpa only [signVector_norm] using abs_real_inner_le_norm (signVector s) x
  have harg : ∀ s : Signs d, |inner ℝ (signVector s) x| ≤ 1 := by
    intro s
    have hm := mul_le_mul_of_nonneg_left hx hD
    have hratio : D*(1/(D+1)) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one (by positivity : 0 < D+1)).mpr (by linarith)
    exact (hinner s).trans (hm.trans hratio)
  have hrem : ∀ s : Signs d, |remainder s| ≤ C*(D*‖x‖)^6 := by
    intro s
    have h := hscalar (inner ℝ (signVector s) x) (harg s)
    have hp := pow_le_pow_left₀ (abs_nonneg (inner ℝ (signVector s) x)) (hinner s) 6
    exact h.trans (mul_le_mul_of_nonneg_left hp (le_of_lt hC))
  have hidentity : gauge d beta x-quarticPolynomial d beta x =
      beta/(2:ℝ)^d*(∑ s : Signs d, remainder s) := by
    unfold PaperLogCosh.gauge quarticPolynomial remainder
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div]
    rw [sign_isotropy, sign_fourth_moment]
    field_simp
  calc
    |gauge d beta x-quarticPolynomial d beta x| =
        beta/(2:ℝ)^d*|∑ s : Signs d, remainder s| := by
      rw [hidentity, abs_mul, abs_of_pos (by positivity : 0 < beta/(2:ℝ)^d)]
    _ ≤ beta/(2:ℝ)^d*(∑ s : Signs d, |remainder s|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ beta/(2:ℝ)^d*(∑ _s : Signs d, C*(D*‖x‖)^6) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun s _ => hrem s)
    _ = beta*C*(d:ℝ)^3*‖x‖^6 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, signs_card, Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_pow, show D^6=(D^2)^3 by ring, hD2]
      field_simp

/-- The paper's displayed fourth-order formula has a genuine norm-six remainder. -/
theorem gauge_taylor_bigO (d : ℕ) (hd : 0 < d) (beta : ℝ) (hbeta : 0 < beta) :
    (fun x : Vec d => gauge d beta x-
      (beta/2*‖x‖^2-beta/12*(3*‖x‖^4-2*∑ i : Fin d, (x i)^4))) =O[𝓝 0]
        (fun x : Vec d => ‖x‖^6) := by
  obtain ⟨C,hC,r,hr,hbound⟩ := gauge_taylor_bound d hd beta hbeta
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0:Vec d) hr] with x hx
  have hx' : ‖x‖ ≤ r := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ‖x‖^6 by positivity), quarticPolynomial]
    using hbound x hx'

theorem scalar_equal_norm_pair_eventually :
    ∃ rho : ℝ, 0 < rho ∧ ∀ t : ℝ, 0 < t → t < rho →
      logCosh (2*t)/2 < logCosh (Real.sqrt 2*t) := by
  obtain ⟨C,hC,hbound⟩ := scalar_taylor_bound
  let rho : ℝ := min (1/2) (Real.sqrt (1/(240*C)))
  refine ⟨rho, by dsimp [rho]; positivity, ?_⟩
  intro t ht htrho
  have htone : t < 1/2 := lt_of_lt_of_le htrho (min_le_left _ _)
  have htroot : t < Real.sqrt (1/(240*C)) := lt_of_lt_of_le htrho (min_le_right _ _)
  have hroot : (Real.sqrt (1/(240*C)))^2=1/(240*C) := Real.sq_sqrt (by positivity)
  have htsquare : t^2 < 1/(240*C) := by nlinarith [Real.sqrt_nonneg (1/(240*C))]
  have hbudget : 240*C*t^2 < 1 := by
    have h := (lt_div_iff₀ (show 0 < 240*C by positivity)).mp htsquare
    nlinarith
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (2:ℝ) := by positivity
  have hsbound : Real.sqrt (2:ℝ) ≤ 2 := by nlinarith
  have harg1 : |2*t| ≤ 1 := by rw [abs_of_pos (by positivity : 0 < 2*t)]; linarith
  have harg2 : |Real.sqrt 2*t| ≤ 1 := by
    rw [abs_of_pos (mul_pos hspos ht)]
    nlinarith [mul_le_mul_of_nonneg_right hsbound (le_of_lt ht)]
  have hp1 : (2*t)^2/2-(2*t)^4/12=2*t^2-(4/3:ℝ)*t^4 := by ring
  have hs4 : (Real.sqrt (2:ℝ))^4=4 := by
    calc
      _ = ((Real.sqrt (2:ℝ))^2)^2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  have hs6 : (Real.sqrt (2:ℝ))^6=8 := by
    calc
      _ = ((Real.sqrt (2:ℝ))^2)^3 := by ring
      _ = 8 := by rw [hs2]; norm_num
  have hp2 : (Real.sqrt 2*t)^2/2-(Real.sqrt 2*t)^4/12=t^2-(1/3:ℝ)*t^4 := by
    simp only [mul_pow, hs2, hs4]
    ring
  have h1 := hbound (2*t) harg1
  have h2 := hbound (Real.sqrt 2*t) harg2
  rw [hp1, abs_of_pos (by positivity : 0 < 2*t), mul_pow] at h1
  rw [hp2, abs_of_pos (mul_pos hspos ht), mul_pow, hs6] at h2
  have h1up := (abs_le.mp h1).2
  have h2low := (abs_le.mp h2).1
  have hmul := mul_lt_mul_of_pos_right hbudget (pow_pos ht 4)
  have hmargin : 40*C*t^6 < t^4/3 := by nlinarith [pow_pos ht 4]
  norm_num at h1up
  nlinarith

/-- The particular equal-norm pair in the manuscript differs for every sufficiently small t>0. -/
theorem gauge_equal_norm_pair_eventually (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (i j : Fin d) (hij : i ≠ j) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ t : ℝ, 0 < t → t < rho →
      ‖t • (PaperReflection.axis i+PaperReflection.axis j)‖=‖(Real.sqrt 2*t) • PaperReflection.axis i‖ ∧
      gauge d beta (t • (PaperReflection.axis i+PaperReflection.axis j)) <
        gauge d beta ((Real.sqrt 2*t) • PaperReflection.axis i) := by
  obtain ⟨rho,hrho,hscalar⟩ := scalar_equal_norm_pair_eventually
  refine ⟨rho,hrho,?_⟩
  intro t ht htrho
  constructor
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [smul_add, diagonal_norm_sq d i j hij, axis_norm_sq, mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · rw [smul_add, gauge_diagonal_value d beta t i j hij, gauge_axis_value]
    have h := mul_lt_mul_of_pos_left (hscalar t ht htrho) hbeta
    nlinarith

end PaperLogCoshTaylor


end SnapshotModule_087
/- END logcosh_taylor -/

/- BEGIN logcosh_hessian -/
section SnapshotModule_088

/- Genuine Hessian and vanishing-ray certificates for main.tex:591-593. -/
namespace PaperLogCoshHessian

open PaperLogCosh Set Filter
open scoped Topology RealInnerProductSpace

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

noncomputable def curvature (t : ℝ) : ℝ := 1/(Real.cosh t)^2

theorem curvature_pos (t : ℝ) : 0 < curvature t := by unfold curvature; positivity

theorem curvature_le_one (t : ℝ) : curvature t ≤ 1 := by
  have h := tanh_deriv_norm_le_one t
  rw [deriv_tanh, Real.norm_eq_abs] at h
  change |curvature t| ≤ 1 at h
  rw [abs_of_pos (curvature_pos t)] at h
  exact h

noncomputable def rankOne {d : ℕ} (s : Signs d) : Vec d →L[ℝ] Vec d :=
  (InnerProductSpace.toDual ℝ (Vec d) (signVector s)).smulRight (signVector s)

noncomputable def hessianOperator (d : ℕ) (beta : ℝ) (x : Vec d) : Vec d →L[ℝ] Vec d :=
  (beta/(2:ℝ)^d) • ∑ s : Signs d, curvature (inner ℝ (signVector s) x) • rankOne s

noncomputable def hessianMatrix (d : ℕ) (beta : ℝ) (x : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => beta/(2:ℝ)^d * ∑ s : Signs d,
    curvature (inner ℝ (signVector s) x)*signScalar (s i)*signScalar (s j)

theorem hessian_is_derivative (d : ℕ) (beta : ℝ) (x : Vec d) :
    HasFDerivAt (gaugeGradient d beta) (hessianOperator d beta x) x := by
  have hterm : ∀ s : Signs d,
      HasFDerivAt (fun z : Vec d => Real.tanh (inner ℝ (signVector s) z) • signVector s)
        (curvature (inner ℝ (signVector s) x) • rankOne s) x := by
    intro s
    have hl := (InnerProductSpace.toDual ℝ (Vec d) (signVector s)).hasFDerivAt (x:=x)
    have hc := (hasDerivAt_tanh (inner ℝ (signVector s) x)).comp_hasFDerivAt x hl
    have h := hc.smul_const (signVector s)
    convert! h using 1
    ext v
    simp [rankOne, curvature, InnerProductSpace.toDual_apply_apply, mul_assoc]
  have hsum := HasFDerivAt.sum (fun s (_ : s ∈ Finset.univ) => hterm s)
  have hscaled := hsum.const_smul (beta/(2:ℝ)^d)
  convert! hscaled using 1
  · funext y
    simp [gaugeGradient, Finset.sum_apply]

theorem hessian_matrix_entry (d : ℕ) (beta : ℝ) (x : Vec d) (i j : Fin d) :
    (hessianOperator d beta x (PaperReflection.axis j)) i=hessianMatrix d beta x i j := by
  have hcoord : ∀ v : Vec d, v i=inner ℝ (PaperReflection.axis i) v := by
    intro v
    simp [PaperReflection.axis, EuclideanSpace.inner_single_left]
  rw [hcoord]
  simp [hessianOperator, hessianMatrix, rankOne, InnerProductSpace.toDual_apply_apply,
    PaperReflection.axis, signVector,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem hessian_matrix_symmetric (d : ℕ) (beta : ℝ) (x : Vec d) :
    (hessianMatrix d beta x).transpose=hessianMatrix d beta x := by
  ext i j
  unfold hessianMatrix
  simp only [Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem hessian_quadratic_form (d : ℕ) (beta : ℝ) (x v : Vec d) :
    inner ℝ (hessianOperator d beta x v) v =
      beta/(2:ℝ)^d * ∑ s : Signs d, curvature (inner ℝ (signVector s) x)*(inner ℝ (signVector s) v)^2 := by
  simp [hessianOperator, rankOne, InnerProductSpace.toDual_apply_apply, sum_inner,
    real_inner_smul_left, Finset.mul_sum, pow_two]

theorem hessian_quadratic_bounds (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (x v : Vec d) :
    0 ≤ inner ℝ (hessianOperator d beta x v) v ∧
      inner ℝ (hessianOperator d beta x v) v ≤ beta*‖v‖^2 := by
  rw [hessian_quadratic_form]
  constructor
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (le_of_lt (curvature_pos _)) (sq_nonneg _))
  · have hsum : (∑ s : Signs d, curvature (inner ℝ (signVector s) x)*(inner ℝ (signVector s) v)^2) ≤
        ∑ s : Signs d, (inner ℝ (signVector s) v)^2 := by
      apply Finset.sum_le_sum
      intro s hs
      have h := mul_le_mul_of_nonneg_right (curvature_le_one (inner ℝ (signVector s) x))
        (sq_nonneg (inner ℝ (signVector s) v))
      simpa only [one_mul] using h
    have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ beta/(2:ℝ)^d by positivity)
    rw [sign_isotropy] at hscaled
    calc
      _ ≤ beta/(2:ℝ)^d*((2:ℝ)^d*‖v‖^2) := hscaled
      _ = beta*‖v‖^2 := by field_simp

theorem hessian_quadratic_positive (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x v : Vec d) (hv : v ≠ 0) : 0 < inner ℝ (hessianOperator d beta x v) v := by
  rw [hessian_quadratic_form]
  obtain ⟨s,hs⟩ := exists_distinguishing_sign d v 0 hv
  have hs' : inner ℝ (signVector s) v ≠ 0 := by simpa using hs
  apply mul_pos (by positivity)
  apply Finset.sum_pos'
  · intro s hs
    exact mul_nonneg (le_of_lt (curvature_pos _)) (sq_nonneg _)
  · exact ⟨s,Finset.mem_univ _,mul_pos (curvature_pos _) (sq_pos_of_ne_zero hs')⟩

theorem hessian_outer_product_formula (d : ℕ) (beta : ℝ) (x : Vec d) :
    hessianMatrix d beta x = (beta/(2:ℝ)^d) •
      ∑ s : Signs d, curvature (inner ℝ (signVector s) x) •
        (fun i j : Fin d => signScalar (s i)*signScalar (s j)) := by
  ext i j
  simp [hessianMatrix, Finset.mul_sum, mul_assoc]

theorem cosh_tendsto_atTop : Tendsto Real.cosh atTop atTop := by
  have he : Tendsto (fun t : ℝ => Real.exp t/2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 2) Real.tendsto_exp_atTop
  apply tendsto_atTop_mono (fun t => ?_) he
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-t)]

theorem curvature_linear_tendsto_zero (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun t : ℝ => curvature (c*t)) atTop (𝓝 0) := by
  have hpositive : ∀ a : ℝ, 0 < a → Tendsto (fun t : ℝ => curvature (a*t)) atTop (𝓝 0) := by
    intro a ha
    have hcosh := cosh_tendsto_atTop.comp (tendsto_id.const_mul_atTop ha)
    have h := hcosh.inv_tendsto_atTop.pow 2
    change Tendsto (fun t : ℝ => ((Real.cosh (a*t))⁻¹)^2) atTop (𝓝 ((0:ℝ)^2)) at h
    simpa only [curvature, one_div, inv_pow, zero_pow (by norm_num : (2:ℕ) ≠ 0)] using h
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have h := hpositive (-c) (by linarith)
    simpa only [neg_mul, curvature, Real.cosh_neg] using h
  · exact hpositive c hpos

def signInteger (b : Bool) : ℤ := if b then 1 else -1

def powerCoefficient (d : ℕ) (s : Signs d) : ℤ :=
  ∑ i : Fin d, signInteger (s i)*(2:ℤ)^i.val

theorem powerCoefficient_succ (d : ℕ) (s : Signs (d+1)) :
    powerCoefficient (d+1) s = signInteger (s 0)+2*powerCoefficient d (fun i => s i.succ) := by
  unfold powerCoefficient
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
  have hterm : ∀ i : Fin d,
      signInteger (s i.succ)*(2:ℤ)^(i.val+1)=2*(signInteger (s i.succ)*(2:ℤ)^i.val) := by
    intro i
    rw [pow_succ]
    ring
  simp_rw [hterm]
  rw [Finset.mul_sum]

theorem powerCoefficient_ne_zero (d : ℕ) (hd : 0 < d) (s : Signs d) : powerCoefficient d s ≠ 0 := by
  cases d with
  | zero => omega
  | succ d =>
    rw [powerCoefficient_succ]
    cases hs : s 0 <;> norm_num [signInteger] <;> omega

noncomputable def powerRay (d : ℕ) : Vec d := WithLp.toLp 2 (fun i => (2:ℝ)^i.val)

theorem signed_inner_powerRay (d : ℕ) (s : Signs d) :
    inner ℝ (signVector s) (powerRay d)=(powerCoefficient d s:ℝ) := by
  rw [signed_inner]
  unfold powerCoefficient
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  cases hs : s i <;> simp [signInteger, signScalar, powerRay]

theorem signed_inner_powerRay_ne_zero (d : ℕ) (hd : 0 < d) (s : Signs d) :
    inner ℝ (signVector s) (powerRay d) ≠ 0 := by
  rw [signed_inner_powerRay]
  exact_mod_cast powerCoefficient_ne_zero d hd s

/-- Every sign has nonzero slope on the paper's explicit powers-of-two ray. -/
theorem curvature_powerRay_tendsto_zero (d : ℕ) (hd : 0 < d) (s : Signs d) :
    Tendsto (fun t : ℝ => curvature (inner ℝ (signVector s) (t • powerRay d))) atTop (𝓝 0) := by
  have h := curvature_linear_tendsto_zero (inner ℝ (signVector s) (powerRay d))
    (signed_inner_powerRay_ne_zero d hd s)
  simpa only [real_inner_smul_right, mul_comm] using h

/-- Finite sign summation gives convergence of the actual Hessian in operator norm. -/
theorem hessian_powerRay_tendsto_zero (d : ℕ) (hd : 0 < d) (beta : ℝ) :
    Tendsto (fun t : ℝ => hessianOperator d beta (t • powerRay d)) atTop (𝓝 0) := by
  have hterm : ∀ s : Signs d, Tendsto
      (fun t : ℝ => curvature (inner ℝ (signVector s) (t • powerRay d)) • rankOne s) atTop (𝓝 0) := by
    intro s
    have h := (curvature_powerRay_tendsto_zero d hd s).smul_const (rankOne s)
    convert! h using 1
    congr 1
    ext v i
    simp
  have hsum := tendsto_finsetSum Finset.univ (fun s hs => hterm s)
  have hscaled := (tendsto_const_nhds (x:=beta/(2:ℝ)^d)).smul hsum
  simpa only [hessianOperator, Finset.sum_const_zero, smul_zero] using hscaled

theorem real_eigenvalue_abs_le_opnorm {d : ℕ} (H : Vec d →L[ℝ] Vec d)
    (lambda : ℝ) (v : Vec d) (hv : v ≠ 0) (heigen : H v=lambda • v) : |lambda| ≤ ‖H‖ := by
  have h := H.le_opNorm v
  rw [heigen, norm_smul, Real.norm_eq_abs] at h
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp h

/-- Uniform control of all real eigenpairs, without choosing eigenvectors along the ray. -/
theorem every_eigenvalue_on_powerRay_tends_to_zero (d : ℕ) (hd : 0 < d) (beta epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ t : ℝ in atTop, ∀ (lambda : ℝ) (v : Vec d), v ≠ 0 →
      hessianOperator d beta (t • powerRay d) v=lambda • v → |lambda| < epsilon := by
  have hnorm := (hessian_powerRay_tendsto_zero d hd beta).norm
  have hnorm0 : Tendsto (fun t : ℝ => ‖hessianOperator d beta (t • powerRay d)‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [norm_zero] using hnorm
  have hevent : ∀ᶠ t : ℝ in atTop, ‖hessianOperator d beta (t • powerRay d)‖ < epsilon := by
    exact hnorm0.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hevent] with t ht
  intro lambda v hv heigen
  exact (real_eigenvalue_abs_le_opnorm _ lambda v hv heigen).trans_lt ht

end PaperLogCoshHessian


end SnapshotModule_088
/- END logcosh_hessian -/

/- BEGIN normalization_parameters -/
section SnapshotModule_089

namespace PaperNormalizationParameters
noncomputable section

lemma inverse_q_root (beta R epsilon Q : ℝ) (hb : 0 < beta) (hR : 0 < R)
    (he : 0 < epsilon) (hQ : Q=beta*R^2/epsilon) :
    Real.sqrt (1/Q)=Real.sqrt (epsilon/beta)/R := by
  have hQpos : 0 < Q := by rw [hQ]; positivity
  apply (Real.sqrt_eq_iff_eq_sq (by positivity : 0 ≤ 1/Q) (by positivity)).mpr
  rw [div_pow,Real.sq_sqrt (by positivity),hQ]
  field_simp

lemma centroid_delta (beta R epsilon Q : ℝ) (hb : 0 < beta) (hR : 0 < R)
    (he : 0 < epsilon) (hQ : Q=beta*R^2/epsilon) :
    Real.sqrt (1/Q)/16=Real.sqrt (epsilon/beta)/(16*R) := by
  rw [inverse_q_root beta R epsilon Q hb hR he hQ]
  ring

lemma centroid_volume_ratio (beta R epsilon Q : ℝ) (hb : 0 < beta) (hR : 0 < R)
    (he : 0 < epsilon) (hQ : Q=beta*R^2/epsilon) :
    2/Real.sqrt (1/Q)=(2*R)/Real.sqrt (epsilon/beta) := by
  rw [inverse_q_root beta R epsilon Q hb hR he hQ]
  field_simp

lemma centroid_original_probe (delta beta R epsilon : ℝ)
    (hb : 0 < beta) (hR : 0 < R) :
    R*(delta*(epsilon/(beta*R^2))/3)=(delta*(epsilon/(3*R)))/beta := by
  field_simp
  <;> ring

end
end PaperNormalizationParameters

end SnapshotModule_089
/- END normalization_parameters -/

/- BEGIN series_literals -/
section SnapshotModule_090

namespace PaperSeries

lemma bernoulli_six : bernoulli 6 = (1 / 42 : ℚ) := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, show Nat.choose 5 2 = 10 by decide]
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, h5, show Nat.choose 6 2 = 15 by decide, show Nat.choose 6 4 = 15 by decide]
  norm_num [bernoulli, h6]

lemma hasSum_six : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (Real.pi ^ 6 / 945) := by
  have hh := hasSum_zeta_nat (show (3 : ℕ) ≠ 0 by decide)
  norm_num [bernoulli_six, Nat.factorial] at hh
  convert hh using 1 <;> (first | rfl | ring)

lemma zeta_six_lt : Real.pi ^ 6 / 945 < (102 / 100 : ℝ) := by
  have hp := Real.pi_lt_d4
  have hnonneg := Real.pi_pos.le
  have hpow := pow_le_pow_left₀ hnonneg hp.le 6
  norm_num at hpow
  nlinarith

lemma finite_six_bound (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ^ 6) < (102 / 100 : ℝ) := by
  have hh := Summable.sum_le_tsum (Finset.range (n+1))
    (fun k _ => show (0:ℝ) ≤ 1 / (k:ℝ)^6 by positivity) hasSum_six.summable
  rw [hasSum_six.tsum_eq, Finset.sum_range_succ'] at hh
  have hb : (∑ k ∈ Finset.range n, (1:ℝ)/((k:ℝ)+1)^6) ≤ Real.pi^6/945 := by simpa using hh
  exact hb.trans_lt zeta_six_lt

lemma first_six_envelope (k : ℝ) (hk : 1 ≤ k) :
    (k+1)^2/k^8 ≤ 4/k^6 := by
  have hp : 0 < k := by linarith
  have hn : (k+1)^2 ≤ 4*k^2 := by nlinarith
  calc
    (k+1)^2/k^8 ≤ (4*k^2)/k^8 := by gcongr
    _ = 4/k^6 := by field_simp [ne_of_gt hp]

lemma literal_first_sum (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (9/32:ℝ)*(9/20000)*((k:ℝ)+2)^2/((k:ℝ)+1)^8) ≤
      (41/10:ℝ)*(9/32)*(9/20000) := by
  have hterm : ∀ k : ℕ,
      (9/32:ℝ)*(9/20000)*((k:ℝ)+2)^2/((k:ℝ)+1)^8 ≤
      (4*(9/32:ℝ)*(9/20000))*(1/((k:ℝ)+1)^6) := by
    intro k
    have hh := mul_le_mul_of_nonneg_left
      (first_six_envelope ((k:ℝ)+1) (by linarith [Nat.cast_nonneg (α:=ℝ) k]))
      (by norm_num : (0:ℝ) ≤ (9/32:ℝ)*(9/20000))
    convert hh using 1 <;> (first | rfl | ring)
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => hterm k)
  have hf := mul_lt_mul_of_pos_left (finite_six_bound n)
    (by norm_num : (0:ℝ) < 4*(9/32:ℝ)*(9/20000))
  rw [Finset.mul_sum] at hf
  linarith

open PaperFullHistory
lemma literal_cumulative_bound (n : ℕ) :
    cumulativeError n ≤ (41/10:ℝ)*kap*nu+30*kap*(3/100:ℝ)*Real.pi^2/6 := by
  have hfirst : (∑ k ∈ Finset.range n, weight (k+1)*xi k) ≤ (41/10:ℝ)*kap*nu := by
    apply le_trans (Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => weight_xi_envelope k))
    simpa [kap,nu] using literal_first_sum n
  let env : ℕ → ℝ := fun k =>
    2*kap*(3/100:ℝ)*((k:ℝ)+3)*((k:ℝ)+5)/((k:ℝ)+1)^4
  have hsecond : (∑ k ∈ Finset.range n, stepWeight (k+1)*previousError k) ≤
      ∑ k ∈ Finset.range n, env k := by
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_range_succ']
      simp only [previousError, ↓reduceIte, mul_zero, add_zero]
      calc
        _ ≤ ∑ k ∈ Finset.range n, env k := by
          apply Finset.sum_le_sum
          intro k _
          simpa [env,Nat.add_assoc,previousError] using previousError_envelope k
        _ ≤ ∑ k ∈ Finset.range (n+1), env k := by
          rw [Finset.sum_range_succ]
          have hh : 0 ≤ env n := by unfold env kap; positivity
          linarith
  have henv : (∑ k ∈ Finset.range n, env k) ≤ 30*kap*(3/100:ℝ)*(Real.pi^2/6) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, (30*kap*(3/100:ℝ))*(1/((k:ℝ)+1)^2) := by
        apply Finset.sum_le_sum
        intro k _
        have hh := mul_le_mul_of_nonneg_left
          (error_second_term_envelope ((k:ℝ)+1) (by linarith [Nat.cast_nonneg (α:=ℝ) k]))
          (show 0 ≤ 2*kap*(3/100:ℝ) by norm_num [kap])
        change env k ≤ _
        convert hh using 1 <;> (try dsimp [env]) <;> (first | rfl | ring)
      _ = (30*kap*(3/100:ℝ))*(∑ k ∈ Finset.range n, (1:ℝ)/((k:ℝ)+1)^2) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (shifted_basel_bound n)
          (show 0 ≤ 30*kap*(3/100:ℝ) by norm_num [kap])
        exact hh
  have ht := add_le_add hfirst (hsecond.trans henv)
  simpa only [cumulativeError,additiveError,Finset.sum_add_distrib,mul_div_assoc] using ht

end PaperSeries

end SnapshotModule_090
/- END series_literals -/

/- BEGIN heavy_ball_line_root -/
section SnapshotModule_091

namespace PaperHeavyBallLine
open Set
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def quadratic (A : V→L[ℝ] V) (b : V) (x : V) : ℝ := inner ℝ x (A x)/2-inner ℝ b x

def lineRoot (A : V→L[ℝ] V) (b z v : V) : ℝ := inner ℝ v (b-A z)/inner ℝ v (A v)

lemma energy_symmetry (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (x y : V) :
    inner ℝ x (A y)=inner ℝ y (A x) := by
  have hh := hA x y
  change inner ℝ (A x) y=inner ℝ x (A y) at hh
  rw [←hh,real_inner_comm]

lemma quadratic_line (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b z v : V) (t : ℝ) :
    quadratic A b (z+t • v)=quadratic A b z+t*inner ℝ v (A z-b)+t^2/2*inner ℝ v (A v) := by
  simp only [quadratic,map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,inner_sub_right]
  rw [energy_symmetry A hA z v,real_inner_comm b v]
  ring

lemma root_coefficient (A : V→L[ℝ] V) (b z v : V) (ha : inner ℝ v (A v)≠0) :
    inner ℝ v (A v)*lineRoot A b z v= -inner ℝ v (A z-b) := by
  simp only [lineRoot,inner_sub_right]
  field_simp
  ring

lemma symmetric_comparison_identity (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric)
    (b z v : V) (ha : inner ℝ v (A v)≠0) (t h : ℝ) :
    quadratic A b (z+(t-h) • v)-quadratic A b (z+(t+h) • v)=
      2*h*inner ℝ v (A v)*(lineRoot A b z v-t) := by
  rw [quadratic_line A hA,quadratic_line A hA]
  have hc := root_coefficient A b z v ha
  have he : inner ℝ v (A z-b)= -inner ℝ v (A v)*lineRoot A b z v := by linarith
  rw [he]
  ring

/-- Each executed step uses one comparison between symmetric line points;
the equality branch returns immediately. The depth is a public natural number. -/
def bisect (z v : V) : ℕ→ℝ→ℝ→PaperOracle.Program (V×V) Ordering ℝ
  | 0,l,u => .done ((l+u)/2)
  | k+1,l,u =>
    let mid := (l+u)/2
    .ask (z+(mid-1) • v,z+(mid+1) • v) (fun reply=>
      match reply with
      | .lt=>bisect z v k l mid
      | .eq=>.done mid
      | .gt=>bisect z v k mid u)

lemma bisect_public_cap (z v : V) (k : ℕ) (l u : ℝ) :
    PaperOracle.Program.Cap k (bisect z v k l u) := by
  induction k generalizing l u with
  | zero=>trivial
  | succ k ih=>
    change ∀reply : Ordering,PaperOracle.Program.Cap k (match reply with
      | .lt=>bisect z v k l ((l+u)/2)
      | .eq=>.done ((l+u)/2)
      | .gt=>bisect z v k ((l+u)/2) u)
    intro reply
    cases reply with
    | lt=>exact ih _ _
    | eq=>cases k <;> trivial
    | gt=>exact ih _ _

lemma bisect_stays_in_bracket (C : V×V→Ordering) (z v : V) (k : ℕ) (l u : ℝ) (hlu : l ≤ u) :
    PaperOracle.Program.run C (bisect z v k l u)∈Icc l u := by
  induction k generalizing l u with
  | zero=>dsimp [bisect,PaperOracle.Program.run]; constructor <;> linarith
  | succ k ih=>
    simp only [bisect,PaperOracle.Program.run]
    split
    · have hh:=ih l ((l+u)/2) (by linarith)
      exact ⟨hh.1,hh.2.trans (by linarith)⟩
    · simp only [PaperOracle.Program.run]
      constructor <;> linarith
    · have hh:=ih ((l+u)/2) u (by linarith)
      exact ⟨(by linarith : l ≤ (l+u)/2).trans hh.1,hh.2⟩

lemma bisect_root_error (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric)
    (b z v : V) (ha : 0 < inner ℝ v (A v)) (k : ℕ) (l u : ℝ)
    (hl : l ≤ lineRoot A b z v) (hu : lineRoot A b z v ≤ u) :
    |PaperOracle.Program.run (PaperOracle.comparisonOracle (quadratic A b)) (bisect z v k l u)-lineRoot A b z v|
       ≤ (u-l)/2^(k+1) := by
  induction k generalizing l u with
  | zero=>
    simp only [bisect,PaperOracle.Program.run,pow_one]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  | succ k ih=>
    simp only [bisect,PaperOracle.Program.run]
    split
    · rename_i hlt
      have hh := (PaperOracle.realOrder_eq_lt_iff _ _).mp hlt
      have hid := symmetric_comparison_identity A hA b z v ha.ne' ((l+u)/2) 1
      have hm : lineRoot A b z v ≤ (l+u)/2 := by
        by_contra hn
        have hp := mul_pos (show 0 < 2*inner ℝ v (A v) by positivity) (lt_of_not_ge hn |> sub_pos.mpr)
        nlinarith
      have hi:=ih l ((l+u)/2) hl hm
      rw [pow_succ (2:ℝ) (k+1)]
      have hp : 0 < (2:ℝ)^(k+1) := by positivity
      calc
        _ ≤ ((l+u)/2-l)/(2:ℝ)^(k+1):=hi
        _=(u-l)/((2:ℝ)^(k+1)*2):=by ring
    · rename_i heq
      simp only [PaperOracle.Program.run]
      have hh := (PaperOracle.realOrder_eq_eq_iff _ _).mp heq
      have hid := symmetric_comparison_identity A hA b z v ha.ne' ((l+u)/2) 1
      have hm : (l+u)/2=lineRoot A b z v := by nlinarith
      rw [hm,sub_self,abs_zero]
      exact div_nonneg (by linarith) (by positivity)
    · rename_i hgt
      have hh := (PaperOracle.realOrder_eq_gt_iff _ _).mp hgt
      have hid := symmetric_comparison_identity A hA b z v ha.ne' ((l+u)/2) 1
      have hm : (l+u)/2 ≤ lineRoot A b z v := by
        by_contra hn
        have hp := mul_pos (show 0 < 2*inner ℝ v (A v) by positivity) (sub_pos.mpr (lt_of_not_ge hn))
        nlinarith
      have hi:=ih ((l+u)/2) u hm hu
      rw [pow_succ (2:ℝ) (k+1)]
      calc
        _ ≤ (u-(l+u)/2)/(2:ℝ)^(k+1):=hi
        _=(u-l)/((2:ℝ)^(k+1)*2):=by ring

def horizon (D tolerance : ℝ) : ℕ := ⌈Real.log (D/tolerance)/Real.log 2⌉₊

lemma horizon_precision {D tolerance : ℝ} (hD : 0 < D) (ht : 0 < tolerance) :
    D/(2:ℝ)^(horizon D tolerance) ≤ tolerance := by
  have hceil : Real.logb 2 (D/tolerance) ≤ (horizon D tolerance:ℝ) := Nat.le_ceil _
  have hp : D/tolerance ≤ (2:ℝ)^(horizon D tolerance) := by
    have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (div_pos hD ht)).mp hceil
    simpa only [Real.rpow_natCast] using hh
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(horizon D tolerance))).mpr
  simpa only [mul_comm] using (div_le_iff₀ ht).mp hp

def rootProgram (z v : V) (D tolerance : ℝ) : PaperOracle.Program (V×V) Ordering ℝ :=
  bisect z v (horizon D tolerance) (-D) D

/-- Literal finite comparison implementation of the appendix's line root.
The only objective assumptions here are symmetry, positive line curvature,
and the supplied finite bracket; the bracket is proved from conditioning separately. -/
theorem rootProgram_correct (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric)
    (b z v : V) (ha : 0 < inner ℝ v (A v)) (D tolerance : ℝ)
    (hD : 0 < D) (ht : 0 < tolerance) (hroot : |lineRoot A b z v| ≤ D) :
    PaperOracle.Program.Cap (horizon D tolerance) (rootProgram z v D tolerance) ∧
    |PaperOracle.Program.run (PaperOracle.comparisonOracle (quadratic A b)) (rootProgram z v D tolerance)-lineRoot A b z v|
       ≤ tolerance := by
  refine ⟨bisect_public_cap z v _ _ _,?_⟩
  have hh := bisect_root_error A hA b z v ha (horizon D tolerance) (-D) D
    (abs_le.mp hroot).1 (abs_le.mp hroot).2
  have he : (D- -D)/(2:ℝ)^(horizon D tolerance+1)=D/(2:ℝ)^(horizon D tolerance) := by
    rw [pow_succ]
    ring
  rw [he] at hh
  exact hh.trans (horizon_precision hD ht)

end
end PaperHeavyBallLine

end SnapshotModule_091
/- END heavy_ball_line_root -/

/- BEGIN heavy_ball_conditioned -/
section SnapshotModule_092

namespace PaperHeavyBallLine
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma conditioned_line_curvature (A : V→L[ℝ] V) (mu : ℝ) (hmu : 0 < mu)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (v : V) (hv : v≠0) :
    0 < inner ℝ v (A v) := by
  exact (mul_pos hmu (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hlower v)

lemma conditioned_line_root_bound (A : V→L[ℝ] V) (b xstar z v : V)
    (mu beta R : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ‖A‖ ≤ beta)
    (hsol : A xstar=b) (hstar : ‖xstar‖ ≤ R) (hv : v≠0) :
    |lineRoot A b z v| ≤ (beta/mu)*(‖z‖+R)/‖v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hbeta0 : 0 < beta := hmu.trans_le hbeta
  have hR : 0 ≤ R := (norm_nonneg xstar).trans hstar
  have hdist : ‖xstar-z‖ ≤ ‖z‖+R := (norm_sub_le _ _).trans (by linarith)
  have hnum : |inner ℝ v (b-A z)| ≤ ‖v‖*(beta*(‖z‖+R)) := by
    have hh : ‖b-A z‖ ≤ beta*(‖z‖+R) := by
      rw [←hsol,←map_sub]
      exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hupper (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hdist hbeta0.le))
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hh hvpos.le)
  have ha := conditioned_line_curvature A mu hmu hlower v hv
  rw [lineRoot,abs_div,abs_of_pos ha]
  have hh := div_le_div₀ (by positivity : 0 ≤ ‖v‖*(beta*(‖z‖+R))) hnum
    (mul_pos hmu (sq_pos_of_pos hvpos)) (hlower v)
  have he : (‖v‖*(beta*(‖z‖+R)))/(mu*‖v‖^2)=(beta/mu)*(‖z‖+R)/‖v‖ := by
    field_simp
    <;> ring
  exact hh.trans_eq he

def conditionedBracket (mu beta R : ℝ) (z v : V) : ℝ := (beta/mu)*(‖z‖+R)/‖v‖

/-- The complete actual root bisection from known conditioning and localization;
no root bracket or bisection-correctness premise is supplied. -/
theorem conditioned_root_correct (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b xstar z v : V)
    (mu beta R tolerance : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ‖A‖ ≤ beta)
    (hsol : A xstar=b) (hstar : ‖xstar‖ ≤ R) (hv : v≠0) (ht : 0 < tolerance) :
    PaperOracle.Program.Cap (horizon (conditionedBracket mu beta R z v) tolerance)
      (rootProgram z v (conditionedBracket mu beta R z v) tolerance) ∧
    |PaperOracle.Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (rootProgram z v (conditionedBracket mu beta R z v) tolerance)-lineRoot A b z v| ≤ tolerance := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hb : 0 < beta := hmu.trans_le hbeta
  apply rootProgram_correct A hA b z v (conditioned_line_curvature A mu hmu hlower v hv)
  · dsimp [conditionedBracket]
    positivity
  · exact ht
  · exact conditioned_line_root_bound A b xstar z v mu beta R hmu hbeta hlower hupper hsol hstar hv

end
end PaperHeavyBallLine

end SnapshotModule_092
/- END heavy_ball_conditioned -/

/- BEGIN dorn_development -/
section SnapshotModule_093

/- Genuine intermediate development for Dorn et al. Theorems 2.1 and 2.5.
   This file does NOT assert either external lower bound. In particular, no
   Wishart/posterior theorem is replaced by an axiom or a lower-bound premise. -/
namespace PaperDorn
noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace
open scoped Matrix

theorem antipodal_average_identity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v z : V) :
    (‖v - z‖ ^ 2 + ‖-v - z‖ ^ 2) / 2 = ‖v‖ ^ 2 + ‖z‖ ^ 2 := by
  have hn : ‖-v - z‖ = ‖v + z‖ := by
    rw [show -v - z = -(v + z) by abel, norm_neg]
  rw [hn, norm_sub_sq_real, norm_add_sq_real]
  ring

theorem antipodal_ball_exclusion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v z : V) {r delta : ℝ} (hr : ‖v‖ = r) (hd : 0 ≤ delta) (hsmall : delta < r) :
    ¬ (‖v - z‖ ≤ delta ∧ ‖-v - z‖ ≤ delta) := by
  rintro ⟨hpos, hneg⟩
  have hp := sq_le_sq₀ (norm_nonneg (v - z)) hd |>.mpr hpos
  have hn := sq_le_sq₀ (norm_nonneg (-v - z)) hd |>.mpr hneg
  have havg := antipodal_average_identity v z
  rw [hr] at havg
  have hrpos : 0 < r := lt_of_le_of_lt hd hsmall
  nlinarith [sq_nonneg ‖z‖]

def sphericalCap {V : Type*} [NormedAddCommGroup V] (r delta : ℝ) (z : V) : Set V :=
  {v | ‖v‖ = r ∧ ‖v - z‖ ≤ delta}

theorem measurable_sphericalCap
    {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    (r delta : ℝ) (z : V) : MeasurableSet (sphericalCap r delta z) := by
  apply MeasurableSet.inter
  · exact (isClosed_eq continuous_norm continuous_const).measurableSet
  · exact (isClosed_le (continuous_id.sub continuous_const).norm continuous_const).measurableSet

theorem symmetric_sphericalCap_half
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (mu : Measure V) [IsProbabilityMeasure mu]
    (hsym : MeasurePreserving (fun v : V => -v) mu mu)
    (r delta : ℝ) (z : V) (hd : 0 ≤ delta) (hsmall : delta < r) :
    mu.real (sphericalCap r delta z) ≤ 1 / 2 := by
  let A := sphericalCap r delta z
  have hA : MeasurableSet A := measurable_sphericalCap r delta z
  have hnegA : MeasurableSet ((fun v : V => -v) ⁻¹' A) := hA.preimage measurable_neg
  have hdisj : Disjoint A ((fun v : V => -v) ⁻¹' A) := by
    apply Set.disjoint_left.mpr
    intro v hv hnv
    exact antipodal_ball_exclusion v z hv.1 hd hsmall ⟨hv.2, hnv.2⟩
  have hm : mu ((fun v : V => -v) ⁻¹' A) = mu A := hsym.measure_preimage hA.nullMeasurableSet
  have hmreal : mu.real ((fun v : V => -v) ⁻¹' A) = mu.real A := by
    simp only [measureReal_def, hm]
  have hu := measureReal_union (μ := mu) hdisj hnegA
  rw [hmreal] at hu
  have hle : mu.real (A ∪ ((fun v : V => -v) ⁻¹' A)) ≤ 1 := measureReal_le_one
  linarith

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

theorem measurable_normalize (n : ℕ) :
    Measurable (fun x : Euclidean n => NormedSpace.normalize x) := by
  unfold NormedSpace.normalize
  fun_prop

theorem stdGaussian_zero_singleton (n : ℕ) :
    ProbabilityTheory.stdGaussian (Euclidean n) {0} = 0 := by
  letI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have heq : (WithLp.toLp 2) ⁻¹' ({0} : Set (Euclidean n)) =
      ({0} : Set (Fin (n + 1) → ℝ)) := by
    ext x
    simp
  rw [heq]
  exact measure_singleton 0

def normalizedGaussian (n : ℕ) : Measure (Euclidean n) :=
  (ProbabilityTheory.stdGaussian (Euclidean n)).map NormedSpace.normalize

instance normalizedGaussian_probability (n : ℕ) : IsProbabilityMeasure (normalizedGaussian n) :=
  Measure.isProbabilityMeasure_map (measurable_normalize n).aemeasurable

theorem normalizedGaussian_unit_ae (n : ℕ) :
    ∀ᵐ x ∂normalizedGaussian n, ‖x‖ = 1 := by
  unfold normalizedGaussian
  rw [ae_map_iff (measurable_normalize n).aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  have hnonzero : ∀ᵐ x ∂ProbabilityTheory.stdGaussian (Euclidean n), x ≠ 0 := by
    rw [ae_iff]
    simpa using stdGaussian_zero_singleton n
  filter_upwards [hnonzero] with x hx
  exact NormedSpace.norm_normalize hx

theorem normalizedGaussian_neg_preserving (n : ℕ) :
    MeasurePreserving (fun x : Euclidean n => -x) (normalizedGaussian n) (normalizedGaussian n) := by
  have hmap : (ProbabilityTheory.stdGaussian (Euclidean n)).map (fun x => -x) =
      ProbabilityTheory.stdGaussian (Euclidean n) := by
    simpa using ProbabilityTheory.stdGaussian_map
      (LinearIsometryEquiv.neg ℝ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
  refine ⟨measurable_neg, ?_⟩
  unfold normalizedGaussian
  rw [Measure.map_map measurable_neg (measurable_normalize n)]
  have hcomm : (fun x : Euclidean n => -NormedSpace.normalize x) =
      (fun x => NormedSpace.normalize (-x)) := by
    funext x
    exact (NormedSpace.normalize_neg x).symm
  change (ProbabilityTheory.stdGaussian (Euclidean n)).map
    (fun x => -NormedSpace.normalize x) = _
  rw [hcomm]
  change (ProbabilityTheory.stdGaussian (Euclidean n)).map
    (NormedSpace.normalize ∘ (fun x => -x)) = _
  rw [← Measure.map_map (measurable_normalize n) measurable_neg, hmap]

theorem normalizedGaussian_ball_half (n : ℕ) (z : Euclidean n) {delta : ℝ}
    (hd : 0 ≤ delta) (hsmall : delta < 1) :
    (normalizedGaussian n).real {v | ‖v - z‖ ≤ delta} ≤ 1 / 2 := by
  have hset : sphericalCap 1 delta z =ᵐ[normalizedGaussian n] {v | ‖v - z‖ ≤ delta} := by
    filter_upwards [normalizedGaussian_unit_ae n] with v hv
    apply propext
    change (‖v‖ = 1 ∧ ‖v - z‖ ≤ delta) ↔ ‖v - z‖ ≤ delta
    simp [hv]
  have heq := measureReal_congr hset
  rw [← heq]
  exact symmetric_sphericalCap_half (normalizedGaussian n)
    (normalizedGaussian_neg_preserving n) 1 delta z hd hsmall

theorem normalizedGaussian_isometry_preserving (n : ℕ)
    (T : Euclidean n ≃ₗᵢ[ℝ] Euclidean n) :
    MeasurePreserving T (normalizedGaussian n) (normalizedGaussian n) := by
  refine ⟨T.continuous.measurable, ?_⟩
  unfold normalizedGaussian
  rw [Measure.map_map T.continuous.measurable (measurable_normalize n)]
  have hcomm : T ∘ NormedSpace.normalize = NormedSpace.normalize ∘ T := by
    funext x
    simp [NormedSpace.normalize]
  rw [hcomm, ← Measure.map_map (measurable_normalize n) T.continuous.measurable,
    ProbabilityTheory.stdGaussian_map T]

local instance matrixMeasurableSpace (rows cols : ℕ) : MeasurableSpace (Matrix (Fin rows) (Fin cols) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin rows → Fin cols → ℝ))

def gaussianMatrixLaw (rows cols : ℕ) : Measure (Matrix (Fin rows) (Fin cols) ℝ) :=
  Measure.pi (fun _ : Fin rows => Measure.pi (fun _ : Fin cols => ProbabilityTheory.gaussianReal 0 1))

instance gaussianMatrixLaw_probability (rows cols : ℕ) :
    IsProbabilityMeasure (gaussianMatrixLaw rows cols) := by
  unfold gaussianMatrixLaw
  exact Measure.pi.instIsProbabilityMeasure _

def gramMatrix {rows cols : ℕ} (X : Matrix (Fin rows) (Fin cols) ℝ) : Matrix (Fin cols) (Fin cols) ℝ :=
  Xᵀ * X

theorem gramMatrix_posSemidef {rows cols : ℕ} (X : Matrix (Fin rows) (Fin cols) ℝ) :
    (gramMatrix X).PosSemidef := by
  simpa [gramMatrix] using Matrix.posSemidef_conjTranspose_mul_self X

def wishartGramLaw (rows cols : ℕ) : Measure (Matrix (Fin cols) (Fin cols) ℝ) :=
  (gaussianMatrixLaw rows cols).map gramMatrix

theorem measurable_gramMatrix (rows cols : ℕ) :
    Measurable (gramMatrix : Matrix (Fin rows) (Fin cols) ℝ → Matrix (Fin cols) (Fin cols) ℝ) := by
  change Measurable (fun X : Fin rows → Fin cols → ℝ =>
    fun i j => ∑ k : Fin rows, X k i * X k j)
  fun_prop

instance wishartGramLaw_probability (rows cols : ℕ) :
    IsProbabilityMeasure (wishartGramLaw rows cols) :=
  Measure.isProbabilityMeasure_map (measurable_gramMatrix rows cols).aemeasurable

def shiftedQuadratic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (L R : ℝ) (theta x : V) : ℝ :=
  L * ‖x - R • theta‖ ^ 2 / 2

theorem shiftedQuadratic_value_to_linear
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L R : ℝ) (hL : L ≠ 0) (hR : R ≠ 0) (theta x : V) (htheta : ‖theta‖ = 1) :
    (L * ‖x‖ ^ 2 / 2 + L * R ^ 2 / 2 - shiftedQuadratic L R theta x) / (L * R) =
      inner ℝ x theta := by
  unfold shiftedQuadratic
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, htheta, mul_one, sq_abs,
    real_inner_smul_right]
  field_simp
  ring

theorem shiftedQuadratic_minimum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L R : ℝ) (hL : 0 ≤ L) (theta : V) :
    shiftedQuadratic L R theta (R • theta) = 0 ∧
      ∀ x, shiftedQuadratic L R theta (R • theta) ≤ shiftedQuadratic L R theta x := by
  have hz : shiftedQuadratic L R theta (R • theta) = 0 := by simp [shiftedQuadratic]
  refine ⟨hz, fun x => ?_⟩
  rw [hz]
  unfold shiftedQuadratic
  positivity

def phi (v : ℝ) : ℝ := 1 + v + Real.sqrt (v ^ 2 + 2 * v)

theorem phi_ge_one {v : ℝ} (hv : 0 ≤ v) : 1 ≤ phi v := by
  unfold phi
  have hs := Real.sqrt_nonneg (v ^ 2 + 2 * v)
  linarith

theorem phi_linear_bound {v : ℝ} (hv : 0 ≤ v) : phi v ≤ 2 + 2 * v := by
  have hs : (Real.sqrt (v ^ 2 + 2 * v)) ^ 2 = v ^ 2 + 2 * v :=
    Real.sq_sqrt (by positivity)
  have hn := Real.sqrt_nonneg (v ^ 2 + 2 * v)
  unfold phi
  nlinarith

theorem phi_monotone : MonotoneOn phi (Ici (0 : ℝ)) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  have hsquares := sq_le_sq₀ hu hv |>.mpr huv
  have hsq : u ^ 2 + 2 * u ≤ v ^ 2 + 2 * v := by linarith
  have hs := Real.sqrt_le_sqrt hsq
  unfold phi
  linarith

theorem phi_inverse {v B : ℝ} (hv : 0 ≤ v) (hB : 1 ≤ B) :
    B ≤ phi v ↔ (B - 1) ^ 2 ≤ 2 * B * v := by
  have hs : (Real.sqrt (v ^ 2 + 2 * v)) ^ 2 = v ^ 2 + 2 * v :=
    Real.sq_sqrt (by positivity)
  have hn := Real.sqrt_nonneg (v ^ 2 + 2 * v)
  have hsv : v ≤ Real.sqrt (v ^ 2 + 2 * v) := by nlinarith
  constructor
  · intro h
    have habs : |B - (1 + v)| ≤ Real.sqrt (v ^ 2 + 2 * v) := by
      apply abs_le.mpr
      unfold phi at h
      constructor <;> linarith
    have hsq := sq_le_sq₀ (abs_nonneg (B - (1 + v))) hn |>.mpr habs
    rw [sq_abs] at hsq
    nlinarith
  · intro h
    unfold phi
    by_contra hnot
    have hl : 1 + v + Real.sqrt (v ^ 2 + 2 * v) < B := lt_of_not_ge hnot
    have hp : 0 < B - (1 + v) - Real.sqrt (v ^ 2 + 2 * v) := by linarith
    have hprod := mul_pos hp (show 0 < B - (1 + v) + Real.sqrt (v ^ 2 + 2 * v) by linarith)
    nlinarith

theorem diagonal_deficit_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a * b ≤ 1) :
    0 ≤ (a + b) / 2 - a * b := by
  by_cases hsmall : b ≤ 1 / 2
  · nlinarith [mul_nonneg (le_of_lt ha) (show 0 ≤ 1 / 2 - b by linarith)]
  · have hlarge : 1 / 2 < b := lt_of_not_ge hsmall
    have hprod := mul_nonneg (show 0 ≤ 2 * b - 1 by linarith) (show 0 ≤ 1 - a * b by linarith)
    nlinarith [sq_nonneg (b - 1)]

theorem diagonal_deficit_lower {a b : ℝ} (hb : 1 / 2 ≤ b) (hab : a * b ≤ 1) :
    (b - 1) ^ 2 ≤ 2 * b * ((a + b) / 2 - a * b) := by
  have hprod := mul_nonneg (show 0 ≤ 2 * b - 1 by linarith) (show 0 ≤ 1 - a * b by linarith)
  nlinarith

theorem diagonal_eigenvalue_bound {a b U : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a * b ≤ 1)
    (hU : (a + b) / 2 - a * b ≤ U) : b ≤ phi U := by
  have hUn : 0 ≤ U := (diagonal_deficit_nonneg ha hb hab).trans hU
  by_cases hsmall : b ≤ 1
  · exact hsmall.trans (phi_ge_one hUn)
  · have hb1 : 1 < b := lt_of_not_ge hsmall
    apply (phi_inverse hUn (le_of_lt hb1)).mpr
    have hl := diagonal_deficit_lower (show 1 / 2 ≤ b by linarith) hab
    have hm := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * b by positivity)
    exact hl.trans hm

theorem finite_diagonal_operator_bound {I : Type*} [Fintype I]
    (a b : I → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hab : ∀ i, a i * b i ≤ 1) :
    0 ≤ (∑ i, ((a i + b i) / 2 - a i * b i)) ∧
      ∀ i, b i ≤ phi (∑ j, ((a j + b j) / 2 - a j * b j)) := by
  have hd : ∀ i, 0 ≤ (a i + b i) / 2 - a i * b i :=
    fun i => diagonal_deficit_nonneg (ha i) (hb i) (hab i)
  constructor
  · exact Finset.sum_nonneg (fun i _ => hd i)
  · intro i
    apply diagonal_eigenvalue_bound (ha i) (hb i) (hab i)
    exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)

theorem correlation_budget_query_algebra {B q n : ℝ}
    (hB : 1 ≤ B) (hq : 0 ≤ q) (hn : 0 < n)
    (hbudget : B ≤ phi (2 * q / n)) :
    n * (B - 1) ^ 2 / (4 * B) ≤ q := by
  have hphi := (phi_inverse (show 0 ≤ 2 * q / n by positivity) hB).mp hbudget
  have hm := mul_le_mul_of_nonneg_right hphi (le_of_lt hn)
  have heq : (2 * B * (2 * q / n)) * n = 4 * B * q := by
    field_simp
    ring
  rw [heq] at hm
  apply (div_le_iff₀ (by linarith : 0 < 4 * B)).mpr
  nlinarith

end
end PaperDorn

end SnapshotModule_093
/- END dorn_development -/

/- BEGIN dorn_gaussian_linear -/
section SnapshotModule_094

/- Gaussian linear measurements needed to develop the nondegenerate Wishart
   prior and the residual-sphere experiment. No adaptive lower bound is assumed. -/
namespace PaperDorn
noncomputable section
open MeasureTheory ProbabilityTheory

theorem stdGaussian_linear_law
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    (stdGaussian E).map L = gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
  have hid : HasGaussianLaw (id : E → E) (stdGaussian E) := IsGaussian.hasGaussianLaw_id
  have h := (hid.map L).map_eq_gaussianReal
  simpa only [Function.comp_id, integral_strongDual_stdGaussian, variance_dual_stdGaussian] using h

theorem stdGaussian_hyperplane_null
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) (hL : L ≠ 0) (a : ℝ) :
    stdGaussian E {x | L x = a} = 0 := by
  have hnorm : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hvar : (‖L‖ ^ 2).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos hnorm))
  letI : NullSingletonClass (gaussianReal 0 (‖L‖ ^ 2).toNNReal) :=
    nullSingletonClass_gaussianReal hvar
  have h := congrArg (fun mu : Measure ℝ => mu {a}) (stdGaussian_linear_law L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton a)] at h
  change stdGaussian E {x | L x = a} = _ at h
  simpa only [measure_singleton] using h

theorem stdGaussian_proper_submodule_null
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S : Submodule ℝ E) (hS : S ≠ ⊤) : stdGaussian E (S : Set E) = 0 := by
  have horth : Sᗮ ≠ ⊥ := by
    intro hz
    exact hS (Submodule.orthogonal_eq_bot_iff.mp hz)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  let L : StrongDual ℝ E := innerSL ℝ v
  have hL : L ≠ 0 := by
    intro hz
    have hh := congrArg (fun F : StrongDual ℝ E => F v) hz
    have hn : ‖v‖ ^ 2 = 0 := by simpa [L] using hh
    have hvnorm : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact hv0 (norm_eq_zero.mp hvnorm)
  apply measure_mono_null _ (stdGaussian_hyperplane_null L hL 0)
  intro x hx
  change inner ℝ v x = 0
  exact S.inner_left_of_mem_orthogonal hx hv

theorem iid_stdGaussian_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : ℕ) (hdim : m ≤ Module.finrank ℝ E) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin m => stdGaussian E), LinearIndependent ℝ v := by
  induction m with
  | zero => exact Filter.Eventually.of_forall (fun _ => linearIndependent_empty_type)
  | succ m ih =>
    have htail := ih (by omega)
    have hmeas : MeasurableSet {w : E × (Fin m → E) | LinearIndependent ℝ (Fin.cons w.1 w.2)} := by
      apply IsOpen.measurableSet
      exact isOpen_setOf_linearIndependent.preimage (by fun_prop)
    have htailhead : ∀ᵐ v ∂Measure.pi (fun _ : Fin m => stdGaussian E),
        ∀ᵐ x ∂stdGaussian E, LinearIndependent ℝ (Fin.cons x v) := by
      filter_upwards [htail] with v hv
      obtain ⟨x0, hx0⟩ := exists_linearIndependent_cons_of_lt_finrank hv (by omega)
      let S := Submodule.span ℝ (Set.range v)
      have hS : S ≠ ⊤ := by
        intro hz
        have houtside := (linearIndependent_finCons.mp hx0).2
        apply houtside
        change x0 ∈ S
        rw [hz]
        trivial
      have hnull := stdGaussian_proper_submodule_null S hS
      have hnot : ∀ᵐ x ∂stdGaussian E, x ∉ S := by
        rw [ae_iff]
        simpa using hnull
      filter_upwards [hnot] with x hx
      exact hv.finCons hx
    have hprod : ∀ᵐ w ∂(stdGaussian E).prod (Measure.pi (fun _ : Fin m => stdGaussian E)),
        LinearIndependent ℝ (Fin.cons w.1 w.2) :=
      (Measure.ae_prod_iff_ae_ae hmeas).mpr ((Measure.ae_ae_comm hmeas).mpr htailhead)
    have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => stdGaussian E) 0
    have hback := hsplit.quasiMeasurePreserving.ae hprod
    filter_upwards [hback] with v hv
    have hreconstruct : Fin.cons
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E) 0) v).1
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E) 0) v).2 = v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hreconstruct] at hv
    exact hv

def matrixOfGaussianColumns {rows cols : ℕ}
    (v : Fin cols → EuclideanSpace ℝ (Fin rows)) : Matrix (Fin rows) (Fin cols) ℝ :=
  Matrix.of (fun r i => v i r)

theorem gram_eq_transpose_mul {rows cols : ℕ}
    (v : Fin cols → EuclideanSpace ℝ (Fin rows)) :
    Matrix.gram ℝ v = (matrixOfGaussianColumns v).transpose * matrixOfGaussianColumns v := by
  ext i j
  simp [matrixOfGaussianColumns, Matrix.mul_apply, Matrix.gram_apply, PiLp.inner_apply, mul_comm]

theorem iid_stdGaussian_gram_posDef (rows cols : ℕ) (hdim : cols ≤ rows) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows))),
      (Matrix.gram ℝ v).PosDef := by
  have hd : cols ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin rows)) := by simpa using hdim
  have hli := iid_stdGaussian_linearIndependent (E := EuclideanSpace ℝ (Fin rows)) cols hd
  filter_upwards [hli] with v hv
  exact Matrix.posDef_gram_of_linearIndependent hv

theorem iid_stdGaussian_wishart_posDef (rows cols : ℕ) (hdim : cols ≤ rows) :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows))),
      ((matrixOfGaussianColumns v).transpose * matrixOfGaussianColumns v).PosDef := by
  filter_upwards [iid_stdGaussian_gram_posDef rows cols hdim] with v hv
  rwa [gram_eq_transpose_mul] at hv

end
end PaperDorn

end SnapshotModule_094
/- END dorn_gaussian_linear -/

/- BEGIN dorn_gaussian_moments -/
section SnapshotModule_095

namespace PaperDorn
noncomputable section
open MeasureTheory ProbabilityTheory

theorem stdGaussian_coordinate_mean (d : ℕ) (i : Fin d) :
    (∫ x : EuclideanSpace ℝ (Fin d), x i ∂stdGaussian (EuclideanSpace ℝ (Fin d))) = 0 := by
  simpa using integral_strongDual_stdGaussian (EuclideanSpace.proj (𝕜 := ℝ) i)

theorem stdGaussian_coordinate_memLp_two (d : ℕ) (i : Fin d) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) => x i) 2
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hid : HasGaussianLaw (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := IsGaussian.hasGaussianLaw_id
  have h := (hid.map (EuclideanSpace.proj (𝕜 := ℝ) i)).memLp_two
  simpa using h

theorem stdGaussian_coordinate_product (d : ℕ) (i j : Fin d) :
    (∫ x : EuclideanSpace ℝ (Fin d), x i * x j ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      if i = j then 1 else 0 := by
  have hcov := covariance_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin d)))
    (S := (1 : Matrix (Fin d) (Fin d) ℝ)) Matrix.PosSemidef.one i j
  rw [multivariateGaussian_zero_one,
    covariance_eq_sub (stdGaussian_coordinate_memLp_two d i) (stdGaussian_coordinate_memLp_two d j),
    stdGaussian_coordinate_mean, stdGaussian_coordinate_mean] at hcov
  simpa [Matrix.one_apply] using hcov

theorem stdGaussian_norm_sq_moment (d : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin d))) = d := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp [pow_two, stdGaussian_coordinate_product]
  · intro i _
    exact (stdGaussian_coordinate_memLp_two d i).integrable_sq

theorem gaussian_columns_coordinate_mean (rows cols : ℕ) (i : Fin cols) (r : Fin rows) :
    (∫ v : Fin cols → EuclideanSpace ℝ (Fin rows), v i r
      ∂Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows)))) = 0 := by
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin rows), x r ∂stdGaussian (EuclideanSpace ℝ (Fin rows)) :=
      integral_comp_eval
        (μ := fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows))) (i := i)
        (f := fun x : EuclideanSpace ℝ (Fin rows) => x r) (by fun_prop)
    _ = 0 := stdGaussian_coordinate_mean rows r

theorem gaussian_columns_coordinate_memLp_two (rows cols : ℕ) (i : Fin cols) (r : Fin rows) :
    MemLp (fun v : Fin cols → EuclideanSpace ℝ (Fin rows) => v i r) 2
      (Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows)))) := by
  have hh := (stdGaussian_coordinate_memLp_two rows r).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows))) i)
  simpa only [Function.comp_def, Function.eval] using hh

theorem gaussian_columns_coordinate_product (rows cols : ℕ) (i j : Fin cols) (r : Fin rows) :
    (∫ v : Fin cols → EuclideanSpace ℝ (Fin rows), v i r * v j r
      ∂Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows)))) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hh := integral_comp_eval
      (μ := fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows))) (i := i)
      (f := fun x : EuclideanSpace ℝ (Fin rows) => x r * x r) (by fun_prop)
    rw [hh]
    simpa using stdGaussian_coordinate_product rows r r
  · have hind : iIndepFun
        (fun i (v : Fin cols → EuclideanSpace ℝ (Fin rows)) => v i r)
        (Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows)))) :=
      iIndepFun_pi
        (μ := fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows)))
        (X := fun (_ : Fin cols) (x : EuclideanSpace ℝ (Fin rows)) => x r)
        (fun _ => (by fun_prop))
    have hm := (hind.indepFun hij).integral_mul_eq_mul_integral
      (gaussian_columns_coordinate_memLp_two rows cols i r).aestronglyMeasurable
      (gaussian_columns_coordinate_memLp_two rows cols j r).aestronglyMeasurable
    simpa [Pi.mul_apply, gaussian_columns_coordinate_mean, hij] using hm

theorem gaussian_wishart_entry_mean (rows cols : ℕ) (i j : Fin cols) :
    (∫ v : Fin cols → EuclideanSpace ℝ (Fin rows), (Matrix.gram ℝ v) i j
      ∂Measure.pi (fun _ : Fin cols => stdGaussian (EuclideanSpace ℝ (Fin rows)))) =
      if i = j then rows else 0 := by
  have hgram : ∀ v : Fin cols → EuclideanSpace ℝ (Fin rows),
      (Matrix.gram ℝ v) i j = ∑ r : Fin rows, v i r * v j r := by
    intro v
    simp [Matrix.gram_apply, PiLp.inner_apply, mul_comm]
  simp_rw [hgram]
  rw [integral_finsetSum]
  · by_cases hij : i = j <;> simp [gaussian_columns_coordinate_product, hij]
  · intro r _
    exact (gaussian_columns_coordinate_memLp_two rows cols i r).integrable_mul
      (gaussian_columns_coordinate_memLp_two rows cols j r)

end
end PaperDorn

end SnapshotModule_095
/- END dorn_gaussian_moments -/

/- BEGIN heavy_ball_gaussian -/
section SnapshotModule_096

namespace PaperHeavyBallGaussian
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section

lemma standard_pdf_le_one (x : ℝ) : gaussianPDFReal 0 1 x    ≤    1 := by
  have hs : 1   ≤   Real.sqrt (2*Real.pi) := Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three])
  have hi : (Real.sqrt (2*Real.pi))⁻¹   ≤   1 := inv_le_one_of_one_le₀ hs
  have he : Real.exp (-x^2/2)   ≤   1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  calc
    _   ≤   (Real.sqrt (2*Real.pi))⁻¹*1 := mul_le_mul_of_nonneg_left he (by positivity)
    _   ≤   1 := by simpa only [mul_one] using hi

lemma standard_small_ball (t : ℝ) (ht : 0   ≤   t) :
    (gaussianReal 0 1).real {x : ℝ | |x|   ≤   t}   ≤   2*t := by
  have hset : {x : ℝ | |x|   ≤   t}=Icc (-t) t := by
    ext x
    exact (abs_le : |x|   ≤   t ↔ -t   ≤   x ∧ x   ≤   t)
  rw [hset,measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x=>gaussianPDFReal_nonneg 0 1 x))]
  have hi : IntegrableOn (fun _ : ℝ=> (1:ℝ)) (Icc (-t) t) := integrableOn_const (isCompact_Icc.measure_ne_top)
  have hh := integral_mono_ae ((integrable_gaussianPDFReal 0 1).restrict) hi
    (ae_of_all _ standard_pdf_le_one)
  have he : (∫ _x in Icc (-t) t, (1:ℝ))=2*t := by
    simp only [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith : 0   ≤   t- -t)]
    ring
  exact hh.trans_eq he

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def normalizedFunctional (L : StrongDual ℝ E) : StrongDual ℝ E := ‖L‖⁻¹ •L

lemma normalizedFunctional_norm (L : StrongDual ℝ E) (hL : L≠0) :
    ‖normalizedFunctional L‖ = 1 := by
  have hp : 0 < ‖L‖ := norm_pos_iff.mpr hL
  simp [normalizedFunctional,norm_smul,abs_of_nonneg (inv_nonneg.mpr hp.le),hp.ne']

lemma normalizedFunctional_map (L : StrongDual ℝ E) (hL : L≠0) :
    (stdGaussian E).map (normalizedFunctional L)=gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    normalizedFunctional_norm L hL]
  norm_num

lemma linear_small_ball (L : StrongDual ℝ E) (hL : L≠0) (t : ℝ) (ht : 0   ≤   t) :
    (stdGaussian E).real {g | |L g|   ≤   t*‖L‖}   ≤   2*t := by
  have hp : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hs : {g : E | |L g|   ≤   t*‖L‖}=(normalizedFunctional L) ⁻¹' {x : ℝ | |x|   ≤   t} := by
    ext g
    simp only [mem_setOf_eq,mem_preimage,normalizedFunctional,ContinuousLinearMap.smul_apply,smul_eq_mul,
      abs_mul,abs_inv,abs_norm]
    rw [←div_eq_inv_mul,div_le_iff₀ hp]
  have hm : MeasurableSet {x : ℝ | |x|   ≤   t} := isClosed_le continuous_abs continuous_const |>.measurableSet
  have he := Measure.map_apply (μ:=stdGaussian E) (normalizedFunctional L).continuous.measurable hm
  rw [normalizedFunctional_map L hL] at he
  rw [measureReal_def,hs,←he]
  exact standard_small_ball t ht

lemma gaussian_norm_upper (d : ℕ) (S : ℝ) (hS : 0 < S) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {g | S   ≤   ‖g‖^2}   ≤   (d:ℝ)/S := by
  have hi : Integrable (fun g : EuclideanSpace ℝ (Fin d)=>‖g‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (IsGaussian.memLp_two_id (μ:=stdGaussian (EuclideanSpace ℝ (Fin d)))).norm.integrable_sq
  have hh := mul_meas_ge_le_integral_of_nonneg (μ:=stdGaussian (EuclideanSpace ℝ (Fin d)))
    (f:=fun g=>‖g‖^2) (ae_of_all _ (fun g=>sq_nonneg ‖g‖)) hi S
  rw [PaperDorn.stdGaussian_norm_sq_moment] at hh
  apply (le_div_iff₀ hS).mpr
  simpa only [mul_comm] using hh

lemma gaussian_norm_lower (L : StrongDual ℝ E) (hL : ‖L‖ = 1) (s : ℝ) (hs : 0   ≤   s) :
    (stdGaussian E).real {g | ‖g‖   ≤   s}   ≤   2*s := by
  have hne : L≠0 := by intro hz; simpa [hz] using hL
  have hsub : {g : E | ‖g‖   ≤   s}⊆{g | |L g|   ≤   s*‖L‖} := by
    intro g hg
    have hh := L.le_opNorm g
    rw [Real.norm_eq_abs,hL,one_mul] at hh
    change |L g|   ≤   s*‖L‖
    rw [hL,mul_one]
    exact hh.trans hg
  have hm := ENNReal.toReal_mono (measure_ne_top (stdGaussian E) _) (measure_mono hsub)
  exact hm.trans (linear_small_ball L hne s hs)

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

def calibrationBad {d m : ℕ} (L : Fin m→StrongDual ℝ (Vec d)) (s S q : ℝ) : Set (Vec d) :=
  ({g | ‖g‖  ≤  s} ∪ {g | S  ≤  ‖g‖^2}) ∪ ⋃ i, {g | |L i g|  ≤  q*‖L i‖}

lemma calibrationBad_measurable {d m : ℕ} (L : Fin m→StrongDual ℝ (Vec d)) (s S q : ℝ) :
    MeasurableSet (calibrationBad L s S q) := by
  refine (isClosed_le continuous_norm continuous_const).measurableSet.union
    (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet |>.union ?_
  apply MeasurableSet.iUnion
  intro i
  exact (isClosed_le (L i).continuous.abs continuous_const).measurableSet

/-- Quantitative probability from actual Gaussian density and second moment,
with no Gaussian small-ball or norm event supplied as a premise. -/
theorem calibration_good_probability {d m : ℕ} (L : Fin m→StrongDual ℝ (Vec d))
    (hL : ∀i,L i≠0) (L0 : StrongDual ℝ (Vec d)) (hL0 : ‖L0‖=1)
    (s S q : ℝ) (hs : 0  ≤  s) (hS : 0 < S) (hq : 0  ≤  q) :
    1-(2*s+(d:ℝ)/S+2*(m:ℝ)*q)  ≤  
      (stdGaussian (Vec d)).real (calibrationBad L s S q)ᶜ := by
  have hf := measureReal_iUnion_fintype_le (μ:=stdGaussian (Vec d))
    (fun i : Fin m=>{g : Vec d | |L i g|  ≤  q*‖L i‖})
  have hsum : (∑ i : Fin m,(stdGaussian (Vec d)).real {g | |L i g|  ≤  q*‖L i‖})  ≤  (m:ℝ)*(2*q) := by
    calc
      _  ≤  ∑ _i : Fin m,2*q := Finset.sum_le_sum (fun i _=>linear_small_ball (L i) (hL i) q hq)
      _=(m:ℝ)*(2*q) := by simp
  have hu := measureReal_union_le (μ:=stdGaussian (Vec d))
    ({g : Vec d | ‖g‖  ≤  s} ∪ {g | S  ≤  ‖g‖^2}) (⋃ i,{g | |L i g|  ≤  q*‖L i‖})
  have hu0 := measureReal_union_le (μ:=stdGaussian (Vec d))
    {g : Vec d | ‖g‖  ≤  s} {g | S  ≤  ‖g‖^2}
  have hlow := gaussian_norm_lower L0 hL0 s hs
  have hhigh := gaussian_norm_upper d S hS
  have hbad : (stdGaussian (Vec d)).real (calibrationBad L s S q)  ≤  2*s+(d:ℝ)/S+2*(m:ℝ)*q := by
    unfold calibrationBad
    nlinarith
  rw [measureReal_compl (calibrationBad_measurable L s S q),probReal_univ]
  linarith

lemma calibration_good_properties {d m : ℕ} (L : Fin m→StrongDual ℝ (Vec d)) (s S q : ℝ)
    {g : Vec d} (hg : g∈(calibrationBad L s S q)ᶜ) :
    s < ‖g‖ ∧ ‖g‖^2 < S ∧ ∀i,q*‖L i‖ < |L i g| := by
  simp only [calibrationBad,mem_compl_iff,mem_union,mem_setOf_eq,mem_iUnion,not_or,not_le,not_exists] at hg
  exact ⟨hg.1.1,hg.1.2,hg.2⟩

/-- Explicit polynomial public choices give calibration success at least 1−γ/2. -/
theorem public_calibration_probability (d : ℕ) (hd : 0 < d)
    (L : Fin d→StrongDual ℝ (Vec d)) (hL : ∀i,L i≠0)
    (gamma : ℝ) (hg : 0 < gamma) :
    1-gamma/2  ≤  (stdGaussian (Vec d)).real
      (calibrationBad L (gamma/24) (12*(d:ℝ)/gamma) (gamma/(12*(d:ℝ))))ᶜ := by
  let i0 : Fin d := ⟨0,hd⟩
  have hdpos : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hh := calibration_good_probability L hL (normalizedFunctional (L i0))
    (normalizedFunctional_norm _ (hL i0)) (gamma/24) (12*(d:ℝ)/gamma) (gamma/(12*(d:ℝ)))
    (by positivity) (by positivity) (by positivity)
  have he : 2*(gamma/24)+(d:ℝ)/(12*(d:ℝ)/gamma)+2*(d:ℝ)*(gamma/(12*(d:ℝ)))=gamma/3 := by
    field_simp
    <;> ring
  rw [he] at hh
  exact (by linarith : 1-gamma/2  ≤  1-gamma/3).trans hh

def powerBad {d : ℕ} (L : StrongDual ℝ (Vec d)) (S q : ℝ) : Set (Vec d) :=
  {w | S ≤ ‖w‖^2} ∪ {w | |L w| ≤ q}

lemma powerBad_measurable {d : ℕ} (L : StrongDual ℝ (Vec d)) (S q : ℝ) :
    MeasurableSet (powerBad L S q) :=
  (isClosed_le continuous_const (continuous_norm.pow 2)).measurableSet.union
    (isClosed_le L.continuous.abs continuous_const).measurableSet

lemma power_good_probability {d : ℕ} (L : StrongDual ℝ (Vec d)) (hL : ‖L‖=1)
    (S q : ℝ) (hS : 0 < S) (hq : 0 ≤ q) :
    1-((d:ℝ)/S+2*q) ≤ (stdGaussian (Vec d)).real (powerBad L S q)ᶜ := by
  have hne : L≠0 := by intro hz;simp [hz] at hL
  have hlow:=linear_small_ball L hne q hq
  simp only [hL,mul_one] at hlow
  have hhigh:=gaussian_norm_upper d S hS
  have hu:=measureReal_union_le (μ:=stdGaussian (Vec d)) {w : Vec d | S ≤ ‖w‖^2} {w | |L w| ≤ q}
  have hbad : (stdGaussian (Vec d)).real (powerBad L S q) ≤ (d:ℝ)/S+2*q := by
    unfold powerBad
    linarith
  rw [measureReal_compl (powerBad_measurable L S q),probReal_univ]
  linarith

lemma public_power_probability (d : ℕ) (hd : 0 < d) (L : StrongDual ℝ (Vec d)) (hL : ‖L‖=1)
    (gamma : ℝ) (hg : 0 < gamma) :
    1-gamma/2 ≤ (stdGaussian (Vec d)).real (powerBad L (12*(d:ℝ)/gamma) (gamma/12))ᶜ := by
  have hdpos : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hh:=power_good_probability L hL (12*(d:ℝ)/gamma) (gamma/12) (by positivity) (by positivity)
  have he : (d:ℝ)/(12*(d:ℝ)/gamma)+2*(gamma/12)=gamma/4 := by field_simp <;> ring
  rw [he] at hh
  linarith

/-- Two independent objective-independent Gaussian seeds give the appendix's
quantitative success budget. This theorem integrates their actual joint law. -/
theorem independent_good_probability (d : ℕ) (hd : 0 < d)
    (L : Fin d→StrongDual ℝ (Vec d)) (hL : ∀i,L i≠0)
    (top : StrongDual ℝ (Vec d)) (htop : ‖top‖=1) :
    (2/3:ℝ) ≤ ((stdGaussian (Vec d)).prod (stdGaussian (Vec d))).real
      ((calibrationBad L ((1/3:ℝ)/24) (12*(d:ℝ)/(1/3)) ((1/3:ℝ)/(12*(d:ℝ))))ᶜ ×ˢ
       (powerBad top (12*(d:ℝ)/(1/3)) ((1/3:ℝ)/12))ᶜ) := by
  rw [measureReal_prod_prod]
  have hcal:=public_calibration_probability d hd L hL (1/3) (by norm_num)
  have hpow:=public_power_probability d hd top htop (1/3) (by norm_num)
  have hc : 0 ≤ (stdGaussian (Vec d)).real
      (calibrationBad L ((1/3:ℝ)/24) (12*(d:ℝ)/(1/3)) ((1/3:ℝ)/(12*(d:ℝ))))ᶜ := measureReal_nonneg
  have hp : 0 ≤ (stdGaussian (Vec d)).real (powerBad top (12*(d:ℝ)/(1/3)) ((1/3:ℝ)/12))ᶜ := measureReal_nonneg
  nlinarith



end
end PaperHeavyBallGaussian

end SnapshotModule_096
/- END heavy_ball_gaussian -/

/- BEGIN heavy_ball_parameters -/
section SnapshotModule_097

namespace PaperHeavyBallParameters
noncomputable section

def theta (m M : ℝ) : ℝ := (Real.sqrt M-Real.sqrt m)/(Real.sqrt M+Real.sqrt m)
def alpha (m M : ℝ) : ℝ := 4/(Real.sqrt M+Real.sqrt m)^2

lemma theta_bounds (m M : ℝ) (hm : 0 < m) (hpad : 4*m≤M) :
    (1/3:ℝ)≤theta m M ∧ theta m M<1 := by
  have hM : 0 < M := (by positivity : 0 < 4*m).trans_le hpad
  have ha := Real.sqrt_pos.mpr hm
  have hb := Real.sqrt_pos.mpr hM
  have hasq:=Real.sq_sqrt hm.le
  have hbsq:=Real.sq_sqrt hM.le
  have hroot : 2*Real.sqrt m≤Real.sqrt M := by nlinarith
  have hden : 0 < Real.sqrt M+Real.sqrt m := by positivity
  constructor
  · dsimp [theta]
    apply (le_div_iff₀ hden).mpr
    linarith
  · dsimp [theta]
    apply (div_lt_one hden).mpr
    linarith

lemma alpha_pos (m M : ℝ) (hm : 0 < m) (hM : 0≤M) : 0 < alpha m M := by
  have hs := Real.sqrt_pos.mpr hm
  dsimp [alpha]
  positivity

lemma alpha_times_upper (m M : ℝ) (hm : 0 < m) (hM : 0≤M) : alpha m M*M≤4 := by
  have ha := Real.sqrt_pos.mpr hm
  have hb := Real.sqrt_nonneg M
  have hsq:=Real.sq_sqrt hM
  have hden : 0 < (Real.sqrt M+Real.sqrt m)^2 := by positivity
  dsimp [alpha]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith

lemma lower_endpoint (m M : ℝ) (hm : 0 < m) (hM : 0≤M) :
    1+(theta m M)^2-alpha m M*m=2*theta m M := by
  let a:=Real.sqrt m
  let b:=Real.sqrt M
  have ha : a^2=m := Real.sq_sqrt hm.le
  have hap : 0 < a := Real.sqrt_pos.mpr hm
  have hbn : 0≤b := Real.sqrt_nonneg M
  have hden : b+a≠0 := ne_of_gt (by positivity)
  change 1+((b-a)/(b+a))^2-(4/(b+a)^2)*m=2*((b-a)/(b+a))
  rw [←ha]
  field_simp
  <;> ring

lemma upper_endpoint (m M : ℝ) (hm : 0 < m) (hM : 0≤M) :
    1+(theta m M)^2-alpha m M*M= -2*theta m M := by
  let a:=Real.sqrt m
  let b:=Real.sqrt M
  have hb : b^2=M := Real.sq_sqrt hM
  have hap : 0 < a := Real.sqrt_pos.mpr hm
  have hbn : 0≤b := Real.sqrt_nonneg M
  have hden : b+a≠0 := ne_of_gt (by positivity)
  change 1+((b-a)/(b+a))^2-(4/(b+a)^2)*M= -2*((b-a)/(b+a))
  rw [←hb]
  field_simp
  <;> ring

lemma normalized_spectrum (m M lambda : ℝ) (hm : 0 < m) (hpad : 4*m≤M)
    (hl : m≤lambda) (hu : lambda≤M) :
    |(1+(theta m M)^2-alpha m M*lambda)/(2*theta m M)|≤1 := by
  have hM : 0≤M := by linarith
  have ht := (theta_bounds m M hm hpad).1
  have htp : 0 < theta m M := by linarith
  have halpha:=alpha_pos m M hm hM
  have hlo:=lower_endpoint m M hm hM
  have hup:=upper_endpoint m M hm hM
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*theta m M)).mpr
    nlinarith
  · apply (div_le_one (by positivity : 0 < 2*theta m M)).mpr
    nlinarith

end
end PaperHeavyBallParameters

end SnapshotModule_097
/- END heavy_ball_parameters -/

/- BEGIN heavy_ball_scale_geometry -/
section SnapshotModule_098

namespace PaperHeavyBallScale
open Set PaperHeavyBallGaussian
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

variable {ι : Type*} [Fintype ι]
def row (basis : OrthonormalBasis ι ℝ V) (A : V→L[ℝ] V) (i : ι) : StrongDual ℝ V :=
  (InnerProductSpace.toDual ℝ V (basis i)).comp A

def diagonal (basis : OrthonormalBasis ι ℝ V) (A : V→L[ℝ] V) (i : ι) : ℝ := inner ℝ (basis i) (A (basis i))

lemma row_self (basis : OrthonormalBasis ι ℝ V) (A : V→L[ℝ] V) (i : ι) :
    row basis A i (basis i)=diagonal basis A i := rfl

lemma diagonal_lower (basis : OrthonormalBasis ι ℝ V) (A : V→L[ℝ] V) (mu : ℝ)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (i : ι) : mu ≤ diagonal basis A i := by
  simpa only [diagonal,basis.orthonormal.norm_eq_one,one_pow,mul_one] using hlower (basis i)

lemma row_norm_lower (basis : OrthonormalBasis ι ℝ V) (A : V→L[ℝ] V) (i : ι) :
    diagonal basis A i ≤ ‖row basis A i‖ := by
  have hh:=(row basis A i).le_opNorm (basis i)
  rw [row_self,basis.orthonormal.norm_eq_one,mul_one,Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans hh

lemma row_ne_zero (basis : OrthonormalBasis ι ℝ V) (A : V→L[ℝ] V) (mu : ℝ)
    (hmu : 0 < mu) (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (i : ι) : row basis A i≠0 := by
  have hh:=(diagonal_lower basis A mu hlower i).trans (row_norm_lower basis A i)
  intro hz
  rw [hz,norm_zero] at hh
  linarith

/-- Actual Gaussian row event implies public C/E denominator margins.
This proof uses the stronger elementary row-norm ≥ positive diagonal bound,
which avoids additional covariance/rho regularity assumptions. -/
theorem calibration_seed_bounds (d : ℕ)
    (basis : OrthonormalBasis (Fin d) ℝ (Vec d)) (A : Vec d→L[ℝ] Vec d)
    (mu beta s S q : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hs : 0 < s) (hS : 0 < S) (hq : 0 ≤ q)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2)
    (u : Vec d) (hu : u∈(calibrationBad (row basis A) s S q)ᶜ) :
    0 < inner ℝ u (A u) ∧ inner ℝ u (A u) ≤ beta*S ∧
    (∀i, q ≤ |row basis A i u/diagonal basis A i| ∧
      q/((beta/mu)*S) ≤ |row basis A i u/inner ℝ u (A u)|) := by
  have hg:=calibration_good_properties (row basis A) s S q hu
  have hbeta0 : 0 < beta := hmu.trans_le hbeta
  have hun : 0 < ‖u‖ := hs.trans hg.1
  have ha : 0 < inner ℝ u (A u) := (mul_pos hmu (sq_pos_of_pos hun)).trans_le (hlower u)
  have haup : inner ℝ u (A u) ≤ beta*S := (hupper u).trans
    (mul_le_mul_of_nonneg_left hg.2.1.le hbeta0.le)
  refine ⟨ha,haup,?_⟩
  intro i
  have hdiag : 0 < diagonal basis A i := hmu.trans_le (diagonal_lower basis A mu hlower i)
  have hrow:=row_norm_lower basis A i
  have hnum : q*mu ≤ |row basis A i u| := by
    have hh:=mul_le_mul_of_nonneg_left ((diagonal_lower basis A mu hlower i).trans hrow) hq
    exact hh.trans (hg.2.2 i).le
  constructor
  · rw [abs_div,abs_of_pos hdiag]
    apply (le_div_iff₀ hdiag).mpr
    exact (mul_le_mul_of_nonneg_left hrow hq).trans (hg.2.2 i).le
  · rw [abs_div,abs_of_pos ha]
    have hh:=div_le_div₀ (abs_nonneg (row basis A i u)) hnum ha haup
    have he : q*mu/(beta*S)=q/((beta/mu)*S) := by field_simp
    rw [he] at hh
    exact hh

def scaledOperator (A : V→L[ℝ] V) (u : V) : V→L[ℝ] V := (inner ℝ u (A u))⁻¹ •A

lemma scaled_spectral_bounds (A : V→L[ℝ] V) (mu beta s S : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hs : 0 < s) (hS : 0 < S)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2)
    (hAnorm : ‖A‖ ≤ beta) (u : V) (hun : s ≤ ‖u‖) (huS : ‖u‖^2 ≤ S) :
    (∀x,(1/((beta/mu)*S))*‖x‖^2 ≤ inner ℝ x (scaledOperator A u x)) ∧
    ‖scaledOperator A u‖ ≤ (beta/mu)/s^2 := by
  have hbeta0 : 0 < beta := hmu.trans_le hbeta
  have hu : 0 < ‖u‖ := hs.trans_le hun
  have ha : 0 < inner ℝ u (A u) := (mul_pos hmu (sq_pos_of_pos hu)).trans_le (hlower u)
  have haup : inner ℝ u (A u) ≤ beta*S := (hupper u).trans (mul_le_mul_of_nonneg_left huS hbeta0.le)
  have halow : mu*s^2 ≤ inner ℝ u (A u) := by
    have hsq : s^2 ≤ ‖u‖^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsq hmu.le).trans (hlower u)
  constructor
  · intro x
    have hratio : mu/(beta*S) ≤ mu/inner ℝ u (A u) :=
      div_le_div_of_nonneg_left hmu.le ha haup
    have he : mu/(beta*S)=1/((beta/mu)*S) := by field_simp
    rw [he] at hratio
    have hm:=mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖x‖)
    have hh:=div_le_div_of_nonneg_right (hlower x) ha.le
    simp only [scaledOperator,ContinuousLinearMap.smul_apply,real_inner_smul_right,smul_eq_mul]
    calc
      _ ≤ (mu/inner ℝ u (A u))*‖x‖^2:=hm
      _ ≤ (inner ℝ x (A x))/inner ℝ u (A u):=by convert hh using 1 <;> first | rfl | ring
      _=(inner ℝ u (A u))⁻¹*inner ℝ x (A x):=by ring
  · have hn : ‖scaledOperator A u‖ ≤ beta/inner ℝ u (A u) := by
      rw [scaledOperator,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos ha]
      exact (mul_le_mul_of_nonneg_left hAnorm (inv_nonneg.mpr ha.le)).trans_eq (by ring)
    have hh:=div_le_div_of_nonneg_left hbeta0.le (mul_pos hmu (sq_pos_of_pos hs)) halow
    have he : beta/(mu*s^2)=(beta/mu)/s^2 := by ring
    exact hn.trans (hh.trans_eq he)

end
end PaperHeavyBallScale

end SnapshotModule_098
/- END heavy_ball_scale_geometry -/

/- BEGIN heavy_ball_calibration -/
section SnapshotModule_099

namespace PaperHeavyBallBackend
open MeasureTheory Set PaperOracle PaperHeavyBallLine PaperHeavyBallScale
open scoped RealInnerProductSpace
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-- Finite coordinate collection, preserving the actual scalar comparison tree. -/
def collect {Q Reply A : Type} : (d : ℕ) → (Fin d → Program Q Reply A) → Program Q Reply (Fin d → A)
  | 0,_ => .done Fin.elim0
  | d+1,f => Program.bind (f 0) (fun first => Program.bind (collect d (fun i => f i.succ))
      (fun rest => .done (Fin.cons first rest)))

lemma run_collect {Q Reply A : Type} (C : Q→Reply) (d : ℕ) (f : Fin d→Program Q Reply A) :
    Program.run C (collect d f)=fun i => Program.run C (f i) := by
  induction d with
  | zero => funext i;exact Fin.elim0 i
  | succ d ih =>
    simp only [collect,Program.run_bind,Program.run]
    rw [ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

lemma cap_collect {Q Reply A : Type} (d cost : ℕ) (f : Fin d→Program Q Reply A)
    (hcap : ∀i,Program.Cap cost (f i)) : Program.Cap (d*cost) (collect d f) := by
  induction d with
  | zero => simp only [collect,Nat.zero_mul,Program.Cap]
  | succ d ih =>
    rw [show (d+1)*cost=cost+d*cost by ring]
    apply Program.cap_bind _ _ (hcap 0)
    intro first
    have hrest := Program.cap_bind (collect d (fun i => f i.succ))
      (fun rest => Program.done (Fin.cons first rest : Fin (d+1) → A)) (ih _ (fun i => hcap i.succ)) (b:=0) (by intro a;trivial)
    simpa only [Nat.add_zero] using hrest

lemma root_pair_error (R delta : ℝ) (hR : 0  <  R) (hd : 0  ≤  delta)
    (a b ahat bhat : ℝ) (ha : |ahat-a| ≤ delta) (hb : |bhat-b| ≤ delta) :
    |(ahat-bhat)/(2*R)-(a-b)/(2*R)|  ≤  delta/R := by
  have hn : |(ahat-bhat)-(a-b)| ≤ 2*delta := by
    have hh := abs_sub_le (ahat-a) 0 (bhat-b)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have he : (ahat-bhat)-(a-b)=(ahat-a)-(bhat-b) := by ring
    rw [he]
    linarith
  rw [show (ahat-bhat)/(2*R)-(a-b)/(2*R)=((ahat-bhat)-(a-b))/(2*R) by ring,
    abs_div,abs_of_pos (by positivity : 0 < 2*R)]
  apply (div_le_iff₀ (by positivity : 0 < 2*R)).mpr
  have he : delta/R*(2*R)=2*delta := by field_simp
  rw [he]
  exact hn

lemma ratio_relative_bounds (C E Chat Ehat eta : ℝ)
    (hC : C≠0) (hE : E≠0) (hlambda : 0 < C/E) (heta : 0 ≤ eta) (heta1 : eta ≤ 1/2)
    (hChat : |Chat-C| ≤ eta/4*|C|) (hEhat : |Ehat-E| ≤ eta/4*|E|) :
    Ehat≠0 ∧ (1-eta)*(C/E) ≤ Chat/Ehat ∧ Chat/Ehat ≤ (1+eta)*(C/E) := by
  have hrelC : |Chat/C-1| ≤ eta/4 := by
    rw [show Chat/C-1=(Chat-C)/C by field_simp,abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hC)).mpr hChat
  have hrelE : |Ehat/E-1| ≤ eta/4 := by
    rw [show Ehat/E-1=(Ehat-E)/E by field_simp,abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hE)).mpr hEhat
  have hcb := abs_le.mp hrelC
  have heb := abs_le.mp hrelE
  have hepos : 0 < Ehat/E := by linarith
  have hhat : Ehat≠0 := by intro h;rw [h,zero_div] at hepos;linarith
  have hlow : 1-eta ≤ (Chat/C)/(Ehat/E) := by
    apply (le_div_iff₀ hepos).mpr
    have hm := mul_le_mul_of_nonneg_left (show Ehat/E ≤ 1+eta/4 by linarith)
      (show 0 ≤ 1-eta by linarith)
    nlinarith
  have hup : (Chat/C)/(Ehat/E) ≤ 1+eta := by
    apply (div_le_iff₀ hepos).mpr
    have hm := mul_le_mul_of_nonneg_left (show 1-eta/4 ≤ Ehat/E by linarith)
      (show 0 ≤ 1+eta by linarith)
    nlinarith
  have hid : ((Chat/C)/(Ehat/E))*(C/E)=Chat/Ehat := by field_simp
  refine ⟨hhat,?_,?_⟩
  · simpa only [hid] using mul_le_mul_of_nonneg_right hlow hlambda.le
  · simpa only [hid] using mul_le_mul_of_nonneg_right hup hlambda.le

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {d : ℕ}

def trueC (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V) (u : V) (i : Fin d) : ℝ :=
  inner ℝ u (A (basis i))/inner ℝ u (A u)
def trueE (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V) (u : V) (i : Fin d) : ℝ :=
  inner ℝ (basis i) (A u)/PaperHeavyBallScale.diagonal basis A i

def bracketC (kappa R s : ℝ) : ℝ := 2*kappa*R/s
def bracketE (kappa R S : ℝ) : ℝ := kappa*R*(Real.sqrt S+1)
def toleranceC (kappa R S q eta : ℝ) : ℝ := eta*q*R/(4*kappa*S)
def toleranceE (R q eta : ℝ) : ℝ := eta*q*R/4

lemma trueC_root_identity (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (b u : V) (R : ℝ) (hR : R≠0) (i : Fin d) :
    (lineRoot A b ((-R) •basis i) u-lineRoot A b (R •basis i) u)/(2*R)=trueC basis A u i := by
  simp only [lineRoot,trueC,map_smul,inner_sub_right,real_inner_smul_right]
  field_simp
  ring

lemma trueE_root_identity (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (b u : V) (R : ℝ) (hR : R≠0) (i : Fin d) :
    (lineRoot A b ((-R) •u) (basis i)-lineRoot A b (R •u) (basis i))/(2*R)=trueE basis A u i := by
  simp only [lineRoot,trueE,PaperHeavyBallScale.diagonal,map_smul,inner_sub_right,real_inner_smul_right]
  field_simp
  ring

lemma calibration_ratio_identity (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) (u : V) (i : Fin d)
    (ha : inner ℝ u (A u)≠0) (hdiag : PaperHeavyBallScale.diagonal basis A i≠0)
    (hrow : inner ℝ (basis i) (A u)≠0) :
    trueC basis A u i/trueE basis A u i=PaperHeavyBallScale.diagonal basis A i/inner ℝ u (A u) := by
  unfold trueC trueE
  rw [energy_symmetry A hA u (basis i)]
  field_simp

/-- Four actual finite comparison root programs, in source order Cminus,Cplus,Eminus,Eplus. -/
def coordinateCalibration (basis : OrthonormalBasis (Fin d) ℝ V) (u : V)
    (kappa R s S q eta : ℝ) (i : Fin d) : Program (V×V) Ordering (ℝ×ℝ) :=
  Program.bind (rootProgram ((-R) •basis i) u (bracketC kappa R s) (toleranceC kappa R S q eta)) (fun cm =>
  Program.bind (rootProgram (R •basis i) u (bracketC kappa R s) (toleranceC kappa R S q eta)) (fun cp =>
  Program.bind (rootProgram ((-R) •u) (basis i) (bracketE kappa R S) (toleranceE R q eta)) (fun em =>
  Program.bind (rootProgram (R •u) (basis i) (bracketE kappa R S) (toleranceE R q eta)) (fun ep =>
    .done ((cm-cp)/(2*R),(em-ep)/(2*R))))))

def coordinateCost (kappa R s S q eta : ℝ) : ℕ :=
  2*horizon (bracketC kappa R s) (toleranceC kappa R S q eta)+
    2*horizon (bracketE kappa R S) (toleranceE R q eta)

lemma coordinateCalibration_cap (basis : OrthonormalBasis (Fin d) ℝ V) (u : V)
    (kappa R s S q eta : ℝ) (i : Fin d) :
    Program.Cap (coordinateCost kappa R s S q eta) (coordinateCalibration basis u kappa R s S q eta i) := by
  unfold coordinateCalibration coordinateCost
  have hC := bisect_public_cap ((-R) •basis i) u (horizon (bracketC kappa R s) (toleranceC kappa R S q eta))
    (-(bracketC kappa R s)) (bracketC kappa R s)
  have hCp := bisect_public_cap (R •basis i) u (horizon (bracketC kappa R s) (toleranceC kappa R S q eta))
    (-(bracketC kappa R s)) (bracketC kappa R s)
  have hE := bisect_public_cap ((-R) •u) (basis i) (horizon (bracketE kappa R S) (toleranceE R q eta))
    (-(bracketE kappa R S)) (bracketE kappa R S)
  have hEp := bisect_public_cap (R •u) (basis i) (horizon (bracketE kappa R S) (toleranceE R q eta))
    (-(bracketE kappa R S)) (bracketE kappa R S)
  rw [show 2*horizon (bracketC kappa R s) (toleranceC kappa R S q eta)+
      2*horizon (bracketE kappa R S) (toleranceE R q eta)=
      horizon (bracketC kappa R s) (toleranceC kappa R S q eta)+
      (horizon (bracketC kappa R s) (toleranceC kappa R S q eta)+
      (horizon (bracketE kappa R S) (toleranceE R q eta)+
      (horizon (bracketE kappa R S) (toleranceE R q eta)+0))) by omega]
  apply Program.cap_bind _ _ hC
  intro cm
  apply Program.cap_bind _ _ hCp
  intro cp
  apply Program.cap_bind _ _ hE
  intro em
  apply Program.cap_bind _ _ hEp
  intro ep
  trivial

lemma bracketC_valid (A : V→L[ℝ] V) (b star z u : V) (mu beta R s : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (hs : 0 < s)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hz : ‖z‖ ≤ R) (hu : s ≤ ‖u‖) :
    |lineRoot A b z u| ≤ bracketC (beta/mu) R s := by
  have hk : 0 < beta/mu := div_pos (hmu.trans_le hbeta) hmu
  have hun : 0 < ‖u‖ := hs.trans_le hu
  have hb := conditioned_line_root_bound A b star z u mu beta R hmu hbeta hlower hAnorm hsol hstar
    (norm_pos_iff.mp hun)
  apply hb.trans
  apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ (beta/mu)*(‖z‖+R)) hs hu).trans
  apply div_le_div_of_nonneg_right _ hs.le
  nlinarith

lemma bracketE_valid (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (b star z : V) (mu beta R S : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hz : ‖z‖ ≤ R*Real.sqrt S) (i : Fin d) :
    |lineRoot A b z (basis i)| ≤ bracketE (beta/mu) R S := by
  have hi : basis i≠0 := norm_ne_zero_iff.mp (by rw [basis.orthonormal.norm_eq_one];norm_num)
  have hb := conditioned_line_root_bound A b star z (basis i) mu beta R hmu hbeta hlower hAnorm hsol hstar hi
  rw [basis.orthonormal.norm_eq_one,div_one] at hb
  have hk : 0 < beta/mu := div_pos (hmu.trans_le hbeta) hmu
  apply hb.trans
  dsimp [bracketE]
  nlinarith

lemma coordinateCalibration_correct (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) (b star u : V) (mu beta R s S q eta : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (hs : 0 < s) (hS : 0 < S) (hq : 0 < q)
    (heta : 0 < eta) (heta1 : eta ≤ 1/2)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hun : s ≤ ‖u‖) (huS : ‖u‖ ≤ Real.sqrt S)
    (hmarginC : ∀i,q/((beta/mu)*S) ≤ |trueC basis A u i|)
    (hmarginE : ∀i,q ≤ |trueE basis A u i|) (i : Fin d) :
    let reading := Program.run (PaperOracle.comparisonOracle (quadratic A b))
      (coordinateCalibration basis u (beta/mu) R s S q eta i)
    let lambda := PaperHeavyBallScale.diagonal basis A i/inner ℝ u (A u)
    |reading.1-trueC basis A u i| ≤ eta/4*|trueC basis A u i| ∧
    |reading.2-trueE basis A u i| ≤ eta/4*|trueE basis A u i| ∧
    reading.2≠0 ∧ 0 < reading.1/reading.2 ∧
    (1-eta)*lambda ≤ reading.1/reading.2 ∧ reading.1/reading.2 ≤ (1+eta)*lambda := by
  let Cmp := PaperOracle.comparisonOracle (quadratic A b)
  let DC := bracketC (beta/mu) R s
  let DE := bracketE (beta/mu) R S
  let dC := toleranceC (beta/mu) R S q eta
  let dE := toleranceE R q eta
  have hk : 0 < beta/mu := div_pos (hmu.trans_le hbeta) hmu
  have hDC : 0 < DC := by dsimp [DC,bracketC];positivity
  have hDE : 0 < DE := by dsimp [DE,bracketE];positivity
  have hdC : 0 < dC := by dsimp [dC,toleranceC];positivity
  have hdE : 0 < dE := by dsimp [dE,toleranceE];positivity
  have hu : u≠0 := norm_pos_iff.mp (hs.trans_le hun)
  have hau : 0 < inner ℝ u (A u) := conditioned_line_curvature A mu hmu hlower u hu
  have hei : basis i≠0 := norm_ne_zero_iff.mp (by rw [basis.orthonormal.norm_eq_one];norm_num)
  have hai : 0 < inner ℝ (basis i) (A (basis i)) := conditioned_line_curvature A mu hmu hlower _ hei
  have hzi (sign : ℝ) (hsign : |sign|=R) : ‖sign •basis i‖ ≤ R := by
    rw [norm_smul,Real.norm_eq_abs,hsign,basis.orthonormal.norm_eq_one,mul_one]
  have hzu (sign : ℝ) (hsign : |sign|=R) : ‖sign •u‖ ≤ R*Real.sqrt S := by
    rw [norm_smul,Real.norm_eq_abs,hsign]
    exact mul_le_mul_of_nonneg_left huS hR.le
  have hrCm := (rootProgram_correct A hA b ((-R) •basis i) u hau DC dC hDC hdC
    (bracketC_valid A b star _ u mu beta R s hmu hbeta hR hs hlower hAnorm hsol hstar
      (hzi (-R) (by simp [abs_of_pos hR])) hun)).2
  have hrCp := (rootProgram_correct A hA b (R •basis i) u hau DC dC hDC hdC
    (bracketC_valid A b star _ u mu beta R s hmu hbeta hR hs hlower hAnorm hsol hstar
      (hzi R (abs_of_pos hR)) hun)).2
  have hrEm := (rootProgram_correct A hA b ((-R) •u) (basis i) hai DE dE hDE hdE
    (bracketE_valid basis A b star _ mu beta R S hmu hbeta hR hlower hAnorm hsol hstar
      (hzu (-R) (by simp [abs_of_pos hR])) i)).2
  have hrEp := (rootProgram_correct A hA b (R •u) (basis i) hai DE dE hDE hdE
    (bracketE_valid basis A b star _ mu beta R S hmu hbeta hR hlower hAnorm hsol hstar
      (hzu R (abs_of_pos hR)) i)).2
  have hCerr := root_pair_error R dC hR hdC.le _ _ _ _ hrCm hrCp
  rw [trueC_root_identity basis A b u R hR.ne'] at hCerr
  have hEerr := root_pair_error R dE hR hdE.le _ _ _ _ hrEm hrEp
  rw [trueE_root_identity basis A b u R hR.ne'] at hEerr
  have hdc : dC/R=eta/4*(q/((beta/mu)*S)) := by dsimp [dC,toleranceC];field_simp
  have hde : dE/R=eta/4*q := by dsimp [dE,toleranceE];field_simp
  have hmC : dC/R ≤ eta/4*|trueC basis A u i| := by
    rw [hdc]
    exact mul_le_mul_of_nonneg_left (hmarginC i) (by positivity)
  have hmE : dE/R ≤ eta/4*|trueE basis A u i| := by
    rw [hde]
    exact mul_le_mul_of_nonneg_left (hmarginE i) (by positivity)
  have hrelC := hCerr.trans hmC
  have hrelE := hEerr.trans hmE
  have hCne : trueC basis A u i≠0 := abs_pos.mp ((div_pos hq (mul_pos hk hS)).trans_le (hmarginC i))
  have hEne : trueE basis A u i≠0 := abs_pos.mp (hq.trans_le (hmarginE i))
  have hrow : inner ℝ (basis i) (A u)≠0 := by intro hz;apply hEne;simp [trueE,hz]
  have hidentity := calibration_ratio_identity basis A hA u i hau.ne' hai.ne' hrow
  have hlambda : 0 < trueC basis A u i/trueE basis A u i := by
    rw [hidentity]
    exact div_pos hai hau
  have hratio := ratio_relative_bounds _ _ _ _ eta hCne hEne hlambda heta.le heta1 hrelC hrelE
  rw [hidentity] at hratio
  have hpositive : 0 < ((Program.run Cmp (rootProgram ((-R) •basis i) u DC dC)-
      Program.run Cmp (rootProgram (R •basis i) u DC dC))/(2*R))/
      ((Program.run Cmp (rootProgram ((-R) •u) (basis i) DE dE)-
      Program.run Cmp (rootProgram (R •u) (basis i) DE dE))/(2*R)) := by
    have hl : 0 < PaperHeavyBallScale.diagonal basis A i/inner ℝ u (A u) := div_pos hai hau
    exact (mul_pos (by linarith : 0 < 1-eta) hl).trans_le hratio.2.1
  dsimp only
  simp only [coordinateCalibration,Program.run_bind,Program.run]
  exact ⟨hrelC,hrelE,hratio.1,hpositive,hratio.2⟩

/-- Public norm guard, four roots per coordinate, and total denominator/positivity fallbacks. -/
def calibrationProgram (basis : OrthonormalBasis (Fin d) ℝ V) (u : V)
    (kappa R s S q eta : ℝ) : Program (V×V) Ordering (Option (Fin d→ℝ)) := by
  classical
  exact if s ≤ ‖u‖ ∧ ‖u‖ ≤ Real.sqrt S then
    Program.bind (collect d (coordinateCalibration basis u kappa R s S q eta)) (fun reading =>
      if ∀i,(reading i).2≠0 ∧ 0 < (reading i).1/(reading i).2 then
        .done (some (fun i => (reading i).1/(reading i).2)) else .done none)
    else .done none

lemma calibrationProgram_cap (basis : OrthonormalBasis (Fin d) ℝ V) (u : V)
    (kappa R s S q eta : ℝ) :
    Program.Cap (d*coordinateCost kappa R s S q eta) (calibrationProgram basis u kappa R s S q eta) := by
  classical
  unfold calibrationProgram
  split_ifs
  · rw [show d*coordinateCost kappa R s S q eta=d*coordinateCost kappa R s S q eta+0 by omega]
    apply Program.cap_bind _ _ (cap_collect d (coordinateCost kappa R s S q eta) _
      (coordinateCalibration_cap basis u kappa R s S q eta))
    intro reading
    split_ifs <;> trivial
  · cases d*coordinateCost kappa R s S q eta <;> trivial

lemma calibrationProgram_correct (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) (b star u : V) (mu beta R s S q eta : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (hs : 0 < s) (hS : 0 < S) (hq : 0 < q)
    (heta : 0 < eta) (heta1 : eta ≤ 1/2)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hun : s ≤ ‖u‖) (huS : ‖u‖ ≤ Real.sqrt S)
    (hmarginC : ∀i,q/((beta/mu)*S) ≤ |trueC basis A u i|)
    (hmarginE : ∀i,q ≤ |trueE basis A u i|) :
    ∃ lambdaHat : Fin d→ℝ,
      Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (calibrationProgram basis u (beta/mu) R s S q eta)=some lambdaHat ∧
      ∀i, let lambda := PaperHeavyBallScale.diagonal basis A i/inner ℝ u (A u)
        (1-eta)*lambda ≤ lambdaHat i ∧ lambdaHat i ≤ (1+eta)*lambda ∧
        |lambdaHat i-lambda| ≤ eta*lambda := by
  classical
  let Cmp := PaperOracle.comparisonOracle (quadratic A b)
  let readings := fun i => Program.run Cmp (coordinateCalibration basis u (beta/mu) R s S q eta i)
  have hc := coordinateCalibration_correct basis A hA b star u mu beta R s S q eta hmu hbeta hR hs hS hq
    heta heta1 hlower hAnorm hsol hstar hun huS hmarginC hmarginE
  have hvalid : ∀i,(readings i).2≠0 ∧ 0 < (readings i).1/(readings i).2 := by
    intro i
    exact ⟨(hc i).2.2.1,(hc i).2.2.2.1⟩
  refine ⟨fun i => (readings i).1/(readings i).2,?_,?_⟩
  · simp only [calibrationProgram,if_pos (And.intro hun huS),Program.run_bind,run_collect]
    change Program.run Cmp (if ∀i,(readings i).2≠0 ∧ 0 < (readings i).1/(readings i).2 then
      .done (some (fun i => (readings i).1/(readings i).2)) else .done none)=_
    rw [if_pos hvalid]
    rfl
  · intro i
    have hlo := (hc i).2.2.2.2.1
    have hup := (hc i).2.2.2.2.2
    refine ⟨hlo,hup,?_⟩
    apply abs_le.mpr
    constructor <;> linarith

/-- This wrapper discharges the C/E margins from the actual Gaussian row event. -/
theorem calibration_from_seed_event (d : ℕ)
    (basis : OrthonormalBasis (Fin d) ℝ (PaperHeavyBallGaussian.Vec d))
    (A : PaperHeavyBallGaussian.Vec d→L[ℝ] PaperHeavyBallGaussian.Vec d)
    (hA : A.toLinearMap.IsSymmetric) (b star u : PaperHeavyBallGaussian.Vec d)
    (mu beta R s S q eta : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R)
    (hs : 0 < s) (hS : 0 < S) (hq : 0 < q) (heta : 0 < eta) (heta1 : eta ≤ 1/2)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x))
    (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R)
    (hu : u∈(PaperHeavyBallGaussian.calibrationBad (row basis A) s S q)ᶜ) :
    ∃ lambdaHat : Fin d→ℝ,
      Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (calibrationProgram basis u (beta/mu) R s S q eta)=some lambdaHat ∧
      ∀i, let lambda := PaperHeavyBallScale.diagonal basis A i/inner ℝ u (A u)
        (1-eta)*lambda ≤ lambdaHat i ∧ lambdaHat i ≤ (1+eta)*lambda ∧
        |lambdaHat i-lambda| ≤ eta*lambda := by
  have hg := PaperHeavyBallGaussian.calibration_good_properties (row basis A) s S q hu
  have hb := calibration_seed_bounds d basis A mu beta s S q hmu hbeta hs hS hq.le hlower hupper u hu
  have huS : ‖u‖ ≤ Real.sqrt S := by
    nlinarith [Real.sqrt_nonneg S,Real.sq_sqrt hS.le,norm_nonneg u,hg.2.1]
  apply calibrationProgram_correct basis A hA b star u mu beta R s S q eta hmu hbeta hR hs hS hq heta heta1
    hlower hAnorm hsol hstar hg.1.le huS
  · intro i
    rw [trueC,energy_symmetry A hA u (basis i)]
    exact (hb.2.2 i).2
  · intro i
    exact (hb.2.2 i).1

lemma calibrationC_scale_cancels (kappa R s S q eta : ℝ)
    (hk : 0 < kappa) (hR : 0 < R) (hs : 0 < s) (hS : 0 < S) (hq : 0 < q) (heta : 0 < eta) :
    bracketC kappa R s/toleranceC kappa R S q eta=8*kappa^2*S/(s*eta*q) := by
  unfold bracketC toleranceC
  field_simp
  ring

lemma calibrationE_scale_cancels (kappa R S q eta : ℝ)
    (hk : 0 < kappa) (hR : 0 < R) (hq : 0 < q) (heta : 0 < eta) :
    bracketE kappa R S/toleranceE R q eta=4*kappa*(Real.sqrt S+1)/(eta*q) := by
  unfold bracketE toleranceE
  field_simp

end
end PaperHeavyBallBackend

end SnapshotModule_099
/- END heavy_ball_calibration -/

/- BEGIN heavy_ball_chebyshev -/
section SnapshotModule_100

namespace PaperHeavyBallChebyshev
open Polynomial Polynomial.Chebyshev
open scoped RealInnerProductSpace
noncomputable section

/-- The dimension-free second-kind Chebyshev bound, proved from the first-kind
bound and the exact two-step polynomial identity. Endpoint eigenvalues are included. -/
lemma abs_U_eval_le (k : ℕ) (t : ℝ) (ht : |t|≤1) :
    |(U ℝ (k:ℤ)).eval t|≤(k:ℝ)+1 := by
  induction k using Nat.twoStepInduction with
  | zero=>simp
  | one=>
    simp only [Nat.cast_one,U_one,eval_mul,eval_ofNat,eval_X,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith
  | more n ih0 _=>
    have he : U ℝ ((n+2:ℕ):ℤ)=2*T ℝ ((n+2:ℕ):ℤ)+U ℝ (n:ℤ) := by
      push_cast
      exact U_eq_two_mul_T_add_U ℝ n
    rw [he,eval_add,eval_mul,eval_ofNat]
    have hh := abs_add_le (2*(T ℝ ((n+2:ℕ):ℤ)).eval t) ((U ℝ (n:ℤ)).eval t)
    have hb := abs_eval_T_real_le_one ((n+2:ℕ):ℤ) ht
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at hh
    push_cast at hh hb ⊢
    linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_sq_repr {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ V) (z : V) :
    ‖z‖^2=∑i,(basis.repr z i)^2 := by
  rw [←basis.repr.norm_map,EuclideanSpace.real_norm_sq_eq]

/-- An actual orthonormal eigenbasis turns a polynomial interval bound into a
vector operator bound. No matrix-power bound is assumed. -/
lemma polynomial_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (A : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,A (basis i)=lambda i •basis i)
    (p : Polynomial ℝ) (rho : ℝ) (hrho : 0≤rho) (hb : ∀i,|p.eval (lambda i)|≤rho) (z : V) :
    ‖(aeval A p) z‖≤rho*‖z‖ := by
  have hsq : ‖(aeval A p) z‖^2≤rho^2*‖z‖^2 := by
    rw [norm_sq_repr basis,norm_sq_repr basis,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [PaperCGSpectral.repr_aeval basis A lambda heigen]
    have hh : (p.eval (lambda i))^2≤rho^2 := sq_le_sq' (by linarith [(abs_le.mp (hb i)).1]) (abs_le.mp (hb i)).2
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (basis.repr z i))]
  nlinarith [norm_nonneg ((aeval A p) z),norm_nonneg z,mul_nonneg hrho (norm_nonneg z)]

end
end PaperHeavyBallChebyshev

end SnapshotModule_100
/- END heavy_ball_chebyshev -/

/- BEGIN heavy_ball_products -/
section SnapshotModule_101

namespace PaperHeavyBallBackend
open PaperOracle PaperHeavyBallLine PaperHeavyBallScale
open scoped RealInnerProductSpace
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {d : ℕ}

def assemble (basis : OrthonormalBasis (Fin d) ℝ V) (coordinates : Fin d→ℝ) : V :=
  basis.repr.symm (WithLp.toLp 2 coordinates)

lemma repr_assemble (basis : OrthonormalBasis (Fin d) ℝ V) (coordinates : Fin d→ℝ) (i : Fin d) :
    basis.repr (assemble basis coordinates) i=coordinates i := by simp [assemble]

lemma assemble_norm_sq (basis : OrthonormalBasis (Fin d) ℝ V) (coordinates : Fin d→ℝ) :
    ‖assemble basis coordinates‖^2=∑i,(coordinates i)^2 := by
  rw [PaperHeavyBallChebyshev.norm_sq_repr basis]
  simp only [repr_assemble]

lemma assemble_uniform_bound (basis : OrthonormalBasis (Fin d) ℝ V) (coordinates : Fin d→ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀i,|coordinates i| ≤ C) :
    ‖assemble basis coordinates‖ ≤ Real.sqrt d*C := by
  have hsq : ‖assemble basis coordinates‖^2 ≤ (d:ℝ)*C^2 := by
    rw [assemble_norm_sq]
    have hh : ∑i,(coordinates i)^2 ≤ ∑_i : Fin d,C^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact sq_le_sq' (abs_le.mp (hbound i)).1 (abs_le.mp (hbound i)).2
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (assemble basis coordinates),Real.sqrt_nonneg (d:ℝ),mul_nonneg (Real.sqrt_nonneg (d:ℝ)) hC]

lemma assemble_relative_bound (basis : OrthonormalBasis (Fin d) ℝ V)
    (coeff : Fin d→ℝ) (eta : ℝ) (heta : 0 ≤ eta) (hcoeff : ∀i,|coeff i| ≤ eta) (g : V) :
    ‖assemble basis (fun i => coeff i*basis.repr g i)‖ ≤ eta*‖g‖ := by
  have hsq : ‖assemble basis (fun i => coeff i*basis.repr g i)‖^2 ≤ eta^2*‖g‖^2 := by
    rw [assemble_norm_sq,PaperHeavyBallChebyshev.norm_sq_repr basis,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh := sq_le_sq' (abs_le.mp (hcoeff i)).1 (abs_le.mp (hcoeff i)).2
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (basis.repr g i))]
  nlinarith [norm_nonneg (assemble basis (fun i => coeff i*basis.repr g i)),norm_nonneg g,
    mul_nonneg heta (norm_nonneg g)]

/-- The full norm error is derived from coordinate root errors and calibration errors. -/
lemma calibrated_coordinate_error (basis : OrthonormalBasis (Fin d) ℝ V)
    (lambda lambdaHat tau tauHat : Fin d→ℝ) (g : V) (eta L delta : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1/2) (hL : 0 ≤ L) (hdelta : 0 ≤ delta)
    (hlambda : ∀i,0 < lambda i ∧ lambda i ≤ L)
    (hcal : ∀i,|lambdaHat i-lambda i| ≤ eta*lambda i)
    (hroot : ∀i,|tauHat i-tau i| ≤ delta)
    (hexact : ∀i,lambda i*tau i=basis.repr g i) :
    ‖assemble basis (fun i => lambdaHat i*tauHat i)-g‖ ≤ eta*‖g‖+2*Real.sqrt d*L*delta := by
  let relative := fun i => lambdaHat i/lambda i-1
  let additive := fun i => lambdaHat i*(tauHat i-tau i)
  have hrelative : ∀i,|relative i| ≤ eta := by
    intro i
    dsimp [relative]
    rw [show lambdaHat i/lambda i-1=(lambdaHat i-lambda i)/lambda i by field_simp [(hlambda i).1.ne'],
      abs_div,abs_of_pos (hlambda i).1]
    exact (div_le_iff₀ (hlambda i).1).mpr (hcal i)
  have hhat : ∀i,|lambdaHat i| ≤ 2*L := by
    intro i
    have hh := abs_add_le (lambdaHat i-lambda i) (lambda i)
    rw [sub_add_cancel,abs_of_pos (hlambda i).1] at hh
    have hm : eta*lambda i ≤ lambda i := mul_le_of_le_one_left (hlambda i).1.le (by linarith)
    nlinarith [hcal i,(hlambda i).2]
  have hadd : ∀i,|additive i| ≤ 2*L*delta := by
    intro i
    dsimp [additive]
    rw [abs_mul]
    exact mul_le_mul (hhat i) (hroot i) (abs_nonneg _) (by positivity)
  have hid : assemble basis (fun i => lambdaHat i*tauHat i)-g=
      assemble basis (fun i => relative i*basis.repr g i)+assemble basis additive := by
    apply basis.repr.injective
    ext i
    simp only [map_sub,map_add,PiLp.sub_apply,PiLp.add_apply,repr_assemble]
    rw [←hexact i]
    dsimp [relative,additive]
    field_simp [(hlambda i).1.ne']
    ring
  rw [hid]
  have hrel := assemble_relative_bound basis relative eta heta hrelative g
  have habs := assemble_uniform_bound basis additive (2*L*delta) (by positivity) hadd
  apply (norm_add_le _ _).trans
  convert add_le_add hrel habs using 1 <;> ring

def residualBracket (kappa R X : ℝ) : ℝ := kappa*(2*R+X)
def productBracket (kappa R : ℝ) : ℝ := 2*kappa*R

def residualProgram (basis : OrthonormalBasis (Fin d) ℝ V) (lambdaHat : Fin d→ℝ)
    (z : V) (kappa R X delta : ℝ) : Program (V×V) Ordering V := by
  classical
  exact if ‖z‖ ≤ R+X then
    Program.bind (collect d (fun i => rootProgram z (basis i) (residualBracket kappa R X) delta))
      (fun roots => .done (assemble basis (fun i => lambdaHat i*roots i)))
    else .done 0

def coordinateProduct (basis : OrthonormalBasis (Fin d) ℝ V) (v : V)
    (kappa R delta : ℝ) (i : Fin d) : Program (V×V) Ordering ℝ :=
  Program.bind (rootProgram 0 (basis i) (productBracket kappa R) delta) (fun zeroRoot =>
    Program.bind (rootProgram v (basis i) (productBracket kappa R) delta) (fun vRoot => .done (zeroRoot-vRoot)))

def productProgram (basis : OrthonormalBasis (Fin d) ℝ V) (lambdaHat : Fin d→ℝ)
    (v : V) (kappa R delta : ℝ) : Program (V×V) Ordering V := by
  classical
  exact if ‖v‖ ≤ R then
    Program.bind (collect d (coordinateProduct basis v kappa R delta))
      (fun roots => .done (assemble basis (fun i => lambdaHat i*roots i)))
    else .done 0

def residualCost (d : ℕ) (kappa R X delta : ℝ) : ℕ := d*horizon (residualBracket kappa R X) delta
def productCost (d : ℕ) (kappa R delta : ℝ) : ℕ := d*(2*horizon (productBracket kappa R) delta)

lemma residualProgram_cap (basis : OrthonormalBasis (Fin d) ℝ V) (lambdaHat : Fin d→ℝ)
    (z : V) (kappa R X delta : ℝ) :
    Program.Cap (residualCost d kappa R X delta) (residualProgram basis lambdaHat z kappa R X delta) := by
  classical
  unfold residualProgram residualCost
  split_ifs
  · rw [show d*horizon (residualBracket kappa R X) delta=d*horizon (residualBracket kappa R X) delta+0 by omega]
    apply Program.cap_bind _ _
    · apply cap_collect
      intro i
      exact bisect_public_cap z (basis i) _ _ _
    · intro roots
      trivial
  · cases d*horizon (residualBracket kappa R X) delta <;> trivial

lemma coordinateProduct_cap (basis : OrthonormalBasis (Fin d) ℝ V) (v : V)
    (kappa R delta : ℝ) (i : Fin d) :
    Program.Cap (2*horizon (productBracket kappa R) delta) (coordinateProduct basis v kappa R delta i) := by
  unfold coordinateProduct
  rw [show 2*horizon (productBracket kappa R) delta=
    horizon (productBracket kappa R) delta+(horizon (productBracket kappa R) delta+0) by omega]
  apply Program.cap_bind _ _ (bisect_public_cap 0 (basis i) _ _ _)
  intro zeroRoot
  apply Program.cap_bind _ _ (bisect_public_cap v (basis i) _ _ _)
  intro vRoot
  trivial

lemma productProgram_cap (basis : OrthonormalBasis (Fin d) ℝ V) (lambdaHat : Fin d→ℝ)
    (v : V) (kappa R delta : ℝ) :
    Program.Cap (productCost d kappa R delta) (productProgram basis lambdaHat v kappa R delta) := by
  classical
  unfold productProgram productCost
  split_ifs
  · rw [show d*(2*horizon (productBracket kappa R) delta)=d*(2*horizon (productBracket kappa R) delta)+0 by omega]
    apply Program.cap_bind _ _ (cap_collect _ _ _ (coordinateProduct_cap basis v kappa R delta))
    intro roots
    trivial
  · cases d*(2*horizon (productBracket kappa R) delta) <;> trivial

def scaledDiagonal (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V) (u : V) (i : Fin d) : ℝ :=
  PaperHeavyBallScale.diagonal basis A i/inner ℝ u (A u)
def scaledRhs (A : V→L[ℝ] V) (b u : V) : V := (inner ℝ u (A u))⁻¹ •b
def scaledResidual (A : V→L[ℝ] V) (b u z : V) : V := scaledRhs A b u-scaledOperator A u z

lemma scaledDiagonal_energy (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V) (u : V) (i : Fin d) :
    scaledDiagonal basis A u i=inner ℝ (basis i) (scaledOperator A u (basis i)) := by
  simp only [scaledDiagonal,PaperHeavyBallScale.diagonal,scaledOperator,ContinuousLinearMap.smul_apply,
    real_inner_smul_right]
  ring

lemma scaledDiagonal_positive (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (u : V) (mu : ℝ) (hmu : 0 < mu) (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x))
    (ha : 0 < inner ℝ u (A u)) (i : Fin d) : 0 < scaledDiagonal basis A u i := by
  apply div_pos _ ha
  exact hmu.trans_le (diagonal_lower basis A mu hlower i)

lemma scaledDiagonal_norm_bound (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (u : V) (i : Fin d) : scaledDiagonal basis A u i ≤ ‖scaledOperator A u‖ := by
  rw [scaledDiagonal_energy]
  have hinner := abs_real_inner_le_norm (basis i) (scaledOperator A u (basis i))
  rw [basis.orthonormal.norm_eq_one,one_mul] at hinner
  have hop := (scaledOperator A u).le_opNorm (basis i)
  rw [basis.orthonormal.norm_eq_one,mul_one] at hop
  exact (le_abs_self _).trans (hinner.trans hop)

lemma residual_coordinate_identity (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (b u z : V) (ha : inner ℝ u (A u)≠0) (i : Fin d)
    (hdiag : PaperHeavyBallScale.diagonal basis A i≠0) :
    scaledDiagonal basis A u i*lineRoot A b z (basis i)=basis.repr (scaledResidual A b u z) i := by
  simp only [scaledDiagonal,lineRoot,scaledResidual,scaledRhs,scaledOperator,
    ContinuousLinearMap.smul_apply,map_sub,map_smul,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    basis.repr_apply_apply,inner_sub_right,real_inner_smul_right]
  unfold PaperHeavyBallScale.diagonal at hdiag ⊢
  field_simp

lemma product_coordinate_identity (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (b u v : V) (ha : inner ℝ u (A u)≠0) (i : Fin d)
    (hdiag : PaperHeavyBallScale.diagonal basis A i≠0) :
    scaledDiagonal basis A u i*(lineRoot A b 0 (basis i)-lineRoot A b v (basis i))=
      basis.repr (scaledOperator A u v) i := by
  simp only [scaledDiagonal,lineRoot,scaledOperator,ContinuousLinearMap.smul_apply,map_zero,sub_zero,
    map_smul,PiLp.smul_apply,smul_eq_mul,basis.repr_apply_apply,inner_sub_right,real_inner_smul_right]
  unfold PaperHeavyBallScale.diagonal at hdiag ⊢
  field_simp
  ring

lemma coordinate_root_bracket (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (b star z : V) (mu beta R Z : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hz : ‖z‖ ≤ Z) (i : Fin d) :
    |lineRoot A b z (basis i)| ≤ (beta/mu)*(Z+R) := by
  have hi : basis i≠0 := norm_ne_zero_iff.mp (by rw [basis.orthonormal.norm_eq_one];norm_num)
  have hb := conditioned_line_root_bound A b star z (basis i) mu beta R hmu hbeta hlower hAnorm hsol hstar hi
  rw [basis.orthonormal.norm_eq_one,div_one] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (by linarith : ‖z‖+R ≤ Z+R)
    (le_of_lt (div_pos (hmu.trans_le hbeta) hmu)))

/-- Actual residual backend from true conditioned roots, with no root-error premise. -/
theorem residualProgram_correct (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) (b star u z : V) (mu beta R X eta delta : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (hX : 0 ≤ X) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1/2) (hdelta : 0 < delta)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (ha : 0 < inner ℝ u (A u))
    (lambdaHat : Fin d→ℝ) (hcal : ∀i,|lambdaHat i-scaledDiagonal basis A u i| ≤ eta*scaledDiagonal basis A u i)
    (hz : ‖z‖ ≤ R+X) :
    ‖Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (residualProgram basis lambdaHat z (beta/mu) R X delta)-scaledResidual A b u z‖ ≤
      eta*‖scaledResidual A b u z‖+2*Real.sqrt d*‖scaledOperator A u‖*delta := by
  let Cmp := PaperOracle.comparisonOracle (quadratic A b)
  let D := residualBracket (beta/mu) R X
  have hD : 0 < D := by dsimp [D,residualBracket];exact mul_pos (div_pos (hmu.trans_le hbeta) hmu) (by linarith)
  have hroots : ∀i,|Program.run Cmp (rootProgram z (basis i) D delta)-lineRoot A b z (basis i)| ≤ delta := by
    intro i
    have hi : basis i≠0 := norm_ne_zero_iff.mp (by rw [basis.orthonormal.norm_eq_one];norm_num)
    apply (rootProgram_correct A hA b z (basis i) (conditioned_line_curvature A mu hmu hlower _ hi) D delta hD hdelta _).2
    have hh := coordinate_root_bracket basis A b star z mu beta R (R+X) hmu hbeta hlower hAnorm hsol hstar hz i
    have he : D=(beta/mu)*((R+X)+R) := by dsimp [D,residualBracket];ring
    rw [he]
    exact hh
  have hdiag : ∀i,PaperHeavyBallScale.diagonal basis A i≠0 := by
    intro i
    exact ne_of_gt (hmu.trans_le (diagonal_lower basis A mu hlower i))
  have hh := calibrated_coordinate_error basis (scaledDiagonal basis A u) lambdaHat
    (fun i => lineRoot A b z (basis i)) (fun i => Program.run Cmp (rootProgram z (basis i) D delta))
    (scaledResidual A b u z) eta ‖scaledOperator A u‖ delta heta heta1 (norm_nonneg _) hdelta.le
    (fun i => ⟨scaledDiagonal_positive basis A u mu hmu hlower ha i,scaledDiagonal_norm_bound basis A u i⟩)
    hcal hroots (fun i => residual_coordinate_identity basis A b u z ha.ne' i (hdiag i))
  simpa only [residualProgram,if_pos hz,Program.run_bind,run_collect,Program.run] using hh

/-- Actual product backend with two coordinate roots and the genuine factor-four additive error. -/
theorem productProgram_correct (basis : OrthonormalBasis (Fin d) ℝ V) (A : V→L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) (b star u v : V) (mu beta R eta delta : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1/2) (hdelta : 0 < delta)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (ha : 0 < inner ℝ u (A u))
    (lambdaHat : Fin d→ℝ) (hcal : ∀i,|lambdaHat i-scaledDiagonal basis A u i| ≤ eta*scaledDiagonal basis A u i)
    (hv : ‖v‖ ≤ R) :
    ‖Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (productProgram basis lambdaHat v (beta/mu) R delta)-scaledOperator A u v‖ ≤
      eta*‖scaledOperator A u v‖+4*Real.sqrt d*‖scaledOperator A u‖*delta := by
  let Cmp := PaperOracle.comparisonOracle (quadratic A b)
  let D := productBracket (beta/mu) R
  have hk : 0 < beta/mu := div_pos (hmu.trans_le hbeta) hmu
  have hD : 0 < D := by dsimp [D,productBracket];positivity
  have hroots (z : V) (hz : ‖z‖ ≤ R) (i : Fin d) :
      |Program.run Cmp (rootProgram z (basis i) D delta)-lineRoot A b z (basis i)| ≤ delta := by
    have hi : basis i≠0 := norm_ne_zero_iff.mp (by rw [basis.orthonormal.norm_eq_one];norm_num)
    apply (rootProgram_correct A hA b z (basis i) (conditioned_line_curvature A mu hmu hlower _ hi) D delta hD hdelta _).2
    have hh := coordinate_root_bracket basis A b star z mu beta R R hmu hbeta hlower hAnorm hsol hstar hz i
    have he : D=(beta/mu)*(R+R) := by dsimp [D,productBracket];ring
    rw [he]
    exact hh
  have hdiff : ∀i,|Program.run Cmp (coordinateProduct basis v (beta/mu) R delta i)-
      (lineRoot A b 0 (basis i)-lineRoot A b v (basis i))| ≤ 2*delta := by
    intro i
    have h0 := hroots 0 (by simpa only [norm_zero] using hR.le) i
    have hvv := hroots v hv i
    have hs := abs_sub_le
      (Program.run Cmp (rootProgram 0 (basis i) D delta)-lineRoot A b 0 (basis i)) 0
      (Program.run Cmp (rootProgram v (basis i) D delta)-lineRoot A b v (basis i))
    simp only [sub_zero,zero_sub,abs_neg] at hs
    simp only [coordinateProduct,Program.run_bind,Program.run]
    have he : (Program.run Cmp (rootProgram 0 (basis i) D delta)-
        Program.run Cmp (rootProgram v (basis i) D delta))-(lineRoot A b 0 (basis i)-lineRoot A b v (basis i))=
      (Program.run Cmp (rootProgram 0 (basis i) D delta)-lineRoot A b 0 (basis i))-
        (Program.run Cmp (rootProgram v (basis i) D delta)-lineRoot A b v (basis i)) := by ring
    rw [he]
    linarith
  have hdiag : ∀i,PaperHeavyBallScale.diagonal basis A i≠0 := by
    intro i
    exact ne_of_gt (hmu.trans_le (diagonal_lower basis A mu hlower i))
  have hh := calibrated_coordinate_error basis (scaledDiagonal basis A u) lambdaHat
    (fun i => lineRoot A b 0 (basis i)-lineRoot A b v (basis i))
    (fun i => Program.run Cmp (coordinateProduct basis v (beta/mu) R delta i))
    (scaledOperator A u v) eta ‖scaledOperator A u‖ (2*delta) heta heta1 (norm_nonneg _) (by positivity)
    (fun i => ⟨scaledDiagonal_positive basis A u mu hmu hlower ha i,scaledDiagonal_norm_bound basis A u i⟩)
    hcal hdiff (fun i => product_coordinate_identity basis A b u v ha.ne' i (hdiag i))
  simp only [productProgram,if_pos hv,Program.run_bind,run_collect,Program.run]
  convert hh using 1 <;> ring

def powerRootTolerance (d : ℕ) (kappa R s S sigma : ℝ) : ℝ :=
  sigma*s^2*R/(8*Real.sqrt d*kappa^2*S)
def residualRootTolerance (d : ℕ) (kappa s tau : ℝ) : ℝ :=
  tau*s^2/(4*Real.sqrt d*kappa)

lemma scaledOperator_norm_lower (A : V→L[ℝ] V) (u v : V) (kappa R S : ℝ)
    (hk : 0 < kappa) (hR : 0 < R) (hS : 0 < S) (hv : ‖v‖=R)
    (hlower : ∀x,(1/(kappa*S))*‖x‖^2 ≤ inner ℝ x (scaledOperator A u x)) :
    R/(kappa*S) ≤ ‖scaledOperator A u v‖ := by
  have hh := (hlower v).trans ((le_abs_self _).trans (abs_real_inner_le_norm v (scaledOperator A u v)))
  rw [hv] at hh
  have he : R/(kappa*S)=(1/(kappa*S))*R := by ring
  rw [he]
  nlinarith

/-- Source public power precision yields the required relative product error. -/
theorem productProgram_public_precision (basis : OrthonormalBasis (Fin d) ℝ V) (hd : 0 < d)
    (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b star u v : V)
    (mu beta R s S eta sigma delta : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta)
    (hR : 0 < R) (hs : 0 < s) (hS : 0 < S) (heta : 0 ≤ eta) (hsigma : 0 < sigma)
    (hsigma1 : sigma ≤ 1/2) (hetasigma : eta ≤ sigma/2) (hdelta : 0 < delta)
    (hdeltapublic : delta ≤ powerRootTolerance d (beta/mu) R s S sigma)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x))
    (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hun : s ≤ ‖u‖) (huS : ‖u‖^2 ≤ S)
    (lambdaHat : Fin d→ℝ) (hcal : ∀i,|lambdaHat i-scaledDiagonal basis A u i| ≤ eta*scaledDiagonal basis A u i)
    (hv : ‖v‖=R) :
    ‖Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (productProgram basis lambdaHat v (beta/mu) R delta)-scaledOperator A u v‖ ≤
      sigma*‖scaledOperator A u v‖ := by
  have hk : 0 < beta/mu := div_pos (hmu.trans_le hbeta) hmu
  have hu : u≠0 := norm_pos_iff.mp (hs.trans_le hun)
  have ha := conditioned_line_curvature A mu hmu hlower u hu
  have hscaled := scaled_spectral_bounds A mu beta s S hmu hbeta hs hS hlower hupper hAnorm u hun huS
  have hh := productProgram_correct basis A hA b star u v mu beta R eta delta hmu hbeta hR heta
    (by linarith) hdelta hlower hAnorm hsol hstar ha lambdaHat hcal hv.le
  have hnormlow := scaledOperator_norm_lower A u v (beta/mu) R S hk hR hS hv hscaled.1
  have hdim : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hfactor : 0 ≤ 4*Real.sqrt d*((beta/mu)/s^2) := by positivity
  have hbudget := mul_le_mul_of_nonneg_left hdeltapublic hfactor
  have he : 4*Real.sqrt d*((beta/mu)/s^2)*powerRootTolerance d (beta/mu) R s S sigma=
      sigma*R/(2*(beta/mu)*S) := by
    unfold powerRootTolerance
    field_simp
    ring
  rw [he] at hbudget
  have hop := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscaled.2 (show 0 ≤ 4*Real.sqrt d by positivity)) hdelta.le
  have hadd : 4*Real.sqrt d*‖scaledOperator A u‖*delta ≤ sigma*R/(2*(beta/mu)*S) :=
    hop.trans hbudget
  have hlowerhalf := mul_le_mul_of_nonneg_left hnormlow (show 0 ≤ sigma/2 by positivity)
  have hetahalf := mul_le_mul_of_nonneg_right hetasigma (norm_nonneg (scaledOperator A u v))
  have hehalf : sigma/2*(R/((beta/mu)*S))=sigma*R/(2*(beta/mu)*S) := by ring
  rw [hehalf] at hlowerhalf
  linarith

/-- The public residual precision supplies the heavy-ball additive tolerance. -/
theorem residualProgram_public_precision (basis : OrthonormalBasis (Fin d) ℝ V) (hd : 0 < d)
    (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b star u z : V)
    (mu beta R X s S eta tau delta : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta)
    (hR : 0 < R) (hX : 0 ≤ X) (hs : 0 < s) (hS : 0 < S) (heta : 0 ≤ eta) (heta1 : eta ≤ 1/2)
    (htau : 0 ≤ tau) (hdelta : 0 < delta) (hdeltapublic : delta ≤ residualRootTolerance d (beta/mu) s tau)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x))
    (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2) (hAnorm : ‖A‖ ≤ beta)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (hun : s ≤ ‖u‖) (huS : ‖u‖^2 ≤ S)
    (lambdaHat : Fin d→ℝ) (hcal : ∀i,|lambdaHat i-scaledDiagonal basis A u i| ≤ eta*scaledDiagonal basis A u i)
    (hz : ‖z‖ ≤ R+X) :
    ‖Program.run (PaperOracle.comparisonOracle (quadratic A b))
        (residualProgram basis lambdaHat z (beta/mu) R X delta)-scaledResidual A b u z‖ ≤
      eta*‖scaledResidual A b u z‖+tau := by
  have hk : 0 < beta/mu := div_pos (hmu.trans_le hbeta) hmu
  have hu : u≠0 := norm_pos_iff.mp (hs.trans_le hun)
  have ha := conditioned_line_curvature A mu hmu hlower u hu
  have hscaled := scaled_spectral_bounds A mu beta s S hmu hbeta hs hS hlower hupper hAnorm u hun huS
  have hh := residualProgram_correct basis A hA b star u z mu beta R X eta delta hmu hbeta hR hX heta
    heta1 hdelta hlower hAnorm hsol hstar ha lambdaHat hcal hz
  have hdim : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hfactor : 0 ≤ 2*Real.sqrt d*((beta/mu)/s^2) := by positivity
  have hbudget := mul_le_mul_of_nonneg_left hdeltapublic hfactor
  have he : 2*Real.sqrt d*((beta/mu)/s^2)*residualRootTolerance d (beta/mu) s tau=tau/2 := by
    unfold residualRootTolerance
    field_simp [ne_of_gt (hmu.trans_le hbeta)] <;> ring
  rw [he] at hbudget
  have hop := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscaled.2 (show 0 ≤ 2*Real.sqrt d by positivity)) hdelta.le
  have hadd : 2*Real.sqrt d*‖scaledOperator A u‖*delta ≤ tau/2 := hop.trans hbudget
  linarith

lemma product_precision_scale_cancels (d : ℕ) (hd : 0 < d)
    (kappa R s S sigma : ℝ) (hk : 0 < kappa) (hR : 0 < R) (hs : 0 < s) (hS : 0 < S) (hsigma : 0 < sigma) :
    productBracket kappa R/powerRootTolerance d kappa R s S sigma=
      16*Real.sqrt d*kappa^3*S/(sigma*s^2) := by
  have hdim : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  unfold productBracket powerRootTolerance
  field_simp
  ring

lemma residual_precision_scale (d : ℕ) (hd : 0 < d)
    (kappa R X s tau : ℝ) (hk : 0 < kappa) (hs : 0 < s) (htau : 0 < tau) :
    residualBracket kappa R X/residualRootTolerance d kappa s tau=
      4*Real.sqrt d*kappa^2*(2*R+X)/(tau*s^2) := by
  have hdim : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  unfold residualBracket residualRootTolerance
  field_simp

end
end PaperHeavyBallBackend

end SnapshotModule_101
/- END heavy_ball_products -/

/- BEGIN heavy_ball_power_spectral -/
section SnapshotModule_102

namespace PaperHeavyBallPowerSpectral
open Polynomial
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma repr_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (B : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i) (k : ℕ) (w : V) (i : ι) :
    basis.repr ((B^k) w) i=(lambda i)^k*basis.repr w i := by
  have hh:=PaperCGSpectral.repr_aeval basis B lambda heigen (X^k) w i
  simpa only [map_pow,aeval_X,eval_pow,eval_X] using hh

lemma scalar_spectral_deficit (M nu lambda : ℝ) (hM : 0 ≤ M) (hn : 0 ≤ nu) (hn1 : nu ≤ 1)
    (hl : 0 ≤ lambda) (hu : lambda ≤ M) (k : ℕ) :
    (M*(1-nu)-lambda)*lambda^(2*k)  ≤  M*(M*(1-nu))^(2*k) := by
  have ha : 0 ≤ M*(1-nu) := by positivity
  by_cases hlow : lambda ≤ M*(1-nu)
  · have hdiff : M*(1-nu)-lambda ≤ M := by nlinarith
    have hp:=pow_le_pow_left₀ hl hlow (2*k)
    exact mul_le_mul hdiff hp (pow_nonneg hl _) hM
  · have hd : M*(1-nu)-lambda ≤ 0 := by linarith
    exact (mul_nonpos_of_nonpos_of_nonneg hd (pow_nonneg hl _)).trans (by positivity)

def rayleigh (B : Module.End ℝ V) (z : V) : ℝ := inner ℝ z (B z)/‖z‖^2

/-- The exact power Rayleigh estimate is proved for the actual operator powers,
from a top-eigenvector component and an orthonormal spectral decomposition. -/
theorem exact_power_rayleigh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (B : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i)
    (M nu S q0 : ℝ) (hM : 0 < M) (hn : 0 ≤ nu) (hn1 : nu ≤ 1) (hS : 0 ≤ S) (hq : 0 < q0)
    (hlambda : ∀i,0 ≤ lambda i ∧ lambda i ≤ M)
    (top : ι) (htop : lambda top=M) (w : V) (hwn : ‖w‖^2 ≤ S)
    (hwt : q0 ≤ |basis.repr w top|) (k : ℕ) :
    (M^k*q0) ≤ ‖(B^k) w‖ ∧
    M*(1-nu)-M*(1-nu)^(2*k)*S/q0^2 ≤ rayleigh B ((B^k) w) := by
  let z:=(B^k) w
  have hden : M^(2*k)*q0^2 ≤ ‖z‖^2 := by
    have hs : (basis.repr z top)^2 ≤ ∑i,(basis.repr z i)^2 :=
      Finset.single_le_sum (fun i _=>sq_nonneg (basis.repr z i)) (Finset.mem_univ top)
    rw [←PaperHeavyBallChebyshev.norm_sq_repr basis z] at hs
    have he: basis.repr z top=M^k*basis.repr w top := by simpa only [z,htop] using repr_power basis B lambda heigen k w top
    rw [he] at hs
    have hq2 : q0^2 ≤ (basis.repr w top)^2 := by nlinarith [sq_abs (basis.repr w top),abs_nonneg (basis.repr w top)]
    have hh:=mul_le_mul_of_nonneg_left hq2 (pow_nonneg hM.le (2*k))
    have heq : (M^k*basis.repr w top)^2=M^(2*k)*(basis.repr w top)^2 := by
      rw [mul_pow,←pow_mul,Nat.mul_comm k 2]
    rw [heq] at hs
    exact hh.trans hs
  have hz : 0 < ‖z‖^2 := (mul_pos (pow_pos hM (2*k)) (sq_pos_of_pos hq)).trans_le hden
  have hdeficit : M*(1-nu)*‖z‖^2-inner ℝ z (B z) ≤ M*(M*(1-nu))^(2*k)*S := by
    have he : M*(1-nu)*‖z‖^2-inner ℝ z (B z)=
        ∑i,(M*(1-nu)-lambda i)*(lambda i)^(2*k)*(basis.repr w i)^2 := by
      rw [PaperHeavyBallChebyshev.norm_sq_repr basis z,
        show inner ℝ z (B z)=PaperCGExact.energy B z from rfl,
        PaperCGSpectral.energy_diagonal basis B lambda heigen,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show basis.repr z i=(lambda i)^k*basis.repr w i by exact repr_power basis B lambda heigen k w i]
      rw [mul_pow,←pow_mul]
      have hk : k*2=2*k := by omega
      rw [hk]
      ring
    rw [he]
    have hh : (∑i,(M*(1-nu)-lambda i)*(lambda i)^(2*k)*(basis.repr w i)^2) ≤ 
        ∑i,(M*(M*(1-nu))^(2*k))*(basis.repr w i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (scalar_spectral_deficit M nu (lambda i) hM.le hn hn1
        (hlambda i).1 (hlambda i).2 k) (sq_nonneg _)
    rw [←Finset.mul_sum,←PaperHeavyBallChebyshev.norm_sq_repr basis w] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hwn (by positivity))
  have hcoeff : 0 ≤ M*(1-nu)^(2*k)*S/q0^2 := by positivity
  have hmul:=mul_le_mul_of_nonneg_left hden hcoeff
  have hcancel : (M*(1-nu)^(2*k)*S/q0^2)*(M^(2*k)*q0^2)=M*(M*(1-nu))^(2*k)*S := by
    rw [mul_pow]
    field_simp
    <;> ring
  rw [hcancel] at hmul
  constructor
  · have hpow : (M^k*q0)^2=M^(2*k)*q0^2 := by rw [mul_pow,←pow_mul,Nat.mul_comm k 2]
    nlinarith [norm_nonneg z,pow_pos hM k]
  · dsimp [rayleigh]
    apply (le_div_iff₀ hz).mpr
    nlinarith

end
end PaperHeavyBallPowerSpectral

end SnapshotModule_102
/- END heavy_ball_power_spectral -/

/- BEGIN heavy_ball_power_iteration -/
section SnapshotModule_103

namespace PaperHeavyBallPower
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
local instance : DecidableEq V := Classical.decEq V

def normalizedStep (R : ℝ) (product : V→V) (v : V) : V :=
  if product v=0 then 0 else R •NormedSpace.normalize (product v)

def normalizedIterate (R : ℝ) (product : V→V) (w : V) : ℕ→V
  | 0=>R •NormedSpace.normalize w
  | k+1=>normalizedStep R product (normalizedIterate R product w k)

lemma relative_product_ne_zero (B : V→L[ℝ] V) (product : V→V)
    (sigma : ℝ) (hsigma : sigma<1) (v : V) (hBv : B v≠0)
    (herror : ‖product v-B v‖  ≤  sigma*‖B v‖) : product v≠0 := by
  intro hz
  rw [hz,zero_sub,norm_neg] at herror
  have hp : 0 < ‖B v‖ := norm_pos_iff.mpr hBv
  nlinarith

lemma iterate_norm {B : V→L[ℝ] V} (product : V→V) (R sigma : ℝ) (hR : 0 < R)
    (hsigma : sigma<1) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖  ≤  sigma*‖B v‖) (w : V) (hw : w≠0) :
    ∀k,‖normalizedIterate R product w k‖=R := by
  intro k
  induction k with
  | zero=>simp [normalizedIterate,norm_smul,NormedSpace.norm_normalize hw,abs_of_pos hR]
  | succ k ih=>
    have hv : normalizedIterate R product w k≠0 := by intro hz;rw [hz,norm_zero] at ih;linarith
    have hp:=relative_product_ne_zero B product sigma hsigma _ (hnondegenerate _ hv) (hproduct _ ih)
    simp only [normalizedIterate,normalizedStep,if_neg hp,norm_smul,NormedSpace.norm_normalize hp,
      Real.norm_eq_abs,abs_of_pos hR,mul_one]

lemma product_iterate_ne_zero {B : V→L[ℝ] V} (product : V→V) (R sigma : ℝ) (hR : 0 < R)
    (hsigma : sigma<1) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖  ≤  sigma*‖B v‖) (w : V) (hw : w≠0) (k : ℕ) :
    product (normalizedIterate R product w k)≠0 := by
  have hn:=iterate_norm product R sigma hR hsigma hnondegenerate hproduct w hw k
  have hv : normalizedIterate R product w k≠0 := by intro hz;rw [hz,norm_zero] at hn;linarith
  exact relative_product_ne_zero B product sigma hsigma _ (hnondegenerate _ hv) (hproduct _ hn)

def scale (R : ℝ) (product : V→V) (w : V) : ℕ→ℝ
  | 0=>‖w‖/R
  | k+1=>scale R product w k*‖product (normalizedIterate R product w k)‖/R

def homogeneous (R : ℝ) (product : V→V) (w : V) (k : ℕ) : V :=
  scale R product w k •normalizedIterate R product w k

lemma scale_pos {B : V→L[ℝ] V} (product : V→V) (R sigma : ℝ) (hR : 0 < R)
    (hsigma : sigma<1) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖  ≤  sigma*‖B v‖) (w : V) (hw : w≠0) :
    ∀k,0 < scale R product w k := by
  intro k
  induction k with
  | zero=>exact div_pos (norm_pos_iff.mpr hw) hR
  | succ k ih=>
    exact div_pos (mul_pos ih (norm_pos_iff.mpr (product_iterate_ne_zero product R sigma hR hsigma
      hnondegenerate hproduct w hw k))) hR

lemma homogeneous_zero (product : V→V) (R : ℝ) (hR : 0 < R) (w : V) (hw : w≠0) :
    homogeneous R product w 0=w := by
  have hn : ‖w‖≠0 := norm_ne_zero_iff.mpr hw
  simp only [homogeneous,scale,normalizedIterate,NormedSpace.normalize,smul_smul]
  have hc : (‖w‖/R)*(R*‖w‖⁻¹)=1 := by field_simp
  rw [hc,one_smul]

lemma homogeneous_successor (product : V→V) (R : ℝ) (hR : 0 < R) (w : V) (k : ℕ)
    (hp : product (normalizedIterate R product w k)≠0) :
    homogeneous R product w (k+1)=scale R product w k •product (normalizedIterate R product w k) := by
  have hn : ‖product (normalizedIterate R product w k)‖≠0 := norm_ne_zero_iff.mpr hp
  simp only [homogeneous,scale,normalizedIterate,normalizedStep,if_neg hp,NormedSpace.normalize,smul_smul]
  congr 1
  field_simp

lemma homogeneous_local_error {B : V→L[ℝ] V} (product : V→V) (R sigma : ℝ) (hR : 0 < R)
    (hsigma : sigma<1) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖  ≤  sigma*‖B v‖) (w : V) (hw : w≠0) (k : ℕ) :
    ‖homogeneous R product w (k+1)-B (homogeneous R product w k)‖  ≤  
      sigma*‖B (homogeneous R product w k)‖ := by
  have hp:=product_iterate_ne_zero product R sigma hR hsigma hnondegenerate hproduct w hw k
  have hs: 0  ≤  scale R product w k := (scale_pos product R sigma hR hsigma hnondegenerate hproduct w hw k).le
  rw [homogeneous_successor product R hR w k hp]
  change ‖scale R product w k •product (normalizedIterate R product w k)-
      B (scale R product w k •normalizedIterate R product w k)‖  ≤  _
  rw [map_smul,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  have hh:=mul_le_mul_of_nonneg_left (hproduct _ (iterate_norm product R sigma hR hsigma hnondegenerate hproduct w hw k)) hs
  simpa only [homogeneous,map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs,mul_assoc,mul_left_comm] using hh

/-- Literal normalized power program with a fixed public iteration count.
A zero returned product triggers a fallback. -/
def powerProgram {Q Reply : Type*} (product : V→PaperOracle.Program Q Reply V) (R : ℝ) :
    ℕ→V→PaperOracle.Program Q Reply V
  | 0,v=>.done v
  | k+1,v=>PaperOracle.Program.bind (product v) (fun z=>
      if z=0 then .done 0 else powerProgram product R k (R •NormedSpace.normalize z))

lemma powerProgram_cap {Q Reply : Type*} (product : V→PaperOracle.Program Q Reply V) (R : ℝ)
    (budget : ℕ) (hbudget : ∀v,PaperOracle.Program.Cap budget (product v)) (k : ℕ) (v : V) :
    PaperOracle.Program.Cap (k*budget) (powerProgram product R k v) := by
  induction k generalizing v with
  | zero=>simp only [powerProgram,Nat.zero_mul,PaperOracle.Program.Cap]
  | succ k ih=>
    change PaperOracle.Program.Cap ((k+1)*budget) (PaperOracle.Program.bind (product v) _)
    rw [show (k+1)*budget=budget+k*budget by ring]
    apply PaperOracle.Program.cap_bind (product v) _ (hbudget v)
    intro z
    split_ifs
    · cases k*budget <;> trivial
    · exact ih _

lemma normalizedIterate_eq_iterate (R : ℝ) (product : V→V) (w : V) (k : ℕ) :
    normalizedIterate R product w k=(normalizedStep R product)^[k] (R •NormedSpace.normalize w) := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [normalizedIterate,ih,Function.iterate_succ_apply']

lemma powerProgram_eval {Q Reply : Type*} (C : Q→Reply)
    (product : V→PaperOracle.Program Q Reply V) (R : ℝ) (hR : 0 < R)
    (hprod : ∀v,‖v‖=R→PaperOracle.Program.run C (product v)≠0) (k : ℕ) (v : V) (hv : ‖v‖=R) :
    PaperOracle.Program.run C (powerProgram product R k v)=
      (normalizedStep R (fun x=>PaperOracle.Program.run C (product x)))^[k] v := by
  induction k generalizing v with
  | zero=>rfl
  | succ k ih=>
    have hp:=hprod v hv
    rw [powerProgram,PaperOracle.Program.run_bind,if_neg hp]
    rw [ih _ (by simp [norm_smul,Real.norm_eq_abs,abs_of_pos hR,NormedSpace.norm_normalize hp])]
    rw [Function.iterate_succ_apply]
    simp only [normalizedStep,if_neg hp]


end
end PaperHeavyBallPower

end SnapshotModule_103
/- END heavy_ball_power_iteration -/

/- BEGIN heavy_ball_power_error -/
section SnapshotModule_104

namespace PaperHeavyBallPower
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma homogeneous_growth {B : V→L[ℝ] V} (product : V→V) (R sigma M : ℝ) (hR : 0 < R)
    (hs0 : 0 ≤ sigma) (hs1 : sigma<1) (hM : 0 ≤ M)
    (hB : ∀v,‖B v‖ ≤ M*‖v‖) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖ ≤ sigma*‖B v‖) (w : V) (hw : w≠0) :
    ∀k,‖homogeneous R product w k‖ ≤ (1+sigma)^k*M^k*‖w‖ := by
  intro k
  induction k with
  | zero=>rw [homogeneous_zero product R hR w hw];simp
  | succ k ih=>
    have he:=homogeneous_local_error product R sigma hR hs1 hnondegenerate hproduct w hw k
    have hn:=norm_add_le (homogeneous R product w (k+1)-B (homogeneous R product w k)) (B (homogeneous R product w k))
    have hid : homogeneous R product w (k+1)-B (homogeneous R product w k)+B (homogeneous R product w k)=
      homogeneous R product w (k+1) := by abel
    rw [hid] at hn
    have hb:=hB (homogeneous R product w k)
    have h1:=mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+sigma by positivity)
    have h2:=mul_le_mul_of_nonneg_left ih (show 0 ≤ (1+sigma)*M by positivity)
    rw [pow_succ (1+sigma),pow_succ M]
    nlinarith

/-- The inexact normalized power run admits the manuscript's homogeneous
perturbation analysis, derived from the executed normalization recurrence. -/
theorem homogeneous_deviation {B : V→L[ℝ] V} (product : V→V) (R sigma M : ℝ) (hR : 0 < R)
    (hs0 : 0 ≤ sigma) (hs1 : sigma<1) (hM : 0 ≤ M)
    (hB : ∀v,‖B v‖ ≤ M*‖v‖) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖ ≤ sigma*‖B v‖) (w : V) (hw : w≠0) :
    ∀k,‖homogeneous R product w k-(B.toLinearMap^k) w‖ ≤ ((1+sigma)^k-1)*M^k*‖w‖ := by
  intro k
  induction k with
  | zero=>rw [homogeneous_zero product R hR w hw];simp
  | succ k ih=>
    have he:=homogeneous_local_error product R sigma hR hs1 hnondegenerate hproduct w hw k
    have hg:=homogeneous_growth product R sigma M hR hs0 hs1 hM hB hnondegenerate hproduct w hw k
    have hn:=norm_add_le (homogeneous R product w (k+1)-B (homogeneous R product w k))
      (B (homogeneous R product w k-(B.toLinearMap^k) w))
    have hid : homogeneous R product w (k+1)-B (homogeneous R product w k)+
        B (homogeneous R product w k-(B.toLinearMap^k) w)=
        homogeneous R product w (k+1)-(B.toLinearMap^(k+1)) w := by
      rw [pow_succ',Module.End.mul_apply,map_sub]
      abel
    rw [hid] at hn
    have hb:=hB (homogeneous R product w k-(B.toLinearMap^k) w)
    have h1:=mul_le_mul_of_nonneg_left ih hM
    have hb2:=hB (homogeneous R product w k)
    have h2:=mul_le_mul_of_nonneg_left hg hM
    have h3:=mul_le_mul_of_nonneg_left hb2 hs0
    have h4:=mul_le_mul_of_nonneg_left h2 hs0
    rw [pow_succ (1+sigma),pow_succ M]
    nlinarith

lemma perturbationFactor_bound (sigma : ℝ) (hs : 0 ≤ sigma) (k : ℕ)
    (hsmall : (k:ℝ)*sigma ≤ 1/2) : (1+sigma)^k-1 ≤ 2*(k:ℝ)*sigma := by
  have hx : 0 ≤ (k:ℝ)*sigma := by positivity
  have hh:=pow_le_pow_left₀ (show 0 ≤ 1+sigma by positivity) (by simpa only [add_comm] using Real.add_one_le_exp sigma) k
  rw [←Real.exp_nat_mul] at hh
  have he:=Real.exp_bound_div_one_sub_of_interval hx (by linarith : (k:ℝ)*sigma<1)
  have hden : 0 < 1-(k:ℝ)*sigma := by linarith
  have hu : 1/(1-(k:ℝ)*sigma) ≤ 1+2*(k:ℝ)*sigma := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  nlinarith

end
end PaperHeavyBallPower

end SnapshotModule_104
/- END heavy_ball_power_error -/

/- BEGIN heavy_ball_power_horizon -/
section SnapshotModule_105

namespace PaperHeavyBallPowerHorizon
open PaperHeavyBallPower PaperHeavyBallPowerSpectral
open scoped RealInnerProductSpace
noncomputable section

def iterations (S q : ℝ) : ℕ := ⌊Real.log (8*S/q^2)/(-Real.log (49/64:ℝ))⌋₊+1

def sigma (S q : ℝ) : ℝ := q/(1024*(iterations S q:ℝ)*Real.sqrt S)

lemma iterations_pos (S q : ℝ) : 0 < iterations S q := by unfold iterations;omega

lemma iterations_precision (S q : ℝ) (hS : 0 < S) (hq : 0 < q) :
    (7/8:ℝ)^(2*iterations S q)*S/q^2 < (1/8:ℝ) := by
  have hh:=PaperVolumeBudget.public_horizon 1 (49/64:ℝ) S (q^2/8)
    (by norm_num) (by norm_num) hS (by positivity)
  simp only [Nat.cast_one,one_mul,pow_one] at hh
  have hratio : S/(q^2/8)=8*S/q^2 := by ring
  rw [hratio] at hh
  have hp : (7/8:ℝ)^(2*iterations S q)=(49/64:ℝ)^(iterations S q) := by
    rw [pow_mul]
    norm_num
  rw [hp]
  apply (div_lt_iff₀ (sq_pos_of_pos hq)).mpr
  simpa only [iterations,div_eq_mul_inv,mul_comm,one_mul] using hh

lemma sigma_bounds (S q : ℝ) (hS : 0 < S) (hq : 0 < q) (hqs : q ≤ Real.sqrt S) :
    0 < sigma S q ∧ sigma S q ≤ 1/1024 ∧ (iterations S q:ℝ)*sigma S q ≤ 1/1024 := by
  have hk : 1 ≤ (iterations S q:ℝ) := by exact_mod_cast iterations_pos S q
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hsig : 0 < sigma S q := by dsimp [sigma];positivity
  have hks : (iterations S q:ℝ)*sigma S q=q/(1024*Real.sqrt S) := by
    dsimp [sigma]
    field_simp
  have hh : q/(1024*Real.sqrt S) ≤ 1/1024 := by
    apply (div_le_iff₀ (by positivity : 0 < 1024*Real.sqrt S)).mpr
    linarith
  refine ⟨hsig,?_,by rw [hks];exact hh⟩
  have hm:=mul_le_mul_of_nonneg_right hk hsig.le
  rw [hks] at hm
  linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Public logarithmic iteration count makes the true power direction good;
this theorem invokes the actual eigenbasis power estimate. -/
lemma exact_rayleigh_public {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (B : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i)
    (M S q : ℝ) (hM : 0 < M) (hS : 0 < S) (hq : 0 < q)
    (hlambda : ∀i,0 ≤ lambda i ∧ lambda i ≤ M)
    (top : ι) (htop : lambda top=M) (w : V) (hwn : ‖w‖^2 ≤ S)
    (hwt : q ≤ |basis.repr w top|) :
    (M^(iterations S q)*q) ≤ ‖(B^(iterations S q)) w‖ ∧
    (3/4:ℝ)*M ≤ rayleigh B ((B^(iterations S q)) w) := by
  have hh:=exact_power_rayleigh basis B lambda heigen M (1/8) S q hM (by norm_num) (by norm_num)
    hS.le hq hlambda top htop w hwn hwt (iterations S q)
  have hp:=iterations_precision S q hS hq
  have hm:=mul_lt_mul_of_pos_left hp hM
  refine ⟨hh.1,?_⟩
  norm_num only [one_div,sub_eq_add_neg] at hh
  have he : M*(1/8:ℝ)=M/8 := by ring
  have hm2 : M*(7/8:ℝ)^(2*iterations S q)*S/q^2<M/8 := by
    convert hm using 1 <;> first | rfl | ring
  linarith [hh.2]

/-- The actual normalized inexact power run stays within relative 1/512 of
the true power at the same public horizon. -/
lemma inexact_vector_public {B : V→L[ℝ] V} (product : V→V)
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    (M R S q : ℝ) (hM : 0 < M) (hR : 0 < R) (hS : 0 < S) (hq : 0 < q) (hqs : q ≤ Real.sqrt S)
    (hB : ∀v,‖B v‖ ≤ M*‖v‖) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖ ≤ sigma S q*‖B v‖)
    (w : V) (hw : w≠0) (hwn : ‖w‖ ≤ Real.sqrt S)
    (htop : M^(iterations S q)*q ≤ ‖(B.toLinearMap^(iterations S q)) w‖) :
    ‖homogeneous R product w (iterations S q)-(B.toLinearMap^(iterations S q)) w‖ ≤ 
      (1/512:ℝ)*‖(B.toLinearMap^(iterations S q)) w‖ := by
  have hs:=sigma_bounds S q hS hq hqs
  have hsig : 0 < sigma S q := hs.1
  have hd:=homogeneous_deviation product R (sigma S q) M hR hs.1.le (by linarith [hs.2.1]) hM.le
    hB hnondegenerate hproduct w hw (iterations S q)
  have hfac:=perturbationFactor_bound (sigma S q) hs.1.le (iterations S q) (by linarith [hs.2.2])
  have hfac2:=mul_le_mul_of_nonneg_right hfac (show 0 ≤ M^(iterations S q)*‖w‖ by positivity)
  have hwn2:=mul_le_mul_of_nonneg_left hwn (show 0 ≤ 2*(iterations S q:ℝ)*sigma S q*M^(iterations S q) by positivity)
  have hcancel : 2*(iterations S q:ℝ)*sigma S q*Real.sqrt S=q/512 := by
    dsimp [sigma]
    have hk : (iterations S q:ℝ)≠0 := by exact_mod_cast (iterations_pos S q).ne'
    have hsqrt : Real.sqrt S≠0 := (Real.sqrt_pos.mpr hS).ne'
    field_simp
    <;> ring
  have he : 2*(iterations S q:ℝ)*sigma S q*M^(iterations S q)*Real.sqrt S=
      (1/512:ℝ)*(M^(iterations S q)*q) := by
    have hh:=congrArg (fun t : ℝ=>M^(iterations S q)*t) hcancel
    convert hh using 1 <;> ring
  rw [he] at hwn2
  have ht:=mul_le_mul_of_nonneg_left htop (by norm_num : (0:ℝ) ≤ 1/512)
  nlinarith

end
end PaperHeavyBallPowerHorizon

end SnapshotModule_105
/- END heavy_ball_power_horizon -/

/- BEGIN heavy_ball_rayleigh -/
section SnapshotModule_106

namespace PaperHeavyBallRayleigh
open PaperHeavyBallPowerSpectral
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma energy_perturbation (B : Module.End ℝ V) (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀x,‖B x‖ ≤ M*‖x‖) (y z : V) :
    |inner ℝ y (B y)-inner ℝ z (B z)| ≤ M*‖y-z‖*(‖y‖+‖z‖) := by
  have he : inner ℝ y (B y)-inner ℝ z (B z)=inner ℝ (y-z) (B y)+inner ℝ z (B (y-z)) := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [he]
  have h1:=(abs_real_inner_le_norm (y-z) (B y)).trans
    (mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _))
  have h2:=(abs_real_inner_le_norm z (B (y-z))).trans
    (mul_le_mul_of_nonneg_left (hB (y-z)) (norm_nonneg _))
  have hh:=abs_add_le (inner ℝ (y-z) (B y)) (inner ℝ z (B (y-z)))
  nlinarith

/-- Rayleigh estimation remains accurate under a small relative vector error;
all normalization denominators are proved nonzero. -/
lemma perturbed_rayleigh_lower (B : Module.End ℝ V) (M : ℝ) (hM : 0 < M)
    (hB : ∀x,‖B x‖ ≤ M*‖x‖) (y z : V) (hz : z≠0)
    (hclose : ‖y-z‖ ≤ (1/64:ℝ)*‖z‖)
    (hRay : (3/4:ℝ)*M ≤ rayleigh B z) :
    y≠0 ∧ (5/8:ℝ)*M ≤ rayleigh B y := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzn2 : 0 < ‖z‖^2 := by positivity
  have hyup : ‖y‖ ≤ (65/64:ℝ)*‖z‖ := by
    have hn:=norm_add_le (y-z) z
    have he : y-z+z=y := by abel
    rw [he] at hn
    linarith
  have hyn : 0 < ‖y‖ := by
    have hn:=norm_sub_norm_le y z
    have hh:=norm_sub_norm_le z y
    rw [norm_sub_rev z y] at hh
    linarith
  have hy : y≠0 := norm_pos_iff.mp hyn
  have henergy : (3/4:ℝ)*M*‖z‖^2 ≤ inner ℝ z (B z) := (le_div_iff₀ hzn2).mp hRay
  have hdiff:=energy_perturbation B M hM.le hB y z
  have hprod:=mul_le_mul_of_nonneg_left hclose hM.le
  have hsum : ‖y‖+‖z‖ ≤ (129/64:ℝ)*‖z‖ := by linarith
  have hprod2:=mul_le_mul hprod hsum (by positivity : 0 ≤ ‖y‖+‖z‖) (by positivity : 0 ≤ M*((1/64:ℝ)*‖z‖))
  have hsq : ‖y‖^2 ≤ (65/64:ℝ)^2*‖z‖^2 := by nlinarith [sq_nonneg ((65/64:ℝ)*‖z‖-‖y‖)]
  have hMnorm : 0 < M*‖z‖^2 := by positivity
  have hlower:= (abs_le.mp hdiff).1
  have hmul:=mul_le_mul_of_nonneg_left hsq (show 0 ≤ (5/8:ℝ)*M by positivity)
  refine ⟨hy,?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos hyn)).mpr
  nlinarith

lemma rayleigh_upper (B : Module.End ℝ V) (M : ℝ) (hB : ∀x,‖B x‖ ≤ M*‖x‖)
    (y : V) (hy : y≠0) : rayleigh B y ≤ M := by
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  apply (div_le_iff₀ (sq_pos_of_pos hypos)).mpr
  have hh:=(real_inner_le_norm y (B y)).trans (mul_le_mul_of_nonneg_left (hB y) hypos.le)
  nlinarith

lemma rayleigh_smul (B : Module.End ℝ V) (a : ℝ) (ha : a≠0) (v : V) :
    rayleigh B (a •v)=rayleigh B v := by
  simp only [rayleigh,map_smul,real_inner_smul_left,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  field_simp
  <;> ring

/-- One final inexact product on a vector of norm R gives the scale estimate
Mstar/2  ≤  rhohat  ≤  2 Mstar used by the heavy-ball parameters. -/
lemma estimate_bounds (B : Module.End ℝ V) (product : V→V) (M R sigma : ℝ)
    (hM : 0 < M) (hR : 0 < R) (hs0 : 0 ≤ sigma) (hs1 : sigma ≤ 1/8)
    (hB : ∀x,‖B x‖ ≤ M*‖x‖) (v : V) (hv : ‖v‖=R)
    (hproduct : ‖product v-B v‖ ≤ sigma*‖B v‖) (hRay : (5/8:ℝ)*M ≤ rayleigh B v) :
    M/2 ≤ inner ℝ v (product v)/R^2 ∧ inner ℝ v (product v)/R^2 ≤ 2*M := by
  have hvpos : 0 < ‖v‖ := by rw [hv];exact hR
  have hdiff : |inner ℝ v (product v)-inner ℝ v (B v)| ≤ sigma*M*R^2 := by
    rw [←inner_sub_right]
    have hh:=(abs_real_inner_le_norm v (product v-B v)).trans
      (mul_le_mul_of_nonneg_left hproduct (norm_nonneg v))
    have hb:=mul_le_mul_of_nonneg_left (hB v) (show 0 ≤ ‖v‖*sigma by positivity)
    rw [hv] at hh hb
    nlinarith
  have hupper:=rayleigh_upper B M hB v (norm_pos_iff.mp hvpos)
  dsimp [rayleigh] at hRay hupper
  rw [hv] at hRay hupper
  have hr2 : 0 < R^2 := by positivity
  have hlo:=(le_div_iff₀ hr2).mp hRay
  have hup:=(div_le_iff₀ hr2).mp hupper
  rcases abs_le.mp hdiff with ⟨hdlo,hdup⟩
  have hsm:=mul_le_mul_of_nonneg_right hs1 (show 0 ≤ M*R^2 by positivity)
  constructor
  · apply (le_div_iff₀ hr2).mpr
    nlinarith
  · apply (div_le_iff₀ hr2).mpr
    nlinarith

end
end PaperHeavyBallRayleigh

end SnapshotModule_106
/- END heavy_ball_rayleigh -/

/- BEGIN heavy_ball_power_complete -/
section SnapshotModule_107

namespace PaperHeavyBallPowerComplete
open PaperHeavyBallPower PaperHeavyBallPowerHorizon PaperHeavyBallPowerSpectral PaperHeavyBallRayleigh
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def estimateProgram {Q Reply : Type*} (product : V→PaperOracle.Program Q Reply V)
    (R : ℝ) (k : ℕ) (w : V) : PaperOracle.Program Q Reply ℝ :=
  PaperOracle.Program.bind (powerProgram product R k (R •NormedSpace.normalize w)) (fun v=>
    PaperOracle.Program.bind (product v) (fun image=>.done (inner ℝ v image/R^2)))

lemma estimateProgram_cap {Q Reply : Type*} (product : V→PaperOracle.Program Q Reply V)
    (R : ℝ) (budget : ℕ) (hbudget : ∀v,PaperOracle.Program.Cap budget (product v)) (k : ℕ) (w : V) :
    PaperOracle.Program.Cap ((k+1)*budget) (estimateProgram product R k w) := by
  have hsecond : ∀v,PaperOracle.Program.Cap budget
      (PaperOracle.Program.bind (product v) (fun image=>.done (inner ℝ v image/R^2))) := by
    intro v
    have hh:=PaperOracle.Program.cap_bind (product v) (fun image=>PaperOracle.Program.done (inner ℝ v image/R^2)) (hbudget v) (b:=0) (by intro image;trivial)
    simpa only [Nat.add_zero] using hh
  unfold estimateProgram
  rw [show (k+1)*budget=k*budget+budget by ring]
  exact PaperOracle.Program.cap_bind _ _ (powerProgram_cap product R budget hbudget k _) hsecond

/-- Full finite normalized power-and-Rayleigh estimator, with no exact-power,
perturbation, normalization, or Rayleigh accuracy result as a premise. -/
theorem estimateProgram_correct {Q Reply : Type*} [FiniteDimensional ℝ V]
    (C : Q→Reply) (product : V→PaperOracle.Program Q Reply V)
    (B : V→L[ℝ] V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i)
    (M R S q : ℝ) (hM : 0 < M) (hR : 0 < R) (hS : 0 < S) (hq : 0 < q)
    (hlambda : ∀i,0 ≤ lambda i ∧ lambda i ≤ M)
    (hB : ∀v,‖B v‖ ≤ M*‖v‖) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖PaperOracle.Program.run C (product v)-B v‖ ≤ sigma S q*‖B v‖)
    (top : ι) (htop : lambda top=M) (w : V) (hwn : ‖w‖^2 ≤ S)
    (hwt : q ≤ |basis.repr w top|) :
    M/2 ≤ PaperOracle.Program.run C (estimateProgram product R (iterations S q) w) ∧
    PaperOracle.Program.run C (estimateProgram product R (iterations S q) w) ≤ 2*M := by
  let p : V→V:=fun x=>PaperOracle.Program.run C (product x)
  let K:=iterations S q
  let v:=normalizedIterate R p w K
  let y:=homogeneous R p w K
  let z:=(B.toLinearMap^K) w
  have hw : w≠0 := by
    intro hz
    have hh : q≤0 := by simpa [hz] using hwt
    linarith
  have hwnorm : ‖w‖ ≤ Real.sqrt S := Real.le_sqrt_of_sq_le hwn
  have hcoord : |basis.repr w top| ≤ ‖w‖ := by
    rw [basis.repr_apply_apply]
    simpa only [basis.orthonormal.norm_eq_one,one_mul] using abs_real_inner_le_norm (basis top) w
  have hqs : q ≤ Real.sqrt S := hwt.trans (hcoord.trans hwnorm)
  have hs:=sigma_bounds S q hS hq hqs
  have hs1 : sigma S q<1 := by linarith [hs.2.1]
  have hv : ‖v‖=R := iterate_norm p R (sigma S q) hR hs1 hnondegenerate hproduct w hw K
  have hexact:=exact_rayleigh_public basis B.toLinearMap lambda heigen M S q hM hS hq hlambda top htop w hwn hwt
  have hclose:=inexact_vector_public p (stdOrthonormalBasis ℝ V) M R S q hM hR hS hq hqs hB hnondegenerate hproduct
    w hw hwnorm hexact.1
  have hz : z≠0 := by
    have hp: 0 < ‖z‖ := (mul_pos (pow_pos hM K) hq).trans_le hexact.1
    exact norm_pos_iff.mp hp
  have hclose2 : ‖y-z‖ ≤ (1/64:ℝ)*‖z‖ := hclose.trans (by nlinarith [norm_nonneg z])
  have hyray:= (perturbed_rayleigh_lower B.toLinearMap M hM hB y z hz hclose2 hexact.2).2
  have hscale : scale R p w K≠0 := (scale_pos p R (sigma S q) hR hs1 hnondegenerate hproduct w hw K).ne'
  have hRay : (5/8:ℝ)*M ≤ rayleigh B.toLinearMap v := by
    dsimp [y,homogeneous] at hyray
    rw [rayleigh_smul B.toLinearMap _ hscale] at hyray
    exact hyray
  have hestimate:=estimate_bounds B.toLinearMap p M R (sigma S q) hM hR hs.1.le (by linarith [hs.2.1]) hB v hv
    (hproduct v hv) hRay
  have hnonzero : ∀v,‖v‖=R→p v≠0 := by
    intro v hv
    have hvne : v≠0 := by intro hz;rw [hz,norm_zero] at hv;linarith
    exact relative_product_ne_zero B p (sigma S q) hs1 v (hnondegenerate v hvne) (hproduct v hv)
  have hinit : ‖R •NormedSpace.normalize w‖=R := by simp [norm_smul,Real.norm_eq_abs,abs_of_pos hR,NormedSpace.norm_normalize hw]
  have hvalue : PaperOracle.Program.run C (powerProgram product R K (R •NormedSpace.normalize w))=v := by
    rw [powerProgram_eval C product R hR hnonzero K _ hinit]
    exact (normalizedIterate_eq_iterate R p w K).symm
  simp only [estimateProgram,PaperOracle.Program.run_bind,PaperOracle.Program.run]
  rw [hvalue]
  exact hestimate

end
end PaperHeavyBallPowerComplete

end SnapshotModule_107
/- END heavy_ball_power_complete -/

/- BEGIN heavy_ball_kernel -/
section SnapshotModule_108

namespace PaperHeavyBallKernel
open Polynomial Polynomial.Chebyshev
open scoped RealInnerProductSpace
noncomputable section

def kernelPolynomial (theta : ℝ) (k : ℕ) : Polynomial ℝ := C (theta^k)*U ℝ (k:ℤ)

lemma kernelPolynomial_zero (theta : ℝ) : kernelPolynomial theta 0=1 := by simp [kernelPolynomial]
lemma kernelPolynomial_one (theta : ℝ) : kernelPolynomial theta 1=C (2*theta)*X := by
  simp only [kernelPolynomial,pow_one,Nat.cast_one,U_one,map_mul,map_ofNat]
  ring

lemma kernelPolynomial_recurrence (theta : ℝ) (k : ℕ) :
    kernelPolynomial theta (k+2)=C (2*theta)*X*kernelPolynomial theta (k+1)-C (theta^2)*kernelPolynomial theta k := by
  simp only [kernelPolynomial,Nat.cast_add,Nat.cast_ofNat,U_add_two,pow_succ,map_mul,map_ofNat]
  ring_nf
  simp only [Polynomial.C_1,mul_one]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def kernel (S : Module.End ℝ V) (theta : ℝ) (k : ℕ) : Module.End ℝ V :=
  aeval S (kernelPolynomial theta k)

lemma kernel_zero (S : Module.End ℝ V) (theta : ℝ) : kernel S theta 0=1 := by
  simp [kernel,kernelPolynomial_zero]

lemma kernel_one (S : Module.End ℝ V) (theta : ℝ) : kernel S theta 1=(2*theta) •S := by
  rw [kernel,kernelPolynomial_one,map_mul,Polynomial.aeval_C,aeval_X]
  rw [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]

lemma kernel_recurrence (S : Module.End ℝ V) (theta : ℝ) (k : ℕ) :
    kernel S theta (k+2)=(2*theta) •(S*kernel S theta (k+1))-theta^2 •kernel S theta k := by
  simp only [kernel,kernelPolynomial_recurrence,map_sub,map_mul,Polynomial.aeval_C,aeval_X]
  simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,smul_smul]

lemma kernel_apply_recurrence (S : Module.End ℝ V) (theta : ℝ) (k : ℕ) (x : V) :
    kernel S theta (k+2) x=(2*theta) •S (kernel S theta (k+1) x)-theta^2 •kernel S theta k x := by
  rw [kernel_recurrence]
  rfl

/-- Actual operator kernel estimate obtained from the orthonormal eigenbasis
and the scalar U bound, including the repeated-root endpoints. -/
lemma kernel_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (S : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,S (basis i)=lambda i •basis i) (hlambda : ∀i,|lambda i|≤1)
    (theta : ℝ) (htheta : 0≤theta) (k : ℕ) (x : V) :
    ‖kernel S theta k x‖≤((k:ℝ)+1)*theta^k*‖x‖ := by
  apply PaperHeavyBallChebyshev.polynomial_norm_bound basis S lambda heigen
    (kernelPolynomial theta k) (((k:ℝ)+1)*theta^k) (by positivity)
  intro i
  simp only [kernelPolynomial,eval_mul,eval_C,abs_mul,abs_of_nonneg (pow_nonneg htheta k)]
  have hh := PaperHeavyBallChebyshev.abs_U_eval_le k (lambda i) (hlambda i)
  exact (mul_le_mul_of_nonneg_left hh (pow_nonneg htheta k)).trans_eq (by ring)

end
end PaperHeavyBallKernel

end SnapshotModule_108
/- END heavy_ball_kernel -/

/- BEGIN heavy_ball_dynamics -/
section SnapshotModule_109

namespace PaperHeavyBallDynamics
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def transition (S : Module.End ℝ V) (theta : ℝ) : Module.End ℝ (V×V) where
  toFun p := (p.2,(2*theta) •S p.2-theta^2 •p.1)
  map_add' p q := by ext <;> simp [map_add,smul_add,sub_add_sub_comm]
  map_smul' r p := by ext <;> simp [map_smul,smul_sub,smul_smul]; ring

lemma transition_apply (S : Module.End ℝ V) (theta : ℝ) (p : V×V) :
    transition S theta p=(p.2,(2*theta) •S p.2-theta^2 •p.1) := rfl

lemma transition_pow_two (S : Module.End ℝ V) (theta : ℝ) (p : V×V) :
    (transition S theta^2) p=
      (PaperHeavyBallKernel.kernel S theta 1 p.2-theta^2 •PaperHeavyBallKernel.kernel S theta 0 p.1,
       PaperHeavyBallKernel.kernel S theta 2 p.2-theta^2 •PaperHeavyBallKernel.kernel S theta 1 p.1) := by
  rw [PaperHeavyBallKernel.kernel_apply_recurrence S theta 0 p.2]
  simp only [Nat.zero_add,PaperHeavyBallKernel.kernel_zero,PaperHeavyBallKernel.kernel_one,
    Module.End.one_apply,LinearMap.smul_apply,pow_two,Module.End.mul_apply]
  rw [transition_apply,transition_apply]
  ext <;> simp only [map_sub,map_smul,smul_sub,smul_smul] <;> module

/-- Exact powers of the actual two-state heavy-ball transition. -/
lemma transition_pow_formula (S : Module.End ℝ V) (theta : ℝ) (k : ℕ) (p : V×V) :
    (transition S theta^(k+2)) p=
      (PaperHeavyBallKernel.kernel S theta (k+1) p.2-theta^2 •PaperHeavyBallKernel.kernel S theta k p.1,
       PaperHeavyBallKernel.kernel S theta (k+2) p.2-theta^2 •PaperHeavyBallKernel.kernel S theta (k+1) p.1) := by
  induction k with
  | zero=>exact transition_pow_two S theta p
  | succ k ih=>
    rw [show k+1+2=(k+2)+1 by omega,pow_succ',Module.End.mul_apply,ih]
    rw [transition_apply]
    apply Prod.ext
    · rfl
    · change (2*theta) •S (_-_) - theta^2 •(_-_) = _
      simp only [map_sub,map_smul,smul_sub,smul_smul]
      rw [PaperHeavyBallKernel.kernel_apply_recurrence S theta (k+1) p.2,
        PaperHeavyBallKernel.kernel_apply_recurrence S theta k p.1]
      simp only [show k+1+1=k+2 by omega,map_sub,map_smul,smul_sub,smul_smul]
      module

/-- First-order forced state recurrence, executed literally for a public horizon. -/
def forcedTrajectory {W : Type*} [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ W) (initial : W) (noise : ℕ→W) : ℕ→W
  | 0=>initial
  | k+1=>T (forcedTrajectory T initial noise k)+noise k

lemma forcedTrajectory_formula {W : Type*} [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ W) (initial : W) (noise : ℕ→W) (k : ℕ) :
    forcedTrajectory T initial noise k=(T^k) initial+
      ∑i∈Finset.range k,(T^(k-1-i)) (noise i) := by
  induction k with
  | zero=>simp [forcedTrajectory]
  | succ k ih=>
    rw [forcedTrajectory,ih,map_add,map_sum,Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel,Nat.sub_self,pow_zero,Module.End.one_apply]
    rw [←add_assoc,pow_succ',Module.End.mul_apply]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Module.End.mul_apply,←pow_succ']
    have he : k-1-i+1=k-i := by have hii:=Finset.mem_range.mp hi; omega
    rw [he]

end
end PaperHeavyBallDynamics

end SnapshotModule_109
/- END heavy_ball_dynamics -/

/- BEGIN heavy_ball_decay -/
section SnapshotModule_110

namespace PaperHeavyBallDecay
noncomputable section

lemma weighted_geometric_identity (theta : ℝ) (n : ℕ) :
    (1-theta)^2*(∑j∈Finset.range n,((j:ℝ)+1)*theta^j)=
      1-((n:ℝ)+1)*theta^n+(n:ℝ)*theta^(n+1) := by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [Finset.sum_range_succ]
    push_cast
    rw [pow_succ theta (n+1),pow_succ theta n] at *
    linear_combination ih

lemma weighted_geometric_bound (theta : ℝ) (ht : 0≤theta) (ht1 : theta<1) (n : ℕ) :
    (∑j∈Finset.range n,((j:ℝ)+1)*theta^j)≤1/(1-theta)^2 := by
  have he:=weighted_geometric_identity theta n
  have hp : 0≤theta^n*(1+(n:ℝ)*(1-theta)) := by positivity
  rw [pow_succ theta n] at he
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0<1-theta))).mpr
  nlinarith

lemma geometric_sum_bound (theta : ℝ) (ht : 0≤theta) (ht1 : theta<1) (n : ℕ) :
    (∑j∈Finset.range n,theta^j)≤1/(1-theta) := by
  have he:=geom_sum_mul_neg theta n
  apply (le_div_iff₀ (by linarith : 0<1-theta)).mpr
  nlinarith [pow_nonneg ht n]

lemma homogeneous_public_bound (theta : ℝ) (ht : 0≤theta) (ht1 : theta<1) (k : ℕ) :
    ((k:ℝ)+1)*theta^k≤1/(1-theta) := by
  have hh : ((k:ℝ)+1)*theta^k≤∑j∈Finset.range (k+1),theta^j := by
    calc
      _=∑ _j∈Finset.range (k+1),theta^k := by simp
      _≤_ := Finset.sum_le_sum (fun j hj=>pow_le_pow_of_le_one ht ht1.le (by have hjj:=Finset.mem_range.mp hj; omega))
  exact hh.trans (geometric_sum_bound theta ht ht1 (k+1))

lemma theta_exp_bound (theta : ℝ) : theta≤Real.exp (-(1-theta)) := by
  have hh:=Real.add_one_le_exp (theta-1)
  convert hh using 1 <;> ring

lemma homogeneous_exponential_bound (theta : ℝ) (ht : 0≤theta) (ht1 : theta<1) (k : ℕ) :
    ((k:ℝ)+1)*theta^k≤(3/(1-theta))*Real.exp (-(1-theta)*(k:ℝ)/2) := by
  let t:=1-theta
  have hp : 0<t := by dsimp [t];linarith
  have hp1 : t≤1 := by dsimp [t];linarith
  have he1 : 1≤Real.exp (t*(k:ℝ)/2) := Real.one_le_exp_iff.mpr (by positivity)
  have he:=Real.add_one_le_exp (t*(k:ℝ)/2)
  have hfactor : (k:ℝ)+1≤(3/t)*Real.exp (t*(k:ℝ)/2) := by
    have hh : ((k:ℝ)+1)*t≤3*Real.exp (t*(k:ℝ)/2) := by nlinarith
    calc
      _=(((k:ℝ)+1)*t)/t := by field_simp
      _≤(3*Real.exp (t*(k:ℝ)/2))/t := div_le_div_of_nonneg_right hh hp.le
      _=(3/t)*Real.exp (t*(k:ℝ)/2) := by ring
  have hpow : theta^k≤Real.exp (-t*(k:ℝ)) := by
    have hh:=pow_le_pow_left₀ ht (theta_exp_bound theta) k
    rw [←Real.exp_nat_mul] at hh
    convert hh using 1 <;> first | rfl | (dsimp only [t]; ring)
  have hh:=mul_le_mul hfactor hpow (pow_nonneg ht k) (by positivity : 0≤(3/t)*Real.exp (t*(k:ℝ)/2))
  have heq : ((3/t)*Real.exp (t*(k:ℝ)/2))*Real.exp (-t*(k:ℝ))=
      (3/t)*Real.exp (-t*(k:ℝ)/2) := by
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  exact hh.trans_eq heq

def publicHorizon (theta R delta : ℝ) : ℕ :=
  ⌈(2/(1-theta))*Real.log (24*R/((1-theta)*delta))⌉₊

lemma publicHorizon_precision (theta R delta : ℝ) (ht : 0≤theta) (ht1 : theta<1)
    (hR : 0<R) (hd : 0<delta) :
    4*(((publicHorizon theta R delta:ℕ):ℝ)+1)*theta^(publicHorizon theta R delta)*R≤delta/2 := by
  have htpos : 0<1-theta := by linarith
  have hratio : 0<24*R/((1-theta)*delta) := by positivity
  have hceil : (2/(1-theta))*Real.log (24*R/((1-theta)*delta))≤(publicHorizon theta R delta:ℝ) := Nat.le_ceil _
  have hexp : Real.exp (-(1-theta)*(publicHorizon theta R delta:ℝ)/2)≤((1-theta)*delta)/(24*R) := by
    have hh:=mul_le_mul_of_nonneg_left hceil (show 0≤(1-theta)/2 by positivity)
    have hc : ((1-theta)/2)*((2/(1-theta))*Real.log (24*R/((1-theta)*delta)))=
      Real.log (24*R/((1-theta)*delta)) := by field_simp
    rw [hc] at hh
    have he:=Real.exp_le_exp.mpr (neg_le_neg hh)
    have heq : -((1-theta)/2*(publicHorizon theta R delta:ℝ))=
      -(1-theta)*(publicHorizon theta R delta:ℝ)/2 := by ring
    rw [heq,Real.exp_neg,Real.exp_log hratio,inv_div] at he
    exact he
  have hb:=homogeneous_exponential_bound theta ht ht1 (publicHorizon theta R delta)
  have hh:=mul_le_mul_of_nonneg_right hb (show 0≤4*R by positivity)
  have hfinal:=mul_le_mul_of_nonneg_left hexp (show 0≤12*R/(1-theta) by positivity)
  have hc : (12*R/(1-theta))*(((1-theta)*delta)/(24*R))=delta/2 := by field_simp <;> norm_num
  rw [hc] at hfinal
  have heq : (3/(1-theta))*Real.exp (-(1-theta)*(publicHorizon theta R delta:ℝ)/2)*(4*R)=
      (12*R/(1-theta))*Real.exp (-(1-theta)*(publicHorizon theta R delta:ℝ)/2) := by ring
  rw [heq] at hh
  convert hh.trans hfinal using 1 <;> first | rfl | ring

end
end PaperHeavyBallDecay

end SnapshotModule_110
/- END heavy_ball_decay -/

/- BEGIN heavy_ball_stability -/
section SnapshotModule_111

namespace PaperHeavyBallStability
open PaperHeavyBallKernel PaperHeavyBallDynamics
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma pair_coefficient_bounds (a theta : ℝ) (ha : 0 ≤ a) (ht : (1/3:ℝ) ≤ theta) (ht1 : theta ≤ 1) :
    (a+2)*theta+(a+1)*theta^2 ≤ 4*(a+3)*theta^2 ∧
    (a+3)*theta^2+(a+2)*theta^3 ≤ 4*(a+3)*theta^2 := by
  have ht0 : 0 ≤ theta := by linarith
  have hh : theta ≤ 3*theta^2 := by nlinarith
  have hh1:=mul_le_mul_of_nonneg_left hh (show 0 ≤ a+2 by linarith)
  have hh2 : theta^3 ≤ theta^2 := by
    have h:=mul_le_mul_of_nonneg_right ht1 (sq_nonneg theta)
    nlinarith
  have hh3:=mul_le_mul_of_nonneg_left hh2 (show 0 ≤ a+2 by linarith)
  constructor <;> nlinarith

/-- Dimension-free norm bound on actual powers of the two-state transition,
proved from exact power formula and eigenbasis Chebyshev kernels. -/
theorem transition_pow_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (S : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,S (basis i)=lambda i •basis i) (hlambda : ∀i,|lambda i| ≤ 1)
    (theta : ℝ) (ht : (1/3:ℝ) ≤ theta) (ht1 : theta ≤ 1) (k : ℕ) (p : V×V) :
    ‖(transition S theta^k) p‖ ≤ 4*((k:ℝ)+1)*theta^k*‖p‖ := by
  have ht0 : 0 ≤ theta := by linarith
  have hp0:=norm_nonneg p
  have hp1:=norm_fst_le p
  have hp2:=norm_snd_le p
  cases k with
  | zero=>simp only [pow_zero,Module.End.one_apply,Nat.cast_zero,zero_add,one_mul,mul_one];nlinarith
  | succ k=>
    cases k with
    | zero=>
      rw [pow_one,transition_apply]
      apply norm_prod_le_iff.mpr
      constructor
      · norm_num only [Nat.cast_one,pow_one]
        nlinarith
      · have hk:=kernel_norm_bound basis S lambda heigen hlambda theta ht0 1 p.2
        rw [kernel_one] at hk
        norm_num only [LinearMap.smul_apply,Nat.cast_one,pow_one] at hk
        have hn: ‖(2*theta) •S p.2-theta^2 •p.1‖ ≤ 2*theta*‖p.2‖+theta^2*‖p.1‖ := by
          exact (norm_sub_le _ _).trans (add_le_add hk (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg theta)]))
        have h1:=mul_le_mul_of_nonneg_left hp1 (sq_nonneg theta)
        have h2:=mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 2*theta by positivity)
        have hsq : theta^2 ≤ theta := sq_le ht0 ht1
        have h3:=mul_le_mul_of_nonneg_right hsq hp0
        norm_num only [Nat.cast_one,pow_one]
        nlinarith
    | succ j=>
      rw [transition_pow_formula]
      apply norm_prod_le_iff.mpr
      have hK1:=kernel_norm_bound basis S lambda heigen hlambda theta ht0 (j+1) p.2
      have hK0:=kernel_norm_bound basis S lambda heigen hlambda theta ht0 j p.1
      have hK2:=kernel_norm_bound basis S lambda heigen hlambda theta ht0 (j+2) p.2
      have hK1s:=kernel_norm_bound basis S lambda heigen hlambda theta ht0 (j+1) p.1
      have hprevious : ‖kernel S theta (j+1) p.2-theta^2 •kernel S theta j p.1‖ ≤ 
          (((j:ℝ)+2)*theta+((j:ℝ)+1)*theta^2)*theta^j*‖p‖ := by
        have hn: ‖kernel S theta (j+1) p.2-theta^2 •kernel S theta j p.1‖ ≤ 
          ‖kernel S theta (j+1) p.2‖+theta^2*‖kernel S theta j p.1‖ := by
          have hn:=norm_sub_le (kernel S theta (j+1) p.2) (theta^2 •kernel S theta j p.1)
          rw [norm_smul,Real.norm_eq_abs] at hn
          rw [abs_of_nonneg (sq_nonneg theta)] at hn
          exact hn
        have h0:=mul_le_mul_of_nonneg_left hK0 (sq_nonneg theta)
        have h1:=mul_le_mul_of_nonneg_left hp1 (show 0 ≤ theta^2*(((j:ℝ)+1)*theta^j) by positivity)
        have h2:=mul_le_mul_of_nonneg_left hp2 (show 0 ≤ (((j+1:ℕ):ℝ)+1)*theta^(j+1) by positivity)
        push_cast at *
        rw [pow_succ theta j] at *
        nlinarith
      have hcurrent : ‖kernel S theta (j+2) p.2-theta^2 •kernel S theta (j+1) p.1‖ ≤ 
          (((j:ℝ)+3)*theta^2+((j:ℝ)+2)*theta^3)*theta^j*‖p‖ := by
        have hn: ‖kernel S theta (j+2) p.2-theta^2 •kernel S theta (j+1) p.1‖ ≤ 
          ‖kernel S theta (j+2) p.2‖+theta^2*‖kernel S theta (j+1) p.1‖ := by
          have hn:=norm_sub_le (kernel S theta (j+2) p.2) (theta^2 •kernel S theta (j+1) p.1)
          rw [norm_smul,Real.norm_eq_abs] at hn
          rw [abs_of_nonneg (sq_nonneg theta)] at hn
          exact hn
        have h1:=mul_le_mul_of_nonneg_left hK1s (sq_nonneg theta)
        have h2:=mul_le_mul_of_nonneg_left hp2 (show 0 ≤ (((j+2:ℕ):ℝ)+1)*theta^(j+2) by positivity)
        have h3:=mul_le_mul_of_nonneg_left hp1 (show 0 ≤ theta^2*((((j+1:ℕ):ℝ)+1)*theta^(j+1)) by positivity)
        push_cast at *
        rw [pow_succ theta (j+1),pow_succ theta j] at *
        nlinarith
      have hc:=pair_coefficient_bounds (j:ℝ) theta (Nat.cast_nonneg j) ht ht1
      have hm1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc.1 (pow_nonneg ht0 j)) hp0
      have hm2:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc.2 (pow_nonneg ht0 j)) hp0
      have he : 4*((j:ℝ)+3)*theta^2*theta^j*‖p‖=4*(((j+1+1:ℕ):ℝ)+1)*theta^(j+1+1)*‖p‖ := by
        push_cast
        rw [pow_add theta j 2]
        ring
      constructor
      · exact hprevious.trans (hm1.trans_eq he)
      · exact hcurrent.trans (hm2.trans_eq he)

/-- Forced heavy-ball state estimate with its proved transition kernel.
The only forcing premise is a pointwise residual-error bound at preceding steps. -/
lemma forcedTrajectory_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (S : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,S (basis i)=lambda i •basis i) (hlambda : ∀i,|lambda i| ≤ 1)
    (theta : ℝ) (ht : (1/3:ℝ) ≤ theta) (ht1 : theta<1)
    (initial : V×V) (noise : ℕ→V×V) (R Z : ℝ) (hR : ‖initial‖ ≤ R) (hZ : 0 ≤ Z)
    (k : ℕ) (hnoise : ∀i < k,‖noise i‖ ≤ Z) :
    ‖forcedTrajectory (transition S theta) initial noise k‖ ≤ 
      4*((k:ℝ)+1)*theta^k*R+4*Z/(1-theta)^2 := by
  have ht0 : 0 ≤ theta := by linarith
  have hinit := (transition_pow_norm_bound basis S lambda heigen hlambda theta ht ht1.le k initial).trans
    (mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 4*((k:ℝ)+1)*theta^k))
  have hsum : ‖∑i∈Finset.range k,(transition S theta^(k-1-i)) (noise i)‖ ≤ 4*Z/(1-theta)^2 := by
    have hh := norm_sum_le (Finset.range k) (fun i=>(transition S theta^(k-1-i)) (noise i))
    have hb : (∑i∈Finset.range k,‖(transition S theta^(k-1-i)) (noise i)‖) ≤ 
        ∑i∈Finset.range k,4*(((k-1-i:ℕ):ℝ)+1)*theta^(k-1-i)*Z := by
      apply Finset.sum_le_sum
      intro i hi
      exact (transition_pow_norm_bound basis S lambda heigen hlambda theta ht ht1.le _ _).trans
        (mul_le_mul_of_nonneg_left (hnoise i (Finset.mem_range.mp hi)) (by positivity))
    have hrefl := Finset.sum_range_reflect (fun j=>4*((j:ℝ)+1)*theta^j*Z) k
    have he : (∑j∈Finset.range k,4*((j:ℝ)+1)*theta^j*Z)=
        (4*Z)*(∑j∈Finset.range k,((j:ℝ)+1)*theta^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hrefl,he] at hb
    have hgeom:=mul_le_mul_of_nonneg_left
      (PaperHeavyBallDecay.weighted_geometric_bound theta ht0 ht1 k) (show 0 ≤ 4*Z by positivity)
    exact hh.trans (hb.trans (by simpa only [mul_one_div] using hgeom))
  rw [forcedTrajectory_formula]
  exact (norm_add_le _ _).trans (add_le_add hinit hsum)

/-- Closing the public guard invariant from local noise accuracy, followed by
an explicit finite-horizon accuracy theorem. No trajectory-norm or stability
conclusion is supplied as a premise. -/
theorem guarded_forcing_stability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (S : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,S (basis i)=lambda i •basis i) (hlambda : ∀i,|lambda i| ≤ 1)
    (theta : ℝ) (ht : (1/3:ℝ) ≤ theta) (ht1 : theta<1)
    (initial : V×V) (noise : ℕ→V×V) (R delta Z : ℝ)
    (hR : 0 < R) (hd : 0 < delta) (hdR : delta ≤ R) (hinit : ‖initial‖ ≤ R) (hZ : 0 ≤ Z)
    (hsmall : Z ≤ (1-theta)^2*delta/8)
    (hlocal : ∀i, ‖forcedTrajectory (transition S theta) initial noise i‖ ≤ 8*R/(1-theta) → ‖noise i‖ ≤ Z) :
    (∀k,‖forcedTrajectory (transition S theta) initial noise k‖ ≤ 8*R/(1-theta)) ∧
    ‖forcedTrajectory (transition S theta) initial noise (PaperHeavyBallDecay.publicHorizon theta R delta)‖ ≤ delta := by
  have ht0 : 0 ≤ theta := by linarith
  have hgap : 0 < 1-theta := by linarith
  have hgap1 : 1-theta ≤ 1 := by linarith
  have hforce : 4*Z/(1-theta)^2 ≤ delta/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hgap)).mpr
    nlinarith
  have huniform : ∀k,‖forcedTrajectory (transition S theta) initial noise k‖ ≤ 8*R/(1-theta) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih=>
      have hh:=forcedTrajectory_norm_bound basis S lambda heigen hlambda theta ht ht1 initial noise R Z hinit hZ k
        (fun i hi=>hlocal i (ih i hi))
      have hhom:=mul_le_mul_of_nonneg_left
        (PaperHeavyBallDecay.homogeneous_public_bound theta ht0 ht1 k) (show 0 ≤ 4*R by positivity)
      have hbound : 4*((k:ℝ)+1)*theta^k*R ≤ 4*R/(1-theta) := by convert hhom using 1 <;> first | rfl | ring
      have hRgap : R ≤ R/(1-theta) := (le_div_iff₀ hgap).mpr (by nlinarith)
      have he : 8*R/(1-theta)=2*(4*R/(1-theta)) := by ring
      have he4 : 4*R/(1-theta)=4*(R/(1-theta)) := by ring
      rw [he,he4]
      rw [he4] at hbound
      nlinarith
  refine ⟨huniform,?_⟩
  have hh:=forcedTrajectory_norm_bound basis S lambda heigen hlambda theta ht ht1 initial noise R Z hinit hZ
    (PaperHeavyBallDecay.publicHorizon theta R delta) (fun i _=>hlocal i (huniform i))
  have hhom:=PaperHeavyBallDecay.publicHorizon_precision theta R delta ht0 ht1 hR hd
  linarith


end
end PaperHeavyBallStability

end SnapshotModule_111
/- END heavy_ball_stability -/

/- BEGIN heavy_ball_iteration_stability -/
section SnapshotModule_112

namespace PaperHeavyBallIteration
open PaperHeavyBallDynamics PaperHeavyBallParameters
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def normalizedOperator (B : Module.End ℝ V) (m M : ℝ) : Module.End ℝ V :=
  (2*theta m M)⁻¹ •((1+(theta m M)^2) •(1 : Module.End ℝ V)-alpha m M •B)

lemma normalizedOperator_eigen (B : Module.End ℝ V) (m M : ℝ) (v : V) (lambda : ℝ)
    (heigen : B v=lambda •v) :
    normalizedOperator B m M v=((1+(theta m M)^2-alpha m M*lambda)/(2*theta m M)) •v := by
  simp only [normalizedOperator,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.one_apply,heigen,
    smul_sub,smul_smul]
  rw [←sub_smul]
  congr 1
  ring

lemma normalizedOperator_identity (B : Module.End ℝ V) (m M : ℝ) (ht : theta m M≠0) (v : V) :
    (2*theta m M) •normalizedOperator B m M v=(1+(theta m M)^2) •v-alpha m M •B v := by
  simp only [normalizedOperator,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.one_apply,smul_smul]
  have hh : (2*theta m M)*(2*theta m M)⁻¹=1 := mul_inv_cancel₀ (by exact mul_ne_zero (by norm_num) ht)
  rw [hh,one_smul]

/-- The physical heavy-ball state depends only on approximate residuals and public
step parameters; no minimizer or exact residual is used in this definition. -/
def step (estimate : V→V) (alpha theta : ℝ) (p : V×V) : V×V :=
  (p.2,p.2+alpha •estimate p.2+theta^2 •(p.2-p.1))

def states (estimate : V→V) (alpha theta : ℝ) : ℕ→V×V
  | 0=>(0,0)
  | k+1=>step estimate alpha theta (states estimate alpha theta k)

def forcing (B : Module.End ℝ V) (c : V) (estimate : V→V) (alpha theta : ℝ) (k : ℕ) : V×V :=
  (0,alpha •(estimate (states estimate alpha theta k).2-(c-B (states estimate alpha theta k).2)))

lemma step_error (B : Module.End ℝ V) (c star : V) (hsol : B star=c)
    (m M : ℝ) (ht : theta m M≠0) (estimate : V→V) (p : V×V) :
    step estimate (alpha m M) (theta m M) p-(star,star)=
      transition (normalizedOperator B m M) (theta m M) (p-(star,star))+
      (0,alpha m M •(estimate p.2-(c-B p.2))) := by
  rw [transition_apply]
  apply Prod.ext
  · simp [step]
  · change p.2+alpha m M •estimate p.2+(theta m M)^2 •(p.2-p.1)-star=
      (2*theta m M) •normalizedOperator B m M (p.2-star)-(theta m M)^2 •(p.1-star)+
        alpha m M •(estimate p.2-(c-B p.2))
    rw [normalizedOperator_identity B m M ht,map_sub,hsol]
    module

lemma error_states (B : Module.End ℝ V) (c star : V) (hsol : B star=c)
    (m M : ℝ) (ht : theta m M≠0) (estimate : V→V) (k : ℕ) :
    states estimate (alpha m M) (theta m M) k-(star,star)=
      forcedTrajectory (transition (normalizedOperator B m M) (theta m M)) (-star,-star)
        (forcing B c estimate (alpha m M) (theta m M)) k := by
  induction k with
  | zero=>simp [states,forcedTrajectory]
  | succ k ih=>
    rw [states,step_error B c star hsol m M ht,ih,forcedTrajectory]
    rfl

/-- The actual physical heavy-ball recursion is stable and accurate under the
local residual error model. The public guard is proved for every iterate. -/
theorem actual_iteration_stability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (B : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i)
    (m M : ℝ) (hm : 0 < m) (hpad : 4*m≤M) (hspectrum : ∀i,m≤lambda i ∧ lambda i≤M)
    (c star : V) (hsol : B star=c) (R delta eta tau : ℝ)
    (hR : 0 < R) (hd : 0 < delta) (hdR : delta≤R) (hstar : ‖star‖≤R)
    (heta : 0≤eta) (htau : 0≤tau)
    (heta_small : eta≤(1-theta m M)^2*delta/(64*(8*R/(1-theta m M))))
    (htau_small : alpha m M*tau≤(1-theta m M)^2*delta/16)
    (estimate : V→V)
    (hestimate : ∀x,‖x‖≤R+8*R/(1-theta m M) → ‖estimate x-(c-B x)‖≤eta*‖c-B x‖+tau) :
    (∀k,‖(states estimate (alpha m M) (theta m M) k).2‖≤R+8*R/(1-theta m M)) ∧
    ‖(states estimate (alpha m M) (theta m M)
      (PaperHeavyBallDecay.publicHorizon (theta m M) R delta)).2-star‖≤delta := by
  have hM : 0≤M := by linarith
  have ht:=theta_bounds m M hm hpad
  have htheta0 : 0 < theta m M := by linarith [ht.1]
  have hgap : 0 < 1-theta m M := by linarith [ht.2]
  have ha:=alpha_pos m M hm hM
  let X:=8*R/(1-theta m M)
  let Z:=4*eta*X+alpha m M*tau
  have hX : 0 < X := by dsimp [X];positivity
  have hZ : 0≤Z := by dsimp [Z];positivity
  have hsmall : Z≤(1-theta m M)^2*delta/8 := by
    have hh: eta*(64*X)≤(1-theta m M)^2*delta := (le_div_iff₀ (by positivity)).mp heta_small
    dsimp [Z]
    nlinarith
  have hinit : ‖(-star,-star)‖≤R := by simpa [Prod.norm_def] using hstar
  have hnormB : ∀v,‖B v‖≤M*‖v‖ := by
    intro v
    have hh:=PaperHeavyBallChebyshev.polynomial_norm_bound basis B lambda heigen Polynomial.X M hM
      (fun i=>by rw [Polynomial.eval_X,abs_of_nonneg (hm.le.trans (hspectrum i).1)];exact (hspectrum i).2) v
    simpa only [Polynomial.aeval_X] using hh
  have hlambda : ∀i,|((1+(theta m M)^2-alpha m M*lambda i)/(2*theta m M))|≤1 :=
    fun i=>normalized_spectrum m M (lambda i) hm hpad (hspectrum i).1 (hspectrum i).2
  have hlocal : ∀i,‖forcedTrajectory (transition (normalizedOperator B m M) (theta m M)) (-star,-star)
      (forcing B c estimate (alpha m M) (theta m M)) i‖≤X →
      ‖forcing B c estimate (alpha m M) (theta m M) i‖≤Z := by
    intro i hi
    rw [←error_states B c star hsol m M htheta0.ne' estimate i] at hi
    let x:=(states estimate (alpha m M) (theta m M) i).2
    have hex : ‖x-star‖≤X := (norm_snd_le _).trans hi
    have hx : ‖x‖≤R+X := by
      have hn:=norm_add_le (x-star) star
      have he : x-star+star=x := by abel
      rw [he] at hn
      linarith
    have hb : ‖c-B x‖≤M*X := by
      have he : c-B x= -B (x-star) := by rw [map_sub,hsol];abel
      rw [he,norm_neg]
      exact (hnormB _).trans (mul_le_mul_of_nonneg_left hex hM)
    have herr:=hestimate x hx
    have hn: ‖forcing B c estimate (alpha m M) (theta m M) i‖=
        alpha m M*‖estimate x-(c-B x)‖ := by
      simp only [forcing,x,Prod.norm_def,norm_zero,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
      apply max_eq_right
      positivity
    rw [hn]
    have hnoise:=mul_le_mul_of_nonneg_left herr ha.le
    have hb2:=mul_le_mul_of_nonneg_left hb heta
    have hb3:=mul_le_mul_of_nonneg_left hb2 ha.le
    have hAM:=alpha_times_upper m M hm hM
    have hAMX:=mul_le_mul_of_nonneg_right hAM (show 0≤eta*X by positivity)
    dsimp [Z]
    nlinarith
  have hstable:=PaperHeavyBallStability.guarded_forcing_stability basis (normalizedOperator B m M)
    (fun i=>(1+(theta m M)^2-alpha m M*lambda i)/(2*theta m M))
    (fun i=>normalizedOperator_eigen B m M _ _ (heigen i)) hlambda (theta m M) ht.1 ht.2
    (-star,-star) (forcing B c estimate (alpha m M) (theta m M)) R delta Z hR hd hdR hinit hZ hsmall hlocal
  constructor
  · intro k
    have hi:=hstable.1 k
    rw [←error_states B c star hsol m M htheta0.ne' estimate k] at hi
    have hex:= (norm_snd_le _).trans hi
    change ‖(states estimate (alpha m M) (theta m M) k).2-star‖≤8*R/(1-theta m M) at hex
    have hn:=norm_add_le ((states estimate (alpha m M) (theta m M) k).2-star) star
    have he : (states estimate (alpha m M) (theta m M) k).2-star+star=
        (states estimate (alpha m M) (theta m M) k).2 := by abel
    rw [he] at hn
    linarith
  · have hi:=hstable.2
    rw [←error_states B c star hsol m M htheta0.ne' estimate] at hi
    exact (norm_snd_le _).trans hi

end
end PaperHeavyBallIteration

end SnapshotModule_112
/- END heavy_ball_iteration_stability -/

/- BEGIN heavy_ball_program -/
section SnapshotModule_113

namespace PaperHeavyBallProgram
open PaperHeavyBallIteration
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def nextState (alpha theta : ℝ) (p : V×V) (residual : V) : V×V :=
  (p.2,p.2+alpha •residual+theta^2 •(p.2-p.1))

/-- Fixed-horizon comparison program with the public iterate norm guard.
In every failure branch it returns zero immediately. -/
def loopProgram {Q Reply : Type*} (estimate : V→PaperOracle.Program Q Reply V)
    (alpha theta guard : ℝ) : ℕ→V×V→PaperOracle.Program Q Reply (V×V)
  | 0,p=>.done p
  | k+1,p=>if ‖p.2‖ ≤ guard then
      PaperOracle.Program.bind (estimate p.2) (fun r=>loopProgram estimate alpha theta guard k (nextState alpha theta p r))
    else .done (0,0)

def program {Q Reply : Type*} (estimate : V→PaperOracle.Program Q Reply V)
    (alpha theta guard : ℝ) (k : ℕ) : PaperOracle.Program Q Reply V :=
  PaperOracle.Program.bind (loopProgram estimate alpha theta guard k (0,0)) (fun p=>.done p.2)

lemma loopProgram_cap {Q Reply : Type*} (estimate : V→PaperOracle.Program Q Reply V)
    (alpha theta guard : ℝ) (budget : ℕ) (hbudget : ∀x,PaperOracle.Program.Cap budget (estimate x)) (k : ℕ) (p : V×V) :
    PaperOracle.Program.Cap (k*budget) (loopProgram estimate alpha theta guard k p) := by
  induction k generalizing p with
  | zero=>simp only [loopProgram,Nat.zero_mul,PaperOracle.Program.Cap]
  | succ k ih=>
    simp only [loopProgram]
    split_ifs
    · rw [show (k+1)*budget=budget+k*budget by ring]
      exact PaperOracle.Program.cap_bind _ _ (hbudget _) (fun r=>ih _)
    · cases (k+1)*budget <;> trivial

lemma program_cap {Q Reply : Type*} (estimate : V→PaperOracle.Program Q Reply V)
    (alpha theta guard : ℝ) (budget : ℕ) (hbudget : ∀x,PaperOracle.Program.Cap budget (estimate x)) (k : ℕ) :
    PaperOracle.Program.Cap (k*budget) (program estimate alpha theta guard k) := by
  have hh:=PaperOracle.Program.cap_bind _ (fun p : V×V=>PaperOracle.Program.done p.2)
    (loopProgram_cap estimate alpha theta guard budget hbudget k (0,0)) (b:=0) (by intro p;trivial)
  simpa only [program,Nat.add_zero] using hh

lemma states_eq_iterate (estimate : V→V) (alpha theta : ℝ) (k : ℕ) :
    states estimate alpha theta k=(step estimate alpha theta)^[k] (0,0) := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [states,ih,Function.iterate_succ_apply']

lemma loopProgram_eval {Q Reply : Type*} (C : Q→Reply) (estimate : V→PaperOracle.Program Q Reply V)
    (alpha theta guard : ℝ) (k : ℕ) (p : V×V)
    (hguard : ∀j < k,‖((step (fun x=>PaperOracle.Program.run C (estimate x)) alpha theta)^[j] p).2‖ ≤ guard) :
    PaperOracle.Program.run C (loopProgram estimate alpha theta guard k p)=
      (step (fun x=>PaperOracle.Program.run C (estimate x)) alpha theta)^[k] p := by
  induction k generalizing p with
  | zero=>rfl
  | succ k ih=>
    have hp : ‖p.2‖ ≤ guard := by simpa using hguard 0 (by omega)
    rw [loopProgram,if_pos hp,PaperOracle.Program.run_bind]
    rw [ih]
    · rw [Function.iterate_succ_apply]
      rfl
    · intro j hj
      have hh:=hguard (j+1) (by omega)
      rw [Function.iterate_succ_apply] at hh
      exact hh

lemma program_eval {Q Reply : Type*} (C : Q→Reply) (estimate : V→PaperOracle.Program Q Reply V)
    (alpha theta guard : ℝ) (k : ℕ)
    (hguard : ∀j < k,‖(states (fun x=>PaperOracle.Program.run C (estimate x)) alpha theta j).2‖ ≤ guard) :
    PaperOracle.Program.run C (program estimate alpha theta guard k)=
      (states (fun x=>PaperOracle.Program.run C (estimate x)) alpha theta k).2 := by
  have hh:=loopProgram_eval C estimate alpha theta guard k (0,0) (by
    intro j hj
    rw [←states_eq_iterate]
    exact hguard j hj)
  simp only [program,PaperOracle.Program.run_bind,PaperOracle.Program.run,hh,←states_eq_iterate]

/-- Full actual finite heavy-ball comparison recursion from a finite residual backend.
The backend's local error certificate is instantiated from calibration/root estimates
in a separate module; the guard and terminal accuracy are proved here. -/
theorem program_accuracy_from_residual {Q Reply : Type*} (C : Q→Reply)
    (estimate : V→PaperOracle.Program Q Reply V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (B : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i)
    (m M : ℝ) (hm : 0 < m) (hpad : 4*m ≤ M) (hspectrum : ∀i,m ≤ lambda i ∧ lambda i ≤ M)
    (c star : V) (hsol : B star=c) (R delta eta tau : ℝ)
    (hR : 0 < R) (hd : 0 < delta) (hdR : delta ≤ R) (hstar : ‖star‖ ≤ R)
    (heta : 0 ≤ eta) (htau : 0 ≤ tau)
    (heta_small : eta ≤ (1-PaperHeavyBallParameters.theta m M)^2*delta/
      (64*(8*R/(1-PaperHeavyBallParameters.theta m M))))
    (htau_small : PaperHeavyBallParameters.alpha m M*tau ≤ (1-PaperHeavyBallParameters.theta m M)^2*delta/16)
    (hestimate : ∀x,‖x‖ ≤ R+8*R/(1-PaperHeavyBallParameters.theta m M) →
      ‖PaperOracle.Program.run C (estimate x)-(c-B x)‖ ≤ eta*‖c-B x‖+tau) :
    ‖PaperOracle.Program.run C (program estimate (PaperHeavyBallParameters.alpha m M)
      (PaperHeavyBallParameters.theta m M) (R+8*R/(1-PaperHeavyBallParameters.theta m M))
      (PaperHeavyBallDecay.publicHorizon (PaperHeavyBallParameters.theta m M) R delta))-star‖ ≤ delta := by
  have hs:=actual_iteration_stability basis B lambda heigen m M hm hpad hspectrum c star hsol R delta eta tau
    hR hd hdR hstar heta htau heta_small htau_small (fun x=>PaperOracle.Program.run C (estimate x)) hestimate
  rw [program_eval C estimate _ _ _ _ (fun j _=>hs.1 j)]
  exact hs.2

end
end PaperHeavyBallProgram

end SnapshotModule_113
/- END heavy_ball_program -/

/- BEGIN heavy_ball_public_parameters -/
section SnapshotModule_114

namespace PaperHeavyBallPublic
open PaperHeavyBallParameters
noncomputable section

def publicTheta (kappa : ℝ) : ℝ := theta 1 (8*kappa)
def publicDelta (R Q : ℝ) : ℝ := R*Real.sqrt (2/Q)
def publicX (kappa R : ℝ) : ℝ := 8*R/(1-publicTheta kappa)
def publicEta (kappa Q S q : ℝ) : ℝ :=
  min (1/2) (min (PaperHeavyBallPowerHorizon.sigma S q/2)
    ((1-publicTheta kappa)^3*Real.sqrt (2/Q)/512))
def publicTau (kappa R Q S : ℝ) : ℝ :=
  (1-publicTheta kappa)^2*publicDelta R Q/(64*kappa*S)

lemma theta_scale (m M c : ℝ) (hc : 0 < c) : theta (c*m) (c*M)=theta m M := by
  have hs : Real.sqrt c≠0 := (Real.sqrt_pos.mpr hc).ne'
  dsimp [theta]
  rw [Real.sqrt_mul hc.le,Real.sqrt_mul hc.le]
  calc
    _=(Real.sqrt c*(Real.sqrt M-Real.sqrt m))/(Real.sqrt c*(Real.sqrt M+Real.sqrt m)) := by ring
    _=(Real.sqrt M-Real.sqrt m)/(Real.sqrt M+Real.sqrt m) := mul_div_mul_left _ _ hs

lemma theta_from_estimate (rho kappa : ℝ) (hrho : 0 < rho) (hk : 0 < kappa) :
    theta (rho/(4*kappa)) (2*rho)=publicTheta kappa := by
  have hm : 0 < rho/(4*kappa) := by positivity
  have he : (rho/(4*kappa))*(8*kappa)=2*rho := by field_simp;ring
  change theta (rho/(4*kappa)) (2*rho)=theta 1 (8*kappa)
  rw [←he]
  convert theta_scale 1 (8*kappa) (rho/(4*kappa)) hm using 1 <;> ring

lemma publicTheta_bounds (kappa : ℝ) (hk : 1 ≤ kappa) :
    (1/3:ℝ) ≤ publicTheta kappa ∧ publicTheta kappa<1 :=
  theta_bounds 1 (8*kappa) (by norm_num) (by linarith)

lemma estimate_spectrum (rho kappa Mstar lambda : ℝ) (hk : 1 ≤ kappa) (hM : 0 < Mstar)
    (hrlo : Mstar/2 ≤ rho) (hrup : rho ≤ 2*Mstar)
    (hlambda : Mstar/kappa ≤ lambda ∧ lambda ≤ Mstar) :
    0 < rho/(4*kappa) ∧ 4*(rho/(4*kappa)) ≤ 2*rho ∧
      rho/(4*kappa) ≤ lambda ∧ lambda ≤ 2*rho ∧ (2*rho)/(rho/(4*kappa))=8*kappa := by
  have hkp : 0 < kappa := by linarith
  have hrho : 0 < rho := by linarith
  have hl : 0 < lambda := (div_pos hM hkp).trans_le hlambda.1
  have hlow : Mstar ≤ lambda*kappa := (div_le_iff₀ hkp).mp hlambda.1
  have hm : 0 < rho/(4*kappa) := by positivity
  refine ⟨hm,?_,?_,by linarith [hlambda.2],?_⟩
  · have he : 4*(rho/(4*kappa))=rho/kappa := by ring
    rw [he]
    apply (div_le_iff₀ hkp).mpr
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 4*kappa)).mpr
    nlinarith
  · field_simp
    <;> ring

lemma alpha_public_bound (rho kappa S Mstar : ℝ) (hk : 1 ≤ kappa) (hS : 0 < S)
    (hMlo : 1/(kappa*S) ≤ Mstar) (hrlo : Mstar/2 ≤ rho) :
    alpha (rho/(4*kappa)) (2*rho) ≤ 4*kappa*S := by
  have hkp : 0 < kappa := by linarith
  have hM : 0 < Mstar := (by positivity : 0 < 1/(kappa*S)).trans_le hMlo
  have hr : 0 < rho := by linarith
  have hm : 0 < rho/(4*kappa) := by positivity
  have ha:=alpha_pos (rho/(4*kappa)) (2*rho) hm (by positivity)
  have hupper:=alpha_times_upper (rho/(4*kappa)) (2*rho) hm (by positivity)
  have hlow : 1/(kappa*S) ≤ 2*rho := by linarith
  have hh:=mul_le_mul_of_nonneg_left hlow ha.le
  have hd : alpha (rho/(4*kappa)) (2*rho)/(kappa*S) ≤ 4 := by
    simpa only [div_eq_mul_inv,mul_one,one_mul] using hh.trans hupper
  simpa only [mul_assoc] using (div_le_iff₀ (by positivity : 0 < kappa*S)).mp hd

lemma publicEta_positive (kappa Q S q : ℝ) (hk : 1 ≤ kappa) (hQ : 0 < Q) (hS : 0 < S) (hq : 0 < q) :
    0 < publicEta kappa Q S q := by
  have ht:=publicTheta_bounds kappa hk
  have hgap : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have hs : 0 < PaperHeavyBallPowerHorizon.sigma S q := by
    dsimp [PaperHeavyBallPowerHorizon.sigma]
    have hK:=PaperHeavyBallPowerHorizon.iterations_pos S q
    have hKr : 0 < (PaperHeavyBallPowerHorizon.iterations S q:ℝ) := Nat.cast_pos.mpr hK
    positivity
  dsimp [publicEta]
  positivity

lemma publicEta_small (kappa Q S q : ℝ) : publicEta kappa Q S q ≤ 1/2 ∧
    publicEta kappa Q S q ≤ PaperHeavyBallPowerHorizon.sigma S q/2 ∧
    publicEta kappa Q S q ≤ (1-publicTheta kappa)^3*Real.sqrt (2/Q)/512 := by
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

lemma publicEta_iteration (kappa R Q S q : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) :
    publicEta kappa Q S q ≤ (1-publicTheta kappa)^2*publicDelta R Q/(64*publicX kappa R) := by
  have ht:=publicTheta_bounds kappa hk
  have hgap : 1-publicTheta kappa≠0 := ne_of_gt (by linarith [ht.2])
  have he : (1-publicTheta kappa)^2*publicDelta R Q/(64*publicX kappa R)=
      (1-publicTheta kappa)^3*Real.sqrt (2/Q)/512 := by
    dsimp [publicDelta,publicX]
    field_simp
    <;> ring
  rw [he]
  exact (publicEta_small kappa Q S q).2.2

lemma publicTau_iteration (rho kappa R Q S Mstar : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) (hQ : 0 < Q) (hS : 0 < S)
    (hMlo : 1/(kappa*S) ≤ Mstar) (hrlo : Mstar/2 ≤ rho) :
    alpha (rho/(4*kappa)) (2*rho)*publicTau kappa R Q S ≤ 
      (1-publicTheta kappa)^2*publicDelta R Q/16 := by
  have ht:=publicTheta_bounds kappa hk
  have htau : 0 ≤ publicTau kappa R Q S := by dsimp [publicTau,publicDelta];positivity
  have hh:=mul_le_mul_of_nonneg_right (alpha_public_bound rho kappa S Mstar hk hS hMlo hrlo) htau
  have he : (4*kappa*S)*publicTau kappa R Q S=(1-publicTheta kappa)^2*publicDelta R Q/16 := by
    have hkp : 0 < kappa := by linarith
    dsimp [publicTau]
    field_simp
    <;> ring
  exact hh.trans_eq he

end
end PaperHeavyBallPublic

end SnapshotModule_114
/- END heavy_ball_public_parameters -/

/- BEGIN heavy_ball_public_iteration -/
section SnapshotModule_115

namespace PaperHeavyBallPublic
open PaperHeavyBallParameters PaperHeavyBallProgram
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def publicIterationProgram {Query Reply : Type*} (estimate : V→PaperOracle.Program Query Reply V)
    (rho kappa R Q : ℝ) : PaperOracle.Program Query Reply V :=
  program estimate (alpha (rho/(4*kappa)) (2*rho)) (publicTheta kappa) (R+publicX kappa R)
    (PaperHeavyBallDecay.publicHorizon (publicTheta kappa) R (publicDelta R Q))

lemma publicDelta_bounds (R Q : ℝ) (hR : 0 < R) (hQ : 32 ≤ Q) :
    0 < publicDelta R Q ∧ publicDelta R Q ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hsmall : 2/Q ≤ 1 := (div_le_one hQ0).mpr (by linarith)
  have hs : Real.sqrt (2/Q) ≤ 1 := Real.sqrt_le_one.mpr hsmall
  constructor
  · dsimp [publicDelta];positivity
  · exact (mul_le_mul_of_nonneg_left hs hR.le).trans_eq (mul_one R)

/-- Public tolerances chosen before calibration satisfy the actual residual
accuracy and stability requirements for every successful spectral estimate. -/
theorem publicIterationProgram_correct {Query Reply : Type*} (C : Query→Reply)
    (estimate : V→PaperOracle.Program Query Reply V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : OrthonormalBasis ι ℝ V) (B : Module.End ℝ V) (lambda : ι→ℝ)
    (heigen : ∀i,B (basis i)=lambda i •basis i) (top : ι)
    (rho kappa Mstar R Q S q : ℝ) (hk : 1 ≤ kappa) (hM : 0 < Mstar) (hR : 0 < R) (hQ : 32 ≤ Q)
    (hS : 0 < S) (hq : 0 < q) (hMlo : 1/(kappa*S) ≤ Mstar)
    (hrlo : Mstar/2 ≤ rho) (hrup : rho ≤ 2*Mstar)
    (hspectrum : ∀i,Mstar/kappa ≤ lambda i ∧ lambda i ≤ Mstar)
    (c star : V) (hsol : B star=c) (hstar : ‖star‖ ≤ R)
    (hestimate : ∀x,‖x‖ ≤ R+publicX kappa R →
      ‖PaperOracle.Program.run C (estimate x)-(c-B x)‖ ≤ publicEta kappa Q S q*‖c-B x‖+publicTau kappa R Q S) :
    ‖PaperOracle.Program.run C (publicIterationProgram estimate rho kappa R Q)-star‖ ≤ publicDelta R Q := by
  have hkp : 0 < kappa := by linarith
  have hrho : 0 < rho := by linarith
  have hQ0 : 0 < Q := by linarith
  have heq:=theta_from_estimate rho kappa hrho hkp
  have hsp:=estimate_spectrum rho kappa Mstar (lambda top) hk hM hrlo hrup (hspectrum top)
  have hs : ∀i,rho/(4*kappa) ≤ lambda i ∧ lambda i ≤ 2*rho := by
    intro i
    have hh:=estimate_spectrum rho kappa Mstar (lambda i) hk hM hrlo hrup (hspectrum i)
    exact ⟨hh.2.2.1,hh.2.2.2.1⟩
  have hd:=publicDelta_bounds R Q hR hQ
  have heta: 0 ≤ publicEta kappa Q S q := (publicEta_positive kappa Q S q hk hQ0 hS hq).le
  have htau : 0 ≤ publicTau kappa R Q S := by dsimp [publicTau,publicDelta];positivity
  have hetaSmall:=publicEta_iteration kappa R Q S q hk hR
  dsimp only [publicX] at hetaSmall
  rw [←heq] at hetaSmall
  have htauSmall:=publicTau_iteration rho kappa R Q S Mstar hk hR hQ0 hS hMlo hrlo
  rw [←heq] at htauSmall
  have hbackend : ∀x,‖x‖ ≤ R+8*R/(1-theta (rho/(4*kappa)) (2*rho)) →
      ‖PaperOracle.Program.run C (estimate x)-(c-B x)‖ ≤ publicEta kappa Q S q*‖c-B x‖+publicTau kappa R Q S := by
    intro x hx
    rw [heq] at hx
    exact hestimate x hx
  have hh:=program_accuracy_from_residual C estimate basis B lambda heigen (rho/(4*kappa)) (2*rho)
    hsp.1 hsp.2.1 hs c star hsol R (publicDelta R Q) (publicEta kappa Q S q) (publicTau kappa R Q S)
    hR hd.1 hd.2 hstar heta htau hetaSmall htauSmall hbackend
  rw [heq] at hh
  exact hh

end
end PaperHeavyBallPublic

end SnapshotModule_115
/- END heavy_ball_public_iteration -/

/- BEGIN heavy_ball_algorithm -/
section SnapshotModule_116

namespace PaperHeavyBallAlgorithm
open PaperOracle PaperHeavyBallBackend PaperHeavyBallGaussian PaperHeavyBallPublic PaperHeavyBallPowerHorizon
noncomputable section

abbrev Space (d : ℕ) := Vec d
abbrev Seed (d : ℕ) := Space d×Space d

def basis (d : ℕ) : OrthonormalBasis (Fin d) ℝ (Space d) := EuclideanSpace.basisFun (Fin d) ℝ

def S (d : ℕ) : ℝ := 36*(d:ℝ)
def s : ℝ := 1/72
def calibrationQ (d : ℕ) : ℝ := 1/(36*(d:ℝ))
def powerQ : ℝ := 1/36

def eta (d : ℕ) (kappa Q : ℝ) : ℝ := publicEta kappa Q (S d) powerQ

def powerTolerance (d : ℕ) (kappa R : ℝ) : ℝ :=
  powerRootTolerance d kappa R s (S d) (sigma (S d) powerQ)

def residualTolerance (d : ℕ) (kappa R Q : ℝ) : ℝ :=
  residualRootTolerance d kappa s (publicTau kappa R Q (S d))

def powerCount (d : ℕ) : ℕ := iterations (S d) powerQ

def heavyCount (kappa R Q : ℝ) : ℕ := PaperHeavyBallDecay.publicHorizon (publicTheta kappa) R (publicDelta R Q)

def residualBackend (d : ℕ) (kappa R Q : ℝ) (lambdaHat : Fin d→ℝ) (x : Space d) : Program (Space d×Space d) Ordering (Space d) :=
  residualProgram (basis d) lambdaHat x kappa R (publicX kappa R) (residualTolerance d kappa R Q)

def productBackend (d : ℕ) (kappa R : ℝ) (lambdaHat : Fin d→ℝ) (v : Space d) : Program (Space d×Space d) Ordering (Space d) :=
  productProgram (basis d) lambdaHat v kappa R (powerTolerance d kappa R)

/-- The whole post-calibration computation uses a fixed power count, a checked
positive scale estimate, and the public guarded heavy-ball horizon. -/
def afterCalibration (d : ℕ) (kappa R Q : ℝ) (lambdaHat : Fin d→ℝ) (w : Space d) : Program (Space d×Space d) Ordering (Space d) :=
  Program.bind (PaperHeavyBallPowerComplete.estimateProgram (productBackend d kappa R lambdaHat) R (powerCount d) w)
    (fun rho=>if 0 < rho then publicIterationProgram (residualBackend d kappa R Q lambdaHat) rho kappa R Q else .done 0)

/-- The actual comparison-only randomized algorithm. Its two raw Gaussian seeds
are independent of the unknown objective; only public conditioning/radius/accuracy
parameters enter its fixed schedules and guards. -/
def algorithm (d : ℕ) (kappa R Q : ℝ) (seed : Seed d) : Program (Space d×Space d) Ordering (Space d) :=
  Program.bind (calibrationProgram (basis d) seed.1 kappa R s (S d) (calibrationQ d) (eta d kappa Q))
    (fun result=>match result with
      | none=>.done 0
      | some lambdaHat=>afterCalibration d kappa R Q lambdaHat seed.2)

def calibrationCap (d : ℕ) (kappa R Q : ℝ) : ℕ :=
  d*coordinateCost kappa R s (S d) (calibrationQ d) (eta d kappa Q)
def powerProductCap (d : ℕ) (kappa R : ℝ) : ℕ := productCost d kappa R (powerTolerance d kappa R)
def residualCap (d : ℕ) (kappa R Q : ℝ) : ℕ := residualCost d kappa R (publicX kappa R) (residualTolerance d kappa R Q)
def powerCap (d : ℕ) (kappa R : ℝ) : ℕ := (powerCount d+1)*powerProductCap d kappa R
def heavyCap (d : ℕ) (kappa R Q : ℝ) : ℕ := heavyCount kappa R Q*residualCap d kappa R Q
def totalCap (d : ℕ) (kappa R Q : ℝ) : ℕ := calibrationCap d kappa R Q+(powerCap d kappa R+heavyCap d kappa R Q)

lemma done_cap {Query Reply A : Type} (a : A) (n : ℕ) : Program.Cap n (Program.done (Q:=Query) (R:=Reply) a) := by
  cases n <;> trivial

lemma residualBackend_cap (d : ℕ) (kappa R Q : ℝ) (lambdaHat : Fin d→ℝ) (x : Space d) :
    Program.Cap (residualCap d kappa R Q) (residualBackend d kappa R Q lambdaHat x) :=
  residualProgram_cap (basis d) lambdaHat x kappa R _ _

lemma productBackend_cap (d : ℕ) (kappa R : ℝ) (lambdaHat : Fin d→ℝ) (v : Space d) :
    Program.Cap (powerProductCap d kappa R) (productBackend d kappa R lambdaHat v) :=
  productProgram_cap (basis d) lambdaHat v kappa R _

lemma publicIteration_cap (d : ℕ) (kappa R Q rho : ℝ) (lambdaHat : Fin d→ℝ) :
    Program.Cap (heavyCap d kappa R Q)
      (publicIterationProgram (residualBackend d kappa R Q lambdaHat) rho kappa R Q) :=
  PaperHeavyBallProgram.program_cap _ _ _ _ _ (residualBackend_cap d kappa R Q lambdaHat) _

lemma afterCalibration_cap (d : ℕ) (kappa R Q : ℝ) (lambdaHat : Fin d→ℝ) (w : Space d) :
    Program.Cap (powerCap d kappa R+heavyCap d kappa R Q) (afterCalibration d kappa R Q lambdaHat w) := by
  apply Program.cap_bind _ _ (PaperHeavyBallPowerComplete.estimateProgram_cap _ R _ (productBackend_cap d kappa R lambdaHat) _ w)
  intro rho
  split_ifs
  · exact publicIteration_cap d kappa R Q rho lambdaHat
  · exact done_cap _ _

/-- Every random seed and every arbitrary response branch obey the deterministic
public cap, including calibration failure, zero normalization and norm fallbacks. -/
theorem algorithm_cap (d : ℕ) (kappa R Q : ℝ) (seed : Seed d) :
    Program.Cap (totalCap d kappa R Q) (algorithm d kappa R Q seed) := by
  apply Program.cap_bind _ _ (calibrationProgram_cap (basis d) seed.1 kappa R s (S d) (calibrationQ d) (eta d kappa Q))
  intro result
  cases result with
  | none=>exact done_cap _ _
  | some lambdaHat=>exact afterCalibration_cap d kappa R Q lambdaHat seed.2

end
end PaperHeavyBallAlgorithm

end SnapshotModule_116
/- END heavy_ball_algorithm -/

/- BEGIN heavy_ball_spectral_data -/
section SnapshotModule_117

namespace PaperHeavyBallSpectral
open PaperHeavyBallScale PaperHeavyBallGaussian
open scoped RealInnerProductSpace
noncomputable section

structure Data (d : ℕ) (A : Vec d→L[ℝ] Vec d) (mu beta : ℝ) where
  basis : OrthonormalBasis (Fin d) ℝ (Vec d)
  values : Fin d→ℝ
  top : Fin d
  eigen : ∀i,A (basis i)=values i •basis i
  bounds : ∀i,mu ≤ values i ∧ values i ≤ beta
  maximal : ∀i,values i ≤ values top

/-- Spectral data and a top eigendirection are derived from the original actual
self-adjoint positive definite operator, once per fixed instance in the proof. -/
theorem exists_data (d : ℕ) (hd : 0 < d) (A : Vec d→L[ℝ] Vec d)
    (hA : A.toLinearMap.IsSymmetric) (mu beta : ℝ)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2) :
    Nonempty (Data d A mu beta) := by
  have hdim : Module.finrank ℝ (Vec d)=d := by simp [Vec]
  let basis:=hA.eigenvectorBasis hdim
  let values:=hA.eigenvalues hdim
  have heigen : ∀i,A (basis i)=values i •basis i := hA.apply_eigenvectorBasis hdim
  have hb : ∀i,mu ≤ values i ∧ values i ≤ beta := by
    intro i
    have hlo:=hlower (basis i)
    have hup:=hupper (basis i)
    rw [heigen i,real_inner_smul_right,real_inner_self_eq_norm_sq,basis.orthonormal.norm_eq_one,one_pow,mul_one] at hlo hup
    simpa only [basis.orthonormal.norm_eq_one,one_pow,mul_one] using And.intro hlo hup
  have hn : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0,hd⟩,by simp⟩
  obtain ⟨top,_,htop⟩:=Finset.exists_max_image Finset.univ values hn
  exact ⟨⟨basis,values,top,heigen,hb,fun i=>htop i (Finset.mem_univ i)⟩⟩

variable {d : ℕ} {A : Vec d→L[ℝ] Vec d} {mu beta : ℝ}

lemma norm_upper (D : Data d A mu beta) (hmu : 0 < mu) : ‖A‖ ≤ beta := by
  have hbetapos : 0 < beta := hmu.trans_le (D.bounds D.top).1 |>.trans_le (D.bounds D.top).2
  apply A.opNorm_le_bound hbetapos.le
  intro v
  have hh:=PaperHeavyBallChebyshev.polynomial_norm_bound D.basis A.toLinearMap D.values D.eigen Polynomial.X beta
    hbetapos.le (fun i=>by rw [Polynomial.eval_X,abs_of_pos (hmu.trans_le (D.bounds i).1)];exact (D.bounds i).2) v
  simp only [Polynomial.aeval_X] at hh
  convert hh using 1 <;> rfl

def topFunctional (D : Data d A mu beta) : StrongDual ℝ (Vec d) := InnerProductSpace.toDual ℝ (Vec d) (D.basis D.top)

lemma topFunctional_norm (D : Data d A mu beta) : ‖topFunctional D‖=1 := by
  exact ((InnerProductSpace.toDual ℝ (Vec d)).norm_map (D.basis D.top)).trans
    (D.basis.orthonormal.norm_eq_one D.top)

lemma topFunctional_apply (D : Data d A mu beta) (w : Vec d) : topFunctional D w=D.basis.repr w D.top := by
  rw [topFunctional,InnerProductSpace.toDual_apply_apply,D.basis.repr_apply_apply]

def scaledValues (D : Data d A mu beta) (u : Vec d) (i : Fin d) : ℝ :=
  D.values i/inner ℝ u (A u)
def scaledMaximum (D : Data d A mu beta) (u : Vec d) : ℝ := scaledValues D u D.top

lemma scaled_eigen (D : Data d A mu beta) (u : Vec d) (i : Fin d) :
    scaledOperator A u (D.basis i)=scaledValues D u i •D.basis i := by
  simp only [scaledOperator,ContinuousLinearMap.smul_apply,D.eigen i,smul_smul,scaledValues]
  congr 1
  ring

/-- Actual normalized spectrum and operator norm share the original fixed
instance eigenbasis, so the second independent Gaussian event is static. -/
theorem scaled_data (D : Data d A mu beta) (hmu : 0 < mu) (hbeta : mu ≤ beta)
    (u : Vec d) (ha : 0 < inner ℝ u (A u)) (S : ℝ) (hS : 0 < S)
    (haup : inner ℝ u (A u) ≤ beta*S) :
    0 < scaledMaximum D u ∧
    (∀i,0 < scaledValues D u i ∧ scaledValues D u i ≤ scaledMaximum D u) ∧
    (∀i,scaledMaximum D u/(beta/mu) ≤ scaledValues D u i) ∧
    1/((beta/mu)*S) ≤ scaledMaximum D u ∧
    (∀v,‖scaledOperator A u v‖ ≤ scaledMaximum D u*‖v‖) ∧
    (∀v,v≠0→scaledOperator A u v≠0) := by
  have hbeta0 : 0 < beta := hmu.trans_le hbeta
  have hk : 0 < beta/mu := div_pos hbeta0 hmu
  have hlpos : ∀i,0 < D.values i := fun i=>hmu.trans_le (D.bounds i).1
  have hmax : 0 < scaledMaximum D u := div_pos (hlpos D.top) ha
  have hbounds : ∀i,0 < scaledValues D u i ∧ scaledValues D u i ≤ scaledMaximum D u := by
    intro i
    exact ⟨div_pos (hlpos i) ha,div_le_div_of_nonneg_right (D.maximal i) ha.le⟩
  have hcondition : ∀i,scaledMaximum D u/(beta/mu) ≤ scaledValues D u i := by
    intro i
    have hh:=div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (D.bounds D.top).2 ha.le) hk.le
    have he : (beta/inner ℝ u (A u))/(beta/mu)=mu/inner ℝ u (A u) := by field_simp
    rw [he] at hh
    exact hh.trans (div_le_div_of_nonneg_right (D.bounds i).1 ha.le)
  have hlow : 1/((beta/mu)*S) ≤ scaledMaximum D u := by
    have hh:=div_le_div₀ (hlpos D.top).le (D.bounds D.top).1 ha haup
    have he : mu/(beta*S)=1/((beta/mu)*S) := by field_simp
    rw [he] at hh
    exact hh
  have hnorm : ∀v,‖scaledOperator A u v‖ ≤ scaledMaximum D u*‖v‖ := by
    intro v
    have hh:=PaperHeavyBallChebyshev.polynomial_norm_bound D.basis (scaledOperator A u).toLinearMap
      (scaledValues D u) (scaled_eigen D u) Polynomial.X (scaledMaximum D u) hmax.le
      (fun i=>by rw [Polynomial.eval_X,abs_of_pos (hbounds i).1];exact (hbounds i).2) v
    simp only [Polynomial.aeval_X] at hh
    convert hh using 1 <;> rfl
  refine ⟨hmax,hbounds,hcondition,hlow,hnorm,?_⟩
  intro v hv hz
  have hrepr : ∀i,D.basis.repr v i=0 := by
    intro i
    have hh:=PaperCGSpectral.repr_aeval D.basis (scaledOperator A u).toLinearMap (scaledValues D u)
      (scaled_eigen D u) Polynomial.X v i
    simp only [Polynomial.aeval_X,Polynomial.eval_X] at hh
    have he : D.basis.repr (scaledOperator A u v) i=scaledValues D u i*D.basis.repr v i := by
      convert hh using 1 <;> rfl
    rw [hz,map_zero] at he
    change (0:ℝ)=scaledValues D u i*D.basis.repr v i at he
    exact (mul_eq_zero.mp he.symm).resolve_left (hbounds i).1.ne'

  apply hv
  apply D.basis.repr.injective
  ext i
  simp [hrepr i]

end
end PaperHeavyBallSpectral

end SnapshotModule_117
/- END heavy_ball_spectral_data -/

/- BEGIN heavy_ball_objective -/
section SnapshotModule_118

namespace PaperHeavyBallObjective
open PaperHeavyBallLine PaperHeavyBallPublic
open scoped RealInnerProductSpace
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma quadratic_gap (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b star x : V) (hsol : A star=b) :
    quadratic A b x-quadratic A b star=inner ℝ (x-star) (A (x-star))/2 := by
  have hh:=quadratic_line A hA b star (x-star) 1
  have he : star+(1:ℝ) •(x-star)=x := by module
  rw [he,hsol,sub_self,inner_zero_right] at hh
  norm_num at hh
  rw [map_sub]
  linarith

lemma distance_to_objective (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b star x : V) (hsol : A star=b)
    (beta delta : ℝ) (hb : 0 ≤ beta) (hd : 0 ≤ delta)
    (hupper : ∀v,inner ℝ v (A v) ≤ beta*‖v‖^2) (hx : ‖x-star‖ ≤ delta) :
    quadratic A b x-quadratic A b star ≤ beta*delta^2/2 := by
  rw [quadratic_gap A hA b star x hsol]
  have hsq : ‖x-star‖^2 ≤ delta^2 := by nlinarith [norm_nonneg (x-star)]
  have hh:=mul_le_mul_of_nonneg_left hsq hb
  linarith [hupper (x-star)]

lemma original_accuracy (A : V→L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) (b star x : V) (hsol : A star=b)
    (beta R epsilon Q c0 : ℝ) (hb : 0 < beta) (hR : 0 < R) (he : 0 < epsilon) (hQ : 32 ≤ Q)
    (hQdef : Q=beta*R^2/epsilon) (hupper : ∀v,inner ℝ v (A v) ≤ beta*‖v‖^2)
    (hx : ‖x-star‖ ≤ publicDelta R Q) :
    (quadratic A b x+c0)-(quadratic A b star+c0) ≤ epsilon := by
  have hQ0 : 0 < Q := by linarith
  have hd:=publicDelta_bounds R Q hR hQ
  have hh:=distance_to_objective A hA b star x hsol beta (publicDelta R Q) hb.le hd.1.le hupper hx
  have hc : beta*(publicDelta R Q)^2/2=epsilon := by
    rw [publicDelta,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2/Q),hQdef]
    field_simp
    <;> ring
  rw [hc] at hh
  linarith

lemma comparison_add_const {E : Type*} (f : E→ℝ) (c : ℝ) :
    PaperOracle.comparisonOracle (fun x=>f x+c)=PaperOracle.comparisonOracle f := by
  funext pair
  simp only [PaperOracle.comparisonOracle,PaperOracle.realOrder,add_lt_add_iff_right,add_left_inj]

end
end PaperHeavyBallObjective

end SnapshotModule_118
/- END heavy_ball_objective -/

/- BEGIN heavy_ball_success -/
section SnapshotModule_119

namespace PaperHeavyBallAlgorithm
open MeasureTheory Set PaperOracle PaperHeavyBallBackend PaperHeavyBallGaussian PaperHeavyBallPublic
open PaperHeavyBallScale PaperHeavyBallSpectral PaperHeavyBallLine
open scoped RealInnerProductSpace
noncomputable section

/-- Both good events imply success of the complete actually executed algorithm.
Every calibration, product, normalized power, spectral scaling, residual, guard,
iteration and objective-gap step is instantiated from the original assumptions. -/
theorem good_seed_accuracy (d : ℕ) (hd : 0 < d)
    (A : Space d→L[ℝ] Space d) (hA : A.toLinearMap.IsSymmetric) (b star : Space d)
    (mu beta R epsilon Q : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQ : 32 ≤ Q) (hQdef : Q=beta*R^2/epsilon)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) (D : Data d A mu beta)
    (u w : Space d) (hu : u∈(calibrationBad (row (basis d) A) s (S d) (calibrationQ d))ᶜ)
    (hw : w∈(powerBad (topFunctional D) (S d) powerQ)ᶜ) :
    quadratic A b (Program.run (comparisonOracle (quadratic A b)) (algorithm d (beta/mu) R Q (u,w)))-quadratic A b star ≤ epsilon := by
  let kappa:=beta/mu
  let Cmp:=comparisonOracle (quadratic A b)
  have hdpos : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hkp : 0 < kappa := div_pos (hmu.trans_le hbeta) hmu
  have hk : 1 ≤ kappa := (le_div_iff₀ hmu).mpr (by simpa using hbeta)
  have hQ0 : 0 < Q := by linarith
  have hS : 0 < S d := by dsimp [S];positivity
  have hs : 0 < s := by norm_num [s]
  have hqcal : 0 < calibrationQ d := by dsimp [calibrationQ];positivity
  have hqpow : 0 < powerQ := by norm_num [powerQ]
  have hdim : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdpos
  have hSbig : 36 ≤ S d := by
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    dsimp [S]
    linarith
  have hqS : powerQ ≤ Real.sqrt (S d) := by
    have hh : (6:ℝ) ≤ Real.sqrt (S d) := Real.le_sqrt_of_sq_le (by norm_num;exact hSbig)
    exact (by norm_num [powerQ] : powerQ ≤ (6:ℝ)).trans hh
  have hsig:=PaperHeavyBallPowerHorizon.sigma_bounds (S d) powerQ hS hqpow hqS
  have hsigma : 0 < PaperHeavyBallPowerHorizon.sigma (S d) powerQ := hsig.1
  have hsigHalf : PaperHeavyBallPowerHorizon.sigma (S d) powerQ ≤ 1/2 := by linarith [hsig.2.1]
  have heta : 0 < eta d kappa Q := publicEta_positive kappa Q (S d) powerQ hk hQ0 hS hqpow
  have hetaSmall:=publicEta_small kappa Q (S d) powerQ
  have hetaHalf : eta d kappa Q ≤ 1/2 := hetaSmall.1
  have hetaSigma : eta d kappa Q ≤ PaperHeavyBallPowerHorizon.sigma (S d) powerQ/2 := hetaSmall.2.1
  have hAnorm:=norm_upper D hmu
  have hcalprops:=calibration_good_properties (row (basis d) A) s (S d) (calibrationQ d) hu
  have hgeom:=calibration_seed_bounds d (basis d) A mu beta s (S d) (calibrationQ d) hmu hbeta hs hS hqcal.le hlower hupper u hu
  obtain ⟨lambdaHat,hcal,hcalAccuracy⟩:=calibration_from_seed_event d (basis d) A hA b star u mu beta R s (S d)
    (calibrationQ d) (eta d kappa Q) hmu hbeta hR hs hS hqcal heta hetaHalf hlower hupper hAnorm hsol hstar hu
  have hcalAbs : ∀i,|lambdaHat i-scaledDiagonal (basis d) A u i| ≤ eta d kappa Q*scaledDiagonal (basis d) A u i :=
    fun i=>(hcalAccuracy i).2.2
  obtain ⟨hM,hvalues,hcondition,hMlo,hnormB,hnondegenerate⟩:=scaled_data D hmu hbeta u hgeom.1 (S d) hS hgeom.2.1
  have hwprops : ‖w‖^2<S d ∧ powerQ < |topFunctional D w| := by
    simpa only [powerBad,mem_compl_iff,mem_union,mem_setOf_eq,not_or,not_le] using hw
  have hwt : powerQ ≤ |D.basis.repr w D.top| := by
    rw [←topFunctional_apply D w]
    exact hwprops.2.le
  have hpowtol : 0 < powerTolerance d kappa R := by
    dsimp [powerTolerance,powerRootTolerance]
    positivity
  have hprod : ∀v,‖v‖=R→‖Program.run Cmp (productBackend d kappa R lambdaHat v)-scaledOperator A u v‖ ≤ 
      PaperHeavyBallPowerHorizon.sigma (S d) powerQ*‖scaledOperator A u v‖ := by
    intro v hv
    exact productProgram_public_precision (basis d) hd A hA b star u v mu beta R s (S d) (eta d kappa Q)
      (PaperHeavyBallPowerHorizon.sigma (S d) powerQ) (powerTolerance d kappa R) hmu hbeta hR hs hS heta.le hsigma
      hsigHalf hetaSigma hpowtol le_rfl hlower hupper hAnorm hsol hstar hcalprops.1.le hcalprops.2.1.le lambdaHat hcalAbs hv
  let rho:=Program.run Cmp (PaperHeavyBallPowerComplete.estimateProgram (productBackend d kappa R lambdaHat) R (powerCount d) w)
  have hrho:=PaperHeavyBallPowerComplete.estimateProgram_correct Cmp (productBackend d kappa R lambdaHat)
    (scaledOperator A u) D.basis (scaledValues D u) (scaled_eigen D u)
    (scaledMaximum D u) R (S d) powerQ hM hR hS hqpow (fun i=>⟨(hvalues i).1.le,(hvalues i).2⟩)
    hnormB hnondegenerate hprod D.top rfl w hwprops.1.le hwt
  have hrhopos : 0 < rho := (by linarith : 0 < scaledMaximum D u/2).trans_le hrho.1
  have htheta:=publicTheta_bounds kappa hk
  have hgap : 0 < 1-publicTheta kappa := by linarith [htheta.2]
  have hX : 0 ≤ publicX kappa R := by dsimp [publicX];positivity
  have htau : 0 < publicTau kappa R Q (S d) := by dsimp [publicTau,publicDelta];positivity
  have hrestol : 0 < residualTolerance d kappa R Q := by dsimp [residualTolerance,residualRootTolerance];positivity
  have hres : ∀x,‖x‖ ≤ R+publicX kappa R→‖Program.run Cmp (residualBackend d kappa R Q lambdaHat x)-
      (scaledRhs A b u-(scaledOperator A u).toLinearMap x)‖ ≤ 
        eta d kappa Q*‖scaledRhs A b u-(scaledOperator A u).toLinearMap x‖+publicTau kappa R Q (S d) := by
    intro x hx
    exact residualProgram_public_precision (basis d) hd A hA b star u x mu beta R (publicX kappa R) s (S d)
      (eta d kappa Q) (publicTau kappa R Q (S d)) (residualTolerance d kappa R Q) hmu hbeta hR hX hs hS heta.le hetaHalf
      htau.le hrestol le_rfl hlower hupper hAnorm hsol hstar hcalprops.1.le hcalprops.2.1.le lambdaHat hcalAbs hx
  have hBsol : (scaledOperator A u).toLinearMap star=scaledRhs A b u := by
    have hh:=congrArg (fun x : Space d=>(inner ℝ u (A u))⁻¹ •x) hsol
    convert hh using 1 <;> rfl
  have hdist:=publicIterationProgram_correct Cmp (residualBackend d kappa R Q lambdaHat) D.basis (scaledOperator A u).toLinearMap
    (scaledValues D u) (scaled_eigen D u) D.top rho kappa (scaledMaximum D u) R Q (S d) powerQ hk hM hR hQ hS hqpow hMlo
    hrho.1 hrho.2 (fun i=>⟨hcondition i,(hvalues i).2⟩) (scaledRhs A b u) star hBsol hstar hres
  have hcalprime : Program.run Cmp (calibrationProgram (basis d) u kappa R s (S d) (calibrationQ d) (eta d kappa Q))=some lambdaHat := hcal
  have hvalue : Program.run Cmp (algorithm d kappa R Q (u,w))=
      Program.run Cmp (publicIterationProgram (residualBackend d kappa R Q lambdaHat) rho kappa R Q) := by
    simp only [algorithm,Program.run_bind,hcalprime,afterCalibration,Program.run_bind]
    rw [if_pos hrhopos]
  rw [←hvalue] at hdist
  have hh:=PaperHeavyBallObjective.original_accuracy A hA b star _ hsol beta R epsilon Q 0 (hmu.trans_le hbeta) hR heps hQ hQdef hupper hdist
  simpa only [add_zero] using hh

end
end PaperHeavyBallAlgorithm

end SnapshotModule_119
/- END heavy_ball_success -/

/- BEGIN heavy_ball_option_measurable -/
section SnapshotModule_120

namespace PaperSeedBorelTree
open MeasureTheory
noncomputable section

/-- The usual disjoint-union sigma algebra on optional intermediate data. -/
instance optionMeasurableSpace {A : Type} [MeasurableSpace A] : MeasurableSpace (Option A) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0,0} A) inferInstance

lemma measurable_option_some {A : Type} [MeasurableSpace A] : Measurable (some : A→Option A) := by
  change @Measurable A (Option A) _ (MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0,0} A) _) some
  rw [measurable_comap_iff]
  simpa only [Function.comp_def,Equiv.optionEquivSumPUnit_some] using (measurable_inl : Measurable (Sum.inl : A→A⊕PUnit.{1}))

lemma measurable_option_sum {A : Type} [MeasurableSpace A] : Measurable (Equiv.optionEquivSumPUnit.{0,0} A) :=
  Measurable.of_comap_le le_rfl

lemma measurable_option_elim {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (b : B) (f : A→B)
    (hf : Measurable f) : Measurable (fun x : Option A=>x.elim b f) := by
  have hh:= (hf.sumElim (measurable_const : Measurable (fun _ : PUnit.{1}=>b))).comp (measurable_option_sum (A:=A))
  convert hh using 1
  funext x
  cases x <;> rfl

lemma measurable_option_getD {A : Type} [MeasurableSpace A] (a : A) : Measurable (fun x : Option A=>x.getD a) :=
by
  convert measurable_option_elim a id measurable_id using 1
  funext x
  cases x <;> rfl

lemma measurable_option_isSome {A : Type} [MeasurableSpace A] : Measurable (Option.isSome : Option A→Bool) :=
by
  convert measurable_option_elim false (fun _ : A=>true) measurable_const using 1
  funext x
  cases x <;> rfl

end
end PaperSeedBorelTree

end SnapshotModule_120
/- END heavy_ball_option_measurable -/

/- BEGIN heavy_ball_borel_tree -/
section SnapshotModule_121

namespace PaperSeedBorelTree
open Set MeasureTheory PaperOracle
noncomputable section

/-- A finite adaptive oracle computation with explicitly Borel seed dependence.
Each ask consumes one oracle response; each guard consumes no response. -/
inductive Tree (Seed Q Reply A : Type) [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace A] where
  | done (output : Seed→A) (measurable_output : Measurable output)
  | ask (query : Seed→Q) (measurable_query : Measurable query) (next : Reply→Tree Seed Q Reply A)
  | guard (condition : Set Seed) (measurable_condition : MeasurableSet condition)
      (yes no : Tree Seed Q Reply A)

namespace Tree
variable {Seed Seed' Q Reply A B : Type} [MeasurableSpace Seed] [MeasurableSpace Seed']
  [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace B]

def specialize : Tree Seed Q Reply A→Seed→Program Q Reply A
  | .done f _,seed=>.done (f seed)
  | .ask q _ next,seed=>.ask (q seed) (fun r=>specialize (next r) seed)
  | .guard s _ yes no,seed=>by classical exact if seed∈s then specialize yes seed else specialize no seed

def pullback (T : Tree Seed' Q Reply A) (f : Seed→Seed') (hf : Measurable f) : Tree Seed Q Reply A :=
  match T with
  | .done a ha=>.done (a ∘f) (ha.comp hf)
  | .ask q hq next=>.ask (q ∘f) (hq.comp hf) (fun r=>pullback (next r) f hf)
  | .guard s hs yes no=>.guard (f ⁻¹' s) (hs.preimage hf) (pullback yes f hf) (pullback no f hf)

lemma specialize_pullback (T : Tree Seed' Q Reply A) (f : Seed→Seed') (hf : Measurable f) (seed : Seed) :
    specialize (pullback T f hf) seed=specialize T (f seed) := by
  induction T with
  | done a ha=>rfl
  | ask q hq next ih=>simp only [pullback,specialize];congr 1;funext r;exact ih r
  | guard s hs yes no ihy ihn=>
    by_cases h : f seed∈s
    · have hp : seed∈f ⁻¹' s := h
      simp only [pullback,specialize,if_pos h,if_pos hp]
      exact ihy
    · have hp : seed∉f ⁻¹' s := h
      simp only [pullback,specialize,if_neg h,if_neg hp]
      exact ihn

def bind (T : Tree Seed Q Reply A) (next : Tree (Seed×A) Q Reply B) : Tree Seed Q Reply B :=
  match T with
  | .done a ha=>pullback next (fun seed=>(seed,a seed)) (measurable_id.prodMk ha)
  | .ask q hq cont=>.ask q hq (fun r=>bind (cont r) next)
  | .guard s hs yes no=>.guard s hs (bind yes next) (bind no next)

lemma specialize_bind (T : Tree Seed Q Reply A) (next : Tree (Seed×A) Q Reply B) (seed : Seed) :
    specialize (bind T next) seed=Program.bind (specialize T seed) (fun a=>specialize next (seed,a)) := by
  induction T with
  | done a ha=>exact specialize_pullback next _ _ seed
  | ask q hq cont ih=>simp only [bind,specialize,Program.bind];congr 1;funext r;exact ih r
  | guard s hs yes no ihy ihn=>simp only [bind,specialize];split_ifs <;> assumption

def consume (T : Tree Seed Q Reply A) (r : Reply) : Tree Seed Q Reply A :=
  match T with
  | .done a ha=>.done a ha
  | .ask _ _ next=>next r
  | .guard s hs yes no=>.guard s hs (consume yes r) (consume no r)

lemma specialize_consume (T : Tree Seed Q Reply A) (r : Reply) (seed : Seed) :
    specialize (consume T r) seed=PaperProgramBorel.consume (specialize T seed) r := by
  induction T with
  | done a ha=>rfl
  | ask q hq next ih=>rfl
  | guard s hs yes no ihy ihn=>simp only [consume,specialize];split_ifs <;> assumption

def afterReplies (T : Tree Seed Q Reply A) : (t : ℕ)→(Fin t→Reply)→Tree Seed Q Reply A
  | 0,_=>T
  | t+1,h=>consume (afterReplies T t (fun i=>h i.succ)) (h 0)

lemma afterReplies_cons (T : Tree Seed Q Reply A) (t : ℕ) (history : Fin t→Reply) (r : Reply) :
    afterReplies T (t+1) (Fin.cons r history)=consume (afterReplies T t history) r := by
  simp only [afterReplies,Fin.cons_zero,Fin.cons_succ]

lemma specialize_afterReplies (T : Tree Seed Q Reply A) (t : ℕ) (history : Fin t→Reply) (seed : Seed) :
    specialize (afterReplies T t history) seed=PaperProgramBorel.afterReplies (specialize T seed) t history := by
  induction t with
  | zero=>rfl
  | succ t ih=>rw [afterReplies,specialize_consume,ih,PaperProgramBorel.afterReplies]

variable [Inhabited Q] [Inhabited A]

def rootQuery : Tree Seed Q Reply A→Seed→Q
  | .done _ _,_=>default
  | .ask q _ _,seed=>q seed
  | .guard s _ yes no,seed=>by classical exact if seed∈s then rootQuery yes seed else rootQuery no seed

def rootOutput : Tree Seed Q Reply A→Seed→A
  | .done a _,seed=>a seed
  | .ask _ _ _,_=>default
  | .guard s _ yes no,seed=>by classical exact if seed∈s then rootOutput yes seed else rootOutput no seed

def rootStop : Tree Seed Q Reply A→Seed→Bool
  | .done _ _,_=>true
  | .ask _ _ _,_=>false
  | .guard s _ yes no,seed=>by classical exact if seed∈s then rootStop yes seed else rootStop no seed

lemma rootQuery_measurable (T : Tree Seed Q Reply A) : Measurable (rootQuery T) := by
  induction T with
  | done a ha=>exact measurable_const
  | ask q hq next ih=>exact hq
  | guard s hs yes no ihy ihn=>exact Measurable.ite hs ihy ihn

lemma rootOutput_measurable (T : Tree Seed Q Reply A) : Measurable (rootOutput T) := by
  induction T with
  | done a ha=>exact ha
  | ask q hq next ih=>exact measurable_const
  | guard s hs yes no ihy ihn=>exact Measurable.ite hs ihy ihn

lemma rootStop_measurable (T : Tree Seed Q Reply A) : Measurable (rootStop T) := by
  induction T with
  | done a ha=>exact measurable_const
  | ask q hq next ih=>exact measurable_const
  | guard s hs yes no ihy ihn=>exact Measurable.ite hs ihy ihn

lemma root_views (T : Tree Seed Q Reply A) (seed : Seed) :
    rootQuery T seed=(match specialize T seed with | .done _=>default | .ask q _=>q) ∧
    rootOutput T seed=(match specialize T seed with | .done a=>a | .ask _ _=>default) ∧
    rootStop T seed=(match specialize T seed with | .done _=>true | .ask _ _=>false) := by
  induction T with
  | done a ha=>exact ⟨rfl,rfl,rfl⟩
  | ask q hq next ih=>exact ⟨rfl,rfl,rfl⟩
  | guard s hs yes no ihy ihn=>simp only [rootQuery,rootOutput,rootStop,specialize];split_ifs <;> assumption

variable [MeasurableSpace Reply] [Countable Reply] [MeasurableSingletonClass Reply]

def policy (T : Tree Seed Q Reply A) : PaperBorelPolicy.Policy Seed Q Reply A where
  query t st:=rootQuery (afterReplies T t st.2) st.1
  output t st:=rootOutput (afterReplies T t st.2) st.1
  stop t st:=rootStop (afterReplies T t st.2) st.1
  query_measurable t:=measurable_from_prod_countable_left (fun history=>rootQuery_measurable (afterReplies T t history))
  output_measurable t:=measurable_from_prod_countable_left (fun history=>rootOutput_measurable (afterReplies T t history))
  stop_measurable t:=by
    have hm : Measurable (fun st : Seed×(Fin t→Reply)=>rootStop (afterReplies T t st.2) st.1) :=
      measurable_from_prod_countable_left (fun history=>rootStop_measurable (afterReplies T t history))
    exact measurableSet_eq_fun hm measurable_const

lemma policy_unroll (T : Tree Seed Q Reply A) (budget t : ℕ) (seed : Seed) (history : Fin t→Reply) :
    (policy T).unroll budget t (seed,history)=
      PaperProgramBorel.truncate budget (specialize (afterReplies T t history) seed) := by
  induction budget generalizing t with
  | zero=>
    simp only [PaperBorelPolicy.Policy.unroll,policy]
    rw [(root_views (afterReplies T t history) seed).2.1]
    cases specialize (afterReplies T t history) seed <;> rfl
  | succ budget ih=>
    simp only [PaperBorelPolicy.Policy.unroll,policy]
    rw [(root_views (afterReplies T t history) seed).1,(root_views (afterReplies T t history) seed).2.1,(root_views (afterReplies T t history) seed).2.2]
    cases he : specialize (afterReplies T t history) seed with
    | done a=>simp [PaperProgramBorel.truncate]
    | ask q next=>
      simp only [Bool.false_eq_true,↓reduceIte,PaperProgramBorel.truncate]
      congr 1
      funext r
      change (policy T).unroll budget (t+1) (seed,Fin.cons r history)=PaperProgramBorel.truncate budget (next r)
      rw [ih,afterReplies_cons,specialize_consume,he]
      rfl

/-- The resulting total seed/history policy has exactly the same finite oracle
program, so queries, stopping, outputs and public cap are all preserved. -/
theorem full_borel_realization (T : Tree Seed Q Reply A) (budget : ℕ)
    (hcap : ∀seed,Program.Cap budget (specialize T seed)) :
    ∀seed,(policy T).fromSeed budget seed=specialize T seed := by
  intro seed
  rw [PaperBorelPolicy.Policy.fromSeed,policy_unroll]
  exact PaperProgramBorel.truncate_eq budget _ (hcap seed)

end Tree
end
end PaperSeedBorelTree

end SnapshotModule_121
/- END heavy_ball_borel_tree -/

/- BEGIN heavy_ball_borel_root -/
section SnapshotModule_122

namespace PaperHeavyBallBorel
open PaperSeedBorelTree MeasureTheory
noncomputable section
variable {Seed V : Type} [MeasurableSpace Seed]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]
local instance : Inhabited V := ⟨0⟩

/-- The exact public-depth root bisection as a seed-Borel adaptive tree. -/
def bisectTree (z v : Seed→V) (hz : Measurable z) (hv : Measurable v) :
    ℕ→ℝ→ℝ→Tree Seed (V×V) Ordering ℝ
  | 0,l,u=>.done (fun _=>(l+u)/2) measurable_const
  | k+1,l,u=>
    let mid:=(l+u)/2
    .ask (fun seed=>(z seed+(mid-1) •v seed,z seed+(mid+1) •v seed)) (by fun_prop)
      (fun reply=>match reply with
      | .lt=>bisectTree z v hz hv k l mid
      | .eq=>.done (fun _=>mid) measurable_const
      | .gt=>bisectTree z v hz hv k mid u)

lemma specialize_bisectTree (z v : Seed→V) (hz : Measurable z) (hv : Measurable v)
    (k : ℕ) (l u : ℝ) (seed : Seed) :
    Tree.specialize (bisectTree z v hz hv k l u) seed=PaperHeavyBallLine.bisect (z seed) (v seed) k l u := by
  induction k generalizing l u with
  | zero=>rfl
  | succ k ih=>
    simp only [bisectTree,Tree.specialize,PaperHeavyBallLine.bisect]
    congr 1
    funext reply
    cases reply with
    | lt=>exact ih _ _
    | eq=>rfl
    | gt=>exact ih _ _

def rootTree (z v : Seed→V) (hz : Measurable z) (hv : Measurable v) (D tolerance : ℝ) :
    Tree Seed (V×V) Ordering ℝ :=
  bisectTree z v hz hv (PaperHeavyBallLine.horizon D tolerance) (-D) D

lemma specialize_rootTree (z v : Seed→V) (hz : Measurable z) (hv : Measurable v)
    (D tolerance : ℝ) (seed : Seed) :
    Tree.specialize (rootTree z v hz hv D tolerance) seed=
      PaperHeavyBallLine.rootProgram (z seed) (v seed) D tolerance :=
  specialize_bisectTree z v hz hv _ _ _ seed

/-- For every seed and every finite trinary reply history, the actual root
program has Borel queries, outputs and stopping; the entire specialized tree
is identical, including its early equality branch. -/
theorem root_full_borel (z v : Seed→V) (hz : Measurable z) (hv : Measurable v) (D tolerance : ℝ) :
    ∀seed,(Tree.policy (rootTree z v hz hv D tolerance)).fromSeed
      (PaperHeavyBallLine.horizon D tolerance) seed=
      PaperHeavyBallLine.rootProgram (z seed) (v seed) D tolerance := by
  intro seed
  have hh:=Tree.full_borel_realization (rootTree z v hz hv D tolerance)
    (PaperHeavyBallLine.horizon D tolerance) (fun seed=>by
      rw [specialize_rootTree]
      exact PaperHeavyBallLine.bisect_public_cap _ _ _ _ _) seed
  exact hh.trans (specialize_rootTree z v hz hv D tolerance seed)

end
end PaperHeavyBallBorel

end SnapshotModule_122
/- END heavy_ball_borel_root -/

/- BEGIN heavy_ball_borel_collect -/
section SnapshotModule_123

namespace PaperSeedBorelTree
open MeasureTheory
noncomputable section
variable {Seed Q Reply A : Type} [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace A]

/-- Finite coordinate collection as a composable seed-Borel oracle tree. -/
def collectTree : (d : ℕ)→(Fin d→Tree Seed Q Reply A)→Tree Seed Q Reply (Fin d→A)
  | 0,_=>.done (fun _=>Fin.elim0) (by apply measurable_pi_lambda;intro i;exact Fin.elim0 i)
  | d+1,f=>Tree.bind (f 0)
      (Tree.bind (Tree.pullback (collectTree d (fun i=>f i.succ)) Prod.fst measurable_fst)
        (.done (fun st : (Seed×A)×(Fin d→A)=>Fin.cons st.1.2 st.2) (by
          apply measurable_pi_lambda
          intro i
          refine Fin.cases ?_ (fun j=>?_) i
          · exact measurable_snd.comp measurable_fst
          · exact (measurable_pi_apply j).comp measurable_snd)))

end
end PaperSeedBorelTree

end SnapshotModule_123
/- END heavy_ball_borel_collect -/

/- BEGIN heavy_ball_borel_calibration -/
section SnapshotModule_124

namespace PaperHeavyBallBorel
open PaperSeedBorelTree MeasureTheory PaperHeavyBallBackend
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable {d : ℕ}

/-- The actual four-root calibration computation, with all Gaussian-seed query
maps explicitly Borel and no unknown objective data in the tree. -/
def coordinateCalibrationTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R s S q eta : ℝ) (i : Fin d) : Tree V (V×V) Ordering (ℝ×ℝ) :=
  Tree.bind (rootTree (fun _ : V=>(-R) •basis i) id measurable_const measurable_id
    (bracketC kappa R s) (toleranceC kappa R S q eta))
  (Tree.bind (rootTree (fun _ : V×ℝ=>R •basis i) Prod.fst measurable_const measurable_fst
    (bracketC kappa R s) (toleranceC kappa R S q eta))
  (Tree.bind (rootTree (fun st : (V×ℝ)×ℝ=>(-R) •st.1.1) (fun _=>basis i) (by fun_prop) measurable_const
    (bracketE kappa R S) (toleranceE R q eta))
  (Tree.bind (rootTree (fun st : ((V×ℝ)×ℝ)×ℝ=>R •st.1.1.1) (fun _=>basis i) (by fun_prop) measurable_const
    (bracketE kappa R S) (toleranceE R q eta))
  (.done (fun st : (((V×ℝ)×ℝ)×ℝ)×ℝ=>
    ((st.1.1.1.2-st.1.1.2)/(2*R),(st.1.2-st.2)/(2*R))) (by fun_prop)))))

lemma specialize_coordinateCalibrationTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R s S q eta : ℝ) (i : Fin d) (u : V) :
    Tree.specialize (coordinateCalibrationTree basis kappa R s S q eta i) u=
      coordinateCalibration basis u kappa R s S q eta i := by
  simp only [coordinateCalibrationTree,Tree.specialize_bind,specialize_rootTree,Tree.specialize,coordinateCalibration]
  rfl

lemma specialize_collectTree {Seed Q Reply A : Type} [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace A]
    (n : ℕ) (f : Fin n→Tree Seed Q Reply A) (seed : Seed) :
    Tree.specialize (collectTree n f) seed=collect n (fun i=>Tree.specialize (f i) seed) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [collectTree,Tree.specialize_bind,Tree.specialize_pullback,Tree.specialize,collect]
    congr 1
    funext first
    rw [ih]

lemma calibrationValid_measurable : MeasurableSet
    {st : V×(Fin d→ℝ×ℝ) | ∀i,(st.2 i).2≠0 ∧ 0 < (st.2 i).1/(st.2 i).2} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun (by fun_prop : Measurable (fun st : V×(Fin d→ℝ×ℝ)=>(st.2 i).2)) measurable_const).compl.inter
    (measurableSet_lt measurable_const (by fun_prop : Measurable (fun st : V×(Fin d→ℝ×ℝ)=>(st.2 i).1/(st.2 i).2)))

def calibrationTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R s S q eta : ℝ) : Tree V (V×V) Ordering (Option (Fin d→ℝ)) :=
  .guard {u : V | s ≤ ‖u‖ ∧ ‖u‖ ≤ Real.sqrt S}
    ((measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const))
    (Tree.bind (collectTree d (coordinateCalibrationTree basis kappa R s S q eta))
      (.guard {st : V×(Fin d→ℝ×ℝ) | ∀i,(st.2 i).2≠0 ∧ 0 < (st.2 i).1/(st.2 i).2} calibrationValid_measurable
        (.done (fun st=>some (fun i=>(st.2 i).1/(st.2 i).2)) (by
          apply measurable_option_some.comp
          apply measurable_pi_lambda
          intro i
          fun_prop))
        (.done (fun _=>none) measurable_const)))
    (.done (fun _=>none) measurable_const)

lemma specialize_calibrationTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R s S q eta : ℝ) (u : V) :
    Tree.specialize (calibrationTree basis kappa R s S q eta) u=
      calibrationProgram basis u kappa R s S q eta := by
  classical
  simp only [calibrationTree,Tree.specialize,Set.mem_setOf_eq,calibrationProgram]
  split_ifs
  · rw [Tree.specialize_bind,specialize_collectTree]
    simp only [specialize_coordinateCalibrationTree]
    congr 1
    funext reading
    simp only [Tree.specialize,Set.mem_setOf_eq]
  · rfl

local instance : Inhabited V := ⟨0⟩

/-- The literal calibration Program, including both public guards, is a total
Borel adaptive policy on the Gaussian seed and every trinary reply history. -/
theorem calibration_full_borel (basis : OrthonormalBasis (Fin d) ℝ V) (kappa R s S q eta : ℝ) :
    ∀u,(Tree.policy (calibrationTree basis kappa R s S q eta)).fromSeed
      (d*coordinateCost kappa R s S q eta) u=calibrationProgram basis u kappa R s S q eta := by
  intro u
  have hh:=Tree.full_borel_realization (calibrationTree basis kappa R s S q eta)
    (d*coordinateCost kappa R s S q eta) (fun u=>by
      rw [specialize_calibrationTree]
      exact calibrationProgram_cap basis u kappa R s S q eta) u
  exact hh.trans (specialize_calibrationTree basis kappa R s S q eta u)

end
end PaperHeavyBallBorel

end SnapshotModule_124
/- END heavy_ball_borel_calibration -/

/- BEGIN heavy_ball_borel_products -/
section SnapshotModule_125

namespace PaperHeavyBallBorel
open PaperSeedBorelTree MeasureTheory PaperHeavyBallBackend
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable {d : ℕ}

lemma measurable_assemble (basis : OrthonormalBasis (Fin d) ℝ V) : Measurable (assemble basis) :=
  basis.repr.symm.continuous.measurable.comp (WithLp.measurable_toLp 2 _)

def coordinateProductTree (basis : OrthonormalBasis (Fin d) ℝ V) (kappa R delta : ℝ) (i : Fin d) :
    Tree ((Fin d→ℝ)×V) (V×V) Ordering ℝ :=
  Tree.bind (rootTree (fun _ : (Fin d→ℝ)×V=>0) (fun _=>basis i) measurable_const measurable_const
      (productBracket kappa R) delta)
    (Tree.bind (rootTree (fun st : ((Fin d→ℝ)×V)×ℝ=>st.1.2) (fun _=>basis i) (by fun_prop) measurable_const
      (productBracket kappa R) delta)
      (.done (fun st : (((Fin d→ℝ)×V)×ℝ)×ℝ=>st.1.2-st.2) (by fun_prop)))

lemma specialize_coordinateProductTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R delta : ℝ) (i : Fin d) (lambdaHat : Fin d→ℝ) (v : V) :
    Tree.specialize (coordinateProductTree basis kappa R delta i) (lambdaHat,v)=
      coordinateProduct basis v kappa R delta i := by
  simp only [coordinateProductTree,Tree.specialize_bind,specialize_rootTree,Tree.specialize,coordinateProduct]

def productTree (basis : OrthonormalBasis (Fin d) ℝ V) (kappa R delta : ℝ) :
    Tree ((Fin d→ℝ)×V) (V×V) Ordering V :=
  .guard {st | ‖st.2‖ ≤ R} (measurableSet_le (by fun_prop) measurable_const)
    (Tree.bind (collectTree d (coordinateProductTree basis kappa R delta))
      (.done (fun st : ((Fin d→ℝ)×V)×(Fin d→ℝ)=>assemble basis (fun i=>st.1.1 i*st.2 i)) (by
        apply (measurable_assemble basis).comp
        fun_prop)))
    (.done (fun _=>0) measurable_const)

lemma specialize_productTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R delta : ℝ) (lambdaHat : Fin d→ℝ) (v : V) :
    Tree.specialize (productTree basis kappa R delta) (lambdaHat,v)=
      productProgram basis lambdaHat v kappa R delta := by
  classical
  simp only [productTree,Tree.specialize,Set.mem_setOf_eq,productProgram]
  split_ifs
  · rw [Tree.specialize_bind,specialize_collectTree]
    simp only [specialize_coordinateProductTree,Tree.specialize]
  · rfl

def residualTree (basis : OrthonormalBasis (Fin d) ℝ V) (kappa R X delta : ℝ) :
    Tree ((Fin d→ℝ)×V) (V×V) Ordering V :=
  .guard {st | ‖st.2‖ ≤ R+X} (measurableSet_le (by fun_prop) measurable_const)
    (Tree.bind (collectTree d (fun i=>rootTree (Prod.snd : ((Fin d→ℝ)×V)→V) (fun _=>basis i)
      measurable_snd measurable_const (residualBracket kappa R X) delta))
      (.done (fun st : ((Fin d→ℝ)×V)×(Fin d→ℝ)=>assemble basis (fun i=>st.1.1 i*st.2 i)) (by
        apply (measurable_assemble basis).comp
        fun_prop)))
    (.done (fun _=>0) measurable_const)

lemma specialize_residualTree (basis : OrthonormalBasis (Fin d) ℝ V)
    (kappa R X delta : ℝ) (lambdaHat : Fin d→ℝ) (z : V) :
    Tree.specialize (residualTree basis kappa R X delta) (lambdaHat,z)=
      residualProgram basis lambdaHat z kappa R X delta := by
  classical
  simp only [residualTree,Tree.specialize,Set.mem_setOf_eq,residualProgram]
  split_ifs
  · rw [Tree.specialize_bind,specialize_collectTree]
    simp only [specialize_rootTree,Tree.specialize]
  · rfl

local instance : Inhabited V := ⟨0⟩

/-- Actual finite product and residual programs preserve the whole Borel
seed/history policy, with the same public cap and both norm fallback guards. -/
theorem product_full_borel (basis : OrthonormalBasis (Fin d) ℝ V) (kappa R delta : ℝ) :
    ∀st,(Tree.policy (productTree basis kappa R delta)).fromSeed (productCost d kappa R delta) st=
      productProgram basis st.1 st.2 kappa R delta := by
  intro st
  have hh:=Tree.full_borel_realization (productTree basis kappa R delta) (productCost d kappa R delta) (fun st=>by
    rw [specialize_productTree]
    exact productProgram_cap basis st.1 st.2 kappa R delta) st
  exact hh.trans (specialize_productTree basis kappa R delta st.1 st.2)

theorem residual_full_borel (basis : OrthonormalBasis (Fin d) ℝ V) (kappa R X delta : ℝ) :
    ∀st,(Tree.policy (residualTree basis kappa R X delta)).fromSeed (residualCost d kappa R X delta) st=
      residualProgram basis st.1 st.2 kappa R X delta := by
  intro st
  have hh:=Tree.full_borel_realization (residualTree basis kappa R X delta) (residualCost d kappa R X delta) (fun st=>by
    rw [specialize_residualTree]
    exact residualProgram_cap basis st.1 st.2 kappa R X delta) st
  exact hh.trans (specialize_residualTree basis kappa R X delta st.1 st.2)

end
end PaperHeavyBallBorel

end SnapshotModule_125
/- END heavy_ball_borel_products -/

/- BEGIN heavy_ball_borel_power -/
section SnapshotModule_126

namespace PaperHeavyBallBorel
open PaperSeedBorelTree MeasureTheory
noncomputable section
variable {Seed V Q Reply : Type} [MeasurableSpace Seed] [MeasurableSpace Q]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

lemma measurable_normalize : Measurable (NormedSpace.normalize : V→V) := by
  unfold NormedSpace.normalize
  fun_prop

/-- Composable Borel power loop, including zero-product fallback. -/
def powerTree (product : Tree (Seed×V) Q Reply V) (R : ℝ) : ℕ→Tree (Seed×V) Q Reply V
  | 0=>.done Prod.snd measurable_snd
  | k+1=>Tree.bind product
      (.guard {st : (Seed×V)×V | st.2=0} (measurableSet_eq_fun measurable_snd measurable_const)
        (.done (fun _=>0) measurable_const)
        (Tree.pullback (powerTree product R k)
          (fun st : (Seed×V)×V=>(st.1.1,R •NormedSpace.normalize st.2)) (by
            exact (measurable_fst.comp measurable_fst).prodMk
              ((measurable_normalize.comp measurable_snd).const_smul R))))

lemma specialize_powerTree (product : Tree (Seed×V) Q Reply V) (R : ℝ) (k : ℕ) (seed : Seed) (v : V) :
    Tree.specialize (powerTree product R k) (seed,v)=
      PaperHeavyBallPower.powerProgram (fun x=>Tree.specialize product (seed,x)) R k v := by
  induction k generalizing v with
  | zero=>rfl
  | succ k ih=>
    rw [powerTree,Tree.specialize_bind]
    simp only [PaperHeavyBallPower.powerProgram]
    congr 1
    funext image
    simp only [Tree.specialize,Set.mem_setOf_eq]
    split_ifs
    · rfl
    · rw [Tree.specialize_pullback,ih]

end
end PaperHeavyBallBorel

end SnapshotModule_126
/- END heavy_ball_borel_power -/

/- BEGIN heavy_ball_borel_iteration -/
section SnapshotModule_127

namespace PaperHeavyBallBorel
open PaperSeedBorelTree MeasureTheory
noncomputable section
variable {Seed V Q Reply : Type} [MeasurableSpace Seed] [MeasurableSpace Q]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

/-- Borel physical heavy-ball loop, including public seed-dependent step
parameters and the actual iterate norm fallback guard. -/
def iterationLoopTree (estimate : Tree (Seed×V) Q Reply V)
    (alpha theta guard : Seed→ℝ) (ha : Measurable alpha) (ht : Measurable theta) (hg : Measurable guard) :
    ℕ→Tree (Seed×(V×V)) Q Reply (V×V)
  | 0=>.done Prod.snd measurable_snd
  | k+1=>.guard {st : Seed×(V×V) | ‖st.2.2‖ ≤ guard st.1} (measurableSet_le (by fun_prop) (hg.comp measurable_fst))
      (Tree.bind (Tree.pullback estimate (fun st : Seed×(V×V)=>(st.1,st.2.2)) (by fun_prop))
        (Tree.pullback (iterationLoopTree estimate alpha theta guard ha ht hg k)
          (fun st : (Seed×(V×V))×V=>(st.1.1,
            PaperHeavyBallProgram.nextState (alpha st.1.1) (theta st.1.1) st.1.2 st.2)) (by
              unfold PaperHeavyBallProgram.nextState
              fun_prop)))
      (.done (fun _=>(0,0)) measurable_const)

lemma specialize_iterationLoopTree (estimate : Tree (Seed×V) Q Reply V)
    (alpha theta guard : Seed→ℝ) (ha : Measurable alpha) (ht : Measurable theta) (hg : Measurable guard)
    (k : ℕ) (seed : Seed) (p : V×V) :
    Tree.specialize (iterationLoopTree estimate alpha theta guard ha ht hg k) (seed,p)=
      PaperHeavyBallProgram.loopProgram (fun x=>Tree.specialize estimate (seed,x))
        (alpha seed) (theta seed) (guard seed) k p := by
  induction k generalizing p with
  | zero=>rfl
  | succ k ih=>
    simp only [iterationLoopTree,Tree.specialize,Set.mem_setOf_eq,PaperHeavyBallProgram.loopProgram]
    split_ifs
    · rw [Tree.specialize_bind,Tree.specialize_pullback]
      congr 1
      funext residual
      rw [Tree.specialize_pullback,ih]
    · rfl

def iterationTree (estimate : Tree (Seed×V) Q Reply V)
    (alpha theta guard : Seed→ℝ) (ha : Measurable alpha) (ht : Measurable theta) (hg : Measurable guard) (k : ℕ) :
    Tree Seed Q Reply V :=
  Tree.bind (Tree.pullback (iterationLoopTree estimate alpha theta guard ha ht hg k)
    (fun seed=>(seed,(0,0))) (by fun_prop))
    (.done (fun st : Seed×(V×V)=>st.2.2) (by fun_prop))

lemma specialize_iterationTree (estimate : Tree (Seed×V) Q Reply V)
    (alpha theta guard : Seed→ℝ) (ha : Measurable alpha) (ht : Measurable theta) (hg : Measurable guard)
    (k : ℕ) (seed : Seed) :
    Tree.specialize (iterationTree estimate alpha theta guard ha ht hg k) seed=
      PaperHeavyBallProgram.program (fun x=>Tree.specialize estimate (seed,x))
        (alpha seed) (theta seed) (guard seed) k := by
  rw [iterationTree,Tree.specialize_bind,Tree.specialize_pullback,specialize_iterationLoopTree]
  rfl

variable [MeasurableSpace Reply] [Countable Reply] [MeasurableSingletonClass Reply] [Inhabited Q]
local instance : Inhabited V := ⟨0⟩

/-- The actual finite heavy-ball loop admits a total Borel finite-history policy
with identical queries, stopping and postprocessing on every seed. -/
theorem iteration_full_borel (estimate : Tree (Seed×V) Q Reply V)
    (alpha theta guard : Seed→ℝ) (ha : Measurable alpha) (ht : Measurable theta) (hg : Measurable guard)
    (k budget : ℕ) (hbudget : ∀seed x,PaperOracle.Program.Cap budget (Tree.specialize estimate (seed,x))) :
    ∀seed,(Tree.policy (iterationTree estimate alpha theta guard ha ht hg k)).fromSeed (k*budget) seed=
      PaperHeavyBallProgram.program (fun x=>Tree.specialize estimate (seed,x))
        (alpha seed) (theta seed) (guard seed) k := by
  intro seed
  have hh:=Tree.full_borel_realization (iterationTree estimate alpha theta guard ha ht hg k) (k*budget) (fun seed=>by
    rw [specialize_iterationTree]
    exact PaperHeavyBallProgram.program_cap _ _ _ _ budget (hbudget seed) k) seed
  exact hh.trans (specialize_iterationTree estimate alpha theta guard ha ht hg k seed)

end
end PaperHeavyBallBorel

end SnapshotModule_127
/- END heavy_ball_borel_iteration -/

/- BEGIN heavy_ball_borel_algorithm -/
section SnapshotModule_128

namespace PaperHeavyBallAlgorithmBorel
open PaperHeavyBallBorel PaperSeedBorelTree PaperHeavyBallBackend PaperHeavyBallAlgorithm MeasureTheory
noncomputable section

abbrev Lambda (d : ℕ) := Fin d→ℝ

def scaleEstimateTree (d : ℕ) (kappa R : ℝ) :
    Tree (Lambda d×Space d) (Space d×Space d) Ordering ℝ :=
  Tree.bind (Tree.pullback (powerTree (productTree (basis d) kappa R (powerTolerance d kappa R)) R (powerCount d))
    (fun st : Lambda d×Space d=>(st.1,R •NormedSpace.normalize st.2)) (by
      exact measurable_fst.prodMk ((measurable_normalize.comp measurable_snd).const_smul R)))
    (Tree.bind (Tree.pullback (productTree (basis d) kappa R (powerTolerance d kappa R))
      (fun st : (Lambda d×Space d)×Space d=>(st.1.1,st.2)) (by fun_prop))
      (.done (fun st : ((Lambda d×Space d)×Space d)×Space d=>inner ℝ st.1.2 st.2/R^2) (by fun_prop)))

lemma specialize_scaleEstimateTree (d : ℕ) (kappa R : ℝ) (lambdaHat : Lambda d) (w : Space d) :
    Tree.specialize (scaleEstimateTree d kappa R) (lambdaHat,w)=
      PaperHeavyBallPowerComplete.estimateProgram (productBackend d kappa R lambdaHat) R (powerCount d) w := by
  simp only [scaleEstimateTree,Tree.specialize_bind,Tree.specialize_pullback,specialize_powerTree,
    specialize_productTree,Tree.specialize,PaperHeavyBallPowerComplete.estimateProgram,productBackend]
  rfl

def heavyTree (d : ℕ) (kappa R Q : ℝ) : Tree (Lambda d×ℝ) (Space d×Space d) Ordering (Space d) :=
  iterationTree
    (Tree.pullback (residualTree (basis d) kappa R (PaperHeavyBallPublic.publicX kappa R) (residualTolerance d kappa R Q))
      (fun st : (Lambda d×ℝ)×Space d=>(st.1.1,st.2)) (by fun_prop))
    (fun st : Lambda d×ℝ=>PaperHeavyBallParameters.alpha (st.2/(4*kappa)) (2*st.2))
    (fun _=>PaperHeavyBallPublic.publicTheta kappa)
    (fun _=>R+PaperHeavyBallPublic.publicX kappa R)
    (by unfold PaperHeavyBallParameters.alpha;fun_prop) measurable_const measurable_const (heavyCount kappa R Q)

lemma specialize_heavyTree (d : ℕ) (kappa R Q rho : ℝ) (lambdaHat : Lambda d) :
    Tree.specialize (heavyTree d kappa R Q) (lambdaHat,rho)=
      PaperHeavyBallPublic.publicIterationProgram (residualBackend d kappa R Q lambdaHat) rho kappa R Q := by
  simp only [heavyTree,specialize_iterationTree,Tree.specialize_pullback,specialize_residualTree,
    PaperHeavyBallPublic.publicIterationProgram,residualBackend,heavyCount]
  rfl

def afterCalibrationTree (d : ℕ) (kappa R Q : ℝ) :
    Tree (Lambda d×Space d) (Space d×Space d) Ordering (Space d) :=
  Tree.bind (scaleEstimateTree d kappa R)
    (.guard {st : (Lambda d×Space d)×ℝ | 0 < st.2} (measurableSet_lt measurable_const measurable_snd)
      (Tree.pullback (heavyTree d kappa R Q) (fun st : (Lambda d×Space d)×ℝ=>(st.1.1,st.2)) (by fun_prop))
      (.done (fun _=>0) measurable_const))

lemma specialize_afterCalibrationTree (d : ℕ) (kappa R Q : ℝ) (lambdaHat : Lambda d) (w : Space d) :
    Tree.specialize (afterCalibrationTree d kappa R Q) (lambdaHat,w)=afterCalibration d kappa R Q lambdaHat w := by
  simp only [afterCalibrationTree,Tree.specialize_bind,specialize_scaleEstimateTree,afterCalibration]
  congr 1
  funext rho
  simp only [Tree.specialize,Set.mem_setOf_eq]
  split_ifs
  · rw [Tree.specialize_pullback,specialize_heavyTree]
  · rfl

def algorithmTree (d : ℕ) (kappa R Q : ℝ) : Tree (Seed d) (Space d×Space d) Ordering (Space d) :=
  Tree.bind (Tree.pullback (calibrationTree (basis d) kappa R s (S d) (calibrationQ d) (eta d kappa Q))
    (Prod.fst : Seed d→Space d) measurable_fst)
    (.guard {st : Seed d×Option (Lambda d) | st.2.isSome=true}
      (measurableSet_eq_fun (measurable_option_isSome.comp measurable_snd) measurable_const)
      (Tree.pullback (afterCalibrationTree d kappa R Q)
        (fun st : Seed d×Option (Lambda d)=>(st.2.getD (fun _=>0),st.1.2)) (by
          exact ((measurable_option_getD (fun _ : Fin d=>0)).comp measurable_snd).prodMk
            (measurable_snd.comp measurable_fst)))
      (.done (fun _=>0) measurable_const))

lemma specialize_algorithmTree (d : ℕ) (kappa R Q : ℝ) (seed : Seed d) :
    Tree.specialize (algorithmTree d kappa R Q) seed=algorithm d kappa R Q seed := by
  rw [algorithmTree,Tree.specialize_bind,Tree.specialize_pullback,specialize_calibrationTree]
  unfold algorithm
  congr 1
  funext result
  cases result with
  | none=>simp only [Tree.specialize,Set.mem_setOf_eq,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  | some lambdaHat=>
    simp only [Tree.specialize,Set.mem_setOf_eq,Option.isSome_some,↓reduceIte]
    rw [Tree.specialize_pullback]
    exact specialize_afterCalibrationTree d kappa R Q lambdaHat seed.2

local instance {d : ℕ} : Inhabited (Space d) := ⟨0⟩

/-- Complete seed/history Borel legality of the actually executed randomized
algorithm: queries, early stops and outputs match on every seed and every reply tree. -/
theorem algorithm_full_borel (d : ℕ) (kappa R Q : ℝ) :
    ∀seed,(Tree.policy (algorithmTree d kappa R Q)).fromSeed (totalCap d kappa R Q) seed=algorithm d kappa R Q seed := by
  intro seed
  have hh:=Tree.full_borel_realization (algorithmTree d kappa R Q) (totalCap d kappa R Q) (fun seed=>by
    rw [specialize_algorithmTree]
    exact algorithm_cap d kappa R Q seed) seed
  exact hh.trans (specialize_algorithmTree d kappa R Q seed)

lemma algorithm_output_measurable (d : ℕ) (kappa R Q : ℝ) (f : Space d→ℝ) (hf : Measurable f) :
    Measurable (fun seed=>PaperOracle.Program.run (PaperOracle.comparisonOracle f) (algorithm d kappa R Q seed)) := by
  have hh:=(Tree.policy (algorithmTree d kappa R Q)).fixed_oracle_output_measurable
    (PaperOracle.comparisonOracle f) (PaperBorelPolicy.comparisonOracle_measurable f hf) (totalCap d kappa R Q)
  convert hh using 1
  funext seed
  rw [algorithm_full_borel]

end
end PaperHeavyBallAlgorithmBorel

end SnapshotModule_128
/- END heavy_ball_borel_algorithm -/

/- BEGIN heavy_ball_probability -/
section SnapshotModule_129

namespace PaperHeavyBallAlgorithm
open Set MeasureTheory ProbabilityTheory PaperOracle PaperHeavyBallGaussian PaperHeavyBallScale PaperHeavyBallSpectral PaperHeavyBallLine
open PaperHeavyBallAlgorithmBorel
open scoped ENNReal NNReal
noncomputable section

def seedLaw (d : ℕ) : Measure (Seed d) := (stdGaussian (Space d)).prod (stdGaussian (Space d))

instance seedLaw_probability (d : ℕ) : IsProbabilityMeasure (seedLaw d) := inferInstanceAs (IsProbabilityMeasure ((stdGaussian (Space d)).prod (stdGaussian (Space d))))

def goodSeeds (d : ℕ) (A : Space d→L[ℝ] Space d) {mu beta : ℝ} (D : Data d A mu beta) : Set (Seed d) :=
  (calibrationBad (row (basis d) A) s (S d) (calibrationQ d))ᶜ ×ˢ
    (powerBad (topFunctional D) (S d) powerQ)ᶜ

lemma goodSeeds_measurable (d : ℕ) (A : Space d→L[ℝ] Space d) {mu beta : ℝ} (D : Data d A mu beta) :
    MeasurableSet (goodSeeds d A D) :=
  (calibrationBad_measurable _ _ _ _).compl.prod (powerBad_measurable _ _ _).compl

/-- Actual independent standard Gaussian probability of both complete good events. -/
lemma goodSeeds_probability (d : ℕ) (hd : 0 < d) (A : Space d→L[ℝ] Space d) (mu beta : ℝ)
    (hmu : 0 < mu) (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (D : Data d A mu beta) :
    (2/3:ℝ) ≤ (seedLaw d).real (goodSeeds d A D) := by
  have hh:=independent_good_probability d hd (row (basis d) A) (row_ne_zero (basis d) A mu hmu hlower)
    (topFunctional D) (topFunctional_norm D)
  have hS : 12*(d:ℝ)/(1/3:ℝ)=S d := by dsimp [S];ring
  have hs : (1/3:ℝ)/24=s := by norm_num [s]
  have hq : (1/3:ℝ)/(12*(d:ℝ))=calibrationQ d := by dsimp [calibrationQ];field_simp;ring
  have hq0 : (1/3:ℝ)/12=powerQ := by norm_num [powerQ]
  rw [hS,hs,hq,hq0] at hh
  exact hh

/-- The fully instantiated comparison algorithm has per-instance success at least
2/3 under its actual double-Gaussian law, a measurable success event, an exact
whole-program Borel policy, and a deterministic cap on all seeds/reply branches. -/
theorem actual_algorithm_probability (d : ℕ) (hd : 0 < d)
    (A : Space d→L[ℝ] Space d) (hA : A.toLinearMap.IsSymmetric) (b star : Space d)
    (mu beta R epsilon Q c0 : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQ : 32 ≤ Q) (hQdef : Q=beta*R^2/epsilon)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) :
    let f:=fun x=>quadratic A b x+c0
    let event:={seed : Seed d | f (Program.run (comparisonOracle f) (algorithm d (beta/mu) R Q seed))-f star ≤ epsilon}
    MeasurableSet event ∧ (2/3:ℝ≥0∞) ≤ seedLaw d event ∧
      (∀seed,Program.Cap (totalCap d (beta/mu) R Q) (algorithm d (beta/mu) R Q seed)) ∧
      (∀seed,(PaperSeedBorelTree.Tree.policy (PaperHeavyBallAlgorithmBorel.algorithmTree d (beta/mu) R Q)).fromSeed
        (totalCap d (beta/mu) R Q) seed=algorithm d (beta/mu) R Q seed) := by
  let f:=fun x=>quadratic A b x+c0
  let event:={seed : Seed d | f (Program.run (comparisonOracle f) (algorithm d (beta/mu) R Q seed))-f star ≤ epsilon}
  have hf : Measurable f := by unfold f quadratic;fun_prop
  have hOut:=algorithm_output_measurable d (beta/mu) R Q f hf
  have hEvent : MeasurableSet event := measurableSet_le ((hf.comp hOut).sub_const (f star)) measurable_const
  obtain ⟨D⟩:=exists_data d hd A hA mu beta hlower hupper
  have hgood:=goodSeeds_probability d hd A mu beta hmu hlower D
  have hsub : goodSeeds d A D⊆event := by
    intro seed hseed
    have hh:=good_seed_accuracy d hd A hA b star mu beta R epsilon Q hmu hbeta hR heps hQ hQdef hlower hupper hsol hstar
      D seed.1 seed.2 hseed.1 hseed.2
    have hOracle : comparisonOracle f=comparisonOracle (quadratic A b) := PaperHeavyBallObjective.comparison_add_const _ c0
    change f (Program.run (comparisonOracle f) (algorithm d (beta/mu) R Q seed))-f star ≤ epsilon
    rw [hOracle]
    dsimp [f]
    convert hh using 1 <;> ring
  have hmono:=ENNReal.toReal_mono (measure_ne_top (seedLaw d) event) (measure_mono hsub)
  have hReal : (2/3:ℝ) ≤ (seedLaw d).real event := hgood.trans hmono
  have hProb : (2/3:ℝ≥0∞) ≤ seedLaw d event := by
    apply (ENNReal.toReal_le_toReal (by finiteness : (2/3:ℝ≥0∞)≠⊤) (measure_ne_top (seedLaw d) event)).mp
    norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
    exact hReal
  exact ⟨hEvent,hProb,algorithm_cap d (beta/mu) R Q,algorithm_full_borel d (beta/mu) R Q⟩

end
end PaperHeavyBallAlgorithm

end SnapshotModule_129
/- END heavy_ball_probability -/

/- BEGIN heavy_ball_root_ratios -/
section SnapshotModule_130

namespace PaperHeavyBallRootRatios
open PaperHeavyBallAlgorithm PaperHeavyBallBackend PaperHeavyBallPublic
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def commonRatio (d : ℕ) (kappa Q : ℝ) : ℝ := (1000000000:ℝ)*kappa^3*(d:ℝ)^2/(eta d kappa Q)

/-- Each actual finite bisection has a precision-to-bracket ratio bounded by
one public expression, independent of the physical radius R. -/
theorem all_root_ratios (d : ℕ) (hd : 0 < d) (kappa R Q : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) (hQ : 32 ≤ Q) :
    bracketC kappa R s/toleranceC kappa R (S d) (calibrationQ d) (eta d kappa Q) ≤ commonRatio d kappa Q ∧
    bracketE kappa R (S d)/toleranceE R (calibrationQ d) (eta d kappa Q) ≤ commonRatio d kappa Q ∧
    productBracket kappa R/powerTolerance d kappa R ≤ commonRatio d kappa Q ∧
    residualBracket kappa R (publicX kappa R)/residualTolerance d kappa R Q ≤ commonRatio d kappa Q := by
  have hdpos : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hkp : 0 < kappa := by linarith
  have hQpos : 0 < Q := by linarith
  have hS : 0 < S d := by dsimp [S];positivity
  have hs : 0 < s := by norm_num [s]
  have hq : 0 < calibrationQ d := by dsimp [calibrationQ];positivity
  have hq0 : 0 < powerQ := by norm_num [powerQ]
  have ht:=publicTheta_bounds kappa hk
  have hgap : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have hgap1 : 1-publicTheta kappa ≤ 1 := by linarith [ht.1]
  have hsqrtQ : 0 < Real.sqrt (2/Q) := Real.sqrt_pos.mpr (by positivity)
  have hsqrtd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdpos
  have heta : 0 < eta d kappa Q := publicEta_positive kappa Q (S d) powerQ hk hQpos hS hq0
  have hrootd : Real.sqrt (d:ℝ) ≤ d := by
    nlinarith [Real.sq_sqrt hdpos.le,Real.sqrt_nonneg (d:ℝ)]
  have hrootS : Real.sqrt (S d) ≤ 6*(d:ℝ) := by
    have hsq:=Real.sq_sqrt hS.le
    dsimp [S] at hsq ⊢
    nlinarith [Real.sqrt_nonneg (36*(d:ℝ))]
  have hqS : powerQ ≤ Real.sqrt (S d) := by
    have hSbig : 36 ≤ S d := by dsimp [S];linarith
    have hh : (6:ℝ) ≤ Real.sqrt (S d) := Real.le_sqrt_of_sq_le (by norm_num;exact hSbig)
    exact (by norm_num [powerQ] : powerQ ≤ (6:ℝ)).trans hh
  have hsig:=PaperHeavyBallPowerHorizon.sigma_bounds (S d) powerQ hS hq0 hqS
  have hsigma : 0 < PaperHeavyBallPowerHorizon.sigma (S d) powerQ := hsig.1
  have heSmall:=publicEta_small kappa Q (S d) powerQ
  have hetaSigma : eta d kappa Q ≤ PaperHeavyBallPowerHorizon.sigma (S d) powerQ := by
    dsimp only [eta]
    linarith [heSmall.2.1]
  have hetaDen : eta d kappa Q ≤ (1-publicTheta kappa)^3*Real.sqrt (2/Q) := by
    dsimp only [eta]
    have hh:=heSmall.2.2
    have hp : 0 ≤ (1-publicTheta kappa)^3*Real.sqrt (2/Q) := by positivity
    linarith
  have htau : 0 < publicTau kappa R Q (S d) := by dsimp [publicTau,publicDelta];positivity
  have hkpow : kappa^2 ≤ kappa^3 := by nlinarith [mul_nonneg (sq_nonneg kappa) (sub_nonneg.mpr hk)]
  have hdk : 0 ≤ kappa^3*(d:ℝ)^2 := by positivity
  have hCeq : bracketC kappa R s/toleranceC kappa R (S d) (calibrationQ d) (eta d kappa Q)=
      746496*kappa^2*(d:ℝ)^2/(eta d kappa Q) := by
    rw [calibrationC_scale_cancels kappa R s (S d) (calibrationQ d) (eta d kappa Q) hkp hR hs hS hq heta]
    dsimp [S,s,calibrationQ]
    field_simp
    <;> ring
  have hC : bracketC kappa R s/toleranceC kappa R (S d) (calibrationQ d) (eta d kappa Q) ≤ commonRatio d kappa Q := by
    rw [hCeq]
    unfold commonRatio
    apply div_le_div_of_nonneg_right _ heta.le
    have hh:=mul_le_mul_of_nonneg_right hkpow (sq_nonneg (d:ℝ))
    nlinarith
  have hEeq : bracketE kappa R (S d)/toleranceE R (calibrationQ d) (eta d kappa Q)=
      144*kappa*(d:ℝ)*(Real.sqrt (S d)+1)/(eta d kappa Q) := by
    rw [calibrationE_scale_cancels kappa R (S d) (calibrationQ d) (eta d kappa Q) hkp hR hq heta]
    dsimp [calibrationQ]
    field_simp
    <;> ring
  have hE : bracketE kappa R (S d)/toleranceE R (calibrationQ d) (eta d kappa Q) ≤ commonRatio d kappa Q := by
    rw [hEeq]
    unfold commonRatio
    apply div_le_div_of_nonneg_right _ heta.le
    have hh:=mul_le_mul_of_nonneg_left (show Real.sqrt (S d)+1 ≤ 7*(d:ℝ) by linarith) (show 0 ≤ 144*kappa*(d:ℝ) by positivity)
    have hk3 : kappa ≤ kappa^3 := by nlinarith
    have hh2:=mul_le_mul_of_nonneg_right hk3 (sq_nonneg (d:ℝ))
    nlinarith
  have hPeq : productBracket kappa R/powerTolerance d kappa R=
      2985984*kappa^3*(d:ℝ)*Real.sqrt (d:ℝ)/(PaperHeavyBallPowerHorizon.sigma (S d) powerQ) := by
    rw [powerTolerance,product_precision_scale_cancels d hd kappa R s (S d) _ hkp hR hs hS hsigma]
    dsimp [S,s]
    ring
  have hP : productBracket kappa R/powerTolerance d kappa R ≤ commonRatio d kappa Q := by
    rw [hPeq]
    unfold commonRatio
    apply div_le_div₀ (by positivity) _ heta hetaSigma
    have hh:=mul_le_mul_of_nonneg_left hrootd (show 0 ≤ 2985984*kappa^3*(d:ℝ) by positivity)
    nlinarith
  have hReq : residualBracket kappa R (publicX kappa R)/residualTolerance d kappa R Q=
      47775744*kappa^3*(d:ℝ)*Real.sqrt (d:ℝ)*(2*(1-publicTheta kappa)+8)/
        ((1-publicTheta kappa)^3*Real.sqrt (2/Q)) := by
    rw [residualTolerance,residual_precision_scale d hd kappa R (publicX kappa R) s _ hkp hs htau]
    dsimp [publicX,publicTau,publicDelta,S,s]
    field_simp
    <;> ring
  have hRes : residualBracket kappa R (publicX kappa R)/residualTolerance d kappa R Q ≤ commonRatio d kappa Q := by
    rw [hReq]
    unfold commonRatio
    apply div_le_div₀ (by positivity) _ heta hetaDen
    have hh:=mul_le_mul_of_nonneg_left hrootd (show 0 ≤ 47775744*kappa^3*(d:ℝ) by positivity)
    have hh2:=mul_le_mul_of_nonneg_left (show 2*(1-publicTheta kappa)+8 ≤ 10 by linarith)
      (show 0 ≤ 47775744*kappa^3*(d:ℝ)*Real.sqrt (d:ℝ) by positivity)
    nlinarith
  exact ⟨hC,hE,hP,hRes⟩

end
end PaperHeavyBallRootRatios

end SnapshotModule_130
/- END heavy_ball_root_ratios -/

/- BEGIN heavy_ball_power_rate -/
section SnapshotModule_131

namespace PaperHeavyBallPowerRate
open PaperHeavyBallAlgorithm PaperHeavyBallPowerHorizon
noncomputable section
set_option maxHeartbeats 1000000

lemma power_log_denom : (1/5:ℝ) ≤ -Real.log (49/64:ℝ) := by
  have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<49/64)
  linarith

lemma power_count_formula (d : ℕ) :
    powerCount d=⌊Real.log (373248*(d:ℝ))/(-Real.log (49/64:ℝ))⌋₊+1 := by
  unfold powerCount iterations S powerQ
  congr 3
  ring

lemma constant_log_bound : Real.log (373248:ℝ) ≤ 19 := by
  have hm:=Real.log_le_log (by norm_num : (0:ℝ)<373248)
    (show (373248:ℝ)≤2^19 by norm_num)
  rw [Real.log_pow] at hm
  have h2:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hm
  linarith

lemma dimension_log_lower (d : ℕ) (hd : 1 ≤ d) : 1 ≤ Real.log (2+(d:ℝ)) := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hm:=Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ 2+(d:ℝ) by linarith [Real.exp_one_lt_three])
  simpa only [Real.log_exp] using hm

lemma count_plus_one_sharp (d : ℕ) (hd : 1 ≤ d) :
    ((powerCount d+1:ℕ):ℝ) ≤ 102*Real.log (2+(d:ℝ)) := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : 0 < (d:ℝ) := by linarith
  have hl:=dimension_log_lower d hd
  have hnum : 0 ≤ Real.log (373248*(d:ℝ)) := Real.log_nonneg (by nlinarith)
  have hden : 0 < -Real.log (49/64:ℝ) := by linarith [power_log_denom]
  have hfloor := Nat.floor_le (show 0 ≤ Real.log (373248*(d:ℝ))/(-Real.log (49/64:ℝ)) by positivity)
  have hf : ((powerCount d+1:ℕ):ℝ) ≤ Real.log (373248*(d:ℝ))/(-Real.log (49/64:ℝ))+2 := by
    rw [power_count_formula]
    push_cast
    linarith
  have hdiv : Real.log (373248*(d:ℝ))/(-Real.log (49/64:ℝ)) ≤ 5*Real.log (373248*(d:ℝ)) := by
    apply (div_le_iff₀ hden).mpr
    have hm:=mul_le_mul_of_nonneg_left power_log_denom (show 0 ≤ 5*Real.log (373248*(d:ℝ)) by positivity)
    nlinarith
  have hlogd:=Real.log_le_log hdp (show (d:ℝ)≤2+(d:ℝ) by linarith)
  rw [Real.log_mul (by norm_num : (373248:ℝ)≠0) hdp.ne'] at hf hdiv
  have hc:=constant_log_bound
  linarith

/-- Actual normalized-power horizon, including its final Rayleigh product. -/
theorem powerCount_rate (d : ℕ) (hd : 1 ≤ d) :
    ((powerCount d+1:ℕ):ℝ) ≤ 2000*Real.log (2+(d:ℝ)) := by
  have h:=count_plus_one_sharp d hd
  have hl:=dimension_log_lower d hd
  linarith

/-- Coarse polynomial control used only in the public precision lower bound. -/
theorem powerCount_linear (d : ℕ) (hd : 1 ≤ d) :
    (powerCount d:ℝ) ≤ 2000000*(d:ℝ) := by
  have h:=count_plus_one_sharp d hd
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlog:=Real.log_le_sub_one_of_pos (show 0<2+(d:ℝ) by positivity)
  push_cast at h
  linarith

end
end PaperHeavyBallPowerRate

end SnapshotModule_131
/- END heavy_ball_power_rate -/

/- BEGIN heavy_ball_iteration_rate -/
section SnapshotModule_132

namespace PaperHeavyBallIterationRate
open PaperHeavyBallPublic PaperHeavyBallDecay
noncomputable section
set_option maxHeartbeats 1000000

lemma inverse_public_gap (kappa : ℝ) (hk : 1 ≤ kappa) :
    1/(1-publicTheta kappa)=(Real.sqrt (8*kappa)+1)/2 := by
  have hs : 0 ≤ Real.sqrt (8*kappa) := Real.sqrt_nonneg _
  have hd : Real.sqrt (8*kappa)+1≠0 := ne_of_gt (by positivity)
  dsimp [publicTheta,PaperHeavyBallParameters.theta]
  rw [Real.sqrt_one]
  field_simp
  <;> ring

lemma public_gap_cost (kappa : ℝ) (hk : 1 ≤ kappa) :
    2/(1-publicTheta kappa) ≤ 4*Real.sqrt kappa := by
  have hs := Real.sq_sqrt (show 0 ≤ kappa by linarith)
  have hs0 := Real.sqrt_nonneg kappa
  have ht := Real.sq_sqrt (show 0 ≤ 8*kappa by linarith)
  have ht0 := Real.sqrt_nonneg (8*kappa)
  have hroot : Real.sqrt (8*kappa) ≤ 3*Real.sqrt kappa := by nlinarith
  have hone : 1 ≤ Real.sqrt kappa := by nlinarith
  have he : 2/(1-publicTheta kappa)=Real.sqrt (8*kappa)+1 := by
    calc
      _=2*(1/(1-publicTheta kappa)) := by ring
      _=Real.sqrt (8*kappa)+1 := by rw [inverse_public_gap kappa hk]; ring
  rw [he]
  linarith

lemma horizon_scale_cancels (kappa R Q : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) :
    publicHorizon (publicTheta kappa) R (publicDelta R Q)=
      ⌈(2/(1-publicTheta kappa))*Real.log (24/((1-publicTheta kappa)*Real.sqrt (2/Q)))⌉₊ := by
  unfold publicHorizon publicDelta
  congr 3
  field_simp

lemma horizon_argument_bounds (kappa Q : ℝ) (hk : 1 ≤ kappa) (hQ : 32 ≤ Q) :
    1 ≤ 24/((1-publicTheta kappa)*Real.sqrt (2/Q)) ∧
    24/((1-publicTheta kappa)*Real.sqrt (2/Q)) ≤ 48*kappa*Q := by
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have ht := publicTheta_bounds kappa hk
  have hg : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have hs : 0 < Real.sqrt (2/Q) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2/Q by positivity)
  have hsle : Real.sqrt (2/Q) ≤ 1 := by
    have hh : 2/Q ≤ 1 := (div_le_one hQp).mpr (by linarith)
    nlinarith
  have hg1 : 1-publicTheta kappa ≤ 1 := by linarith [ht.1]
  have hprod := mul_le_mul hg1 hsle hs.le (by norm_num : (0:ℝ) ≤ 1)
  constructor
  · apply (le_div_iff₀ (mul_pos hg hs)).mpr
    nlinarith
  · have hscaled : (Q*Real.sqrt (2/Q))^2=2*Q := by rw [mul_pow,hsq]; field_simp
    have hinv : 1 ≤ Q*Real.sqrt (2/Q) := by
      have hp : 0 < Q*Real.sqrt (2/Q) := mul_pos hQp hs
      nlinarith
    have hrec : 1/Real.sqrt (2/Q) ≤ Q := (div_le_iff₀ hs).mpr (by nlinarith)
    have hroot : Real.sqrt kappa ≤ kappa := by
      have hk0 := Real.sqrt_nonneg kappa
      have hk2 := Real.sq_sqrt hkp.le
      nlinarith
    have hc := public_gap_cost kappa hk
    have hmul := mul_le_mul hc hrec (by positivity : 0 ≤ 1/Real.sqrt (2/Q)) (by positivity : 0 ≤ 4*Real.sqrt kappa)
    have hmul2 := mul_le_mul_of_nonneg_right hroot hQp.le
    have he : 24/((1-publicTheta kappa)*Real.sqrt (2/Q))=
        12*((2/(1-publicTheta kappa))*(1/Real.sqrt (2/Q))) := by field_simp <;> ring
    rw [he]
    nlinarith

lemma horizon_log_envelope (kappa Q : ℝ) (hk : 1 ≤ kappa) (hQ : 32 ≤ Q) :
    1 ≤ Real.log (2+kappa*Q) ∧
    Real.log (24/((1-publicTheta kappa)*Real.sqrt (2/Q))) ≤ 48*Real.log (2+kappa*Q) := by
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have hkQ : 32 ≤ kappa*Q := by nlinarith
  have hL : 1 ≤ Real.log (2+kappa*Q) := by
    have hm := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 2+kappa*Q by linarith [Real.exp_one_lt_three])
    simpa only [Real.log_exp] using hm
  refine ⟨hL,?_⟩
  have ha := horizon_argument_bounds kappa Q hk hQ
  have hp : 0 < 24/((1-publicTheta kappa)*Real.sqrt (2/Q)) := by linarith [ha.1]
  have hm := Real.log_le_log hp ha.2
  rw [show 48*kappa*Q=48*(kappa*Q) by ring] at hm
  rw [Real.log_mul (by norm_num : (48:ℝ)≠0) (mul_pos hkp hQp).ne'] at hm
  have h48 : Real.log 48 ≤ 47 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<48)]
  have harg := Real.log_le_log (mul_pos hkp hQp) (show kappa*Q ≤ 2+kappa*Q by linarith)
  linarith

/-- The actual public fixed horizon, uniformly in physical scale R. -/
theorem publicHorizon_rate (kappa R Q : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) (hQ : 32 ≤ Q) :
    (publicHorizon (publicTheta kappa) R (publicDelta R Q):ℝ) ≤
      200*Real.sqrt kappa*Real.log (2+kappa*Q) := by
  rw [horizon_scale_cancels kappa R Q hk hR]
  have ht := publicTheta_bounds kappa hk
  have hg : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have ha := horizon_argument_bounds kappa Q hk hQ
  have hlog0 : 0 ≤ Real.log (24/((1-publicTheta kappa)*Real.sqrt (2/Q))) := Real.log_nonneg ha.1
  have hfloor := Nat.ceil_lt_add_one (show 0 ≤ (2/(1-publicTheta kappa))*
      Real.log (24/((1-publicTheta kappa)*Real.sqrt (2/Q))) by positivity)
  have hL := horizon_log_envelope kappa Q hk hQ
  have hc := public_gap_cost kappa hk
  have hm := mul_le_mul hc hL.2 hlog0 (by positivity : 0 ≤ 4*Real.sqrt kappa)
  have hs := Real.sq_sqrt (show 0 ≤ kappa by linarith)
  have hs0 := Real.sqrt_nonneg kappa
  have hs1 : 1 ≤ Real.sqrt kappa := by nlinarith
  have htotal : 1 ≤ Real.sqrt kappa*Real.log (2+kappa*Q) := by nlinarith [hL.1]
  nlinarith

end
end PaperHeavyBallIterationRate

end SnapshotModule_132
/- END heavy_ball_iteration_rate -/

/- BEGIN heavy_ball_eta_lower -/
section SnapshotModule_133

namespace PaperHeavyBallEtaLower
open PaperHeavyBallAlgorithm PaperHeavyBallPublic PaperHeavyBallPowerHorizon
noncomputable section
set_option maxHeartbeats 2000000

def etaLower (d : ℕ) (kappa Q : ℝ) : ℝ := 1/((1000000000000:ℝ)*(d:ℝ)^2*kappa^3*Q)

lemma gap_lower (kappa : ℝ) (hk : 1 ≤ kappa) :
    1/(2*kappa) ≤ 1-publicTheta kappa := by
  have ht:=publicTheta_bounds kappa hk
  have hgap : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have hkp : 0 < kappa := by linarith
  have hroot : Real.sqrt kappa ≤ kappa := by nlinarith [Real.sq_sqrt hkp.le,Real.sqrt_nonneg kappa]
  have hc:=(PaperHeavyBallIterationRate.public_gap_cost kappa hk).trans
    (mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 4))
  have hh:=(div_le_iff₀ hgap).mp hc
  apply (div_le_iff₀ (by positivity : 0 < 2*kappa)).mpr
  nlinarith

lemma sqrt_precision_lower (Q : ℝ) (hQ : 32 ≤ Q) : 1/Q ≤ Real.sqrt (2/Q) := by
  have hp : 0 < Q := by linarith
  have hq : 1/Q ≤ 1 := (div_le_one hp).mpr (by linarith)
  have hsq : (1/Q)^2 ≤ 2/Q := by
    have hh:=sq_le (show 0 ≤ 1/Q by positivity) hq
    have hm:=div_le_div_of_nonneg_right (show (1:ℝ) ≤ 2 by norm_num) hp.le
    exact hh.trans hm
  exact Real.le_sqrt_of_sq_le hsq

lemma sigma_lower (d : ℕ) (hd : 0 < d) :
    1/((500000000000:ℝ)*(d:ℝ)^2) ≤ sigma (S d) powerQ := by
  have hd1 : 1 ≤ d := hd
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hSp : 0 < S d := by dsimp [S];positivity
  have hK:=PaperHeavyBallPowerRate.powerCount_linear d hd1
  have hKp : 0 < (powerCount d:ℝ) := Nat.cast_pos.mpr (iterations_pos (S d) powerQ)
  have hroot : Real.sqrt (S d) ≤ 6*(d:ℝ) := by
    have hsq:=Real.sq_sqrt hSp.le
    dsimp [S] at hsq ⊢
    nlinarith [Real.sqrt_nonneg (36*(d:ℝ))]
  have hden : (36864:ℝ)*(powerCount d:ℝ)*Real.sqrt (S d) ≤ (500000000000:ℝ)*(d:ℝ)^2 := by
    have hm:=mul_le_mul hK hroot (Real.sqrt_nonneg (S d)) (by positivity : 0 ≤ 2000000*(d:ℝ))
    nlinarith
  have he : sigma (S d) powerQ=1/((36864:ℝ)*(powerCount d:ℝ)*Real.sqrt (S d)) := by
    dsimp [sigma,powerQ,powerCount]
    field_simp
    <;> ring
  rw [he]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

/-- The actual public common calibration tolerance has a uniform polynomial
lower bound, obtained from its three public min branches and the actual K count. -/
theorem eta_polynomial_lower (d : ℕ) (hd : 0 < d) (kappa Q : ℝ) (hk : 1 ≤ kappa) (hQ : 32 ≤ Q) :
    etaLower d kappa Q ≤ eta d kappa Q := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have hk3 : 1 ≤ kappa^3 := one_le_pow₀ hk
  have hd2 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hkQ : 1 ≤ kappa^3*Q := by nlinarith
  have hgap:=gap_lower kappa hk
  have ht:=publicTheta_bounds kappa hk
  have hgp : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have hprec:=sqrt_precision_lower Q hQ
  have hsig:=sigma_lower d hd
  have hterm : 1/((4096:ℝ)*kappa^3*Q) ≤ (1-publicTheta kappa)^3*Real.sqrt (2/Q)/512 := by
    have hp:=pow_le_pow_left₀ (show 0 ≤ 1/(2*kappa) by positivity) hgap 3
    have hm:=mul_le_mul hp hprec (show 0 ≤ 1/Q by positivity) (by positivity : 0 ≤ (1-publicTheta kappa)^3)
    have hh:=div_le_div_of_nonneg_right hm (by norm_num : (0:ℝ) ≤ 512)
    have he : (1/(2*kappa))^3*(1/Q)/512=1/((4096:ℝ)*kappa^3*Q) := by field_simp;ring
    rw [he] at hh
    exact hh
  have hsmallHalf : etaLower d kappa Q ≤ 1/2 := by
    unfold etaLower
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have hm:=mul_le_mul_of_nonneg_left hkQ (show 0 ≤ (1000000000000:ℝ)*(d:ℝ)^2 by positivity)
    nlinarith
  have hsmallSigma : etaLower d kappa Q ≤ sigma (S d) powerQ/2 := by
    have hh:=div_le_div_of_nonneg_right hsig (by norm_num : (0:ℝ) ≤ 2)
    have he : (1/((500000000000:ℝ)*(d:ℝ)^2))/2=1/((1000000000000:ℝ)*(d:ℝ)^2) := by ring
    rw [he] at hh
    apply (le_trans _ hh)
    unfold etaLower
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hm:=mul_le_mul_of_nonneg_left hkQ (show 0 ≤ (1000000000000:ℝ)*(d:ℝ)^2 by positivity)
    nlinarith
  have hsmallTerm : etaLower d kappa Q ≤ (1-publicTheta kappa)^3*Real.sqrt (2/Q)/512 := by
    apply (le_trans _ hterm)
    unfold etaLower
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hm:=mul_le_mul_of_nonneg_right (show (4096:ℝ) ≤ (1000000000000:ℝ)*(d:ℝ)^2 by nlinarith)
      (show 0 ≤ kappa^3*Q by positivity)
    nlinarith
  exact le_min hsmallHalf (le_min hsmallSigma hsmallTerm)

end
end PaperHeavyBallEtaLower

end SnapshotModule_133
/- END heavy_ball_eta_lower -/

/- BEGIN heavy_ball_uniform_rate -/
section SnapshotModule_134

namespace PaperHeavyBallUniformRate
open PaperHeavyBallAlgorithm PaperHeavyBallBackend PaperHeavyBallPublic PaperHeavyBallLine
open PaperHeavyBallRootRatios PaperHeavyBallEtaLower
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def dimensionless (d : ℕ) (kappa Q : ℝ) : ℝ := 2+(d:ℝ)*kappa*Q
def polynomial (d : ℕ) (kappa Q : ℝ) : ℝ := (1000000000000000000000:ℝ)*(dimensionless d kappa Q)^11
def rootConstant : ℝ := (Real.log (1000000000000000000000:ℝ)/Real.log 2+12)/Real.log 2

theorem dimensionless_bounds (d : ℕ) (hd : 0 < d) (kappa Q : ℝ) (hk : 1 ≤ kappa) (hQ : 32 ≤ Q) :
    2 < dimensionless d kappa Q ∧ (d:ℝ) ≤ dimensionless d kappa Q ∧ kappa ≤ dimensionless d kappa Q ∧ Q ≤ dimensionless d kappa Q := by
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have hdk : 1 ≤ (d:ℝ)*kappa := by nlinarith
  have hkQ : 1 ≤ kappa*Q := by nlinarith
  have hdQ : 1 ≤ (d:ℝ)*Q := by nlinarith
  dsimp [dimensionless]
  constructor
  · have hp : 0 < (d:ℝ)*kappa*Q := by positivity
    linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hkQ (by positivity : 0 ≤ (d:ℝ))]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hdQ hkp.le]
  · nlinarith [mul_le_mul_of_nonneg_right hdk hQp.le]

theorem commonRatio_polynomial (d : ℕ) (hd : 0 < d) (kappa Q : ℝ) (hk : 1 ≤ kappa) (hQ : 32 ≤ Q) :
    commonRatio d kappa Q ≤ polynomial d kappa Q := by
  have hdp : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have hp:=eta_polynomial_lower d hd kappa Q hk hQ
  have hlow : 0 < etaLower d kappa Q := by dsimp [etaLower];positivity
  have he : commonRatio d kappa Q ≤ (1000000000000000000000:ℝ)*(d:ℝ)^4*kappa^6*Q := by
    have hh:=div_le_div_of_nonneg_left (show 0 ≤ (1000000000:ℝ)*kappa^3*(d:ℝ)^2 by positivity) hlow hp
    dsimp only [commonRatio]
    apply hh.trans
    dsimp [etaLower]
    apply le_of_eq
    field_simp
    <;> ring
  have hb:=dimensionless_bounds d hd kappa Q hk hQ
  have hD : 0 ≤ dimensionless d kappa Q := by linarith [hb.1]
  have hd4:=pow_le_pow_left₀ hdp.le hb.2.1 4
  have hk6:=pow_le_pow_left₀ hkp.le hb.2.2.1 6
  have hmul:=mul_le_mul hd4 hk6 (by positivity : 0 ≤ kappa^6) (by positivity : 0 ≤ (dimensionless d kappa Q)^4)
  have hmul2:=mul_le_mul hmul hb.2.2.2 hQp.le (mul_nonneg (pow_nonneg hD 4) (pow_nonneg hD 6))
  have hfinal:=mul_le_mul_of_nonneg_left hmul2 (by norm_num : (0:ℝ) ≤ 1000000000000000000000)
  apply he.trans
  dsimp [polynomial]
  convert hfinal using 1 <;> ring

lemma rootConstant_positive : 0 < rootConstant := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hconst : 0 ≤ Real.log (1000000000000000000000:ℝ) := Real.log_nonneg (by norm_num)
  dsimp [rootConstant]
  positivity

/-- A generic actual bisection horizon is logarithmic whenever its true bracket
ratio is bounded by the proved public polynomial. -/
theorem horizon_rate (d : ℕ) (hd : 0 < d) (kappa Q D delta : ℝ) (hk : 1 ≤ kappa) (hQ : 32 ≤ Q)
    (hD : 0 < D) (hdelta : 0 < delta) (hratio : D/delta ≤ polynomial d kappa Q) :
    (horizon D delta:ℝ) ≤ rootConstant*Real.log (dimensionless d kappa Q) := by
  have hb:=dimensionless_bounds d hd kappa Q hk hQ
  have hdim : 0 < dimensionless d kappa Q := by linarith [hb.1]
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogD : Real.log 2 ≤ Real.log (dimensionless d kappa Q) := Real.log_le_log (by norm_num) hb.1.le
  have hlogDp : 0 ≤ Real.log (dimensionless d kappa Q) := le_trans hlog2.le hlogD
  have hpoly : 1 ≤ polynomial d kappa Q := by
    have hp : (1:ℝ) ≤ (dimensionless d kappa Q)^11 := one_le_pow₀ (by linarith [hb.1])
    dsimp [polynomial]
    nlinarith
  have hpolylog : 0 ≤ Real.log (polynomial d kappa Q)/Real.log 2 := div_nonneg (Real.log_nonneg hpoly) hlog2.le
  have hmono : horizon D delta ≤ ⌈Real.log (polynomial d kappa Q)/Real.log 2⌉₊ := by
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) hratio) hlog2.le
  have hceil:=Nat.ceil_lt_add_one hpolylog
  have hexpand : Real.log (polynomial d kappa Q)=Real.log (1000000000000000000000:ℝ)+11*Real.log (dimensionless d kappa Q) := by
    rw [polynomial,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    norm_num
  have hconst : 0 ≤ Real.log (1000000000000000000000:ℝ)/Real.log 2+1 := by
    have hc:=Real.log_nonneg (by norm_num : (1:ℝ) ≤ 1000000000000000000000)
    positivity
  have habs : Real.log (1000000000000000000000:ℝ)/Real.log 2+1 ≤
      (Real.log (1000000000000000000000:ℝ)/Real.log 2+1)/Real.log 2*Real.log (dimensionless d kappa Q) := by
    calc
      _ = (Real.log (1000000000000000000000:ℝ)/Real.log 2+1)/Real.log 2*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogD (div_nonneg hconst hlog2.le)
  have hcast : (horizon D delta:ℝ) ≤ (⌈Real.log (polynomial d kappa Q)/Real.log 2⌉₊:ℝ) := by exact_mod_cast hmono
  apply hcast.trans (le_trans hceil.le _)
  rw [hexpand]
  dsimp [rootConstant]
  have heq : (Real.log (1000000000000000000000:ℝ)+11*Real.log (dimensionless d kappa Q))/Real.log 2+1 =
      (Real.log (1000000000000000000000:ℝ)/Real.log 2+1)+11/Real.log 2*Real.log (dimensionless d kappa Q) := by ring
  rw [heq]
  calc
    _ ≤ (Real.log (1000000000000000000000:ℝ)/Real.log 2+1)/Real.log 2*Real.log (dimensionless d kappa Q)+11/Real.log 2*Real.log (dimensionless d kappa Q) := by linarith only [habs]
    _ = _ := by ring

end
end PaperHeavyBallUniformRate

end SnapshotModule_134
/- END heavy_ball_uniform_rate -/

/- BEGIN heavy_ball_total_rate -/
section SnapshotModule_135

namespace PaperHeavyBallTotalRate
open PaperHeavyBallAlgorithm PaperHeavyBallBackend PaperHeavyBallPublic PaperHeavyBallLine
open PaperHeavyBallRootRatios PaperHeavyBallUniformRate
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def rateConstant : ℝ := 208*rootConstant

theorem all_horizon_rates (d : ℕ) (hd : 0 < d) (kappa R Q : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) (hQ : 32 ≤ Q) :
    (horizon (bracketC kappa R s) (toleranceC kappa R (S d) (calibrationQ d) (eta d kappa Q)):ℝ) ≤ rootConstant*Real.log (dimensionless d kappa Q) ∧
    (horizon (bracketE kappa R (S d)) (toleranceE R (calibrationQ d) (eta d kappa Q)):ℝ) ≤ rootConstant*Real.log (dimensionless d kappa Q) ∧
    (horizon (productBracket kappa R) (powerTolerance d kappa R):ℝ) ≤ rootConstant*Real.log (dimensionless d kappa Q) ∧
    (horizon (residualBracket kappa R (publicX kappa R)) (residualTolerance d kappa R Q):ℝ) ≤ rootConstant*Real.log (dimensionless d kappa Q) := by
  have hdp : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have hS : 0 < S d := by dsimp [S];positivity
  have hs : 0 < s := by norm_num [s]
  have hq : 0 < calibrationQ d := by dsimp [calibrationQ];positivity
  have hq0 : 0 < powerQ := by norm_num [powerQ]
  have heta : 0 < eta d kappa Q := publicEta_positive kappa Q (S d) powerQ hk hQp hS hq0
  have hK : 0 < (PaperHeavyBallPowerHorizon.iterations (S d) powerQ:ℝ) := Nat.cast_pos.mpr (PaperHeavyBallPowerHorizon.iterations_pos _ _)
  have hsig : 0 < PaperHeavyBallPowerHorizon.sigma (S d) powerQ := by dsimp [PaperHeavyBallPowerHorizon.sigma];positivity
  have ht:=publicTheta_bounds kappa hk
  have hgap : 0 < 1-publicTheta kappa := by linarith [ht.2]
  have hX : 0 < publicX kappa R := by dsimp [publicX];positivity
  have htau : 0 < publicTau kappa R Q (S d) := by dsimp [publicTau,publicDelta];positivity
  have ratios:=all_root_ratios d hd kappa R Q hk hR hQ
  have poly:=commonRatio_polynomial d hd kappa Q hk hQ
  constructor
  · apply horizon_rate d hd kappa Q _ _ hk hQ
    · dsimp [bracketC];positivity
    · dsimp [toleranceC];positivity
    · exact ratios.1.trans poly
  constructor
  · apply horizon_rate d hd kappa Q _ _ hk hQ
    · dsimp [bracketE];positivity
    · dsimp [toleranceE];positivity
    · exact ratios.2.1.trans poly
  constructor
  · apply horizon_rate d hd kappa Q _ _ hk hQ
    · dsimp [productBracket];positivity
    · dsimp [powerTolerance,powerRootTolerance];positivity
    · exact ratios.2.2.1.trans poly
  · apply horizon_rate d hd kappa Q _ _ hk hQ
    · dsimp [residualBracket];positivity
    · dsimp [residualTolerance,residualRootTolerance];positivity
    · exact ratios.2.2.2.trans poly

/-- Uniform numerical envelope for the actual all-seed/all-response cap. No
algorithmic count or precision bound occurs as a premise. -/
theorem totalCap_rate (d : ℕ) (hd : 0 < d) (kappa R Q : ℝ) (hk : 1 ≤ kappa) (hR : 0 < R) (hQ : 32 ≤ Q) :
    (totalCap d kappa R Q:ℝ) ≤ rateConstant*(d:ℝ)*Real.log (2+(d:ℝ)*kappa*Q)*
      (Real.log (2+(d:ℝ))+Real.sqrt kappa*Real.log (2+kappa*Q)) := by
  let B:=rootConstant*Real.log (dimensionless d kappa Q)
  have hb:=dimensionless_bounds d hd kappa Q hk hQ
  have hB : 0 ≤ B := mul_nonneg rootConstant_positive.le (Real.log_nonneg (by linarith [hb.1]))
  have hdp : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  have hr:=all_horizon_rates d hd kappa R Q hk hR hQ
  have hC:=mul_le_mul_of_nonneg_left hr.1 (show 0 ≤ 2*(d:ℝ) by positivity)
  have hE:=mul_le_mul_of_nonneg_left hr.2.1 (show 0 ≤ 2*(d:ℝ) by positivity)
  have hP:=mul_le_mul_of_nonneg_left hr.2.2.1 (show 0 ≤ 2*(d:ℝ)*((powerCount d:ℝ)+1) by positivity)
  have hRes:=mul_le_mul_of_nonneg_left hr.2.2.2 (show 0 ≤ (d:ℝ)*(heavyCount kappa R Q:ℝ) by positivity)
  have hcap : (totalCap d kappa R Q:ℝ) ≤ (d:ℝ)*B*(4+2*((powerCount d:ℝ)+1)+(heavyCount kappa R Q:ℝ)) := by
    dsimp [totalCap,calibrationCap,coordinateCost,powerCap,powerProductCap,productCost,heavyCap,residualCap,residualCost]
    push_cast
    dsimp [B]
    nlinarith only [hC,hE,hP,hRes]
  have hcount:=PaperHeavyBallPowerRate.count_plus_one_sharp d hd
  have hheavy:=PaperHeavyBallIterationRate.publicHorizon_rate kappa R Q hk hR hQ
  change (heavyCount kappa R Q:ℝ) ≤ 200*Real.sqrt kappa*Real.log (2+kappa*Q) at hheavy
  have hlogd:=PaperHeavyBallPowerRate.dimension_log_lower d hd
  have hnonneg : 0 ≤ Real.sqrt kappa*Real.log (2+kappa*Q) := by
    have hkp : 0 < kappa := by linarith
    have hQp : 0 < Q := by linarith
    exact mul_nonneg (Real.sqrt_nonneg kappa) (Real.log_nonneg (by nlinarith [mul_pos hkp hQp]))
  have hfactor : 4+2*((powerCount d:ℝ)+1)+(heavyCount kappa R Q:ℝ) ≤
      208*(Real.log (2+(d:ℝ))+Real.sqrt kappa*Real.log (2+kappa*Q)) := by
    push_cast at hcount
    nlinarith only [hcount,hheavy,hlogd,hnonneg]
  have hm:=mul_le_mul_of_nonneg_left hfactor (mul_nonneg hdp hB)
  apply hcap.trans
  convert hm using 1 <;> dsimp [rateConstant,B,dimensionless] <;> ring

lemma rateConstant_positive : 0 < rateConstant := mul_pos (by norm_num) rootConstant_positive

end
end PaperHeavyBallTotalRate

end SnapshotModule_135
/- END heavy_ball_total_rate -/

/- BEGIN heavy_ball_gaussian_tail -/
section SnapshotModule_136

namespace PaperHeavyBallGaussianTail
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000

lemma weighted_standard_density (x : ℝ) :
    gaussianPDFReal 0 1 x*Real.exp (x^2/4)=Real.sqrt 2*gaussianPDFReal 0 2 x := by
  have hs2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : Real.sqrt (2*Real.pi)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hscale : Real.sqrt (2*Real.pi*2)=Real.sqrt 2*Real.sqrt (2*Real.pi) := by
    rw [show 2*Real.pi*2=2*(2*Real.pi) by ring,Real.sqrt_mul (by norm_num)]
  simp only [gaussianPDFReal,NNReal.coe_one,NNReal.coe_ofNat,sub_zero,mul_one]
  rw [mul_assoc,←Real.exp_add]
  have hexp : -x^2/2+x^2/4= -x^2/(2*2) := by ring
  rw [hexp,hscale]
  field_simp

lemma integrable_standard_exp_sq :
    Integrable (fun x : ℝ=>Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0)≠0)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun _=>gaussianPDF_lt_top))).mpr
  have heq : (fun x : ℝ=>(gaussianPDF 0 1 x).toReal •Real.exp (x^2/4))=
      (fun x=>Real.sqrt 2*gaussianPDFReal 0 2 x) := by
    funext x
    simp only [smul_eq_mul,gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x)]
    exact weighted_standard_density x
  rw [heq]
  exact (integrable_gaussianPDFReal 0 2).const_mul _

lemma integral_standard_exp_sq :
    (∫x : ℝ,Real.exp (x^2/4) ∂gaussianReal 0 1)=Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  simp only [smul_eq_mul,weighted_standard_density]
  rw [integral_const_mul,integral_gaussianPDFReal_eq_one 0 (by norm_num : (2:ℝ≥0)≠0),mul_one]

lemma exp_sq_toLp (d : ℕ) (x : Fin d→ℝ) :
    Real.exp (‖WithLp.toLp 2 x‖^2/4)=∏i,Real.exp ((x i)^2/4) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [Finset.sum_div,Real.exp_sum]

lemma integrable_euclidean_exp_sq (d : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d)=>Real.exp (‖x‖^2/4))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rw [←map_pi_eq_stdGaussian]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  change Integrable (fun x : Fin d→ℝ=>Real.exp (‖WithLp.toLp 2 x‖^2/4)) _
  simp_rw [exp_sq_toLp]
  exact Integrable.fintype_prod (fun _ : Fin d=>integrable_standard_exp_sq)

lemma integral_euclidean_exp_sq (d : ℕ) :
    (∫x : EuclideanSpace ℝ (Fin d),Real.exp (‖x‖^2/4) ∂stdGaussian (EuclideanSpace ℝ (Fin d)))=
      (Real.sqrt 2)^d := by
  rw [←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [exp_sq_toLp]
  rw [integral_fintype_prod_eq_prod (fun (_i : Fin d) (x : ℝ)=>Real.exp (x^2/4))]
  simp only [integral_standard_exp_sq,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Chernoff bound for the actual Euclidean standard Gaussian, with a
proved exponential moment rather than a Gaussian concentration premise. -/
theorem norm_squared_tail (d : ℕ) (S : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {x | S ≤ ‖x‖^2} ≤
      Real.exp ((d:ℝ)-S/4) := by
  have hp : 0 < Real.exp (S/4) := Real.exp_pos _
  have hevent : {x : EuclideanSpace ℝ (Fin d) | Real.exp (S/4) ≤ Real.exp (‖x‖^2/4)}=
      {x | S ≤ ‖x‖^2} := by
    ext x
    simp only [mem_setOf_eq,Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ:=stdGaussian (EuclideanSpace ℝ (Fin d)))
    (f:=fun x=>Real.exp (‖x‖^2/4)) (ae_of_all _ (fun x=>(Real.exp_pos _).le))
    (integrable_euclidean_exp_sq d) (Real.exp (S/4))
  rw [hevent,integral_euclidean_exp_sq] at hh
  have hs : Real.sqrt 2 ≤ Real.exp 1 := by
    have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg 2
    have he := Real.add_one_le_exp (1:ℝ)
    nlinarith
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg 2) hs d
  rw [←Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((d:ℝ)*1)=Real.exp (d:ℝ) := by congr 1;ring
  rw [hexp] at hpow
  have hdiv : (stdGaussian (EuclideanSpace ℝ (Fin d))).real {x | S ≤ ‖x‖^2} ≤
      (Real.sqrt 2)^d/Real.exp (S/4) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
  have hm := hdiv.trans (div_le_div_of_nonneg_right hpow hp.le)
  have heq : Real.exp (d:ℝ)/Real.exp (S/4)=Real.exp ((d:ℝ)-S/4) := (Real.exp_sub _ _).symm
  exact hm.trans_eq heq

def normBudget (d : ℕ) (gamma : ℝ) : ℝ := 4*(d:ℝ)+4*Real.log (6/gamma)

theorem public_norm_tail (d : ℕ) (gamma : ℝ) (hg : 0 < gamma) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {x | normBudget d gamma ≤ ‖x‖^2} ≤ gamma/6 := by
  have hh := norm_squared_tail d (normBudget d gamma)
  have he : (d:ℝ)-normBudget d gamma/4= -Real.log (6/gamma) := by unfold normBudget;ring
  rw [he,Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<6/gamma),inv_div] at hh
  exact hh

/-- Explicit witness for the manuscript's uniform-gamma O(d+log(1/gamma))
Gaussian norm budget; the main algorithm uses its simpler fixed-gamma variant. -/
theorem public_norm_budget (d : ℕ) (hd : 1 ≤ d) (gamma : ℝ)
    (hg : 0 < gamma) (hg1 : gamma < 1) :
    0 < normBudget d gamma ∧ normBudget d gamma ≤ 24*((d:ℝ)+Real.log (1/gamma)) := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hinv : 1 ≤ 1/gamma := (le_div_iff₀ hg).mpr (by linarith)
  have hlog0 : 0 ≤ Real.log (1/gamma) := Real.log_nonneg hinv
  have h6 : Real.log 6 ≤ 5 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<6)]
  have he : Real.log (6/gamma)=Real.log 6+Real.log (1/gamma) := by
    rw [Real.log_div (by norm_num : (6:ℝ)≠0) hg.ne',Real.log_div (by norm_num : (1:ℝ)≠0) hg.ne',Real.log_one]
    ring
  have h6pos : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  unfold normBudget
  rw [he]
  constructor <;> nlinarith

end
end PaperHeavyBallGaussianTail

end SnapshotModule_136
/- END heavy_ball_gaussian_tail -/

/- BEGIN heavy_ball_complete -/
section SnapshotModule_137

namespace PaperHeavyBallComplete
open Set MeasureTheory ProbabilityTheory PaperOracle PaperHeavyBallLine
open PaperHeavyBallAlgorithm PaperHeavyBallTotalRate
open scoped ENNReal NNReal
noncomputable section

/-- The paper's robust heavy-ball upper bound, with the literal finite
comparison program, independent double-Gaussian law, total Borel query/history
policy, and a uniform cap on every seed and every response branch. All
convergence, calibration, power, probability and complexity facts are derived
from the original quadratic conditioning/localization hypotheses. -/
theorem randomized_robust_heavy_ball (d : ℕ) (hd : 0 < d)
    (A : Space d→L[ℝ] Space d) (hA : A.toLinearMap.IsSymmetric) (b star : Space d)
    (mu beta R epsilon Q c0 : ℝ) (hmu : 0 < mu) (hbeta : mu ≤ beta) (hR : 0 < R) (heps : 0 < epsilon)
    (hQ : 32 ≤ Q) (hQdef : Q=beta*R^2/epsilon)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2)
    (hsol : A star=b) (hstar : ‖star‖ ≤ R) :
    let f:=fun x=>quadratic A b x+c0
    let event:={seed : Seed d | f (Program.run (comparisonOracle f) (algorithm d (beta/mu) R Q seed))-f star ≤ epsilon}
    0 < rateConstant ∧ MeasurableSet event ∧ (2/3:ℝ≥0∞) ≤ seedLaw d event ∧
      (∀seed,Program.Cap (totalCap d (beta/mu) R Q) (algorithm d (beta/mu) R Q seed)) ∧
      (∀seed,(PaperSeedBorelTree.Tree.policy (PaperHeavyBallAlgorithmBorel.algorithmTree d (beta/mu) R Q)).fromSeed
        (totalCap d (beta/mu) R Q) seed=algorithm d (beta/mu) R Q seed) ∧
      (totalCap d (beta/mu) R Q:ℝ) ≤ rateConstant*(d:ℝ)*Real.log (2+(d:ℝ)*(beta/mu)*Q)*
        (Real.log (2+(d:ℝ))+Real.sqrt (beta/mu)*Real.log (2+(beta/mu)*Q)) := by
  have hprob:=actual_algorithm_probability d hd A hA b star mu beta R epsilon Q c0 hmu hbeta hR heps hQ hQdef hlower hupper hsol hstar
  have hk : 1 ≤ beta/mu := (le_div_iff₀ hmu).mpr (by simpa using hbeta)
  have hcap:=totalCap_rate d hd (beta/mu) R Q hk hR hQ
  exact ⟨rateConstant_positive,hprob.1,hprob.2.1,hprob.2.2.1,hprob.2.2.2,hcap⟩

end
end PaperHeavyBallComplete

end SnapshotModule_137
/- END heavy_ball_complete -/

/- BEGIN heavy_ball_rate_corollaries -/
section SnapshotModule_138

namespace PaperHeavyBallRateCorollaries
noncomputable section
set_option maxHeartbeats 1000000

def profile (d kappa Q : ℝ) : ℝ :=
  d*Real.log (2+d*kappa*Q)*(Real.log (2+d)+Real.sqrt kappa*Real.log (2+kappa*Q))

lemma diagonal_profile (d Q : ℝ) (hd : 1 ≤ d) (hQ : 32 ≤ Q) :
    profile d Q Q ≤ 6*d*Real.sqrt Q*(Real.log (2+d*Q))^2 := by
  have hdp : 0 < d := by linarith
  have hQp : 0 < Q := by linarith
  have hDQ : Q ≤ d*Q := by nlinarith
  have hDQsq : Q^2 ≤ (d*Q)^2 := (sq_le_sq₀ hQp.le (by positivity)).mpr hDQ
  have hLd : 0 ≤ Real.log (2+d*Q) := Real.log_nonneg (by nlinarith)
  have hs1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr (by linarith)
  have h1 : Real.log (2+d*Q*Q) ≤ 2*Real.log (2+d*Q) := by
    have hm:=Real.log_le_log (show 0 < 2+d*Q*Q by positivity)
      (show 2+d*Q*Q ≤ (2+d*Q)^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have h2 : Real.log (2+Q*Q) ≤ 2*Real.log (2+d*Q) := by
    have hm:=Real.log_le_log (show 0 < 2+Q*Q by positivity)
      (show 2+Q*Q ≤ (2+d*Q)^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have h3 : Real.log (2+d) ≤ Real.log (2+d*Q) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlogd : 0 ≤ Real.log (2+d) := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log (2+Q*Q) := Real.log_nonneg (by nlinarith)
  have hbr : Real.log (2+d)+Real.sqrt Q*Real.log (2+Q*Q) ≤
      3*Real.sqrt Q*Real.log (2+d*Q) := by
    have hm:=mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg Q)
    have hm2:=mul_le_mul_of_nonneg_right hs1 hLd
    nlinarith
  have hm:=mul_le_mul h1 hbr (by positivity : 0 ≤ Real.log (2+d)+Real.sqrt Q*Real.log (2+Q*Q)) (by positivity : 0 ≤ 2*Real.log (2+d*Q))
  have hm2:=mul_le_mul_of_nonneg_left hm hdp.le
  unfold profile
  nlinarith

lemma fixed_condition_profile (d kappa Q : ℝ) (hd : 1 ≤ d) (hk : 1 ≤ kappa)
    (hQ : 32 ≤ Q) (hwindow : Q ≤ d^2) :
    profile d kappa Q ≤
      d*(3+Real.log kappa)*(1+Real.sqrt kappa*(2+Real.log kappa))*(Real.log (2+d))^2 := by
  have hdp : 0 < d := by linarith
  have hkp : 0 < kappa := by linarith
  have hQp : 0 < Q := by linarith
  have hLd : 1 ≤ Real.log (2+d) := by
    have hm:=Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 2+d by linarith [Real.exp_one_lt_three])
    simpa only [Real.log_exp] using hm
  have hlk : 0 ≤ Real.log kappa := Real.log_nonneg hk
  have hdom : Q ≤ (2+d)^2 := by nlinarith
  have hdom1 : 2+d*kappa*Q ≤ kappa*(2+d)^3 := by
    have hm:=mul_le_mul_of_nonneg_left hwindow (show 0 ≤ d*kappa by positivity)
    have hd3 : 0 ≤ d^3 := by positivity
    nlinarith [mul_nonneg (show 0 ≤ kappa-1 by linarith) (show 0 ≤ 2+12*d+6*d^2 by positivity)]
  have hdom2 : 2+kappa*Q ≤ kappa*(2+d)^2 := by
    have hm:=mul_le_mul_of_nonneg_left hwindow hkp.le
    nlinarith
  have h1 : Real.log (2+d*kappa*Q) ≤ (3+Real.log kappa)*Real.log (2+d) := by
    have hm:=Real.log_le_log (show 0 < 2+d*kappa*Q by positivity) hdom1
    rw [Real.log_mul hkp.ne' (pow_pos (by positivity : 0 < 2+d) 3).ne',Real.log_pow] at hm
    norm_num at hm
    have hm2:=mul_le_mul_of_nonneg_left hLd hlk
    nlinarith
  have h2 : Real.log (2+kappa*Q) ≤ (2+Real.log kappa)*Real.log (2+d) := by
    have hm:=Real.log_le_log (show 0 < 2+kappa*Q by positivity) hdom2
    rw [Real.log_mul hkp.ne' (pow_pos (by positivity : 0 < 2+d) 2).ne',Real.log_pow] at hm
    norm_num at hm
    have hm2:=mul_le_mul_of_nonneg_left hLd hlk
    nlinarith
  have hbr : Real.log (2+d)+Real.sqrt kappa*Real.log (2+kappa*Q) ≤
      (1+Real.sqrt kappa*(2+Real.log kappa))*Real.log (2+d) := by
    have hm:=mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg kappa)
    nlinarith
  have hbr0 : 0 ≤ Real.log (2+d)+Real.sqrt kappa*Real.log (2+kappa*Q) := by
    have hlog : 0 ≤ Real.log (2+kappa*Q) := Real.log_nonneg (by nlinarith)
    positivity
  have hm:=mul_le_mul h1 hbr hbr0 (by positivity : 0 ≤ (3+Real.log kappa)*Real.log (2+d))
  have hm2:=mul_le_mul_of_nonneg_left hm hdp.le
  unfold profile
  nlinarith

end
end PaperHeavyBallRateCorollaries

end SnapshotModule_138
/- END heavy_ball_rate_corollaries -/

/- BEGIN heavy_ball_source_corollaries -/
section SnapshotModule_139

namespace PaperHeavyBallComplete
open PaperHeavyBallAlgorithm PaperHeavyBallTotalRate PaperHeavyBallRateCorollaries
noncomputable section

/-- The same actual comparison program has the paper's diagonal kappa=Q rate. -/
theorem diagonal_totalCap (d : ℕ) (hd : 0 < d) (R Q : ℝ) (hR : 0 < R) (hQ : 32 ≤ Q) :
    (totalCap d Q R Q:ℝ) ≤ (6*rateConstant)*(d:ℝ)*Real.sqrt Q*(Real.log (2+(d:ℝ)*Q))^2 := by
  have hk : 1 ≤ Q := by linarith
  have hrate:=totalCap_rate d hd Q R Q hk hR hQ
  have hp:=diagonal_profile (d:ℝ) Q (by exact_mod_cast hd) hQ
  have hh:=mul_le_mul_of_nonneg_left hp rateConstant_positive.le
  have hbase : (totalCap d Q R Q:ℝ) ≤ rateConstant*profile (d:ℝ) Q Q := by
    convert hrate using 1 <;> dsimp [profile] <;> ring
  apply hbase.trans
  convert hh using 1 <;> ring

/-- For each fixed conditioning kappa, Q<=d^2 gives the stated d polylog(d)
comparison cap, with the dependence on kappa displayed rather than hidden. -/
theorem fixed_condition_totalCap (d : ℕ) (hd : 0 < d) (kappa R Q : ℝ)
    (hk : 1 ≤ kappa) (hR : 0 < R) (hQ : 32 ≤ Q) (hwindow : Q ≤ (d:ℝ)^2) :
    (totalCap d kappa R Q:ℝ) ≤
      (rateConstant*(3+Real.log kappa)*(1+Real.sqrt kappa*(2+Real.log kappa)))*(d:ℝ)*(Real.log (2+(d:ℝ)))^2 := by
  have hrate:=totalCap_rate d hd kappa R Q hk hR hQ
  have hp:=fixed_condition_profile (d:ℝ) kappa Q (by exact_mod_cast hd) hk hQ hwindow
  have hh:=mul_le_mul_of_nonneg_left hp rateConstant_positive.le
  have hbase : (totalCap d kappa R Q:ℝ) ≤ rateConstant*profile (d:ℝ) kappa Q := by
    convert hrate using 1 <;> dsimp [profile] <;> ring
  apply hbase.trans
  convert hh using 1 <;> ring

end
end PaperHeavyBallComplete

end SnapshotModule_139
/- END heavy_ball_source_corollaries -/

/- BEGIN heavy_ball_rho_margins -/
section SnapshotModule_140

namespace PaperHeavyBallRho
open Set MeasureTheory PaperHeavyBallGaussian PaperHeavyBallGaussianTail PaperHeavyBallScale
open scoped RealInnerProductSpace ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1000000

lemma scalar_margins (mu beta s S q a ai num : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hs : 0 < s) (hS : 0 < S) (hq : 0 ≤ q)
    (ha : 0 < a) (hai : 0 < ai) (haiLo : mu ≤ ai) (haiUp : ai ≤ beta)
    (haLo : mu*s^2 ≤ a) (haUp : a ≤ beta*S) (hnum : q*ai ≤ |num|) :
    q/Real.sqrt ((beta/mu)*S) ≤ |num|/Real.sqrt (ai*a) ∧
      (|num|/Real.sqrt (ai*a))/Real.sqrt ((beta/mu)*S) ≤ |num/a| ∧
      (|num|/Real.sqrt (ai*a))*s/Real.sqrt (beta/mu) ≤ |num/ai| := by
  have hb : 0 < beta := hmu.trans_le hbeta
  have hk : 0 < beta/mu := div_pos hb hmu
  have hK : 0 < (beta/mu)*S := mul_pos hk hS
  have hD : 0 < Real.sqrt (ai*a) := Real.sqrt_pos.mpr (mul_pos hai ha)
  have hKr : 0 < Real.sqrt ((beta/mu)*S) := Real.sqrt_pos.mpr hK
  have hkr : 0 < Real.sqrt (beta/mu) := Real.sqrt_pos.mpr hk
  have hsD:=Real.sq_sqrt (mul_pos hai ha).le
  have hsK:=Real.sq_sqrt hK.le
  have hsk:=Real.sq_sqrt hk.le
  have hKa : a ≤ ((beta/mu)*S)*ai := by
    calc
      _ ≤ beta*S := haUp
      _ = ((beta/mu)*S)*mu := by field_simp
      _ ≤ ((beta/mu)*S)*ai := mul_le_mul_of_nonneg_left haiLo hK.le
  have hKB : s^2*ai ≤ (beta/mu)*a := by
    calc
      _ ≤ s^2*beta := mul_le_mul_of_nonneg_left haiUp (sq_nonneg s)
      _ = (beta/mu)*(mu*s^2) := by field_simp
      _ ≤ (beta/mu)*a := mul_le_mul_of_nonneg_left haLo hk.le
  have hDupper : Real.sqrt (ai*a) ≤ ai*Real.sqrt ((beta/mu)*S) := by
    apply (sq_le_sq₀ hD.le (by positivity)).mp
    rw [mul_pow,hsD,hsK]
    have hm:=mul_le_mul_of_nonneg_left hKa hai.le
    nlinarith
  have hCden : a ≤ Real.sqrt (ai*a)*Real.sqrt ((beta/mu)*S) := by
    apply (sq_le_sq₀ ha.le (by positivity)).mp
    rw [mul_pow,hsD,hsK]
    have hm:=mul_le_mul_of_nonneg_left hKa ha.le
    nlinarith
  have hEden : s*ai ≤ Real.sqrt (ai*a)*Real.sqrt (beta/mu) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,hsD,hsk]
    have hm:=mul_le_mul_of_nonneg_left hKB hai.le
    nlinarith
  refine ⟨?_,?_,?_⟩
  · apply (div_le_div_iff₀ hKr hD).mpr
    have h1:=mul_le_mul_of_nonneg_left hDupper hq
    have h2:=mul_le_mul_of_nonneg_right hnum hKr.le
    nlinarith
  · rw [abs_div,abs_of_pos ha,div_div]
    exact div_le_div_of_nonneg_left (abs_nonneg num) ha hCden
  · rw [abs_div,abs_of_pos hai]
    have he : (|num|/Real.sqrt (ai*a))*s/Real.sqrt (beta/mu)=
        (|num| *s)/(Real.sqrt (ai*a)*Real.sqrt (beta/mu)) := by field_simp
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hD hkr) hai).mpr
    have hm:=mul_le_mul_of_nonneg_left hEden (abs_nonneg num)
    nlinarith

/-- Actual row Gaussians have the variance lower bound used in the manuscript. -/
theorem actual_row_variance (d : ℕ) (basis : OrthonormalBasis (Fin d) ℝ (Vec d))
    (A : Vec d→L[ℝ] Vec d) (mu : ℝ) (hmu : 0 < mu)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (i : Fin d) :
    mu*PaperHeavyBallScale.diagonal basis A i ≤
      Var[row basis A i; ProbabilityTheory.stdGaussian (Vec d)] := by
  rw [ProbabilityTheory.variance_dual_stdGaussian]
  have hd:=diagonal_lower basis A mu hlower i
  have hn:=row_norm_lower basis A i
  have hdp : 0 < PaperHeavyBallScale.diagonal basis A i := hmu.trans_le hd
  have hsq:=(sq_le_sq₀ hdp.le (norm_nonneg (row basis A i))).mpr hn
  nlinarith

/-- The original rho/C/E inequalities, on the actual Gaussian row event. -/
theorem actual_rho_margins (d : ℕ) (basis : OrthonormalBasis (Fin d) ℝ (Vec d))
    (A : Vec d→L[ℝ] Vec d) (mu beta s S q : ℝ)
    (hmu : 0 < mu) (hbeta : mu ≤ beta) (hs : 0 < s) (hS : 0 < S) (hq : 0 ≤ q)
    (hlower : ∀x,mu*‖x‖^2 ≤ inner ℝ x (A x)) (hupper : ∀x,inner ℝ x (A x) ≤ beta*‖x‖^2)
    (u : Vec d) (hu : u∈(calibrationBad (row basis A) s S q)ᶜ) :
    ∀ i, q/Real.sqrt ((beta/mu)*S) ≤
      |row basis A i u|/Real.sqrt (diagonal basis A i*inner ℝ u (A u)) ∧
      (|row basis A i u|/Real.sqrt (diagonal basis A i*inner ℝ u (A u)))/Real.sqrt ((beta/mu)*S) ≤
        |row basis A i u/inner ℝ u (A u)| ∧
      (|row basis A i u|/Real.sqrt (diagonal basis A i*inner ℝ u (A u)))*s/Real.sqrt (beta/mu) ≤
        |row basis A i u/diagonal basis A i| := by
  have hg:=calibration_good_properties (row basis A) s S q hu
  have ha:=calibration_seed_bounds d basis A mu beta s S q hmu hbeta hs hS hq hlower hupper u hu
  have haLo : mu*s^2 ≤ inner ℝ u (A u) := by
    have hsq : s^2 ≤ ‖u‖^2 := by nlinarith [hg.1]
    exact (mul_le_mul_of_nonneg_left hsq hmu.le).trans (hlower u)
  intro i
  have haiLo:=diagonal_lower basis A mu hlower i
  have haiUp : diagonal basis A i ≤ beta := by
    simpa only [PaperHeavyBallScale.diagonal,basis.orthonormal.norm_eq_one,one_pow,mul_one] using hupper (basis i)
  have hnum : q*diagonal basis A i ≤ |row basis A i u| :=
    (mul_le_mul_of_nonneg_left (row_norm_lower basis A i) hq).trans (hg.2.2 i).le
  exact scalar_margins mu beta s S q _ _ _ hmu hbeta hs hS hq ha.1 (hmu.trans_le haiLo)
    haiLo haiUp haLo ha.2.1 hnum

/-- Uniform-gamma calibration event with the manuscript's optimized norm
budget. All probability estimates come from actual Gaussian integrals. -/
theorem optimal_calibration_probability (d : ℕ) (hd : 0 < d)
    (L : Fin d→StrongDual ℝ (Vec d)) (hL : ∀i,L i≠0)
    (gamma : ℝ) (hg : 0 < gamma) :
    1-gamma/2 ≤ (ProbabilityTheory.stdGaussian (Vec d)).real
      (calibrationBad L (gamma/24) (normBudget d gamma) (gamma/(12*(d:ℝ))))ᶜ := by
  let i0 : Fin d:=⟨0,hd⟩
  have hdR : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hl:=gaussian_norm_lower (normalizedFunctional (L i0))
    (normalizedFunctional_norm (L i0) (hL i0)) (gamma/24) (by positivity)
  have hh:=public_norm_tail d gamma hg
  have hi:=measureReal_iUnion_fintype_le (μ:=ProbabilityTheory.stdGaussian (Vec d))
    (fun i : Fin d=>{g : Vec d | |L i g| ≤ (gamma/(12*(d:ℝ)))*‖L i‖})
  have hsum : (∑i : Fin d,(ProbabilityTheory.stdGaussian (Vec d)).real
      {g | |L i g| ≤ (gamma/(12*(d:ℝ)))*‖L i‖}) ≤ (d:ℝ)*(2*(gamma/(12*(d:ℝ)))) := by
    calc
      _ ≤ ∑_i : Fin d,2*(gamma/(12*(d:ℝ))) := Finset.sum_le_sum (fun i _=>linear_small_ball (L i) (hL i) _ (by positivity))
      _ = _ := by simp
  have he : (d:ℝ)*(2*(gamma/(12*(d:ℝ))))=gamma/6 := by field_simp <;> norm_num
  rw [he] at hsum
  have hu:=measureReal_union_le (μ:=ProbabilityTheory.stdGaussian (Vec d))
    ({g : Vec d | ‖g‖ ≤ gamma/24} ∪ {g | normBudget d gamma ≤ ‖g‖^2})
    (⋃i,{g | |L i g| ≤ (gamma/(12*(d:ℝ)))*‖L i‖})
  have hu0:=measureReal_union_le (μ:=ProbabilityTheory.stdGaussian (Vec d))
    {g : Vec d | ‖g‖ ≤ gamma/24} {g | normBudget d gamma ≤ ‖g‖^2}
  have hb : (ProbabilityTheory.stdGaussian (Vec d)).real
      (calibrationBad L (gamma/24) (normBudget d gamma) (gamma/(12*(d:ℝ)))) ≤ gamma/2 := by
    unfold calibrationBad
    linarith
  rw [measureReal_compl (calibrationBad_measurable _ _ _ _),probReal_univ]
  linarith

end
end PaperHeavyBallRho

end SnapshotModule_140
/- END heavy_ball_rho_margins -/

/- BEGIN heavy_ball_power_literal -/
section SnapshotModule_141

namespace PaperHeavyBallPowerLiteral
open PaperHeavyBallPower
noncomputable section
open scoped RealInnerProductSpace

lemma geometric_increment_bound (sigma : ℝ) (hs : 0 ≤ sigma) (k : ℕ) :
    (1+sigma)^k-1 ≤ sigma*(k:ℝ)*(1+sigma)^(k-1) := by
  cases k with
  | zero=>simp
  | succ k=>
    have hgeom:=geom_sum_mul_neg (1+sigma) (k+1)
    have hsum : (∑j∈Finset.range (k+1),(1+sigma)^j) ≤ ((k+1:ℕ):ℝ)*(1+sigma)^k := by
      calc
        _ ≤ ∑_j∈Finset.range (k+1),(1+sigma)^k := by
          apply Finset.sum_le_sum
          intro j hj
          exact pow_le_pow_right₀ (by linarith : 1 ≤ 1+sigma) (by have hh:=Finset.mem_range.mp hj;omega)
        _ = _ := by simp
    have hm:=mul_le_mul_of_nonneg_right hsum hs
    simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one] at *
    nlinarith

/-- The precise displayed perturbation estimate in the manuscript, for the
actual normalized inexact-power program's homogeneous analysis sequence. -/
theorem homogeneous_deviation_literal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : V→L[ℝ] V} (product : V→V) (R sigma M : ℝ) (hR : 0 < R)
    (hs0 : 0 ≤ sigma) (hs1 : sigma < 1) (hM : 0 ≤ M)
    (hB : ∀v,‖B v‖ ≤ M*‖v‖) (hnondegenerate : ∀v,v≠0→B v≠0)
    (hproduct : ∀v,‖v‖=R→‖product v-B v‖ ≤ sigma*‖B v‖) (w : V) (hw : w≠0) (k : ℕ) :
    ‖homogeneous R product w k-(B.toLinearMap^k) w‖ ≤
      sigma*(k:ℝ)*(1+sigma)^(k-1)*M^k*‖w‖ := by
  have hh:=homogeneous_deviation product R sigma M hR hs0 hs1 hM hB hnondegenerate hproduct w hw k
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (geometric_increment_bound sigma hs0 k) (pow_nonneg hM k)) (norm_nonneg w))

end
end PaperHeavyBallPowerLiteral

end SnapshotModule_141
/- END heavy_ball_power_literal -/
