import Mathlib

namespace PaperAudit.FenchelDistance


namespace PacketCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def EpsilonSubgradient (g : E → ℝ) (y v : E) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ w : E, g y + inner ℝ v (w - y) - ε ≤ g w

theorem strongConvex_support
    (g : E → ℝ) (μ : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (hdiff : Differentiable ℝ g) (y w : E) :
    g y + inner ℝ (gradient g y) (w - y) +
      μ / 2 * ‖w - y‖ ^ 2 ≤ g w := by
  let h : E → ℝ := fun z => g z - μ / 2 * ‖z‖ ^ 2
  have hc : ConvexOn ℝ (Set.univ : Set E) h :=
    strongConvexOn_iff_convex.mp hsc
  let a : ℝ → E := fun t => y + t • (w - y)
  have ha0 : a 0 = y := by simp [a]
  have ha1 : a 1 = w := by
    dsimp [a]
    simp only [one_smul]
    abel
  have hline : ConvexOn ℝ (Set.univ : Set ℝ)
      (fun t : ℝ => h (a t)) := by
    refine ⟨convex_univ, ?_⟩
    intro s hs t ht p q hp hq hpq
    have haff : a (p * s + q * t) = p • a s + q • a t := by
      calc
        a (p * s + q * t) =
            (p + q) • y + (p * s + q * t) • (w - y) := by
          simp only [a, hpq, one_smul]
        _ = p • a s + q • a t := by
          simp only [a, smul_add, add_smul, mul_smul]
          abel
    have hh := hc.2 (Set.mem_univ (a s)) (Set.mem_univ (a t)) hp hq hpq
    simpa only [smul_eq_mul, ← haff] using hh
  have hcurve : HasDerivAt a (w - y) (0 : ℝ) := by
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (w - y)).const_add y)
  have hgy : HasFDerivAt g (fderiv ℝ g y) (a 0) := by
    rw [ha0]
    exact (hdiff y).hasFDerivAt
  have hgcurve : HasDerivAt (fun t : ℝ => g (a t))
      (inner ℝ (gradient g y) (w - y)) 0 := by
    simpa only [Function.comp_def, inner_gradient_left] using
      (hgy.comp_hasDerivAt (0 : ℝ) hcurve)
  have hnormcurve : HasDerivAt (fun t : ℝ => ‖a t‖ ^ 2)
      (2 * inner ℝ y (w - y)) 0 := by
    simpa only [ha0] using hcurve.norm_sq
  have hder : HasDerivAt (fun t : ℝ => h (a t))
      (inner ℝ (gradient g y) (w - y) -
        μ / 2 * (2 * inner ℝ y (w - y))) 0 := by
    simpa only [h, Pi.sub_def] using
      (hgcurve.sub (hnormcurve.const_mul (μ / 2)))
  have htangent := hline.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hder
  have ht : inner ℝ (gradient g y) (w - y) -
      μ / 2 * (2 * inner ℝ y (w - y)) ≤
      (g w - μ / 2 * ‖w‖ ^ 2) -
        (g y - μ / 2 * ‖y‖ ^ 2) := by
    simpa only [slope_def_field, ha0, ha1, h, sub_zero, div_one]
      using htangent
  rw [inner_sub_right (𝕜 := ℝ) y w y,
    real_inner_self_eq_norm_sq] at ht
  rw [norm_sub_sq_real, real_inner_comm y w]
  nlinarith only [ht]


theorem gradient_eq_zero_at_global_min
    (H : E → ℝ) (z : E) (hmin : ∀ y : E, H z ≤ H y) :
    gradient H z = 0 := by
  have hloc : IsLocalMin H z := Filter.Eventually.of_forall hmin
  have hf := hloc.fderiv_eq_zero
  have hi : inner ℝ (gradient H z) (gradient H z) = 0 := by
    rw [inner_gradient_left, hf]
    simp
  rw [real_inner_self_eq_norm_sq] at hi
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (gradient H z)]

theorem gradient_strong_monotone
    (H : E → ℝ) (k : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) k H)
    (hdiff : Differentiable ℝ H) (y z : E) :
    k * ‖y - z‖ ^ 2 ≤
      inner ℝ (gradient H y - gradient H z) (y - z) := by
  have h1 := strongConvex_support H k hsc hdiff y z
  have h2 := strongConvex_support H k hsc hdiff z y
  have hneg : z - y = -(y - z) := by abel
  rw [norm_sub_rev z y] at h1
  rw [hneg, inner_neg_right] at h1
  rw [inner_sub_left]
  nlinarith only [h1, h2]

theorem strongConvex_gradient_distance
    (H : E → ℝ) (k : ℝ) (hk : 0 < k)
    (hsc : StrongConvexOn (Set.univ : Set E) k H)
    (hdiff : Differentiable ℝ H) (z : E)
    (hmin : ∀ y : E, H z ≤ H y) (y : E) :
    k * ‖y - z‖ ≤ ‖gradient H y‖ := by
  have hz := gradient_eq_zero_at_global_min H z hmin
  have h1 := gradient_strong_monotone H k hsc hdiff y z
  rw [hz, sub_zero] at h1
  have h2 := real_inner_le_norm (gradient H y) (y - z)
  by_cases ht : ‖y - z‖ = 0
  · simpa [ht] using norm_nonneg (gradient H y)
  · have htpos : 0 < ‖y - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht)
    nlinarith only [h1, h2, htpos]


noncomputable def saddleValue (H : E → ℝ) (β c lam m : ℝ) (x y : E) : ℝ :=
  β / 2 * ‖x‖ ^ 2 + lam * inner ℝ x y - (H y - c / 2 * ‖y‖ ^ 2) + m

theorem inner_maximizer_first_order
    (H : E → ℝ) (β c lam m : ℝ) (x y : E)
    (hdiff : Differentiable ℝ H)
    (hmax : ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y) :
    gradient H y = lam • x + c • y := by
  apply ext_inner_right ℝ
  intro v
  let a : ℝ → E := fun t => y + t • v
  have ha0 : a 0 = y := by simp [a]
  have hcurve : HasDerivAt a v (0 : ℝ) := by
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y)
  have hH : HasDerivAt (fun t : ℝ => H (a t))
      (inner ℝ (gradient H y) v) 0 := by
    have hHy : HasFDerivAt H (fderiv ℝ H y) (a 0) := by
      rw [ha0]
      exact (hdiff y).hasFDerivAt
    simpa only [Function.comp_def, inner_gradient_left] using
      (hHy.comp_hasDerivAt (0 : ℝ) hcurve)
  have hi : HasDerivAt (fun t : ℝ => inner ℝ x (a t))
      (inner ℝ x v) 0 := by
    simpa only [inner_zero_left, zero_add, add_zero] using
      (HasDerivAt.inner ℝ (hasDerivAt_const (0 : ℝ) x) hcurve)
  have hn : HasDerivAt (fun t : ℝ => ‖a t‖ ^ 2)
      (2 * inner ℝ y v) 0 := by
    simpa only [ha0] using hcurve.norm_sq
  have hp : HasDerivAt
      (fun t : ℝ => lam * inner ℝ x (a t) - (H (a t) - c / 2 * ‖a t‖ ^ 2))
      (lam * inner ℝ x v - (inner ℝ (gradient H y) v -
        c / 2 * (2 * inner ℝ y v))) 0 :=
    (hi.const_mul lam).sub (hH.sub (hn.const_mul (c / 2)))
  have hpmax : IsLocalMax
      (fun t : ℝ => lam * inner ℝ x (a t) - (H (a t) - c / 2 * ‖a t‖ ^ 2)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hh := hmax (a t)
    dsimp [saddleValue] at hh
    dsimp only
    rw [ha0]
    linarith only [hh]
  have hz := hpmax.hasDerivAt_eq_zero hp
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  nlinarith only [hz]

theorem fenchel_first_order_identity
    (H : E → ℝ) (β c lam m : ℝ) (x y : E)
    (hβ : 0 < β) (hc : 0 < c) (hrel : lam ^ 2 = β * c)
    (hdiff : Differentiable ℝ H)
    (hmax : ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y) :
    gradient H y = c • (y - (-β / lam) • x) := by
  have hlam : lam ≠ 0 := by
    intro hzero
    rw [hzero] at hrel
    nlinarith [mul_pos hβ hc]
  have hcoef : c * (-β / lam) = -lam := by
    field_simp
    nlinarith only [hrel]
  rw [inner_maximizer_first_order H β c lam m x y hdiff hmax,
    smul_sub, smul_smul, hcoef, neg_smul]
  abel

theorem fenchel_candidate_identity
    (β lam : ℝ) (hlam : lam ≠ 0) (x y : E) :
    β • x + lam • y = lam • (y - (-β / lam) • x) := by
  have hcoef : lam * (-β / lam) = -β := by field_simp
  rw [smul_sub, smul_smul, hcoef, neg_smul]
  abel

theorem fenchel_stationarity_distance_core
    (H : E → ℝ) (μ β c lam m : ℝ) (x y z : E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w)
    (hmax : ∀ w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x y) :
    lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
      ‖β • x + lam • y‖ := by
  have hk : 0 < μ + c := by positivity
  have hlam : lam ≠ 0 := by
    intro hzero
    rw [hzero] at hrel
    nlinarith [mul_pos hβ hc]
  let w : E := (-β / lam) • x
  have hg := fenchel_first_order_identity H β c lam m x y hβ hc hrel hdiff hmax
  change gradient H y = c • (y - w) at hg
  have hd := strongConvex_gradient_distance H (μ + c) hk hsc hdiff z hmin y
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hd
  have ht : ‖w - z‖ ≤ ‖y - w‖ + ‖y - z‖ := by
    calc
      ‖w - z‖ ≤ ‖w - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub w y z
      _ = ‖y - w‖ + ‖y - z‖ := by rw [norm_sub_rev w y]
  have hraw : (μ + c) * ‖w - z‖ ≤ (μ + c + c) * ‖y - w‖ := by
    have ht' := mul_le_mul_of_nonneg_left ht (le_of_lt hk)
    nlinarith only [ht', hd]
  have hv := fenchel_candidate_identity β lam hlam x y
  change β • x + lam • y = lam • (y - w) at hv
  rw [hv, norm_smul, Real.norm_eq_abs]
  change lam / (1 + c / (μ + c)) * ‖w - z‖ ≤ |lam| * ‖y - w‖
  have hden : 0 < 1 + c / (μ + c) := by positivity
  by_cases hsign : 0 < lam
  · rw [abs_of_pos hsign]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_left hraw (le_of_lt hsign)
    apply (mul_le_mul_iff_left₀ hk).mp
    have hscaled : lam * ‖y - w‖ * (1 + c / (μ + c)) * (μ + c) =
        lam * (μ + c + c) * ‖y - w‖ := by
      field_simp
      <;> ring
    rw [hscaled]
    nlinarith only [hmul]
  · have hlamle : lam ≤ 0 := le_of_not_gt hsign
    have hleft : lam / (1 + c / (μ + c)) * ‖w - z‖ ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hlamle (le_of_lt hden)) (norm_nonneg _)
    exact le_trans hleft (mul_nonneg (abs_nonneg _) (norm_nonneg _))


noncomputable def valueFromMaximizers (H : E → ℝ) (β c lam m : ℝ) (Y : E → E) (x : E) : ℝ :=
  saddleValue H β c lam m x (Y x)

theorem value_strongConvex_from_actual_maximizers
    (H : E → ℝ) (β c lam m : ℝ) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x)) :
    StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam m Y) := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  let t : E := a • x + b • z
  let y : E := Y t
  have h1 := mul_le_mul_of_nonneg_left (hY x y) ha
  have h2 := mul_le_mul_of_nonneg_left (hY z y) hb
  have hlin : saddleValue H β c lam m t y - β / 2 * ‖t‖ ^ 2 =
      a * (saddleValue H β c lam m x y - β / 2 * ‖x‖ ^ 2) +
      b * (saddleValue H β c lam m z y - β / 2 * ‖z‖ ^ 2) := by
    dsimp [saddleValue, t]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hbeq : b = 1 - a := by linarith only [hab]
    rw [hbeq]
    ring
  change saddleValue H β c lam m t y - β / 2 * ‖t‖ ^ 2 ≤
    a * (saddleValue H β c lam m x (Y x) - β / 2 * ‖x‖ ^ 2) +
    b * (saddleValue H β c lam m z (Y z) - β / 2 * ‖z‖ ^ 2)
  nlinarith only [hlin, h1, h2]

theorem saddle_complete_square
    (H : E → ℝ) (β c lam m : ℝ) (hβ : 0 < β)
    (hrel : lam ^ 2 = β * c) (x y : E) :
    saddleValue H β c lam m x y =
      β / 2 * ‖x + (lam / β) • y‖ ^ 2 - H y + m := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hcformula : c = lam ^ 2 / β := by
    apply (eq_div_iff hβne).mpr
    nlinarith only [hrel]
  dsimp [saddleValue]
  rw [hcformula, norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  <;> ring

theorem saddle_at_candidate_minimum
    (H : E → ℝ) (β c lam m : ℝ) (hβ : 0 < β)
    (hrel : lam ^ 2 = β * c) (z y : E) :
    saddleValue H β c lam m ((-lam / β) • z) y =
      c / 2 * ‖y - z‖ ^ 2 - H y + m := by
  rw [saddle_complete_square H β c lam m hβ hrel]
  have hvec : (-lam / β) • z + (lam / β) • y = (lam / β) • (y - z) := by
    rw [smul_sub, neg_div, neg_smul]
    abel
  rw [hvec, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hcoef : β / 2 * (lam / β) ^ 2 = c / 2 := by
    field_simp
    nlinarith only [hrel]
  calc
    β / 2 * ((lam / β) ^ 2 * ‖y - z‖ ^ 2) - H y + m =
        (β / 2 * (lam / β) ^ 2) * ‖y - z‖ ^ 2 - H y + m := by ring
    _ = c / 2 * ‖y - z‖ ^ 2 - H y + m := by rw [hcoef]

theorem value_minimum_zero_from_actual_maximizers
    (H : E → ℝ) (μ β c lam : ℝ) (z : E) (Y : E → E)
    (hμ : 0 < μ) (hβ : 0 < β) (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w)
    (hY : ∀ x w : E, saddleValue H β c lam (H z) x w ≤
      saddleValue H β c lam (H z) x (Y x)) :
    (∀ x : E, 0 ≤ valueFromMaximizers H β c lam (H z) Y x) ∧
    valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
    (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
      valueFromMaximizers H β c lam (H z) Y x) := by
  have hnonneg : ∀ x : E, 0 ≤ valueFromMaximizers H β c lam (H z) Y x := by
    intro x
    have hs := hY x z
    have hp : 0 ≤ saddleValue H β c lam (H z) x z := by
      rw [saddle_complete_square H β c lam (H z) hβ hrel]
      have hq : 0 ≤ β / 2 * ‖x + (lam / β) • z‖ ^ 2 := by positivity
      linarith only [hq]
    exact le_trans hp hs
  have hg : gradient H z = 0 := gradient_eq_zero_at_global_min H z hmin
  have hupper : ∀ y : E, saddleValue H β c lam (H z) ((-lam / β) • z) y ≤ 0 := by
    intro y
    have hs := strongConvex_support H (μ + c) hsc hdiff z y
    rw [hg, inner_zero_left] at hs
    rw [saddle_at_candidate_minimum H β c lam (H z) hβ hrel]
    nlinarith only [hs, mul_nonneg (le_of_lt hμ) (sq_nonneg ‖y - z‖)]
  have hzero : valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 := by
    apply le_antisymm
    · exact hupper (Y ((-lam / β) • z))
    · exact hnonneg _
  exact ⟨hnonneg, hzero, fun x => by rw [hzero]; exact hnonneg x⟩


theorem saddle_inner_quadratic_gap
    (H : E → ℝ) (μ β c lam m : ℝ) (x y : E)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H)
    (hmax : ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y)
    (z : E) :
    saddleValue H β c lam m x z ≤
      saddleValue H β c lam m x y - μ / 2 * ‖z - y‖ ^ 2 := by
  have hs := strongConvex_support H (μ + c) hsc hdiff y z
  rw [inner_maximizer_first_order H β c lam m x y hdiff hmax,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq] at hs
  rw [norm_sub_sq_real, real_inner_comm z y] at hs
  dsimp [saddleValue]
  rw [norm_sub_sq_real]
  nlinarith only [hs]

theorem saddle_change_center
    (H : E → ℝ) (β c lam m : ℝ) (x x' y z : E) :
    saddleValue H β c lam m x' z - saddleValue H β c lam m x' y =
      saddleValue H β c lam m x z - saddleValue H β c lam m x y +
        lam * inner ℝ (x' - x) (z - y) := by
  dsimp [saddleValue]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  ring

theorem scalar_young (μ A t : ℝ) (hμ : 0 < μ) :
    A * t ≤ μ / 2 * t ^ 2 + A ^ 2 / (2 * μ) := by
  have hden : 0 < 2 * μ := by positivity
  have hcancel : A ^ 2 / (2 * μ) * (2 * μ) = A ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  apply (mul_le_mul_iff_right₀ hμ).mp
  nlinarith only [hcancel, sq_nonneg (μ * t - A)]

theorem value_maximization_gap
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x x' : E) :
    0 ≤ valueFromMaximizers H β c lam m Y x' - saddleValue H β c lam m x' (Y x) ∧
    valueFromMaximizers H β c lam m Y x' - saddleValue H β c lam m x' (Y x) ≤
      lam ^ 2 / (2 * μ) * ‖x' - x‖ ^ 2 := by
  constructor
  · exact sub_nonneg.mpr (hY x' (Y x))
  · have hs := saddle_inner_quadratic_gap H μ β c lam m x (Y x) hsc hdiff
        (hY x) (Y x')
    have hid := saddle_change_center H β c lam m x x' (Y x) (Y x')
    have hi : lam * inner ℝ (x' - x) (Y x' - Y x) ≤
        (|lam| * ‖x' - x‖) * ‖Y x' - Y x‖ := by
      have ht := real_inner_le_norm (lam • (x' - x)) (Y x' - Y x)
      simpa only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_assoc] using ht
    have hy := scalar_young μ (|lam| * ‖x' - x‖) ‖Y x' - Y x‖ hμ
    have hcoeff : (|lam| * ‖x' - x‖) ^ 2 / (2 * μ) =
        lam ^ 2 / (2 * μ) * ‖x' - x‖ ^ 2 := by
      rw [mul_pow, sq_abs]
      ring
    rw [hcoeff] at hy
    change saddleValue H β c lam m x' (Y x') - saddleValue H β c lam m x' (Y x) ≤ _
    nlinarith only [hs, hid, hi, hy]

theorem saddle_outer_remainder
    (H : E → ℝ) (β c lam m : ℝ) (x x' y : E) :
    saddleValue H β c lam m x' y - saddleValue H β c lam m x y -
      inner ℝ (β • x + lam • y) (x' - x) = β / 2 * ‖x' - x‖ ^ 2 := by
  dsimp [saddleValue]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    norm_sub_sq_real, real_inner_comm x' x, real_inner_comm y x', real_inner_comm y x]
  ring

theorem value_quadratic_remainder
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x x' : E) :
    ‖valueFromMaximizers H β c lam m Y x' - valueFromMaximizers H β c lam m Y x -
      inner ℝ (β • x + lam • Y x) (x' - x)‖ ≤
      (β / 2 + lam ^ 2 / (2 * μ)) * ‖x' - x‖ ^ 2 := by
  obtain ⟨hlo, hup⟩ := value_maximization_gap H μ β c lam m hμ hsc hdiff Y hY x x'
  have hid := saddle_outer_remainder H β c lam m x x' (Y x)
  have hq : 0 ≤ β / 2 * ‖x' - x‖ ^ 2 := by positivity
  have hnonneg : 0 ≤ valueFromMaximizers H β c lam m Y x' -
      valueFromMaximizers H β c lam m Y x -
      inner ℝ (β • x + lam • Y x) (x' - x) := by
    dsimp [valueFromMaximizers] at *
    linarith only [hlo, hid, hq]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp [valueFromMaximizers] at *
  nlinarith only [hup, hid]

theorem hasGradientAt_of_quadratic_remainder
    (F : E → ℝ) (v x : E) (C : ℝ)
    (hbound : ∀ z : E, ‖F z - F x - inner ℝ v (z - x)‖ ≤ C * ‖z - x‖ ^ 2) :
    HasGradientAt F v x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : E => F (x + h) - F x - (InnerProductSpace.toDual ℝ E v) h)
      =O[nhds 0] (fun h : E => ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    apply Filter.Eventually.of_forall
    intro h
    simpa using hbound (x + h)
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2))

theorem value_hasGradientAt_from_actual_maximizers
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x : E) :
    HasGradientAt (valueFromMaximizers H β c lam m Y) (β • x + lam • Y x) x := by
  exact hasGradientAt_of_quadratic_remainder _ _ _ _
    (value_quadratic_remainder H μ β c lam m hμ hβ hsc hdiff Y hY x)

theorem value_gradient_identity_from_actual_maximizers
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x : E) :
    gradient (valueFromMaximizers H β c lam m Y) x = β • x + lam • Y x := by
  have hd := value_hasGradientAt_from_actual_maximizers H μ β c lam m hμ hβ hsc hdiff Y hY x
  exact (hd.differentiableAt.hasGradientAt.unique hd)


theorem saddle_upper_quadratic_from_zero
    (H : E → ℝ) (μ β c lam m : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (x y : E) :
    saddleValue H β c lam m x y - saddleValue H β c lam m x 0 ≤
      (|lam| * ‖x‖ + ‖gradient H 0‖) * ‖y‖ - μ / 2 * ‖y‖ ^ 2 := by
  have hs := strongConvex_support H (μ + c) hsc hdiff 0 y
  simp only [sub_zero] at hs
  have h1 := real_inner_le_norm (lam • x) y
  have h2 := real_inner_le_norm (-gradient H 0) y
  simp only [real_inner_smul_left, norm_smul, Real.norm_eq_abs] at h1
  simp only [inner_neg_left, norm_neg] at h2
  dsimp [saddleValue]
  simp only [inner_zero_right, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, sub_zero]
  nlinarith only [hs, h1, h2]

theorem exists_inner_maximizer_finiteDimensional
    [FiniteDimensional ℝ E]
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (x : E) :
    ∃ y : E, ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y := by
  let B : ℝ := |lam| * ‖x‖ + ‖gradient H 0‖
  let R : ℝ := (2 * B + 1) / μ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_self]
    exact le_of_lt hR
  have hHcont : Continuous H := hdiff.continuous
  have hcont : Continuous (fun y : E => saddleValue H β c lam m x y) := by
    dsimp [saddleValue]
    fun_prop
  obtain ⟨y, hy, hmax⟩ :=
    (isCompact_closedBall (0 : E) R).exists_isMaxOn ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨y, ?_⟩
  intro z
  by_cases hz : z ∈ Metric.closedBall 0 R
  · exact hmax hz
  · have hzR : R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    have hzpos : 0 < ‖z‖ := lt_trans hR hzR
    have hμz : 2 * B + 1 < ‖z‖ * μ := (div_lt_iff₀ hμ).mp hzR
    have hneg : B * ‖z‖ - μ / 2 * ‖z‖ ^ 2 < 0 := by
      have hcoef : 0 < μ / 2 * ‖z‖ - B := by nlinarith only [hμz]
      have hp := mul_pos hcoef hzpos
      nlinarith only [hp]
    have hub := saddle_upper_quadratic_from_zero H μ β c lam m hsc hdiff x z
    change saddleValue H β c lam m x z - saddleValue H β c lam m x 0 ≤
      B * ‖z‖ - μ / 2 * ‖z‖ ^ 2 at hub
    have h0 : saddleValue H β c lam m x 0 ≤ saddleValue H β c lam m x y := hmax hzero
    linarith only [hub, hneg, h0]

theorem fenchel_transfer_with_actual_maximizers
    (H : E → ℝ) (μ β c lam : ℝ) (z : E) (Y : E → E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w)
    (hY : ∀ x w : E, saddleValue H β c lam (H z) x w ≤
      saddleValue H β c lam (H z) x (Y x)) :
    (∀ x : E, gradient (valueFromMaximizers H β c lam (H z) Y) x =
      lam • (Y x - (-β / lam) • x)) ∧
    (∀ x : E, gradient H (Y x) = c • (Y x - (-β / lam) • x)) ∧
    (∀ x : E, lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
      ‖gradient (valueFromMaximizers H β c lam (H z) Y) x‖) ∧
    StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam (H z) Y) ∧
    valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
    (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
      valueFromMaximizers H β c lam (H z) Y x) := by
  have hlam : lam ≠ 0 := by
    intro hzero
    rw [hzero] at hrel
    nlinarith [mul_pos hβ hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [value_gradient_identity_from_actual_maximizers H μ β c lam (H z) hμ hβ hsc hdiff Y hY x]
    exact fenchel_candidate_identity β lam hlam x (Y x)
  · intro x
    exact fenchel_first_order_identity H β c lam (H z) x (Y x) hβ hc hrel hdiff (hY x)
  · intro x
    rw [value_gradient_identity_from_actual_maximizers H μ β c lam (H z) hμ hβ hsc hdiff Y hY x]
    exact fenchel_stationarity_distance_core H μ β c lam (H z) x (Y x) z hμ hβ hc hrel hsc hdiff hmin (hY x)
  · exact value_strongConvex_from_actual_maximizers H β c lam (H z) Y hY
  · exact (value_minimum_zero_from_actual_maximizers H μ β c lam z Y hμ hβ hrel hsc hdiff hmin hY).2.1
  · exact (value_minimum_zero_from_actual_maximizers H μ β c lam z Y hμ hβ hrel hsc hdiff hmin hY).2.2

theorem fenchel_transfer_finiteDimensional_smooth
    [FiniteDimensional ℝ E]
    (H : E → ℝ) (μ β c lam : ℝ) (z : E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w) :
    ∃ Y : E → E,
      (∀ x w : E, saddleValue H β c lam (H z) x w ≤
        saddleValue H β c lam (H z) x (Y x)) ∧
      (∀ x : E, gradient (valueFromMaximizers H β c lam (H z) Y) x =
        lam • (Y x - (-β / lam) • x)) ∧
      (∀ x : E, gradient H (Y x) = c • (Y x - (-β / lam) • x)) ∧
      (∀ x : E, lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
        ‖gradient (valueFromMaximizers H β c lam (H z) Y) x‖) ∧
      StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam (H z) Y) ∧
      valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
      (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
        valueFromMaximizers H β c lam (H z) Y x) := by
  classical
  let Y : E → E := fun x => Classical.choose
    (exists_inner_maximizer_finiteDimensional H μ β c lam (H z) hμ hsc hdiff x)
  have hY : ∀ x w : E, saddleValue H β c lam (H z) x w ≤
      saddleValue H β c lam (H z) x (Y x) := by
    intro x
    exact Classical.choose_spec
      (exists_inner_maximizer_finiteDimensional H μ β c lam (H z) hμ hsc hdiff x)
  exact ⟨Y, hY, fenchel_transfer_with_actual_maximizers H μ β c lam z Y hμ hβ hc hrel hsc hdiff hmin hY⟩


theorem value_independent_of_maximizer_selection
    (H : E → ℝ) (β c lam m : ℝ) (Y Z : E → E)
    (hY : ∀ x w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x (Y x))
    (hZ : ∀ x w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x (Z x)) :
    valueFromMaximizers H β c lam m Y = valueFromMaximizers H β c lam m Z := by
  funext x
  apply le_antisymm
  · exact hZ x (Y x)
  · exact hY x (Z x)

theorem unique_inner_maximizer
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (x y z : E)
    (hy : ∀ w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x y)
    (hz : ∀ w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x z) :
    y = z := by
  have hgap := saddle_inner_quadratic_gap H μ β c lam m x y hsc hdiff hy z
  have hrev := hz y
  have hsq : ‖z - y‖ ^ 2 = 0 := by
    have hn := sq_nonneg ‖z - y‖
    nlinarith only [hgap, hrev, hn, hμ]
  have hn : ‖z - y‖ = 0 := by nlinarith only [hsq, norm_nonneg (z - y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm


theorem H_differentiable_from_zero_slice
    (H : E → ℝ) (β c lam m : ℝ)
    (hslice : Differentiable ℝ (fun y : E => saddleValue H β c lam m 0 y)) :
    Differentiable ℝ H := by
  have hn0 : Differentiable ℝ (fun y : E => ‖y‖ ^ 2) :=
    fun y => (hasStrictFDerivAt_norm_sq y).hasFDerivAt.differentiableAt
  have hn : Differentiable ℝ (fun y : E => c / 2 * ‖y‖ ^ 2) := hn0.const_mul (c / 2)
  have hformula : H = fun y : E => -saddleValue H β c lam m 0 y + c / 2 * ‖y‖ ^ 2 + m := by
    funext y
    simp only [saddleValue, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, inner_zero_left, zero_add]
    ring
  rw [hformula]
  exact (hslice.neg.add hn).add_const m

theorem H_differentiable_from_global_saddle
    (H : E → ℝ) (β c lam m : ℝ)
    (hglobal : Differentiable ℝ (fun p : E × E => saddleValue H β c lam m p.1 p.2)) :
    Differentiable ℝ H := by
  have hpair : Differentiable ℝ (fun y : E => ((0 : E), y)) := by fun_prop
  have hs := hglobal.comp hpair
  apply H_differentiable_from_zero_slice H β c lam m
  simpa only [Function.comp_def] using hs

theorem fenchel_transfer_finiteDimensional_from_C2_saddle
    [FiniteDimensional ℝ E]
    (H : E → ℝ) (μ β c lam : ℝ) (z : E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hsaddle : ContDiff ℝ 2 (fun p : E × E => saddleValue H β c lam (H z) p.1 p.2)) (hmin : ∀ w : E, H z ≤ H w) :
    ∃ Y : E → E,
      (∀ x w : E, saddleValue H β c lam (H z) x w ≤
        saddleValue H β c lam (H z) x (Y x)) ∧
      (∀ x : E, gradient (valueFromMaximizers H β c lam (H z) Y) x =
        lam • (Y x - (-β / lam) • x)) ∧
      (∀ x : E, gradient H (Y x) = c • (Y x - (-β / lam) • x)) ∧
      (∀ x : E, lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
        ‖gradient (valueFromMaximizers H β c lam (H z) Y) x‖) ∧
      StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam (H z) Y) ∧
      valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
      (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
        valueFromMaximizers H β c lam (H z) Y x)  := by
  have hg : Differentiable ℝ (fun p : E × E => saddleValue H β c lam (H z) p.1 p.2) :=
    hsaddle.differentiable (by norm_num)
  have hH : Differentiable ℝ H := H_differentiable_from_global_saddle H β c lam (H z) hg
  exact fenchel_transfer_finiteDimensional_smooth H μ β c lam z hμ hβ hc hrel hsc hH hmin

end PacketCore

end PaperAudit.FenchelDistance
