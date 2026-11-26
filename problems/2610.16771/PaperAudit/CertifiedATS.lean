import Mathlib

namespace PaperAudit.CertifiedATS



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

end PacketCore


namespace OriginalCoerciveOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem injective_of_coercive
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    Function.Injective A := by
  intro x y hxy
  have hzero : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := hcoercive (x - y)
  rw [hzero, inner_zero_left] at h
  have hs : ‖x - y‖ ^ 2 ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [mul_zero] using h
  have hn : ‖x - y‖ = 0 := by nlinarith only [hs, norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem bijective_of_coercive
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    Function.Bijective A := by
  have hi := injective_of_coercive A m hm hcoercive
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi⟩

noncomputable def equivalenceOfCoercive
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (bijective_of_coercive A m hm hcoercive).1)
    (LinearMap.range_eq_top.mpr (bijective_of_coercive A m hm hcoercive).2)

theorem equivalenceOfCoercive_apply
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (v : E) :
    equivalenceOfCoercive A m hm hcoercive v = A v := rfl

theorem norm_vector_le_image_div
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) (v : E) :
    ‖v‖ ≤ ‖A v‖ / m := by
  have h1 := hcoercive v
  have h2 := real_inner_le_norm (A v) v
  apply (le_div_iff₀ hm).mpr
  by_cases hv : ‖v‖ = 0
  · rw [hv, zero_mul]
    exact norm_nonneg _
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [h1, h2])

theorem inverse_norm_le
    (A : E →L[ℝ] E) (m : ℝ) (hm : 0 < m)
    (hcoercive : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    ‖(equivalenceOfCoercive A m hm hcoercive).symm.toContinuousLinearMap‖ ≤ 1 / m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 1 / m)
  intro x
  have h := norm_vector_le_image_div A m hm hcoercive
    ((equivalenceOfCoercive A m hm hcoercive).symm x)
  have heq : A ((equivalenceOfCoercive A m hm hcoercive).symm x) = x :=
    (equivalenceOfCoercive A m hm hcoercive).apply_symm_apply x
  rw [heq] at h
  change ‖(equivalenceOfCoercive A m hm hcoercive).symm x‖ ≤ (1 / m) * ‖x‖
  calc
    _ ≤ ‖x‖ / m := h
    _ = (1 / m) * ‖x‖ := by ring

theorem inverse_resolvent_identity (A B : E ≃L[ℝ] E) :
    A.symm.toContinuousLinearMap - B.symm.toContinuousLinearMap =
      A.symm.toContinuousLinearMap.comp
        ((B.toContinuousLinearMap - A.toContinuousLinearMap).comp B.symm.toContinuousLinearMap) := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, map_sub, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem inverse_difference_norm
    (A B : E ≃L[ℝ] E) :
    ‖A.symm.toContinuousLinearMap - B.symm.toContinuousLinearMap‖ ≤
      ‖A.symm.toContinuousLinearMap‖ * ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ *
        ‖B.symm.toContinuousLinearMap‖ := by
  rw [inverse_resolvent_identity]
  let P := A.symm.toContinuousLinearMap
  let R := B.toContinuousLinearMap - A.toContinuousLinearMap
  let S := B.symm.toContinuousLinearMap
  change ‖P.comp (R.comp S)‖ ≤ ‖P‖ * ‖R‖ * ‖S‖
  calc
    ‖P.comp (R.comp S)‖ ≤ ‖P‖ * ‖R.comp S‖ := ContinuousLinearMap.opNorm_comp_le P (R.comp S)
    _ ≤ ‖P‖ * (‖R‖ * ‖S‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le R S) (norm_nonneg P)
    _ = ‖P‖ * ‖R‖ * ‖S‖ := (mul_assoc _ _ _).symm

theorem derivative_coercive_of_strong_monotonicity
    (T : E → E) (m : ℝ)
    (hstrong : ∀ x y : E, m * ‖x - y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y))
    (z : E) (D : E →L[ℝ] E) (hD : HasFDerivAt T D z) (v : E) :
    m * ‖v‖ ^ 2 ≤ inner ℝ (D v) v := by
  let φ : ℝ → ℝ := fun t => inner ℝ (T (z + t • v)) v - (m * ‖v‖ ^ 2) * t
  have hmono : Monotone φ := by
    intro s t hst
    by_cases heq : s = t
    · rw [heq]
    · have hd : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst heq)
      have hdif : (z + t • v) - (z + s • v) = (t - s) • v := by module
      have hh := hstrong (z + t • v) (z + s • v)
      rw [hdif, norm_smul, Real.norm_eq_abs, abs_of_pos hd,
        mul_pow, inner_smul_right] at hh
      have hfactor : (t - s) * (m * (t - s) * ‖v‖ ^ 2) ≤
          (t - s) * inner ℝ (T (z + t • v) - T (z + s • v)) v := by
        nlinarith only [hh]
      have hc := (mul_le_mul_iff_right₀ hd).mp hfactor
      rw [inner_sub_left] at hc
      dsimp only [φ]
      nlinarith only [hc]
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) z).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;>
      first | rfl | simp only [zero_add, one_smul, Pi.add_apply, id_eq]
  have hcomp : HasDerivAt (fun t : ℝ => T (z + t • v)) (D v) 0 := by
    exact hD.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hscalar : HasDerivAt φ (inner ℝ (D v) v - m * ‖v‖ ^ 2) 0 := by
    convert (hcomp.inner ℝ (hasDerivAt_const (0 : ℝ) v)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (m * ‖v‖ ^ 2)) using 1 <;>
      first | rfl | simp only [inner_zero_right, add_zero, zero_add, mul_one]
  have hp := hscalar.nonneg_of_monotone hmono
  linarith only [hp]

end OriginalCoerciveOperator

namespace CertifiedATS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_derivative_selfadjoint
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J) (w : Z) :
    (fderiv ℝ (gradient J) w).adjoint = fderiv ℝ (gradient J) w := by
  have hfd := ((hC2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) w).hasFDerivAt
  have hgrad : HasFDerivAt (gradient J)
      ((InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ J) w)) w := by
    convert! (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
      w hfd using 1 <;> rfl
  have hs : IsSymmSndFDerivAt ℝ J w := hC2.contDiffAt.isSymmSndFDerivAt (by simp)
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro a b
  rw [hgrad.fderiv]
  change inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
      (fderiv ℝ (fderiv ℝ J) w a)) b =
    inner ℝ a ((InnerProductSpace.toDual ℝ Z).symm (fderiv ℝ (fderiv ℝ J) w b))
  calc
    inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w a)) b = fderiv ℝ (fderiv ℝ J) w a b :=
      InnerProductSpace.toDual_symm_apply
    _ = fderiv ℝ (fderiv ℝ J) w b a := hs a b
    _ = inner ℝ ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w b)) a := InnerProductSpace.toDual_symm_apply.symm
    _ = inner ℝ a ((InnerProductSpace.toDual ℝ Z).symm
        (fderiv ℝ (fderiv ℝ J) w b)) := real_inner_comm _ _


theorem convex_of_global_support
    (g : E → ℝ) (v : E → E)
    (hsupport : ∀ x y : E, g x + inner ℝ (v x) (y - x) ≤ g y) :
    ConvexOn ℝ (Set.univ : Set E) g := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hzero : a • (x - z) + b • (y - z) = 0 := by
    calc
      a • (x - z) + b • (y - z) = a • x + b • y - (a + b) • z := by
        simp only [smul_sub, add_smul]
        abel
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi := congrArg (fun w : E => inner ℝ (v z) w) hzero
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  have h1 := mul_le_mul_of_nonneg_left (hsupport z x) ha
  have h2 := mul_le_mul_of_nonneg_left (hsupport z y) hb
  change g z ≤ a * g x + b * g y
  calc
    g z = (a + b) * g z := by rw [hab, one_mul]
    _ = a * (g z + inner ℝ (v z) (x - z)) +
        b * (g z + inner ℝ (v z) (y - z)) := by nlinarith only [hi]
    _ ≤ a * g x + b * g y := add_le_add h1 h2


theorem gradient_differentiable (F : E → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : gradient F = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) := rfl
  rw [heq]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder).differentiable (by norm_num)


noncomputable def sympart (H : E →L[ℝ] E) : E →L[ℝ] E := (1 / 2 : ℝ) • (H + H.adjoint)

noncomputable def model (v : E) (H : E →L[ℝ] E) (Mbar lam : ℝ) (d : E) : ℝ :=
  inner ℝ v d + (1 / 2 : ℝ) * inner ℝ (H d) d +
    Mbar / 6 * ‖d‖ ^ 3 + 1 / (2 * lam) * ‖d‖ ^ 2

noncomputable def trueVector (v : E) (H : E →L[ℝ] E) (Mbar : ℝ) (d : E) : E :=
  v + H d + (Mbar / 2 * ‖d‖) • d

theorem sympart_selfadjoint (H : E →L[ℝ] E) : (sympart H).adjoint = sympart H := by
  simp [sympart, map_smul, map_add, add_comm]

theorem sympart_same_quadratic (H : E →L[ℝ] E) (d : E) :
    inner ℝ (sympart H d) d = inner ℝ (H d) d := by
  simp only [sympart, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    real_inner_smul_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm d (H d)]
  ring

theorem sympart_error_bound (H K : E →L[ℝ] E) (hK : K.adjoint = K) :
    ‖sympart H - K‖ ≤ ‖H - K‖ := by
  have he : sympart H - K = (1 / 2 : ℝ) • ((H - K) + (H - K).adjoint) := by
    simp only [sympart, map_sub, hK]
    module
  rw [he, norm_smul]
  have ht := norm_add_le (H - K) (H - K).adjoint
  rw [ContinuousLinearMap.adjoint.norm_map] at ht
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith only [ht]

theorem actual_hessian_coercive (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (mu : ℝ) (hsc : StrongConvexOn (Set.univ : Set E) mu g) (z d : E) :
    mu * ‖d‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient g) z d) d := by
  exact OriginalCoerciveOperator.derivative_coercive_of_strong_monotonicity (gradient g) mu
    (PacketCore.gradient_strong_monotone g mu hsc (hC2.differentiable (by norm_num)))
    z (fderiv ℝ (gradient g) z) (gradient_differentiable g hC2 z).hasFDerivAt d

theorem approximate_hessian_coercive (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (mu : ℝ) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (H : E →L[ℝ] E) (deltaH : ℝ)
    (herr : ‖H - fderiv ℝ (gradient g) z‖ ≤ deltaH) (hsmall : deltaH ≤ mu / 4) (d : E) :
    (3 * mu / 4) * ‖d‖ ^ 2 ≤ inner ℝ (sympart H d) d := by
  have hbase := actual_hessian_coercive g hC2 mu hsc z d
  have he := le_trans (sympart_error_bound H (fderiv ℝ (gradient g) z)
    (gradient_derivative_selfadjoint g hC2 z)) herr
  have hnorm : ‖(sympart H - fderiv ℝ (gradient g) z) d‖ ≤ deltaH * ‖d‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ d)
      (mul_le_mul_of_nonneg_right he (norm_nonneg d))
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm ((sympart H - fderiv ℝ (gradient g) z) d) d)
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hi
  simp only [ContinuousLinearMap.sub_apply] at hnorm
  have hm := mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
  have hd := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖d‖)
  nlinarith only [hi, hm, hbase, hd]

theorem add_hasGradientAt {f h : E → ℝ} {u v x : E}
    (hf : HasGradientAt f u x) (hh : HasGradientAt h v x) :
    HasGradientAt (fun y => f y + h y) (u + v) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert! hf.add hh using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, inner_add_left, ContinuousLinearMap.add_apply]

theorem mul_hasGradientAt {f : E → ℝ} {v x : E} (hf : HasGradientAt f v x) (a : ℝ) :
    HasGradientAt (fun y => a * f y) (a • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  convert! hf.const_mul a using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem linear_hasGradientAt (v x : E) : HasGradientAt (fun y => inner ℝ v y) v x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ E v).hasFDerivAt

theorem quadratic_hasGradientAt (H : E →L[ℝ] E) (x : E) :
    HasGradientAt (fun d => (1 / 2 : ℝ) * inner ℝ (H d) d) (sympart H x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := ((H.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
  convert! hh using 1
  ext d
  simp only [sympart, InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, real_inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, id_eq]
  rw [real_inner_comm (H d) x]
  ring

theorem cube_hasGradientAt (x : E) :
    HasGradientAt (fun d : E => ‖d‖ ^ 3) ((3 * ‖x‖) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := hasFDerivAt_norm_rpow x (p := (3 : ℝ)) (by norm_num)
  have he : (fun d : E => ‖d‖ ^ (3 : ℝ)) = (fun d : E => ‖d‖ ^ (3 : ℕ)) := by
    funext d
    exact Real.rpow_natCast _ 3
  rw [he] at hh
  convert! hh using 1
  ext d
  norm_num [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, innerSL_apply_apply]

theorem square_hasGradientAt (x : E) :
    HasGradientAt (fun d : E => ‖d‖ ^ 2) ((2 : ℝ) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (hasFDerivAt_id x).norm_sq using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, two_smul,
    inner_add_left, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, id_eq]

theorem model_hasGradientAt (v : E) (H : E →L[ℝ] E) (Mbar lam : ℝ) (d : E) :
    HasGradientAt (model v H Mbar lam)
      (v + sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d) d := by
  have hh := add_hasGradientAt
    (add_hasGradientAt (add_hasGradientAt (linear_hasGradientAt v d) (quadratic_hasGradientAt H d))
      (mul_hasGradientAt (cube_hasGradientAt d) (Mbar / 6)))
    (mul_hasGradientAt (square_hasGradientAt d) (1 / (2 * lam)))
  convert! hh using 1 <;> module

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def halvingCount (a tau : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 1 (a / tau)))

theorem halving_precision (a tau : ℝ) (htau : 0 < tau) :
    a / (2 : ℝ) ^ (halvingCount a tau) ≤ tau := by
  have hm : 0 < max 1 (a / tau) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : Real.logb 2 (max 1 (a / tau)) ≤ (halvingCount a tau : ℝ) := Nat.le_ceil _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hm,
    Real.rpow_natCast] at hp
  have hh := le_trans (le_max_right 1 (a / tau)) hp
  have hmul := (div_le_iff₀ htau).mp hh
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith only [hmul]

theorem center_thresholds_cover (v : E) (delta rhoStop : ℝ)
    (hrho : 0 < rhoStop) (hsmall : delta ≤ rhoStop / 8) :
    ‖v‖ + delta ≤ rhoStop ∨ rhoStop / 2 ≤ ‖v‖ - delta := by
  by_cases hs : ‖v‖ + delta ≤ rhoStop
  · exact Or.inl hs
  · exact Or.inr (by linarith only [lt_of_not_ge hs, hsmall, hrho])

theorem center_stop_certifies (v G : E) (delta rhoStop : ℝ)
    (herr : ‖v - G‖ ≤ delta) (hstop : ‖v‖ + delta ≤ rhoStop) : ‖G‖ ≤ rhoStop := by
  have ht := norm_le_norm_sub_add G v
  rw [norm_sub_rev G v] at ht
  linarith only [ht, herr, hstop]

theorem center_away_certifies (v G : E) (delta rhoStop : ℝ)
    (herr : ‖v - G‖ ≤ delta) (haway : rhoStop / 2 ≤ ‖v‖ - delta) : rhoStop / 2 ≤ ‖G‖ := by
  have ht := norm_le_norm_sub_add v G
  linarith only [ht, herr, haway]

theorem center_geometric_termination (G : E) (v : ℕ → E) (error0 rhoStop : ℝ)
    (hrho : 0 < rhoStop)
    (herr : ∀ n : ℕ, ‖v n - G‖ ≤ error0 / (2 : ℝ) ^ n) :
    let n := halvingCount error0 (rhoStop / 8)
    (‖v n‖ + error0 / (2 : ℝ) ^ n ≤ rhoStop ∧ ‖G‖ ≤ rhoStop) ∨
    (rhoStop / 2 ≤ ‖v n‖ - error0 / (2 : ℝ) ^ n ∧ rhoStop / 2 ≤ ‖G‖) := by
  dsimp only
  have hs := halving_precision error0 (rhoStop / 8) (by positivity)
  rcases center_thresholds_cover (v (halvingCount error0 (rhoStop / 8)))
      (error0 / (2 : ℝ) ^ (halvingCount error0 (rhoStop / 8))) rhoStop hrho hs with hstop | haway
  · exact Or.inl ⟨hstop, center_stop_certifies _ G _ rhoStop (herr _) hstop⟩
  · exact Or.inr ⟨haway, center_away_certifies _ G _ rhoStop (herr _) haway⟩

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem quadratic_remainder (H : E →L[ℝ] E) (x y : E) :
    (1 / 2 : ℝ) * inner ℝ (H y) y - (1 / 2 : ℝ) * inner ℝ (H x) x -
      inner ℝ (sympart H x) (y - x) = (1 / 2 : ℝ) * inner ℝ (H (y - x)) (y - x) := by
  simp only [sympart, map_sub, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    real_inner_smul_left, inner_add_left, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm x (H y), real_inner_comm x (H x)]
  ring

theorem quadratic_strongConvex (H : E →L[ℝ] E) (m : ℝ)
    (hcoer : ∀ d : E, m * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) m (fun d => (1 / 2 : ℝ) * inner ℝ (H d) d) := by
  apply strongConvexOn_iff_convex.mpr
  apply convex_of_global_support _ (fun d => sympart H d - m • d)
  intro x y
  have hr := quadratic_remainder H x y
  have hc := hcoer (y - x)
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right]
  rw [norm_sub_sq_real] at hc
  have hxy : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [hxy] at hc
  simp only [inner_sub_right] at hc
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at hr ⊢
  nlinarith only [hr, hc]

theorem model_strongConvex (v : E) (H : E →L[ℝ] E) (Mbar lam m : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hcoer : ∀ d : E, m * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) m (model v H Mbar lam) := by
  have hlin : ConvexOn ℝ (Set.univ : Set E) (fun d => inner ℝ v d) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul, le_refl]
  have hcub : ConvexOn ℝ (Set.univ : Set E) (fun d => Mbar / 6 * ‖d‖ ^ 3) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ Mbar / 6)
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 3)
  have hprox : ConvexOn ℝ (Set.univ : Set E) (fun d => 1 / (2 * lam) * ‖d‖ ^ 2) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ 1 / (2 * lam))
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 2)
  have hq := strongConvexOn_iff_convex.mp (quadratic_strongConvex H m hcoer)
  have hh := ((hq.add hlin).add hcub).add hprox
  apply strongConvexOn_iff_convex.mpr
  convert! hh using 1
  funext d
  simp only [Pi.add_apply, model]
  ring

theorem exists_model_minimum (v : E) (H : E →L[ℝ] E) (Mbar lam m : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam) (hm : 0 < m)
    (hcoer : ∀ d : E, m * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    ∃ d : E, ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w := by
  have hd : Differentiable ℝ (model v H Mbar lam) := fun d =>
    (model_hasGradientAt v H Mbar lam d).differentiableAt
  obtain ⟨d, hdmin⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    (model v H Mbar lam) m 0 0 0 0 hm
    (by simpa using model_strongConvex v H Mbar lam m hM hlam hcoer) hd (0 : E)
  refine ⟨d, ?_⟩
  intro w
  simpa [PacketCore.saddleValue] using hdmin w

theorem model_minimum_first_order (v : E) (H : E →L[ℝ] E) (Mbar lam : ℝ) (d : E)
    (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    v + sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d = 0 := by
  have hz := PacketCore.gradient_eq_zero_at_global_min (model v H Mbar lam) d hmin
  rw [(model_hasGradientAt v H Mbar lam d).gradient] at hz
  exact hz

theorem residual_from_actual_minimum (G v : E) (K H : E →L[ℝ] E)
    (Mbar lam deltaG deltaH : ℝ) (hlam : 0 < lam) (hK : K.adjoint = K)
    (hgrad : ‖v - G‖ ≤ deltaG) (hhess : ‖H - K‖ ≤ deltaH)
    (d : E) (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    ‖lam • trueVector G K Mbar d + d‖ ≤ lam * (deltaG + deltaH * ‖d‖) := by
  have hfoc := model_minimum_first_order v H Mbar lam d hmin
  have hs : lam • (v + sympart H d + (Mbar / 2 * ‖d‖) • d) + d = 0 := by
    calc
      _ = lam • (v + sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d) := by
        simp only [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]
      _ = 0 := by rw [hfoc, smul_zero]
  have he : lam • trueVector G K Mbar d + d =
      lam • (G - v + (K - sympart H) d) := by
    calc
      _ = lam • (G - v + (K - sympart H) d) +
          (lam • (v + sympart H d + (Mbar / 2 * ‖d‖) • d) + d) := by
            simp only [trueVector, ContinuousLinearMap.sub_apply]
            module
      _ = _ := by rw [hs, add_zero]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  apply mul_le_mul_of_nonneg_left _ hlam.le
  have hsym := le_trans (sympart_error_bound H K hK) hhess
  have hmap : ‖(K - sympart H) d‖ ≤ deltaH * ‖d‖ := by
    apply le_trans (ContinuousLinearMap.le_opNorm _ d)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg d)
    simpa only [norm_sub_rev K (sympart H)] using hsym
  have hg : ‖G - v‖ ≤ deltaG := by simpa only [norm_sub_rev G v] using hgrad
  exact le_trans (norm_add_le _ _) (add_le_add hg hmap)

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def stepFloor (rhoStop A Mbar : ℝ) : ℝ :=
  min 1 (rhoStop / (8 * (A + Mbar / 2)))

theorem stepFloor_positive (rhoStop A Mbar : ℝ)
    (hrho : 0 < rhoStop) (hA : 0 < A) (hM : 0 ≤ Mbar) : 0 < stepFloor rhoStop A Mbar := by
  unfold stepFloor
  exact lt_min zero_lt_one (by positivity)

theorem minimum_gradient_norm_bound (v : E) (H : E →L[ℝ] E) (Mbar lam B : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam) (hB : ‖sympart H‖ ≤ B)
    (d : E) (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    ‖v‖ ≤ (B + lam⁻¹) * ‖d‖ + (Mbar / 2) * ‖d‖ ^ 2 := by
  have hfoc := model_minimum_first_order v H Mbar lam d hmin
  have he : v = -(sympart H d + (Mbar / 2 * ‖d‖) • d + lam⁻¹ • d) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using hfoc
  rw [he, norm_neg]
  have h1 := norm_add_le (sympart H d) ((Mbar / 2 * ‖d‖) • d)
  have h2 := norm_add_le (sympart H d + (Mbar / 2 * ‖d‖) • d) (lam⁻¹ • d)
  have hQ : ‖sympart H d‖ ≤ B * ‖d‖ := le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_mul_of_nonneg_right hB (norm_nonneg d))
  have hC : ‖(Mbar / 2 * ‖d‖) • d‖ = (Mbar / 2) * ‖d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have hP : ‖lam⁻¹ • d‖ = lam⁻¹ * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
  rw [hC] at h1
  rw [hP] at h2
  nlinarith only [h1, h2, hQ]

theorem approximate_minimum_step_lower (v : E) (H : E →L[ℝ] E)
    (Mbar lam B rhoStop : ℝ)
    (hM : 0 ≤ Mbar) (hlam : 0 < lam) (hB : ‖sympart H‖ ≤ B)
    (hA : 0 < B + lam⁻¹) (hrho : 0 < rhoStop) (haway : rhoStop / 4 ≤ ‖v‖)
    (d : E) (hmin : ∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) :
    stepFloor rhoStop (B + lam⁻¹) Mbar ≤ ‖d‖ := by
  have hb := minimum_gradient_norm_bound v H Mbar lam B hM hlam hB d hmin
  by_contra hfail
  have hd : ‖d‖ < stepFloor rhoStop (B + lam⁻¹) Mbar := lt_of_not_ge hfail
  have hd1 : ‖d‖ ≤ 1 := le_trans hd.le (min_le_left _ _)
  have hsq : ‖d‖ ^ 2 ≤ ‖d‖ := by nlinarith only [norm_nonneg d, hd1]
  have hC : 0 < B + lam⁻¹ + Mbar / 2 := by linarith only [hA, hM]
  have hdf : ‖d‖ < rhoStop / (8 * (B + lam⁻¹ + Mbar / 2)) :=
    lt_of_lt_of_le hd (min_le_right _ _)
  have hh := (lt_div_iff₀ (by positivity : 0 < 8 * (B + lam⁻¹ + Mbar / 2))).mp hdf
  have hsqM := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ Mbar / 2)
  nlinarith only [hb, haway, hh, hsqM, hrho]

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def refinementTolerance (mu Lg Mbar lam sigma rhoStop : ℝ) : ℝ :=
  let ell := stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar
  min (rhoStop / 8) (min (mu / 4) (min (sigma * ell / (2 * lam)) (sigma / (2 * lam))))

theorem refinementTolerance_bounds (mu Lg Mbar lam sigma rhoStop : ℝ) :
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤ rhoStop / 8 ∧
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤ mu / 4 ∧
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤
      sigma * stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar / (2 * lam) ∧
    refinementTolerance mu Lg Mbar lam sigma rhoStop ≤ sigma / (2 * lam) := by
  dsimp only [refinementTolerance]
  exact ⟨min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))⟩

theorem refinementTolerance_positive (mu Lg Mbar lam sigma rhoStop : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rhoStop) :
    0 < refinementTolerance mu Lg Mbar lam sigma rhoStop := by
  have hell : 0 < stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar :=
    stepFloor_positive rhoStop _ Mbar hrho (by positivity) hM
  unfold refinementTolerance
  positivity

theorem hessian_norm_from_gradient_lipschitz (g : E → ℝ) (Lg : ℝ) (hLg : 0 ≤ Lg)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖) (z : E) :
    ‖fderiv ℝ (gradient g) z‖ ≤ Lg := by
  let C : NNReal := ⟨Lg, hLg⟩
  have hh : LipschitzWith C (gradient g) := lipschitzWith_iff_norm_sub_le.mpr hlip
  exact norm_fderiv_le_of_lipschitz ℝ hh

theorem halving_precision_of_ge (a tau : ℝ) (ha : 0 ≤ a) (htau : 0 < tau)
    (n : ℕ) (hn : halvingCount a tau ≤ n) : a / (2 : ℝ) ^ n ≤ tau := by
  have hh : a / (2 : ℝ) ^ n ≤ a / (2 : ℝ) ^ (halvingCount a tau) :=
    div_le_div_of_nonneg_left ha (pow_pos (by norm_num) _)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn)
  exact le_trans hh (halving_precision a tau htau)

theorem model_acceptance_at_accuracy
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu Lg Mbar lam sigma rhoStop : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rhoStop)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (z v : E) (H : E →L[ℝ] E) (eta : ℝ)
    (hgerr : ‖v - gradient g z‖ ≤ eta)
    (hHerr : ‖H - fderiv ℝ (gradient g) z‖ ≤ eta)
    (hsmall : eta ≤ refinementTolerance mu Lg Mbar lam sigma rhoStop)
    (haway : rhoStop / 2 ≤ ‖gradient g z‖) :
    ∃ d : E, (∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) ∧
      stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar ≤ ‖d‖ ∧
      lam * (eta + eta * ‖d‖) ≤ sigma * ‖d‖ ∧
      ‖lam • trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + d‖ ≤ sigma * ‖d‖ := by
  have hb := refinementTolerance_bounds mu Lg Mbar lam sigma rhoStop
  have he1 := le_trans hsmall hb.1
  have he2 := le_trans hsmall hb.2.1
  have he3 := le_trans hsmall hb.2.2.1
  have he4 := le_trans hsmall hb.2.2.2
  have hcoer : ∀ d : E, (3 * mu / 4) * ‖d‖ ^ 2 ≤ inner ℝ (H d) d := by
    intro d
    simpa only [sympart_same_quadratic] using
      approximate_hessian_coercive g hC2 mu hsc z H eta hHerr he2 d
  obtain ⟨d, hd⟩ := exists_model_minimum v H Mbar lam (3 * mu / 4) hM hlam (by positivity) hcoer
  have hK := hessian_norm_from_gradient_lipschitz g Lg hLg hlip z
  have hsym := le_trans (sympart_error_bound H (fderiv ℝ (gradient g) z)
    (gradient_derivative_selfadjoint g hC2 z)) hHerr
  have hHnorm : ‖sympart H‖ ≤ Lg + mu / 4 := by
    have ht := norm_le_norm_sub_add (sympart H) (fderiv ℝ (gradient g) z)
    linarith only [ht, hsym, hK, he2]
  have hv : rhoStop / 4 ≤ ‖v‖ := by
    have ht := norm_le_norm_sub_add (gradient g z) v
    rw [norm_sub_rev (gradient g z) v] at ht
    linarith only [ht, hgerr, haway, he1, hrho]
  have hstep := approximate_minimum_step_lower v H Mbar lam (Lg + mu / 4) rhoStop
    hM hlam hHnorm (by positivity) hrho hv d hd
  have hc : lam * (eta + eta * ‖d‖) ≤ sigma * ‖d‖ := by
    have hp1 := (le_div_iff₀ (by positivity : 0 < 2 * lam)).mp he3
    have hp2 := (le_div_iff₀ (by positivity : 0 < 2 * lam)).mp he4
    have hmul := mul_le_mul_of_nonneg_right hp2 (norm_nonneg d)
    have hstepmul := mul_le_mul_of_nonneg_left hstep hsigma.le
    nlinarith only [hp1, hmul, hstepmul]
  refine ⟨d, hd, hstep, hc, ?_⟩
  exact le_trans (residual_from_actual_minimum (gradient g z) v (fderiv ℝ (gradient g) z) H
    Mbar lam eta eta hlam (gradient_derivative_selfadjoint g hC2 z) hgerr hHerr d hd) hc

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem certified_taylor_subroutine_all_items
    (g : E → ℝ) (mu Lg M Mbar lam sigma rhoStop error0 : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hMbar : M ≤ Mbar)
    (hlam : 0 < lam) (hsigma : 0 < sigma) (hrho : 0 < rhoStop) (herror0 : 0 ≤ error0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (hHlip : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z : E) (vseq : ℕ → E) (Hseq : ℕ → E →L[ℝ] E)
    (hgerr : ∀ n : ℕ, ‖vseq n - gradient g z‖ ≤ error0 / (2 : ℝ) ^ n)
    (hHerr : ∀ n : ℕ, ‖Hseq n - fderiv ℝ (gradient g) z‖ ≤ error0 / (2 : ℝ) ^ n) :
    (∀ (v : E) (H : E →L[ℝ] E) (deltaG deltaH : ℝ) (d : E),
      ‖v - gradient g z‖ ≤ deltaG →
      ‖H - fderiv ℝ (gradient g) z‖ ≤ deltaH → deltaH ≤ mu / 4 →
      (∀ w : E, model v H Mbar lam d ≤ model v H Mbar lam w) →
      lam * (deltaG + deltaH * ‖d‖) ≤ sigma * ‖d‖ →
      ‖lam • trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + d‖ ≤ sigma * ‖d‖) ∧
    let nCenter := halvingCount error0 (rhoStop / 8)
    let nAccept := nCenter + halvingCount error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop)
    (‖vseq nCenter‖ + error0 / (2 : ℝ) ^ nCenter ≤ rhoStop ∧ ‖gradient g z‖ ≤ rhoStop) ∨
    (rhoStop / 2 ≤ ‖vseq nCenter‖ - error0 / (2 : ℝ) ^ nCenter ∧
      rhoStop / 2 ≤ ‖gradient g z‖ ∧
      ∃ d : E,
        (∀ w : E, model (vseq nAccept) (Hseq nAccept) Mbar lam d ≤
          model (vseq nAccept) (Hseq nAccept) Mbar lam w) ∧
        stepFloor rhoStop (Lg + mu / 4 + lam⁻¹) Mbar ≤ ‖d‖ ∧
        lam * (error0 / (2 : ℝ) ^ nAccept + error0 / (2 : ℝ) ^ nAccept * ‖d‖) ≤ sigma * ‖d‖ ∧
        ‖lam • trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + d‖ ≤ sigma * ‖d‖) := by
  have hMnonneg : 0 ≤ Mbar := le_trans hM hMbar
  constructor
  · intro v H deltaG deltaH d hv hH hsmall hd hcert
    exact le_trans (residual_from_actual_minimum (gradient g z) v (fderiv ℝ (gradient g) z) H
      Mbar lam deltaG deltaH hlam (gradient_derivative_selfadjoint g hC2 z) hv hH d hd) hcert
  · dsimp only
    rcases center_geometric_termination (gradient g z) vseq error0 rhoStop hrho hgerr with hstop | haway
    · exact Or.inl hstop
    · refine Or.inr ⟨haway.1, haway.2, ?_⟩
      have htau := refinementTolerance_positive mu Lg Mbar lam sigma rhoStop hmu hLg hMnonneg hlam hsigma hrho
      let n := halvingCount error0 (rhoStop / 8) +
        halvingCount error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop)
      have hn : halvingCount error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop) ≤ n := by
        dsimp only [n]
        omega
      have he := halving_precision_of_ge error0 (refinementTolerance mu Lg Mbar lam sigma rhoStop)
        herror0 htau n hn
      exact model_acceptance_at_accuracy g hC2 mu Lg Mbar lam sigma rhoStop
        hmu hLg hMnonneg hlam hsigma hrho hsc hlip z (vseq n) (Hseq n)
        (error0 / (2 : ℝ) ^ n) (hgerr n) (hHerr n) he haway.2

end CertifiedATS

namespace CertifiedATS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def trueTaylorProx (g : E → ℝ) (z : E) (Mbar lam : ℝ) : E → ℝ :=
  model (gradient g z) (fderiv ℝ (gradient g) z) Mbar lam

theorem sympart_eq_of_selfadjoint (K : E →L[ℝ] E) (hK : K.adjoint = K) : sympart K = K := by
  unfold sympart
  rw [hK]
  module

theorem trueTaylorProx_hasGradientAt (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (z d : E) (Mbar lam : ℝ) :
    HasGradientAt (trueTaylorProx g z Mbar lam)
      (trueVector (gradient g z) (fderiv ℝ (gradient g) z) Mbar d + lam⁻¹ • d) d := by
  have hh := model_hasGradientAt (gradient g z) (fderiv ℝ (gradient g) z) Mbar lam d
  rw [sympart_eq_of_selfadjoint _ (gradient_derivative_selfadjoint g hC2 z)] at hh
  exact hh

theorem trueTaylorProx_exists_minimum (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (mu Mbar lam : ℝ) (hmu : 0 < mu) (hM : 0 ≤ Mbar) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g) (z : E) :
    ∃ d : E, ∀ w : E, trueTaylorProx g z Mbar lam d ≤ trueTaylorProx g z Mbar lam w := by
  exact exists_model_minimum (gradient g z) (fderiv ℝ (gradient g) z) Mbar lam mu hM hlam hmu
    (actual_hessian_coercive g hC2 mu hsc z)

end CertifiedATS

namespace CertifiedATSZeroTolerance

noncomputable def g (x : ℝ) : ℝ := x ^ 2 / 2 + x
noncomputable def error (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
noncomputable def approxGradient (n : ℕ) : ℝ := 1 + error n
noncomputable def approxHessian : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem g_contDiff2 : ContDiff ℝ 2 g := by unfold g; fun_prop

theorem g_gradient (x : ℝ) : gradient g x = x + 1 := by
  have hh : HasDerivAt g (x + 1) x := by
    convert! (((hasDerivAt_id x).pow 2).div_const 2).add (hasDerivAt_id x) using 1 <;> simp only [id_eq] <;> ring
  rw [gradient_eq_deriv']
  exact hh.deriv

theorem g_hessian (x : ℝ) : fderiv ℝ (gradient g) x = ContinuousLinearMap.id ℝ ℝ := by
  have he : gradient g = fun t : ℝ => t + 1 := funext g_gradient
  rw [he]
  exact ((hasFDerivAt_id x).add_const 1).fderiv

theorem g_strongConvex : StrongConvexOn (Set.univ : Set ℝ) 1 g := by
  apply strongConvexOn_iff_convex.mpr
  convert! (convexOn_id (convex_univ : Convex ℝ (Set.univ : Set ℝ))) using 1
  funext x
  simp only [g, Real.norm_eq_abs, sq_abs, id_eq]
  ring

theorem g_gradient_lipschitz (x y : ℝ) :
    ‖gradient g x - gradient g y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
  rw [g_gradient, g_gradient]
  simp only [add_sub_add_right_eq_sub, one_mul, le_refl]

theorem g_hessian_lipschitz (x y : ℝ) :
    ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
  rw [g_hessian, g_hessian, sub_self, norm_zero]
  positivity

theorem error_positive (n : ℕ) : 0 < error n := by unfold error; positivity

theorem error_halves (n : ℕ) : error (n + 1) = error n / 2 := by
  simp only [error, pow_succ]
  ring

theorem arbitrarily_accurate (tau : ℝ) (htau : 0 < tau) : ∃ n : ℕ, error n ≤ tau := by
  refine ⟨CertifiedATS.halvingCount 1 tau, ?_⟩
  have he : ∀ n : ℕ, error n = (1 : ℝ) / 2 ^ n := by
    intro n
    simp only [error, div_pow, one_pow]
  rw [he]
  exact CertifiedATS.halving_precision 1 tau htau

theorem approximation_certified (n : ℕ) :
    ‖approxGradient n - gradient g 0‖ ≤ error n ∧
    ‖approxHessian - fderiv ℝ (gradient g) 0‖ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 / 4 := by
  have hp := error_positive n
  rw [g_gradient, g_hessian]
  simp only [approxGradient, approxHessian, zero_add, add_sub_cancel_left,
    sub_self, norm_zero, Real.norm_eq_abs, abs_of_pos hp, le_refl]
  norm_num

theorem center_never_stops_and_is_away (n : ℕ) :
    ¬ (‖approxGradient n‖ + error n ≤ (1 : ℝ)) ∧
    (1 : ℝ) / 2 ≤ ‖approxGradient n‖ - error n := by
  have hp := error_positive n
  have hv : 0 < approxGradient n := by unfold approxGradient; linarith only [hp]
  rw [Real.norm_eq_abs, abs_of_pos hv]
  unfold approxGradient
  constructor <;> linarith only [hp]

theorem actual_model_minimum_exists (n : ℕ) :
    ∃ d : ℝ, ∀ w : ℝ,
      CertifiedATS.model (approxGradient n) approxHessian 1 1 d ≤
        CertifiedATS.model (approxGradient n) approxHessian 1 1 w := by
  apply CertifiedATS.exists_model_minimum (approxGradient n) approxHessian 1 1 1
    (by norm_num) (by norm_num) (by norm_num)
  intro d
  simp only [approxHessian, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq,
    one_mul, le_refl]

theorem no_finite_certificate (n : ℕ) (d : ℝ) :
    ¬ ((1 : ℝ) * (error n + (0 : ℝ) * ‖d‖) ≤ (0 : ℝ) * ‖d‖) := by
  simp only [zero_mul, add_zero, one_mul]
  exact not_le_of_gt (error_positive n)

theorem certified_ats_zero_sigma_refutation :
    ContDiff ℝ 2 g ∧ StrongConvexOn (Set.univ : Set ℝ) 1 g ∧
    (∀ x y : ℝ, ‖gradient g x - gradient g y‖ ≤ (1 : ℝ) * ‖x - y‖) ∧
    (∀ x y : ℝ, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ (1 : ℝ) * ‖x - y‖) ∧
    (∀ n : ℕ, error (n + 1) = error n / 2) ∧
    (∀ tau : ℝ, 0 < tau → ∃ n : ℕ, error n ≤ tau) ∧
    (∀ n : ℕ,
      0 < error n ∧
      ‖approxGradient n - gradient g 0‖ ≤ error n ∧
      ‖approxHessian - fderiv ℝ (gradient g) 0‖ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 / 4 ∧
      ¬ (‖approxGradient n‖ + error n ≤ (1 : ℝ)) ∧
      (1 : ℝ) / 2 ≤ ‖approxGradient n‖ - error n ∧
      (∃ d : ℝ, ∀ w : ℝ,
        CertifiedATS.model (approxGradient n) approxHessian 1 1 d ≤
          CertifiedATS.model (approxGradient n) approxHessian 1 1 w) ∧
      ∀ d : ℝ, ¬ ((1 : ℝ) * (error n + (0 : ℝ) * ‖d‖) ≤ (0 : ℝ) * ‖d‖)) := by
  refine ⟨g_contDiff2, g_strongConvex, g_gradient_lipschitz, g_hessian_lipschitz,
    error_halves, arbitrarily_accurate, ?_⟩
  intro n
  have hc := approximation_certified n
  have hs := center_never_stops_and_is_away n
  exact ⟨error_positive n, hc.1, hc.2.1, hc.2.2, hs.1, hs.2,
    actual_model_minimum_exists n, no_finite_certificate n⟩

end CertifiedATSZeroTolerance

namespace CertifiedATSZeroTolerance

theorem actual_residual_eq_neg_error (n : ℕ) (d : ℝ)
    (hmin : ∀ w : ℝ, CertifiedATS.model (approxGradient n) approxHessian 1 1 d ≤
      CertifiedATS.model (approxGradient n) approxHessian 1 1 w) :
    (1 : ℝ) • CertifiedATS.trueVector (gradient g 0) (fderiv ℝ (gradient g) 0) 1 d + d = -error n := by
  have hfoc := CertifiedATS.model_minimum_first_order (approxGradient n) approxHessian 1 1 d hmin
  have hself : approxHessian.adjoint = approxHessian := by simp only [approxHessian, ContinuousLinearMap.adjoint_id]
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ hself] at hfoc
  simp only [approxGradient, approxHessian, ContinuousLinearMap.id_apply, inv_one, one_smul, smul_eq_mul] at hfoc
  simp only [one_smul, CertifiedATS.trueVector, g_gradient, g_hessian, zero_add,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  linarith only [hfoc]

theorem actual_model_minimum_never_true_ATS (n : ℕ) (d : ℝ)
    (hmin : ∀ w : ℝ, CertifiedATS.model (approxGradient n) approxHessian 1 1 d ≤
      CertifiedATS.model (approxGradient n) approxHessian 1 1 w) :
    ¬ (‖(1 : ℝ) • CertifiedATS.trueVector (gradient g 0) (fderiv ℝ (gradient g) 0) 1 d + d‖ ≤
      (0 : ℝ) * ‖d‖) := by
  rw [actual_residual_eq_neg_error n d hmin, norm_neg, Real.norm_eq_abs,
    abs_of_pos (error_positive n), zero_mul]
  exact not_le_of_gt (error_positive n)

end CertifiedATSZeroTolerance

end PaperAudit.CertifiedATS
