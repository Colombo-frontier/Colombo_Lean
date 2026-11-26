import Mathlib

namespace PaperAudit.OuterCounterexample










namespace OriginalAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem smooth_descent_upper
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x s : E) :
    f (x + s) ≤ f x + inner ℝ (gradient f x) s + L / 2 * ‖s‖ ^ 2 := by
  let a : ℝ → E := fun t => x + t • s
  let p : ℝ → ℝ := fun t =>
    f (a t) - f x - t * inner ℝ (gradient f x) s - L / 2 * t ^ 2 * ‖s‖ ^ 2
  let p' : ℝ → ℝ := fun t =>
    inner ℝ (gradient f (a t)) s - inner ℝ (gradient f x) s -
      L / 2 * (2 * t) * ‖s‖ ^ 2
  have ha : ∀ t : ℝ, HasDerivAt a s t := by
    intro t
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const s).const_add x)
  have hp : ∀ t : ℝ, HasDerivAt p (p' t) t := by
    intro t
    have hf : HasDerivAt (fun t => f (a t)) (inner ℝ (gradient f (a t)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (a t)).hasFDerivAt.comp_hasDerivAt t (ha t))
    have hlin : HasDerivAt (fun t : ℝ => t * inner ℝ (gradient f x) s)
        (inner ℝ (gradient f x) s) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradient f x) s)
    have hquad : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖s‖ ^ 2)
        (L / 2 * (2 * t) * ‖s‖ ^ 2) t := by
      have ht := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖s‖ ^ 2)
      convert ht using 1 <;> first | rfl | simp
    simpa only [p, p', Pi.sub_def] using ((hf.sub_const (f x)).sub hlin).sub hquad
  have hpnonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), p' t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hl := hlip (a t) x
    have hnorm : ‖a t - x‖ = t * ‖s‖ := by
      simp [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [hnorm] at hl
    have hi := real_inner_le_norm (gradient f (a t) - gradient f x) s
    rw [inner_sub_left] at hi
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg s)
    dsimp [p']
    nlinarith only [hi, hm]
  have hm : AntitoneOn p (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hp t).continuousAt.continuousWithinAt)
      (fun t _ => (hp t).hasDerivWithinAt) hpnonpos
  have h := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  have h' := h
  dsimp [p, a] at h'
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_pow, zero_pow (by omega : 2 ≠ 0)] at h'
  linarith

theorem gradient_step_descent
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : E) :
    f (x - L⁻¹ • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
  have h := smooth_descent_upper f L hL hdiff hlip x (- (L⁻¹ • gradient f x))
  rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h
  have hn : L ≠ 0 := ne_of_gt hL
  have heq : f x - L⁻¹ * ‖gradient f x‖ ^ 2 +
      L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 =
      f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
    <;> ring
  have h' : f (x - L⁻¹ • gradient f x) ≤
      f x - L⁻¹ * ‖gradient f x‖ ^ 2 +
        L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 := by
    simpa only [sub_eq_add_neg] using h
  rwa [heq] at h'


theorem exists_small_gradient
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : E, ‖gradient f x‖ ≤ δ := by
  by_contra hgoal
  have hlarge : ∀ x : E, δ < ‖gradient f x‖ := by
    intro x
    exact lt_of_not_ge (fun hx => hgoal ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := hbelow
  let c : ℝ := δ ^ 2 / (2 * L)
  have hc : 0 < c := by dsimp [c]; positivity
  let x : ℕ → E := fun n =>
    Nat.rec (0 : E) (fun _ z => z - L⁻¹ • gradient f z) n
  have hx (n : ℕ) : x (n + 1) = x n - L⁻¹ • gradient f (x n) := by rfl
  have hstep (n : ℕ) : f (x (n + 1)) ≤ f (x n) - c := by
    have hsq : δ ^ 2 ≤ ‖gradient f (x n)‖ ^ 2 :=
      (sq_le_sq₀ hδ.le (norm_nonneg _)).2 (hlarge (x n)).le
    have hquot : c ≤ ‖gradient f (x n)‖ ^ 2 / (2 * L) := by
      dsimp [c]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    rw [hx n]
    exact le_trans (gradient_step_descent f L hL hdiff hlip (x n))
      (sub_le_sub_left hquot (f (x n)))
  have hvalues : ∀ n : ℕ, f (x n) ≤ f (x 0) - (n : ℝ) * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep n
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hncast]
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((f (x 0) - b) / c)
  have hnprod : f (x 0) - b < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have hv := hvalues n
  have hb' := hb (x n)
  linarith


theorem not_uniform_positive_gradient_lower_bound
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ x : E, δ ≤ ‖gradient f x‖ := by
  intro hlarge
  obtain ⟨x, hx⟩ := exists_small_gradient f L hL hdiff hlip hbelow (δ / 2) (by positivity)
  have hh := hlarge x
  linarith


theorem lipschitz_gradient_of_bounded_fderiv_gradient
    (f : E → ℝ) (L : ℝ)
    (hgrad_diff : Differentiable ℝ (gradient f))
    (hbound : ∀ x : E, ‖fderiv ℝ (gradient f) x‖ ≤ L) :
    ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
  intro x y
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (Set.univ : Set E)) => hgrad_diff z)
    (fun z (_ : z ∈ (Set.univ : Set E)) => hbound z)
    (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ y) (Set.mem_univ x)


theorem exists_small_gradient_of_bounded_fderiv_gradient
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hgrad_diff : Differentiable ℝ (gradient f))
    (hbound : ∀ x : E, ‖fderiv ℝ (gradient f) x‖ ≤ L)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : E, ‖gradient f x‖ ≤ δ := by
  exact exists_small_gradient f L hL hdiff
    (lipschitz_gradient_of_bounded_fderiv_gradient f L hgrad_diff hbound) hbelow δ hδ

end OriginalAudit


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


namespace MoreauTransfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def objective (Φ : E → ℝ) (L : ℝ) (x u : E) : ℝ :=
  Φ u + L * ‖u - x‖ ^ 2

noncomputable def envelope (Φ : E → ℝ) (L : ℝ) (x : E) : ℝ :=
  sInf (Set.range (objective Φ L x))

noncomputable def prox (Φ : E → ℝ) (L : ℝ) (x : E) : E :=
  Classical.epsilon (fun u : E => ∀ v : E, objective Φ L x u ≤ objective Φ L x v)


theorem weakConvex_packet_strongConvex
    (Φ : E → ℝ) (L : ℝ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2)) :
    StrongConvexOn (Set.univ : Set E) (L + (-2 * L)) Φ := by
  rw [strongConvexOn_iff_convex]
  have heq : (fun u : E => Φ u - (L + (-2 * L)) / 2 * ‖u‖ ^ 2) =
      (fun u : E => Φ u + L / 2 * ‖u‖ ^ 2) := by
    funext u
    ring
  rw [heq]
  exact hweak


theorem packet_is_negative_objective (Φ : E → ℝ) (L : ℝ) (x u : E) :
    PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x u =
      - objective Φ L x u := by
  dsimp [PacketCore.saddleValue, objective]
  rw [norm_sub_sq_real, real_inner_comm u x]
  ring


theorem exists_unique_minimizer
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    ∃! u : E, ∀ v : E, objective Φ L x u ≤ objective Φ L x v := by
  have hsc := weakConvex_packet_strongConvex Φ L hweak
  obtain ⟨u, hu⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    Φ L (-2 * L) (-2 * L) (2 * L) 0 hL hsc hdiff x
  have hmin : ∀ v : E, objective Φ L x u ≤ objective Φ L x v := by
    intro v
    have hh := hu v
    rw [packet_is_negative_objective, packet_is_negative_objective] at hh
    linarith
  refine ⟨u, hmin, ?_⟩
  intro v hv
  have hvmax : ∀ z : E,
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x z ≤
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x v := by
    intro z
    rw [packet_is_negative_objective, packet_is_negative_objective]
    exact neg_le_neg (hv z)
  exact PacketCore.unique_inner_maximizer Φ L (-2 * L) (-2 * L) (2 * L) 0
    hL hsc hdiff x v u hvmax hu


theorem prox_minimizes
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x v : E) :
    objective Φ L x (prox Φ L x) ≤ objective Φ L x v := by
  exact Classical.epsilon_spec (exists_unique_minimizer Φ L hL hdiff hweak x).exists v


theorem envelope_eq_of_minimizer
    (Φ : E → ℝ) (L : ℝ) (x u : E)
    (hmin : ∀ v : E, objective Φ L x u ≤ objective Φ L x v) :
    envelope Φ L x = objective Φ L x u := by
  have hleast : IsLeast (Set.range (objective Φ L x)) (objective Φ L x u) := by
    constructor
    · exact ⟨u, rfl⟩
    · rintro z ⟨v, rfl⟩
      exact hmin v
  exact hleast.csInf_eq


theorem envelope_eq_prox_objective
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    envelope Φ L x = objective Φ L x (prox Φ L x) := by
  exact envelope_eq_of_minimizer Φ L x (prox Φ L x) (prox_minimizes Φ L hL hdiff hweak x)


theorem prox_is_unique
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x u : E) (hmin : ∀ v : E, objective Φ L x u ≤ objective Φ L x v) :
    u = prox Φ L x := by
  obtain ⟨w, hw, huniq⟩ := exists_unique_minimizer Φ L hL hdiff hweak x
  exact (huniq u hmin).trans (huniq (prox Φ L x) (prox_minimizes Φ L hL hdiff hweak x)).symm


theorem prox_packet_maximizes
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2)) :
    ∀ x z : E,
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x z ≤
      PacketCore.saddleValue Φ (-2 * L) (-2 * L) (2 * L) 0 x (prox Φ L x) := by
  intro x z
  rw [packet_is_negative_objective, packet_is_negative_objective]
  exact neg_le_neg (prox_minimizes Φ L hL hdiff hweak x z)


theorem prox_first_order
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    gradient Φ (prox Φ L x) = (2 * L) • (x - prox Φ L x) := by
  have hh := PacketCore.inner_maximizer_first_order Φ (-2 * L) (-2 * L) (2 * L) 0
    x (prox Φ L x) hdiff (prox_packet_maximizes Φ L hL hdiff hweak x)
  rw [smul_sub]
  convert hh using 1 <;> module


theorem envelope_quadratic_remainder
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x z : E) :
    ‖envelope Φ L z - envelope Φ L x -
      inner ℝ ((2 * L) • (x - prox Φ L x)) (z - x)‖ ≤ L * ‖z - x‖ ^ 2 := by
  have hsc := weakConvex_packet_strongConvex Φ L hweak
  have hmax := prox_packet_maximizes Φ L hL hdiff hweak
  obtain ⟨hlo, hup⟩ := PacketCore.value_maximization_gap Φ L (-2 * L) (-2 * L)
    (2 * L) 0 hL hsc hdiff (prox Φ L) hmax x z
  have hid := PacketCore.saddle_outer_remainder Φ (-2 * L) (-2 * L) (2 * L) 0
    x z (prox Φ L x)
  have hcoeff : (2 * L) ^ 2 / (2 * L) = 2 * L := by
    field_simp
    <;> ring
  have hval (w : E) :
      PacketCore.valueFromMaximizers Φ (-2 * L) (-2 * L) (2 * L) 0 (prox Φ L) w =
      - envelope Φ L w := by
    dsimp [PacketCore.valueFromMaximizers]
    rw [packet_is_negative_objective, envelope_eq_prox_objective Φ L hL hdiff hweak w]
  rw [hval, packet_is_negative_objective] at hlo hup
  rw [hcoeff] at hup
  rw [packet_is_negative_objective, packet_is_negative_objective,
    ← envelope_eq_prox_objective Φ L hL hdiff hweak x] at hid
  have hinner : inner ℝ ((-2 * L) • x + (2 * L) • prox Φ L x) (z - x) =
      - inner ℝ ((2 * L) • (x - prox Φ L x)) (z - x) := by
    rw [inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left, inner_sub_left]
    simp only [conj_trivial]
    ring
  rw [hinner] at hid
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hup, hid]


theorem envelope_hasGradientAt
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    HasGradientAt (envelope Φ L) ((2 * L) • (x - prox Φ L x)) x := by
  exact PacketCore.hasGradientAt_of_quadratic_remainder _ _ _ L
    (envelope_quadratic_remainder Φ L hL hdiff hweak x)


theorem exact_stationarity_transfer
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) :
    gradient (envelope Φ L) x = (2 * L) • (x - prox Φ L x) ∧
      gradient (envelope Φ L) x = gradient Φ (prox Φ L x) := by
  have hE := (envelope_hasGradientAt Φ L hL hdiff hweak x).gradient
  exact ⟨hE, hE.trans (prox_first_order Φ L hL hdiff hweak x).symm⟩


theorem envelope_le_original
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (x : E) : envelope Φ L x ≤ Φ x := by
  rw [envelope_eq_prox_objective Φ L hL hdiff hweak x]
  have hh := prox_minimizes Φ L hL hdiff hweak x x
  simpa only [objective, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] using hh


theorem infimum_equality
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ)) :
    sInf (Set.range (envelope Φ L)) = sInf (Set.range Φ) := by
  have hlower (x : E) : sInf (Set.range Φ) ≤ envelope Φ L x := by
    rw [envelope_eq_prox_objective Φ L hL hdiff hweak x]
    have hh := csInf_le hbelow (Set.mem_range_self (prox Φ L x))
    dsimp [objective]
    have hnonneg : 0 ≤ L * ‖prox Φ L x - x‖ ^ 2 := by positivity
    linarith only [hh, hnonneg]
  have hEbelow : BddBelow (Set.range (envelope Φ L)) := by
    refine ⟨sInf (Set.range Φ), ?_⟩
    rintro z ⟨x, rfl⟩
    exact hlower x
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty Φ)
    rintro z ⟨x, rfl⟩
    exact (csInf_le hEbelow (Set.mem_range_self x)).trans (envelope_le_original Φ L hL hdiff hweak x)
  · apply le_csInf (Set.range_nonempty (envelope Φ L))
    rintro z ⟨x, rfl⟩
    exact hlower x


theorem initial_gap_transfer
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ))
    (x0 : E) (Δ : ℝ) (hgap : Φ x0 - sInf (Set.range Φ) ≤ Δ) :
    envelope Φ L x0 - sInf (Set.range (envelope Φ L)) ≤ Δ := by
  rw [infimum_equality Φ L hL hdiff hweak hbelow]
  have hh := envelope_le_original Φ L hL hdiff hweak x0
  linarith only [hh, hgap]


theorem prox_displacement_sq_gap
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ)) (x : E) :
    L * ‖prox Φ L x - x‖ ^ 2 ≤ Φ x - sInf (Set.range Φ) := by
  have hE := envelope_le_original Φ L hL hdiff hweak x
  rw [envelope_eq_prox_objective Φ L hL hdiff hweak x] at hE
  have hPhi := csInf_le hbelow (Set.mem_range_self (prox Φ L x))
  dsimp [objective] at hE
  linarith only [hE, hPhi]


theorem prox_displacement_le_sqrt_initial_gap
    (Φ : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Φ)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Φ u + L / 2 * ‖u‖ ^ 2))
    (hbelow : BddBelow (Set.range Φ))
    (x : E) (Δ : ℝ) (hgap : Φ x - sInf (Set.range Φ) ≤ Δ) :
    ‖prox Φ L x - x‖ ≤ Real.sqrt (Δ / L) := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hL).2
  have hh := prox_displacement_sq_gap Φ L hL hdiff hweak hbelow x
  nlinarith only [hh, hgap]

end MoreauTransfer


namespace OriginalSaddleRegularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_neg_of_differentiable
    (f : E → ℝ) (hdiff : Differentiable ℝ f) (x : E) :
    gradient (fun y => -f y) x = -gradient f x := by
  have h : HasGradientAt (fun y => -f y) (-gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert ((hdiff x).hasGradientAt.hasFDerivAt.neg) using 1 <;>
      first | rfl | simp only [map_neg, Pi.neg_def]
  exact (hdiff.neg x).hasGradientAt.unique h

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

theorem smooth_gradient_lower_support
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    f x + inner ℝ (gradient f x) (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hneg : ∀ a b : E,
      ‖gradient (fun t => -f t) a - gradient (fun t => -f t) b‖ ≤ L * ‖a - b‖ := by
    intro a b
    rw [gradient_neg_of_differentiable f hdiff a,
      gradient_neg_of_differentiable f hdiff b]
    simpa only [neg_sub_neg, norm_sub_rev] using hlip a b
  have h := OriginalAudit.smooth_descent_upper (fun t => -f t) L hL hdiff.neg hneg x (y - x)
  rw [gradient_neg_of_differentiable f hdiff x, inner_neg_left] at h
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at h
  linarith

theorem smooth_function_weakly_convex
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    StrongConvexOn (Set.univ : Set E) (-L) f := by
  apply strongConvexOn_iff_convex.mpr
  apply convex_of_global_support _ (fun x => gradient f x + L • x)
  intro x y
  have h := smooth_gradient_lower_support f L hL hdiff hlip x y
  rw [norm_sub_sq_real] at h
  have hsym : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [hsym] at h
  simp only [inner_sub_right] at h
  simp only [inner_add_left, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  nlinarith only [h]

noncomputable def value (f : E → F → ℝ) (Y : E → F) (x : E) : ℝ := f x (Y x)

theorem value_weakly_convex_from_actual_maxima
    (f : E → F → ℝ) (L : ℝ)
    (hweak : ∀ y : F, StrongConvexOn (Set.univ : Set E) (-L) (fun x => f x y))
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x)) :
    StrongConvexOn (Set.univ : Set E) (-L) (value f Y) := by
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hc := (strongConvexOn_iff_convex.mp (hweak (Y z))).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have h1 := mul_le_mul_of_nonneg_left (hY x (Y z)) ha
  have h2 := mul_le_mul_of_nonneg_left (hY y (Y z)) hb
  simp only [smul_eq_mul] at hc ⊢
  dsimp only [value, z] at *
  nlinarith only [hc, h1, h2]

theorem exists_inner_maximum
    [FiniteDimensional ℝ F]
    (f : E → F → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiff : ∀ x : E, Differentiable ℝ (f x)) (x : E) :
    ∃ y : F, ∀ z : F, f x z ≤ f x y := by
  obtain ⟨y, hy⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    (fun y => -f x y) μ 0 0 0 0 hμ (by simpa using hsc x) (hdiff x).neg (0 : F)
  refine ⟨y, ?_⟩
  intro z
  simpa [PacketCore.saddleValue] using hy z

theorem inner_maximum_quadratic_gap
    (f : E → F → ℝ) (μ : ℝ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiff : ∀ x : E, Differentiable ℝ (f x))
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x))
    (x : E) (y : F) :
    f x y ≤ f x (Y x) - μ / 2 * ‖y - Y x‖ ^ 2 := by
  have hzero : gradient (fun y => -f x y) (Y x) = 0 :=
    PacketCore.gradient_eq_zero_at_global_min _ _ (fun z => neg_le_neg (hY x z))
  have hs := PacketCore.strongConvex_support (fun y => -f x y) μ
    (hsc x) (hdiff x).neg (Y x) y
  rw [hzero, inner_zero_left] at hs
  linarith

theorem value_quadratic_error_bounds
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x))
    (x z : E) :
    -(L / 2 * ‖z - x‖ ^ 2) ≤
      value f Y z - value f Y x - inner ℝ (gradient (fun t => f t (Y x)) x) (z - x) ∧
    value f Y z - value f Y x - inner ℝ (gradient (fun t => f t (Y x)) x) (z - x) ≤
      (L / 2 + L ^ 2 / (2 * μ)) * ‖z - x‖ ^ 2 := by
  have hlo := smooth_gradient_lower_support (fun t => f t (Y x)) L hL
    (hdiffX (Y x)) (hxx (Y x)) x z
  have hmax := hY z (Y x)
  have hu := OriginalAudit.smooth_descent_upper (fun t => f t (Y z)) L hL
    (hdiffX (Y z)) (hxx (Y z)) x (z - x)
  have hxz : x + (z - x) = z := by abel
  rw [hxz] at hu
  have hgap := inner_maximum_quadratic_gap f μ hsc hdiffY Y hY x (Y z)
  have hi := real_inner_le_norm
    (gradient (fun t => f t (Y z)) x - gradient (fun t => f t (Y x)) x) (z - x)
  rw [inner_sub_left] at hi
  have him := mul_le_mul_of_nonneg_right (hxy x (Y z) (Y x)) (norm_nonneg (z - x))
  have hyoung := PacketCore.scalar_young μ (L * ‖z - x‖) (‖Y z - Y x‖) hμ
  have heq : (L * ‖z - x‖) ^ 2 / (2 * μ) =
      (L ^ 2 / (2 * μ)) * ‖z - x‖ ^ 2 := by ring
  rw [heq] at hyoung
  dsimp only [value]
  constructor
  · linarith only [hlo, hmax]
  · nlinarith only [hu, hgap, hi, him, hyoung]

theorem value_hasGradientAt
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x))
    (x : E) :
    HasGradientAt (value f Y) (gradient (fun t => f t (Y x)) x) x := by
  apply PacketCore.hasGradientAt_of_quadratic_remainder _ _ _ (L / 2 + L ^ 2 / (2 * μ))
  intro z
  have h := value_quadratic_error_bounds f L μ hL hμ hdiffX hdiffY hsc hxx hxy Y hY x z
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hp : 0 ≤ (L ^ 2 / (2 * μ)) * ‖z - x‖ ^ 2 := by positivity
    nlinarith only [h.1, hp]
  · exact h.2

theorem value_differentiable_and_weakly_convex
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x)) :
    Differentiable ℝ (value f Y) ∧ StrongConvexOn (Set.univ : Set E) (-L) (value f Y) := by
  constructor
  · intro x
    exact (value_hasGradientAt f L μ hL hμ hdiffX hdiffY hsc hxx hxy Y hY x).differentiableAt
  · exact value_weakly_convex_from_actual_maxima f L
      (fun y => smooth_function_weakly_convex (fun x => f x y) L hL (hdiffX y) (hxx y)) Y hY

end OriginalSaddleRegularity


namespace JointSliceRegularity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev JointSpace (E F : Type*) := WithLp 2 (E × F)

noncomputable def axisX : E →ₗᵢ[ℝ] JointSpace E F where
  toFun x := WithLp.toLp 2 (x, (0 : F))
  map_add' x x' := by
    apply (WithLp.ext_iff 2).mpr
    change (x + x', (0 : F)) = (x, (0 : F)) + (x', (0 : F))
    simp
  map_smul' r x := by
    apply (WithLp.ext_iff 2).mpr
    change (r • x, (0 : F)) = r • (x, (0 : F))
    simp
  norm_map' x := WithLp.norm_toLp_fst 2 E F x

noncomputable def axisY : F →ₗᵢ[ℝ] JointSpace E F where
  toFun y := WithLp.toLp 2 ((0 : E), y)
  map_add' y y' := by
    apply (WithLp.ext_iff 2).mpr
    change ((0 : E), y + y') = ((0 : E), y) + ((0 : E), y')
    simp
  map_smul' r y := by
    apply (WithLp.ext_iff 2).mpr
    change ((0 : E), r • y) = r • ((0 : E), y)
    simp
  norm_map' y := WithLp.norm_toLp_snd 2 E F y

noncomputable def point (x : E) (y : F) : JointSpace E F := axisX x + axisY y

noncomputable def curry (J : JointSpace E F → ℝ) (x : E) (y : F) : ℝ := J (point x y)


theorem point_eq_toLp (x : E) (y : F) : point x y = WithLp.toLp 2 (x, y) := by
  apply (WithLp.ext_iff 2).mpr
  change (x, (0 : F)) + ((0 : E), y) = (x, y)
  simp


theorem norm_axisX (x : E) : ‖axisX (F := F) x‖ = ‖x‖ :=
  (axisX (E := E) (F := F)).norm_map x


theorem norm_axisY (y : F) : ‖axisY (E := E) y‖ = ‖y‖ :=
  (axisY (E := E) (F := F)).norm_map y


theorem norm_fst_projection (z : JointSpace E F) : ‖z.fst‖ ≤ ‖z‖ :=
  WithLp.norm_fst_le E z


theorem norm_snd_projection (z : JointSpace E F) : ‖z.snd‖ ≤ ‖z‖ :=
  WithLp.norm_snd_le E z


theorem norm_fst_projection_sub (z w : JointSpace E F) : ‖z.fst - w.fst‖ ≤ ‖z - w‖ := by
  simpa only [WithLp.sub_fst] using norm_fst_projection (z - w)


theorem norm_snd_projection_sub (z w : JointSpace E F) : ‖z.snd - w.snd‖ ≤ ‖z - w‖ := by
  simpa only [WithLp.sub_snd] using norm_snd_projection (z - w)


theorem point_sub_same_y (x x' : E) (y : F) :
    point x y - point x' y = axisX (F := F) (x - x') := by
  dsimp [point]
  rw [map_sub]
  abel


theorem point_sub_same_x (x : E) (y y' : F) :
    point x y - point x y' = axisY (E := E) (y - y') := by
  dsimp [point]
  rw [map_sub]
  abel


theorem norm_point_sub_same_y (x x' : E) (y : F) :
    ‖point x y - point x' y‖ = ‖x - x'‖ := by
  rw [point_sub_same_y, norm_axisX]


theorem norm_point_sub_same_x (x : E) (y y' : F) :
    ‖point x y - point x y'‖ = ‖y - y'‖ := by
  rw [point_sub_same_x, norm_axisY]


theorem inner_axisX (z : JointSpace E F) (v : E) :
    inner ℝ z (axisX v) = inner ℝ z.fst v := by
  change inner ℝ z.fst v + inner ℝ z.snd (0 : F) = _
  simp


theorem inner_axisY (z : JointSpace E F) (v : F) :
    inner ℝ z (axisY v) = inner ℝ z.snd v := by
  change inner ℝ z.fst (0 : E) + inner ℝ z.snd v = _
  simp


theorem point_hasFDerivAt_x (x : E) (y : F) :
    HasFDerivAt (fun u : E => point u y)
      (axisX (E := E) (F := F)).toContinuousLinearMap x := by
  exact (axisX (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.add_const (axisY y)


theorem point_hasFDerivAt_y (x : E) (y : F) :
    HasFDerivAt (fun v : F => point x v)
      (axisY (E := E) (F := F)).toContinuousLinearMap y := by
  exact (axisY (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.const_add (axisX x)


theorem differentiable_x_slice
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (y : F) :
    Differentiable ℝ (fun x : E => curry J x y) := by
  intro x
  exact (hJ (point x y)).comp x (point_hasFDerivAt_x x y).differentiableAt


theorem differentiable_y_slice
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) :
    Differentiable ℝ (curry J x) := by
  intro y
  exact (hJ (point x y)).comp y (point_hasFDerivAt_y x y).differentiableAt


theorem gradient_x_slice_eq_projection
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) (y : F) :
    gradient (fun u : E => curry J u y) x = (gradient J (point x y)).fst := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hs := (hJ (point x y)).hasFDerivAt.comp x (point_hasFDerivAt_x x y)
  have hs' : HasFDerivAt (fun u : E => curry J u y)
      ((fderiv ℝ J (point x y)).comp (axisX (E := E) (F := F)).toContinuousLinearMap) x := by
    simpa only [Function.comp_def, curry] using hs
  rw [hs'.fderiv]
  change (fderiv ℝ J (point x y)) (axisX v) = _
  rw [← inner_gradient_left, inner_axisX]


theorem gradient_y_slice_eq_projection
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) (y : F) :
    gradient (curry J x) y = (gradient J (point x y)).snd := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hs := (hJ (point x y)).hasFDerivAt.comp y (point_hasFDerivAt_y x y)
  have hs' : HasFDerivAt (curry J x)
      ((fderiv ℝ J (point x y)).comp (axisY (E := E) (F := F)).toContinuousLinearMap) y := by
    convert! hs using 1 <;> rfl
  rw [hs'.fderiv]
  change (fderiv ℝ J (point x y)) (axisY v) = _
  rw [← inner_gradient_left, inner_axisY]


theorem gradient_x_lipschitz_in_x
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y : F) :
    ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y) x'‖ ≤ L * ‖x - x'‖ := by
  rw [gradient_x_slice_eq_projection J hJ, gradient_x_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x' y)‖ := norm_fst_projection_sub _ _
    _ ≤ L * ‖point x y - point x' y‖ := hLip _ _
    _ = L * ‖x - x'‖ := by rw [norm_point_sub_same_y]


theorem gradient_x_lipschitz_in_y
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y') x‖ ≤ L * ‖y - y'‖ := by
  rw [gradient_x_slice_eq_projection J hJ, gradient_x_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x y')‖ := norm_fst_projection_sub _ _
    _ ≤ L * ‖point x y - point x y'‖ := hLip _ _
    _ = L * ‖y - y'‖ := by rw [norm_point_sub_same_x]


theorem gradient_y_lipschitz_in_x
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y : F) :
    ‖gradient (curry J x) y - gradient (curry J x') y‖ ≤ L * ‖x - x'‖ := by
  rw [gradient_y_slice_eq_projection J hJ, gradient_y_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x' y)‖ := norm_snd_projection_sub _ _
    _ ≤ L * ‖point x y - point x' y‖ := hLip _ _
    _ = L * ‖x - x'‖ := by rw [norm_point_sub_same_y]


theorem gradient_y_lipschitz_in_y
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖gradient (curry J x) y - gradient (curry J x) y'‖ ≤ L * ‖y - y'‖ := by
  rw [gradient_y_slice_eq_projection J hJ, gradient_y_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x y')‖ := norm_snd_projection_sub _ _
    _ ≤ L * ‖point x y - point x y'‖ := hLip _ _
    _ = L * ‖y - y'‖ := by rw [norm_point_sub_same_x]


theorem contDiff2_x_slice
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) (y : F) :
    ContDiff ℝ 2 (fun x : E => curry J x y) := by
  have haxis : ContDiff ℝ 2 (fun u : E => axisX (F := F) u) :=
    (axisX (E := E) (F := F)).toContinuousLinearMap.contDiff
  have hp : ContDiff ℝ 2 (fun u : E => point u y) := haxis.add contDiff_const
  exact hJ.comp hp


theorem contDiff2_y_slice
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) (x : E) :
    ContDiff ℝ 2 (curry J x) := by
  have haxis : ContDiff ℝ 2 (fun v : F => axisY (E := E) v) :=
    (axisY (E := E) (F := F)).toContinuousLinearMap.contDiff
  have hp : ContDiff ℝ 2 (fun v : F => point x v) := contDiff_const.add haxis
  exact hJ.comp hp


theorem strongConvex_negative_y_slice
    (J : JointSpace E F → ℝ) (μ : ℝ)
    (hconcave : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ (curry J x)) (x : E) :
    StrongConvexOn (Set.univ : Set F) μ (fun y => - curry J x y) := by
  exact UniformConcaveOn.neg (hconcave x)


theorem differentiable_joint_of_contDiff2
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) : Differentiable ℝ J := by
  exact hJ.differentiable (by norm_num)


theorem differentiable_negative_y_slice
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) :
    Differentiable ℝ (fun y : F => - curry J x y) := by
  exact (differentiable_y_slice J hJ x).neg


theorem joint_to_slice_conditions
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    (∀ y : F, Differentiable ℝ (fun x : E => curry J x y)) ∧
    (∀ x : E, Differentiable ℝ (curry J x)) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y) x'‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y') x‖ ≤ L * ‖y - y'‖) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (curry J x) y - gradient (curry J x') y‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (curry J x) y - gradient (curry J x) y'‖ ≤ L * ‖y - y'‖) := by
  exact ⟨differentiable_x_slice J hJ, differentiable_y_slice J hJ,
    gradient_x_lipschitz_in_x J hJ L hLip, gradient_x_lipschitz_in_y J hJ L hLip,
    gradient_y_lipschitz_in_x J hJ L hLip, gradient_y_lipschitz_in_y J hJ L hLip⟩


theorem contDiff2_joint_to_slice_conditions
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    (∀ y : F, Differentiable ℝ (fun x : E => curry J x y)) ∧
    (∀ x : E, Differentiable ℝ (curry J x)) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y) x'‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y') x‖ ≤ L * ‖y - y'‖) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (curry J x) y - gradient (curry J x') y‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (curry J x) y - gradient (curry J x) y'‖ ≤ L * ‖y - y'‖) := by
  exact joint_to_slice_conditions J (differentiable_joint_of_contDiff2 J hJ) L hLip

end JointSliceRegularity


namespace OriginalSaddleTransfer

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def phi (f : E → F → ℝ) (x : E) : ℝ := sSup (Set.range (f x))

noncomputable def yStar (f : E → F → ℝ) (x : E) : F :=
  Classical.epsilon (fun y => ∀ z, f x z ≤ f x y)

noncomputable def saddleObjective (f : E → F → ℝ) (L : ℝ) (x u : E) (y : F) : ℝ :=
  f u y + L * ‖u - x‖ ^ 2

noncomputable def saddleEnvelope (f : E → F → ℝ) (L : ℝ) (x : E) : ℝ :=
  sInf (Set.range (fun u : E => sSup (Set.range (saddleObjective f L x u))))

noncomputable def uStar (f : E → F → ℝ) (L : ℝ) (x : E) : E :=
  MoreauTransfer.prox (phi f) L x

noncomputable def vStar (f : E → F → ℝ) (L : ℝ) (x : E) : F :=
  yStar f (uStar f L x)

theorem yStar_maximizes
    (f : E → F → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (x : E) (y : F) : f x y ≤ f x (yStar f x) := by
  exact Classical.epsilon_spec
    (OriginalSaddleRegularity.exists_inner_maximum f μ hμ hsc hdiffY x) y

theorem phi_eq_value_at_yStar
    (f : E → F → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x)) (x : E) :
    phi f x = f x (yStar f x) := by
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨yStar f x, rfl⟩
  · rintro z ⟨y, rfl⟩
    exact yStar_maximizes f μ hμ hsc hdiffY x y

theorem saddle_inner_value
    (f : E → F → ℝ) (L μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x)) (x u : E) :
    sSup (Set.range (saddleObjective f L x u)) = MoreauTransfer.objective (phi f) L x u := by
  rw [MoreauTransfer.objective, phi_eq_value_at_yStar f μ hμ hsc hdiffY u]
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨yStar f u, rfl⟩
  · rintro z ⟨y, rfl⟩
    exact add_le_add (yStar_maximizes f μ hμ hsc hdiffY u y) (le_refl _)

theorem saddleEnvelope_eq_moreau
    (f : E → F → ℝ) (L μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x)) :
    saddleEnvelope f L = MoreauTransfer.envelope (phi f) L := by
  funext x
  unfold saddleEnvelope MoreauTransfer.envelope
  congr 2
  funext u
  exact saddle_inner_value f L μ hμ hsc hdiffY x u

theorem phi_regular_from_slices
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖) :
    Differentiable ℝ (phi f) ∧
      ConvexOn ℝ (Set.univ : Set E) (fun u => phi f u + L / 2 * ‖u‖ ^ 2) := by
  have heq : phi f = OriginalSaddleRegularity.value f (yStar f) := by
    funext x
    exact phi_eq_value_at_yStar f μ hμ hsc hdiffY x
  have hr := OriginalSaddleRegularity.value_differentiable_and_weakly_convex f L μ
    hL hμ hdiffX hdiffY hsc hxx hxy (yStar f) (yStar_maximizes f μ hμ hsc hdiffY)
  rw [← heq] at hr
  refine ⟨hr.1, ?_⟩
  have hc := strongConvexOn_iff_convex.mp hr.2
  convert hc using 1 <;> (first | rfl | (congr 1; funext u; ring))

theorem phi_hasGradientAt_yStar
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x : E) : HasGradientAt (phi f) (gradient (fun t => f t (yStar f x)) x) x := by
  have heq : phi f = OriginalSaddleRegularity.value f (yStar f) := by
    funext z
    exact phi_eq_value_at_yStar f μ hμ hsc hdiffY z
  rw [heq]
  exact OriginalSaddleRegularity.value_hasGradientAt f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy (yStar f) (yStar_maximizes f μ hμ hsc hdiffY) x

theorem exact_transfer_from_slices
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (hbelow : BddBelow (Set.range (phi f)))
    (x0 : E) (Δ : ℝ) (hgap : phi f x0 - sInf (Set.range (phi f)) ≤ Δ) :
    (∀ x : E,
      gradient (saddleEnvelope f L) x = (2 * L) • (x - uStar f L x) ∧
      gradient (saddleEnvelope f L) x = gradient (phi f) (uStar f L x)) ∧
    saddleEnvelope f L x0 - sInf (Set.range (saddleEnvelope f L)) ≤ Δ ∧
    sInf (Set.range (saddleEnvelope f L)) = sInf (Set.range (phi f)) ∧
    (∀ x : E, ∃! u : E, ∀ v : E,
      sSup (Set.range (saddleObjective f L x u)) ≤
      sSup (Set.range (saddleObjective f L x v))) ∧
    (∀ x : E, ∀ u : E,
      sSup (Set.range (saddleObjective f L x (uStar f L x))) ≤
      sSup (Set.range (saddleObjective f L x u))) ∧
    (∀ x : E, ∀ y : F,
      saddleObjective f L x (uStar f L x) y ≤
      saddleObjective f L x (uStar f L x) (vStar f L x)) := by
  obtain ⟨hdiff, hweak⟩ := phi_regular_from_slices f L μ hL hμ hdiffX hdiffY hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L μ hμ hsc hdiffY
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hE]
    exact MoreauTransfer.exact_stationarity_transfer (phi f) L hL hdiff hweak x
  · rw [hE]
    exact MoreauTransfer.initial_gap_transfer (phi f) L hL hdiff hweak hbelow x0 Δ hgap
  · rw [hE]
    exact MoreauTransfer.infimum_equality (phi f) L hL hdiff hweak hbelow
  · intro x
    have h := MoreauTransfer.exists_unique_minimizer (phi f) L hL hdiff hweak x
    simpa only [saddle_inner_value f L μ hμ hsc hdiffY] using h
  · intro x u
    simp only [saddle_inner_value f L μ hμ hsc hdiffY, uStar]
    exact MoreauTransfer.prox_minimizes (phi f) L hL hdiff hweak x u
  · intro x y
    exact add_le_add (yStar_maximizes f μ hμ hsc hdiffY (uStar f L x) y) (le_refl _)


theorem exact_transfer_from_standing_joint
    (J : JointSliceRegularity.JointSpace E F → ℝ)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : JointSliceRegularity.JointSpace E F,
      ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hconcave : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ
      (fun y => J (WithLp.toLp 2 (x, y))))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (x0 : E) (Δ : ℝ)
    (hgap : phi (JointSliceRegularity.curry J) x0 -
      sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Δ) :
    let f := JointSliceRegularity.curry J
    (∀ x : E,
      gradient (saddleEnvelope f L) x = (2 * L) • (x - uStar f L x) ∧
      gradient (saddleEnvelope f L) x = gradient (phi f) (uStar f L x)) ∧
    saddleEnvelope f L x0 - sInf (Set.range (saddleEnvelope f L)) ≤ Δ ∧
    sInf (Set.range (saddleEnvelope f L)) = sInf (Set.range (phi f)) ∧
    (∀ x : E, ∃! u : E, ∀ v : E,
      sSup (Set.range (saddleObjective f L x u)) ≤
      sSup (Set.range (saddleObjective f L x v))) ∧
    (∀ x : E, ∀ u : E,
      sSup (Set.range (saddleObjective f L x (uStar f L x))) ≤
      sSup (Set.range (saddleObjective f L x u))) ∧
    (∀ x : E, ∀ y : F,
      saddleObjective f L x (uStar f L x) y ≤
      saddleObjective f L x (uStar f L x) (vStar f L x)) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hconcave' : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ
      (JointSliceRegularity.curry J x) := by
    intro x
    have heq : JointSliceRegularity.curry J x =
        (fun y : F => J (WithLp.toLp 2 (x, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp x y)
    rw [heq]
    exact hconcave x
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J μ hconcave'
  have hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => JointSliceRegularity.curry J t y) x -
        gradient (fun t => JointSliceRegularity.curry J t y) z‖ ≤ L * ‖x - z‖ := by
    intro y x z
    exact JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x z y
  have hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => JointSliceRegularity.curry J t y) x -
        gradient (fun t => JointSliceRegularity.curry J t z) x‖ ≤ L * ‖y - z‖ := by
    intro x y z
    exact JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y z
  exact exact_transfer_from_slices (JointSliceRegularity.curry J) L μ hL hμ
    hdiffX hdiffY hsc hxx hxy hbelow x0 Δ hgap

end OriginalSaddleTransfer


namespace OriginalSaddleStability

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem norm_square_center_change (x u z : E) :
    ‖z - x‖ ^ 2 - ‖u - x‖ ^ 2 =
      ‖z - u‖ ^ 2 - 2 * inner ℝ (x - u) (z - u) := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm z x, real_inner_comm z u, real_inner_comm u x]
  ring

theorem norm_square_four_points (x x' u u' : E) :
    ‖u' - x‖ ^ 2 - ‖u - x‖ ^ 2 + ‖u - x'‖ ^ 2 - ‖u' - x'‖ ^ 2 =
      2 * inner ℝ (x - x') (u - u') := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
  rw [real_inner_comm u' x, real_inner_comm u x,
    real_inner_comm u x', real_inner_comm u' x']
  ring

theorem fixed_dual_quadratic_growth
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x z : E) :
    OriginalSaddleTransfer.saddleObjective f L x (OriginalSaddleTransfer.uStar f L x)
        (OriginalSaddleTransfer.vStar f L x) +
      L / 2 * ‖z - OriginalSaddleTransfer.uStar f L x‖ ^ 2 ≤
    OriginalSaddleTransfer.saddleObjective f L x z (OriginalSaddleTransfer.vStar f L x) := by
  let u := OriginalSaddleTransfer.uStar f L x
  let v := OriginalSaddleTransfer.vStar f L x
  obtain ⟨hphi, hweak⟩ := OriginalSaddleTransfer.phi_regular_from_slices
    f L μ hL hμ hdiffX hdiffY hsc hxx hxy
  have hFOC := MoreauTransfer.prox_first_order (OriginalSaddleTransfer.phi f) L
    hL hphi hweak x
  have hPhiGrad := (OriginalSaddleTransfer.phi_hasGradientAt_yStar f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy u).gradient
  change gradient (OriginalSaddleTransfer.phi f) u = gradient (fun t => f t v) u at hPhiGrad
  have hgrad : gradient (fun t => f t v) u = (2 * L) • (x - u) := by
    exact hPhiGrad.symm.trans hFOC
  have hs := OriginalSaddleRegularity.smooth_gradient_lower_support
    (fun t => f t v) L hL (hdiffX v) (hxx v) u z
  rw [hgrad, real_inner_smul_left] at hs
  have heq := norm_square_center_change x u z
  have heqL := congrArg (fun t : ℝ => L * t) heq
  change f u v + L * ‖u - x‖ ^ 2 + L / 2 * ‖z - u‖ ^ 2 ≤
    f z v + L * ‖z - x‖ ^ 2
  nlinarith only [hs, heqL]

theorem actual_saddle_energy
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x x' : E) :
    L * ‖OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x'‖ ^ 2 +
      μ * ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ^ 2 ≤
    2 * L * inner ℝ (x - x')
      (OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x') := by
  let u := OriginalSaddleTransfer.uStar f L x
  let u' := OriginalSaddleTransfer.uStar f L x'
  let v := OriginalSaddleTransfer.vStar f L x
  let v' := OriginalSaddleTransfer.vStar f L x'
  have hu := fixed_dual_quadratic_growth f L μ hL hμ hdiffX hdiffY hsc hxx hxy x u'
  have hu' := fixed_dual_quadratic_growth f L μ hL hμ hdiffX hdiffY hsc hxx hxy x' u
  have hv := OriginalSaddleRegularity.inner_maximum_quadratic_gap f μ hsc hdiffY
    (OriginalSaddleTransfer.yStar f)
    (OriginalSaddleTransfer.yStar_maximizes f μ hμ hsc hdiffY) u v'
  have hv' := OriginalSaddleRegularity.inner_maximum_quadratic_gap f μ hsc hdiffY
    (OriginalSaddleTransfer.yStar f)
    (OriginalSaddleTransfer.yStar_maximizes f μ hμ hsc hdiffY) u' v
  have hfour := norm_square_four_points x x' u u'
  have hfourL := congrArg (fun t : ℝ => L * t) hfour
  change L * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
    2 * L * inner ℝ (x - x') (u - u')
  change f u v + L * ‖u - x‖ ^ 2 + L / 2 * ‖u' - u‖ ^ 2 ≤
    f u' v + L * ‖u' - x‖ ^ 2 at hu
  change f u' v' + L * ‖u' - x'‖ ^ 2 + L / 2 * ‖u - u'‖ ^ 2 ≤
    f u v' + L * ‖u - x'‖ ^ 2 at hu'
  change f u v' ≤ f u v - μ / 2 * ‖v' - v‖ ^ 2 at hv
  change f u' v ≤ f u' v' - μ / 2 * ‖v - v'‖ ^ 2 at hv'
  rw [norm_sub_rev u' u] at hu
  rw [norm_sub_rev v' v] at hv
  nlinarith only [hu, hu', hv, hv', hfourL]

theorem scalar_energy_bounds
    (L μ a b c : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : L * a ^ 2 + μ * b ^ 2 ≤ 2 * L * c * a) :
    a ≤ 2 * c ∧ b ≤ 2 * Real.sqrt (L / μ) * c := by
  have ha' : a ≤ 2 * c := by
    by_contra hn
    have hp : 0 < a := by linarith
    have hb' : 0 ≤ μ * b ^ 2 := by positivity
    nlinarith only [h, hb', mul_pos hL hp, hn]
  refine ⟨ha', ?_⟩
  have hb' : μ * b ^ 2 ≤ 4 * L * c ^ 2 := by
    have h1 : 0 ≤ L * a ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left ha' (by positivity : 0 ≤ 2 * L * c)
    nlinarith only [h, h1, h2]
  have hs : (Real.sqrt (L / μ)) ^ 2 = L / μ := Real.sq_sqrt (by positivity)
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hmul : μ * (L / μ) = L := by field_simp
  have hsquare : (2 * Real.sqrt (L / μ) * c) ^ 2 = 4 * (L / μ) * c ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have hsquare' : μ * (2 * Real.sqrt (L / μ) * c) ^ 2 = 4 * L * c ^ 2 := by
    rw [hsquare]
    nlinarith only [hmul]
  have hnonneg : 0 ≤ 2 * Real.sqrt (L / μ) * c := by positivity
  have hbb : b ^ 2 ≤ (2 * Real.sqrt (L / μ) * c) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [hb', hsquare']
  exact (sq_le_sq₀ hb hnonneg).mp hbb

theorem actual_saddle_lipschitz_components
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x x' : E) :
    ‖OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x'‖ ≤
      2 * ‖x - x'‖ ∧
    ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ≤
      2 * Real.sqrt (L / μ) * ‖x - x'‖ := by
  have he := actual_saddle_energy f L μ hL hμ hdiffX hdiffY hsc hxx hxy x x'
  have hi := real_inner_le_norm (x - x')
    (OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x')
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * L)
  apply scalar_energy_bounds L μ _ _ _ hL hμ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  exact he.trans (by nlinarith only [hmul])

noncomputable def zStar (f : E → F → ℝ) (L : ℝ) (x : E) : WithLp 2 (E × F) :=
  WithLp.toLp 2 (OriginalSaddleTransfer.uStar f L x, OriginalSaddleTransfer.vStar f L x)

theorem actual_saddle_lipschitz_joint
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x x' : E) : ‖zStar f L x - zStar f L x'‖ ≤
      2 * Real.sqrt (1 + L / μ) * ‖x - x'‖ := by
  obtain ⟨hu, hv⟩ := actual_saddle_lipschitz_components f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy x x'
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖x - x'‖)).mpr hu
  have hv2 := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 2 * Real.sqrt (L / μ) * ‖x - x'‖)).mpr hv
  have hs := Real.sq_sqrt (by positivity : 0 ≤ L / μ)
  have hs1 := Real.sq_sqrt (by positivity : 0 ≤ 1 + L / μ)
  have hn := WithLp.prod_norm_sq_eq_of_L2 (zStar f L x - zStar f L x')
  change ‖zStar f L x - zStar f L x'‖ ^ 2 =
    ‖OriginalSaddleTransfer.uStar f L x - OriginalSaddleTransfer.uStar f L x'‖ ^ 2 +
    ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ^ 2 at hn
  apply (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 2 * Real.sqrt (1 + L / μ) * ‖x - x'‖)).mp
  have h0 : (2 * Real.sqrt (L / μ) * ‖x - x'‖) ^ 2 =
      4 * (L / μ) * ‖x - x'‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have h1 : (2 * Real.sqrt (1 + L / μ) * ‖x - x'‖) ^ 2 =
      4 * (1 + L / μ) * ‖x - x'‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs1]
    ring
  rw [h0] at hv2
  rw [h1]
  nlinarith only [hn, hu2, hv2]

theorem derivative_bounds_from_checked_differentials
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (x : E) (U : E →L[ℝ] E) (V : E →L[ℝ] F)
    (Z : E →L[ℝ] WithLp 2 (E × F))
    (hU : HasFDerivAt (OriginalSaddleTransfer.uStar f L) U x)
    (hV : HasFDerivAt (OriginalSaddleTransfer.vStar f L) V x)
    (hZ : HasFDerivAt (zStar f L) Z x) (h : E) :
    ‖U h‖ ≤ 2 * ‖h‖ ∧ ‖V h‖ ≤ 2 * Real.sqrt (L / μ) * ‖h‖ ∧
      ‖Z h‖ ≤ 2 * Real.sqrt (1 + L / μ) * ‖h‖ := by
  have hu : ‖U‖ ≤ 2 := hU.le_of_lip' (by norm_num)
    (Filter.Eventually.of_forall (fun z =>
      (actual_saddle_lipschitz_components f L μ hL hμ hdiffX hdiffY hsc hxx hxy z x).1))
  have hv : ‖V‖ ≤ 2 * Real.sqrt (L / μ) := hV.le_of_lip' (by positivity)
    (Filter.Eventually.of_forall (fun z =>
      (actual_saddle_lipschitz_components f L μ hL hμ hdiffX hdiffY hsc hxx hxy z x).2))
  have hz : ‖Z‖ ≤ 2 * Real.sqrt (1 + L / μ) := hZ.le_of_lip' (by positivity)
    (Filter.Eventually.of_forall (fun z =>
      actual_saddle_lipschitz_joint f L μ hL hμ hdiffX hdiffY hsc hxx hxy z x))
  exact ⟨(U.le_opNorm h).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg h)),
    (V.le_opNorm h).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg h)),
    (Z.le_opNorm h).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg h))⟩

end OriginalSaddleStability


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


namespace OriginalSaddleImplicit

open Filter
open scoped Topology

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Actual continuous zero selections agree locally with the implicit branch.
This helper does not assert invertibility from convexity: that is a separate obligation. -/
theorem actual_selection_contDiffAt
    (R : X × W → W) (s : X → W) (x : X)
    (hC1 : ContDiffAt ℝ 1 R (x, s x))
    (hinv : (fderiv ℝ R (x, s x) ∘L ContinuousLinearMap.inr ℝ X W).IsInvertible)
    (hs : ContinuousAt s x) (hzero : ∀ t : X, R (t, s t) = 0) :
    ContDiffAt ℝ 1 s x := by
  let ψ := hC1.implicitFunction (by norm_num) hinv
  have hevent := hC1.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  have hp : Tendsto (fun t : X => (t, s t)) (𝓝 x) (𝓝 (x, s x)) :=
    continuousAt_id.prodMk hs
  have heq : s =ᶠ[𝓝 x] ψ := by
    filter_upwards [hp.eventually hevent] with t ht
    exact (ht.mp (by rw [hzero t, hzero x])).symm
  exact (hC1.contDiffAt_implicitFunction (by norm_num) hinv).congr_of_eventuallyEq heq

variable {Z : Type*}
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

/-- C2 of the scalar objective supplies C1 of its actual Riesz gradient. -/
theorem contDiff_gradient_of_contDiff2 (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (gradient J) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ J) := hC2.fderiv_right (by norm_num)
  have heq : gradient J = fun z => (InnerProductSpace.toDual ℝ Z).symm (fderiv ℝ J z) := by
    funext z
    rfl
  rw [heq]
  exact (InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.contDiff.comp hder


section Saddle
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev Joint (E F : Type*) := WithLp 2 (E × F)

noncomputable def reflection : Joint E F →L[ℝ] Joint E F :=
  (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
      (WithLp.fstL 2 ℝ E F) -
    (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.comp
      (WithLp.sndL 2 ℝ E F)

theorem reflection_fst (w : Joint E F) : (reflection w).fst = w.fst := by
  simp [reflection, JointSliceRegularity.axisX, JointSliceRegularity.axisY]

theorem reflection_snd (w : Joint E F) : (reflection w).snd = -w.snd := by
  simp [reflection, JointSliceRegularity.axisX, JointSliceRegularity.axisY]

noncomputable def signedSaddleMap (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) :
    Joint E F :=
  reflection (gradient J w) + (2 * L) • JointSliceRegularity.axisX w.fst

noncomputable def residual (J : Joint E F → ℝ) (L : ℝ) (p : E × Joint E F) :
    Joint E F :=
  signedSaddleMap J L p.2 - (2 * L) • JointSliceRegularity.axisX p.1

theorem signedSaddleMap_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (signedSaddleMap J L) := by
  unfold signedSaddleMap
  have h1 : ContDiff ℝ 1 (fun w : Joint E F => reflection (gradient J w)) :=
    (reflection (E := E) (F := F)).contDiff.comp (contDiff_gradient_of_contDiff2 J hC2)
  have h2 : ContDiff ℝ 1 (fun w : Joint E F => JointSliceRegularity.axisX w.fst) :=
    (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp
      (WithLp.fstL 2 ℝ E F).contDiff
  exact h1.add (h2.const_smul (2 * L))

theorem residual_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (residual J L) := by
  unfold residual
  exact ((signedSaddleMap_contDiff J L hC2).comp contDiff_snd).sub
    (((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp
      contDiff_fst).const_smul (2 * L))

/-- The signed saddle operator is strongly monotone in the full L2 product.
The mixed terms cancel using four supports, without a symmetry premise on a supplied Hessian. -/
theorem slice_gradient_four_supports
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (u u' : E) (v v' : F) :
    -L * ‖u - u'‖ ^ 2 + μ * ‖v - v'‖ ^ 2 ≤
      inner ℝ (gradient (fun t => f t v) u - gradient (fun t => f t v') u') (u - u') -
      inner ℝ (gradient (f u) v - gradient (f u') v') (v - v') := by
  have hx := OriginalSaddleRegularity.smooth_gradient_lower_support
    (fun t => f t v) L hL (hdiffX v) (hxx v) u u'
  have hx' := OriginalSaddleRegularity.smooth_gradient_lower_support
    (fun t => f t v') L hL (hdiffX v') (hxx v') u' u
  have hy := PacketCore.strongConvex_support (fun y => -f u y) μ
    (hsc u) (hdiffY u).neg v v'
  have hy' := PacketCore.strongConvex_support (fun y => -f u' y) μ
    (hsc u') (hdiffY u').neg v' v
  rw [OriginalSaddleRegularity.gradient_neg_of_differentiable (f u) (hdiffY u),
    inner_neg_left] at hy
  rw [OriginalSaddleRegularity.gradient_neg_of_differentiable (f u') (hdiffY u'),
    inner_neg_left] at hy'
  rw [show u' - u = -(u - u') by abel, norm_neg, inner_neg_right] at hx
  rw [show v' - v = -(v - v') by abel, norm_neg, inner_neg_right] at hy
  simp only [inner_sub_left]
  nlinarith only [hx, hx', hy, hy']


theorem signedSaddleMap_energy
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L)
    (hJ : Differentiable ℝ J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (w w' : Joint E F) :
    L * ‖w.fst - w'.fst‖ ^ 2 + μ * ‖w.snd - w'.snd‖ ^ 2 ≤
      inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w') (w - w') := by
  have he := slice_gradient_four_supports (JointSliceRegularity.curry J) L μ hL
    (JointSliceRegularity.differentiable_x_slice J hJ)
    (JointSliceRegularity.differentiable_y_slice J hJ) hsc
    (fun y x z => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x z y)
    w.fst w'.fst w.snd w'.snd
  rw [JointSliceRegularity.gradient_x_slice_eq_projection J hJ,
    JointSliceRegularity.gradient_x_slice_eq_projection J hJ,
    JointSliceRegularity.gradient_y_slice_eq_projection J hJ,
    JointSliceRegularity.gradient_y_slice_eq_projection J hJ,
    JointSliceRegularity.point_eq_toLp, JointSliceRegularity.point_eq_toLp] at he
  have hw : WithLp.toLp 2 (w.fst, w.snd) = w := by rfl
  have hw' : WithLp.toLp 2 (w'.fst, w'.snd) = w' := by rfl
  rw [hw, hw'] at he
  have hi : inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w') (w - w') =
      inner ℝ ((gradient J w).fst - (gradient J w').fst) (w.fst - w'.fst) -
        inner ℝ ((gradient J w).snd - (gradient J w').snd) (w.snd - w'.snd) +
          2 * L * ‖w.fst - w'.fst‖ ^ 2 := by
    rw [WithLp.prod_inner_apply]
    change inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w').fst (w - w').fst +
      inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w').snd (w - w').snd = _
    simp only [signedSaddleMap, WithLp.sub_fst, WithLp.sub_snd, WithLp.add_fst,
      WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd, reflection_fst, reflection_snd]
    change inner ℝ ((gradient J w).fst + (2 * L) • w.fst -
        ((gradient J w').fst + (2 * L) • w'.fst)) (w.fst - w'.fst) +
      inner ℝ (-(gradient J w).snd + (2 * L) • (0 : F) -
        (-(gradient J w').snd + (2 * L) • (0 : F))) (w.snd - w'.snd) = _
    simp only [smul_zero, add_zero]
    rw [show (gradient J w).fst + (2 * L) • w.fst -
      ((gradient J w').fst + (2 * L) • w'.fst) =
      ((gradient J w).fst - (gradient J w').fst) +
        (2 * L) • (w.fst - w'.fst) by module]
    rw [show -(gradient J w).snd - -(gradient J w').snd =
      -((gradient J w).snd - (gradient J w').snd) by abel]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [hi]
  linarith

theorem signedSaddleMap_strong_monotone
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L)
    (hJ : Differentiable ℝ J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (w w' : Joint E F) :
    min L μ * ‖w - w'‖ ^ 2 ≤
      inner ℝ (signedSaddleMap J L w - signedSaddleMap J L w') (w - w') := by
  have he := signedSaddleMap_energy J L μ hL hJ hsc hLip w w'
  have hn := WithLp.prod_norm_sq_eq_of_L2 (w - w')
  change ‖w - w'‖ ^ 2 = ‖w.fst - w'.fst‖ ^ 2 + ‖w.snd - w'.snd‖ ^ 2 at hn
  have h1 := mul_le_mul_of_nonneg_right (min_le_left L μ) (sq_nonneg ‖w.fst - w'.fst‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right L μ) (sq_nonneg ‖w.snd - w'.snd‖)
  rw [hn, mul_add]
  exact (add_le_add h1 h2).trans he

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem residual_zero_at_actual_saddle
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hJ : Differentiable ℝ J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : residual J L (x,
      OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x) = 0 := by
  let f := JointSliceRegularity.curry J
  let u := OriginalSaddleTransfer.uStar f L x
  let v := OriginalSaddleTransfer.vStar f L x
  let z := OriginalSaddleStability.zStar f L x
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y x t => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x t y
  have hxy := fun x y t => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y t
  obtain ⟨hphi, hweak⟩ := OriginalSaddleTransfer.phi_regular_from_slices
    f L μ hL hμ hdiffX hdiffY hsc hxx hxy
  have hFOC := MoreauTransfer.prox_first_order (OriginalSaddleTransfer.phi f) L
    hL hphi hweak x
  have hPhiGrad := (OriginalSaddleTransfer.phi_hasGradientAt_yStar f L μ hL hμ
    hdiffX hdiffY hsc hxx hxy u).gradient
  change gradient (OriginalSaddleTransfer.phi f) u = gradient (fun t => f t v) u at hPhiGrad
  have hx : gradient (fun t => f t v) u = (2 * L) • (x - u) :=
    hPhiGrad.symm.trans hFOC
  have hy : gradient (f u) v = 0 := by
    have hneg : gradient (fun y => -f u y) v = 0 :=
      PacketCore.gradient_eq_zero_at_global_min _ _
        (fun y => neg_le_neg (OriginalSaddleTransfer.yStar_maximizes
          f μ hμ hsc hdiffY u y))
    rw [OriginalSaddleRegularity.gradient_neg_of_differentiable (f u) (hdiffY u)] at hneg
    exact neg_eq_zero.mp hneg
  have hz : JointSliceRegularity.point u v = z := JointSliceRegularity.point_eq_toLp u v
  have hgx : (gradient J z).fst = (2 * L) • (x - u) := by
    rw [← hz, ← JointSliceRegularity.gradient_x_slice_eq_projection J hJ]
    exact hx
  have hgy : (gradient J z).snd = 0 := by
    rw [← hz, ← JointSliceRegularity.gradient_y_slice_eq_projection J hJ]
    exact hy
  change residual J L (x, z) = 0
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change (residual J L (x, z)).fst = 0
    simp only [residual, signedSaddleMap, WithLp.sub_fst, WithLp.add_fst,
      WithLp.smul_fst, reflection_fst]
    change (gradient J z).fst + (2 * L) • u - (2 * L) • x = 0
    rw [hgx]
    module
  · change (residual J L (x, z)).snd = 0
    simp only [residual, signedSaddleMap, WithLp.sub_snd, WithLp.add_snd,
      WithLp.smul_snd, reflection_snd]
    change -(gradient J z).snd + (2 * L) • (0 : F) - (2 * L) • (0 : F) = 0
    simp only [hgy, neg_zero, smul_zero, add_zero, sub_zero]


theorem residual_partial_fderiv
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J)
    (x : E) (w : Joint E F) :
    fderiv ℝ (residual J L) (x, w) ∘L ContinuousLinearMap.inr ℝ E (Joint E F) =
      fderiv ℝ (signedSaddleMap J L) w := by
  have hR := ((residual_contDiff J L hC2).differentiable (by norm_num) (x, w)).hasFDerivAt
  have hpair : HasFDerivAt (fun t : Joint E F => (x, t))
      (ContinuousLinearMap.inr ℝ E (Joint E F)) w := by
    convert! (hasFDerivAt_const (c := x) w).prodMk (hasFDerivAt_id w) using 1 <;> rfl
  have hcomp := hR.comp w hpair
  have hB := ((signedSaddleMap_contDiff J L hC2).differentiable (by norm_num) w).hasFDerivAt
  have hfixed : HasFDerivAt (fun t => residual J L (x, t))
      (fderiv ℝ (signedSaddleMap J L) w) w := by
    simpa only [residual] using hB.sub_const ((2 * L) • JointSliceRegularity.axisX x)
  exact hcomp.unique hfixed

theorem residual_partial_isInvertible
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (w : Joint E F) :
    (fderiv ℝ (residual J L) (x, w) ∘L ContinuousLinearMap.inr ℝ E (Joint E F)).IsInvertible := by
  rw [residual_partial_fderiv J L hC2]
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hD := ((signedSaddleMap_contDiff J L hC2).differentiable (by norm_num) w).hasFDerivAt
  have hc := OriginalCoerciveOperator.derivative_coercive_of_strong_monotonicity
    (signedSaddleMap J L) (min L μ)
    (signedSaddleMap_strong_monotone J L μ hL hJ hsc hLip) w _ hD
  exact ⟨OriginalCoerciveOperator.equivalenceOfCoercive _ (min L μ)
    (lt_min hL hμ) hc, rfl⟩

theorem actual_saddle_contDiff_from_joint
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    ContDiff ℝ 1 (OriginalSaddleTransfer.uStar (JointSliceRegularity.curry J) L) ∧
    ContDiff ℝ 1 (OriginalSaddleTransfer.vStar (JointSliceRegularity.curry J) L) ∧
    ContDiff ℝ 1 (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y x t => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x t y
  have hxy := fun x y t => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y t
  have hzl : LipschitzWith ⟨2 * Real.sqrt (1 + L / μ), by positivity⟩
      (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    change dist _ _ ≤ (2 * Real.sqrt (1 + L / μ)) * dist x x'
    simpa only [dist_eq_norm] using
      OriginalSaddleStability.actual_saddle_lipschitz_joint (JointSliceRegularity.curry J)
        L μ hL hμ hdiffX hdiffY hsc hxx hxy x x'
  have hz : ContDiff ℝ 1 (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact actual_selection_contDiffAt (residual J L) _ x
      (residual_contDiff J L hC2).contDiffAt
      (residual_partial_isInvertible J L μ hL hμ hC2 hsc hLip x _)
      hzl.continuous.continuousAt
      (residual_zero_at_actual_saddle J L μ hL hμ hJ hsc hLip)
  refine ⟨?_, ?_, hz⟩
  · convert! (WithLp.fstL 2 ℝ E F).contDiff.comp hz using 1 <;> rfl
  · convert! (WithLp.sndL 2 ℝ E F).contDiff.comp hz using 1 <;> rfl


theorem square_root_sensitivity_from_standing_joint
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hconcave : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ
      (fun y => J (WithLp.toLp 2 (x, y))))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    let f := JointSliceRegularity.curry J
    ContDiff ℝ 1 (OriginalSaddleStability.zStar f L) ∧
    (∀ x : E, ∀ h : E,
      ‖(fderiv ℝ (OriginalSaddleStability.zStar f L) x h).fst‖ ≤ 2 * ‖h‖ ∧
      ‖(fderiv ℝ (OriginalSaddleStability.zStar f L) x h).snd‖ ≤
        2 * Real.sqrt (L / μ) * ‖h‖ ∧
      ‖fderiv ℝ (OriginalSaddleStability.zStar f L) x h‖ ≤
        2 * Real.sqrt (1 + L / μ) * ‖h‖) ∧
    (∀ x x' : E,
      ‖OriginalSaddleTransfer.vStar f L x - OriginalSaddleTransfer.vStar f L x'‖ ≤
        2 * Real.sqrt (L / μ) * ‖x - x'‖) := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hconcave' : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ (f x) := by
    intro x
    have heq : f x = (fun y : F => J (WithLp.toLp 2 (x, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp x y)
    rw [heq]
    exact hconcave x
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J μ hconcave'
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y x t => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip x t y
  have hxy := fun x y t => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip x y t
  obtain ⟨hu, hv, hz⟩ := actual_saddle_contDiff_from_joint J L μ hL hμ hC2 hsc hLip
  refine ⟨hz, ?_, ?_⟩
  · intro x h
    let Z := fderiv ℝ (OriginalSaddleStability.zStar f L) x
    have hZ : HasFDerivAt (OriginalSaddleStability.zStar f L) Z x :=
      (hz.differentiable (by norm_num) x).hasFDerivAt
    have hU : HasFDerivAt (OriginalSaddleTransfer.uStar f L)
        ((WithLp.fstL 2 ℝ E F).comp Z) x := by
      convert! (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp x hZ using 1 <;> rfl
    have hV : HasFDerivAt (OriginalSaddleTransfer.vStar f L)
        ((WithLp.sndL 2 ℝ E F).comp Z) x := by
      convert! (WithLp.sndL 2 ℝ E F).hasFDerivAt.comp x hZ using 1 <;> rfl
    exact OriginalSaddleStability.derivative_bounds_from_checked_differentials f L μ hL hμ
      hdiffX hdiffY hsc hxx hxy x _ _ Z hU hV hZ h
  · intro x x'
    exact (OriginalSaddleStability.actual_saddle_lipschitz_components f L μ hL hμ
      hdiffX hdiffY hsc hxx hxy x x').2

end Saddle

end OriginalSaddleImplicit


namespace OriginalSaddleTangent

open OriginalSaddleImplicit

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def primalProjection : Joint E F →L[ℝ] Joint E F :=
  (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
    (WithLp.fstL 2 ℝ E F)

noncomputable def saddleHessian (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) :
    Joint E F →L[ℝ] Joint E F :=
  fderiv ℝ (gradient J) w + (2 * L) • primalProjection

noncomputable def centerDerivative (L : ℝ) : E →L[ℝ] Joint E F :=
  (2 * L) • (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap

theorem reflection_axisX (x : E) :
    reflection (JointSliceRegularity.axisX (F := F) x) =
      JointSliceRegularity.axisX (F := F) x := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · exact reflection_fst _
  · change (reflection (JointSliceRegularity.axisX (F := F) x)).snd = 0
    rw [reflection_snd]
    change -(0 : F) = 0
    exact neg_zero

theorem reflection_involution (w : Joint E F) : reflection (reflection w) = w := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · exact (reflection_fst _).trans (reflection_fst _)
  · change (reflection (reflection w)).snd = w.snd
    rw [reflection_snd, reflection_snd, neg_neg]

noncomputable def reflectionEquiv : Joint E F ≃L[ℝ] Joint E F :=
  ContinuousLinearEquiv.equivOfInverse reflection reflection reflection_involution reflection_involution

theorem signed_map_as_reflection (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) :
    signedSaddleMap J L w = reflection (gradient J w + (2 * L) • JointSliceRegularity.axisX w.fst) := by
  simp only [map_add, map_smul, reflection_axisX, signedSaddleMap]

theorem signed_map_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) (w : Joint E F) :
    HasFDerivAt (signedSaddleMap J L) (reflection.comp (saddleHessian J L w)) w := by
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num) w).hasFDerivAt
  have hproj : HasFDerivAt (fun t : Joint E F => JointSliceRegularity.axisX t.fst)
      (primalProjection (E := E) (F := F)) w := by
    exact primalProjection.hasFDerivAt
  have hraw : HasFDerivAt (fun t : Joint E F => gradient J t +
      (2 * L) • JointSliceRegularity.axisX t.fst) (saddleHessian J L w) w :=
    hgrad.add (hproj.const_smul (2 * L))
  have hc := reflection.hasFDerivAt.comp w hraw
  convert! hc using 1 <;> first | rfl | (funext t; exact signed_map_as_reflection J L t)

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

theorem primalProjection_selfadjoint :
    (primalProjection (E := E) (F := F)).adjoint = primalProjection := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro a b
  change inner ℝ (JointSliceRegularity.axisX a.fst) b =
    inner ℝ a (JointSliceRegularity.axisX b.fst)
  calc
    inner ℝ (JointSliceRegularity.axisX a.fst) b =
        inner ℝ b (JointSliceRegularity.axisX a.fst) := real_inner_comm _ _
    _ = inner ℝ b.fst a.fst := JointSliceRegularity.inner_axisX b a.fst
    _ = inner ℝ a.fst b.fst := real_inner_comm _ _
    _ = inner ℝ a (JointSliceRegularity.axisX b.fst) :=
      (JointSliceRegularity.inner_axisX a b.fst).symm

theorem saddleHessian_selfadjoint
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) (w : Joint E F) :
    (saddleHessian J L w).adjoint = saddleHessian J L w := by
  simp only [saddleHessian, map_add, map_smul,
    gradient_derivative_selfadjoint J hC2 w, primalProjection_selfadjoint]

theorem centerDerivative_adjoint (L : ℝ) :
    (centerDerivative (E := E) (F := F) L).adjoint = (2 * L) • WithLp.fstL 2 ℝ E F := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro w h
  change inner ℝ ((2 * L) • w.fst) h =
    inner ℝ w ((2 * L) • JointSliceRegularity.axisX h)
  rw [real_inner_smul_left, real_inner_smul_right, JointSliceRegularity.inner_axisX]

theorem saddleHessian_difference
    (J : Joint E F → ℝ) (L : ℝ) (w w' : Joint E F) :
    saddleHessian J L w - saddleHessian J L w' =
      fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w' := by
  unfold saddleHessian
  abel

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_saddle_tangent
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) :
    (saddleHessian J L (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)).comp
      (fderiv ℝ (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) x) =
      centerDerivative L := by
  let z := OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hz := (actual_saddle_contDiff_from_joint J L μ hL hμ hC2 hsc hLip).2.2
  have hroot : (fun t : E => signedSaddleMap J L (z t)) = centerDerivative L := by
    funext t
    exact sub_eq_zero.mp (residual_zero_at_actual_saddle J L μ hL hμ hJ hsc hLip t)
  have hcomp := (signed_map_hasFDerivAt J L hC2 (z x)).comp x
    ((hz.differentiable (by norm_num) x).hasFDerivAt)
  change HasFDerivAt (fun t => signedSaddleMap J L (z t)) _ x at hcomp
  rw [hroot] at hcomp
  have heq := hcomp.unique (centerDerivative (E := E) (F := F) L).hasFDerivAt
  ext h
  have hh := congrArg (reflection (E := E) (F := F)) (DFunLike.congr_fun heq h)
  simp only [ContinuousLinearMap.comp_apply, reflection_involution, centerDerivative,
    ContinuousLinearMap.smul_apply, map_smul] at hh
  change (saddleHessian J L (z x))
    (fderiv ℝ (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) x h) =
      (2 * L) • reflection (JointSliceRegularity.axisX h) at hh
  rw [reflection_axisX] at hh
  exact hh

theorem saddleHessian_isInvertible
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (w : Joint E F) : (saddleHessian J L w).IsInvertible := by
  have hD : (fderiv ℝ (signedSaddleMap J L) w).IsInvertible := by
    rw [← residual_partial_fderiv J L hC2 (0 : E)]
    exact residual_partial_isInvertible J L μ hL hμ hC2 hsc hLip 0 w
  rw [(signed_map_hasFDerivAt J L hC2 w).fderiv] at hD
  have heq : saddleHessian J L w = reflection.comp (reflection.comp (saddleHessian J L w)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, reflection_involution]
  rw [heq]
  exact ((ContinuousLinearMap.isInvertible_equiv (f := reflectionEquiv)).comp hD)

theorem actual_saddle_derivative_formula
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J x y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) :
    fderiv ℝ (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L) x =
      (saddleHessian J L (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)).inverse.comp
        (centerDerivative L) := by
  have ht := actual_saddle_tangent J L μ hL hμ hC2 hsc hLip x
  have hi := saddleHessian_isInvertible J L μ hL hμ hC2 hsc hLip
    (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)
  ext h
  have hh := congrArg ((saddleHessian J L
    (OriginalSaddleStability.zStar (JointSliceRegularity.curry J) L x)).inverse)
    (DFunLike.congr_fun ht h)
  simpa only [ContinuousLinearMap.comp_apply, hi.inverse_apply_self] using hh

end OriginalSaddleTangent


namespace OriginalPrimalElimination

open OriginalSaddleImplicit

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E]

noncomputable def primal (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : E :=
  MoreauTransfer.prox (fun u => JointSliceRegularity.curry J u y) L x

noncomputable def blockUU (J : Joint E F → ℝ) (w : Joint E F) : E →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap)

noncomputable def blockUY (J : Joint E F → ℝ) (w : Joint E F) : F →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap)

noncomputable def primalHessian (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : E →L[ℝ] E :=
  blockUU J (JointSliceRegularity.point (primal J L x y) y) +
    (2 * L) • ContinuousLinearMap.id ℝ E

noncomputable def residual (J : Joint E F → ℝ) (L : ℝ) (x : E) (p : F × E) : E :=
  (gradient J (JointSliceRegularity.point p.2 p.1)).fst + (2 * L) • (p.2 - x)

theorem slice_weak_convex
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) (y : F) :
    ConvexOn ℝ (Set.univ : Set E)
      (fun u => JointSliceRegularity.curry J u y + L / 2 * ‖u‖ ^ 2) := by
  have hs := OriginalSaddleRegularity.smooth_function_weakly_convex
    (fun u => JointSliceRegularity.curry J u y) L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y)
  have hc := strongConvexOn_iff_convex.mp hs
  convert hc using 1 <;> (first | rfl | (funext u; ring))

theorem primal_is_unique_minimizer
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    (∀ u : E, JointSliceRegularity.curry J (primal J L x y) y +
      L * ‖primal J L x y - x‖ ^ 2 ≤ JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2) ∧
    (∀ u : E, (∀ v : E, JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2 ≤
      JointSliceRegularity.curry J v y + L * ‖v - x‖ ^ 2) → u = primal J L x y) := by
  have hd := JointSliceRegularity.differentiable_x_slice J hJ y
  have hw := slice_weak_convex J L hL hJ hLip y
  exact ⟨MoreauTransfer.prox_minimizes _ L hL hd hw x,
    fun u hu => MoreauTransfer.prox_is_unique _ L hL hd hw x u hu⟩

theorem primal_first_order
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    gradient (fun u => JointSliceRegularity.curry J u y) (primal J L x y) =
      (2 * L) • (x - primal J L x y) := by
  exact MoreauTransfer.prox_first_order _ L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (slice_weak_convex J L hL hJ hLip y) x

theorem primal_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖primal J L x y - primal J L x y'‖ ≤ ‖y - y'‖ := by
  let u := primal J L x y
  let u' := primal J L x y'
  let f := JointSliceRegularity.curry J
  have hs := OriginalSaddleRegularity.smooth_function_weakly_convex
    (fun t => f t y) L hL (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun t s => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip t s y)
  have he := PacketCore.gradient_strong_monotone (fun t => f t y) (-L) hs
    (JointSliceRegularity.differentiable_x_slice J hJ y) u u'
  have hu := primal_first_order J L hL hJ hLip x y
  have hu' := primal_first_order J L hL hJ hLip x y'
  change gradient (fun t => f t y) u = (2 * L) • (x - u) at hu
  change gradient (fun t => f t y') u' = (2 * L) • (x - u') at hu'
  have hsplit : gradient (fun t => f t y) u - gradient (fun t => f t y) u' =
      -(2 * L) • (u - u') +
        (gradient (fun t => f t y') u' - gradient (fun t => f t y) u') := by
    rw [hu, hu']
    module
  rw [hsplit, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm
    (gradient (fun t => f t y') u' - gradient (fun t => f t y) u') (u - u')
  have hcross := JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u' y' y
  rw [norm_sub_rev y' y] at hcross
  have hm := mul_le_mul_of_nonneg_right hcross (norm_nonneg (u - u'))
  change ‖u - u'‖ ≤ ‖y - y'‖
  by_cases hz : ‖u - u'‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0 < ‖u - u'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmain : L * ‖u - u'‖ * ‖u - u'‖ ≤ L * ‖y - y'‖ * ‖u - u'‖ := by
      nlinarith only [he, hi, hm]
    have hc := (mul_le_mul_iff_left₀ hp).mp hmain
    exact (mul_le_mul_iff_right₀ hL).mp hc

theorem primal_graph_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖JointSliceRegularity.point (primal J L x y) y -
      JointSliceRegularity.point (primal J L x y') y'‖ ≤ Real.sqrt 2 * ‖y - y'‖ := by
  have hu := primal_lipschitz J L hL hJ hLip x y y'
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hu
  have hn := WithLp.prod_norm_sq_eq_of_L2
    (JointSliceRegularity.point (primal J L x y) y -
      JointSliceRegularity.point (primal J L x y') y')
  rw [JointSliceRegularity.point_eq_toLp, JointSliceRegularity.point_eq_toLp] at hn
  change ‖WithLp.toLp 2 (primal J L x y, y) - WithLp.toLp 2 (primal J L x y', y')‖ ^ 2 =
    ‖primal J L x y - primal J L x y'‖ ^ 2 + ‖y - y'‖ ^ 2 at hn
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt 2 * ‖y - y'‖)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [JointSliceRegularity.point_eq_toLp, JointSliceRegularity.point_eq_toLp]
  nlinarith only [hn, hu2]


theorem gradient_x_hasFDerivAt_x
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (u : E) (y : F) :
    HasFDerivAt (fun z : E => gradient (fun t => JointSliceRegularity.curry J t y) z)
      (blockUU J (JointSliceRegularity.point u y)) u := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point u y)).hasFDerivAt
  have hc := (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp u
    (hgrad.comp u (JointSliceRegularity.point_hasFDerivAt_x u y))
  have heq : (fun z : E => gradient (fun t => JointSliceRegularity.curry J t y) z) =
      (fun z => (gradient J (JointSliceRegularity.point z y)).fst) := by
    funext z
    exact JointSliceRegularity.gradient_x_slice_eq_projection J hJ z y
  rw [heq]
  exact hc

theorem gradient_x_hasFDerivAt_y
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (u : E) (y : F) :
    HasFDerivAt (fun z : F => gradient (fun t => JointSliceRegularity.curry J t z) u)
      (blockUY J (JointSliceRegularity.point u y)) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point u y)).hasFDerivAt
  have hc := (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp y
    (hgrad.comp y (JointSliceRegularity.point_hasFDerivAt_y u y))
  have heq : (fun z : F => gradient (fun t => JointSliceRegularity.curry J t z) u) =
      (fun z => (gradient J (JointSliceRegularity.point u z)).fst) := by
    funext z
    exact JointSliceRegularity.gradient_x_slice_eq_projection J hJ u z
  rw [heq]
  exact hc

theorem block_norm_bounds
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) :
    ‖blockUU J (JointSliceRegularity.point u y)‖ ≤ L ∧
      ‖blockUY J (JointSliceRegularity.point u y)‖ ≤ L := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  exact ⟨(gradient_x_hasFDerivAt_x J hC2 u y).le_of_lip' hL.le
    (Filter.Eventually.of_forall (fun z =>
      JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip z u y)),
    (gradient_x_hasFDerivAt_y J hC2 u y).le_of_lip' hL.le
    (Filter.Eventually.of_forall (fun z =>
      JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u z y))⟩

theorem primalHessian_quadratic_bounds
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) (h : E) :
    L * ‖h‖ ^ 2 ≤ inner ℝ (primalHessian J L x y h) h ∧
      inner ℝ (primalHessian J L x y h) h ≤ 3 * L * ‖h‖ ^ 2 := by
  let H := blockUU J (JointSliceRegularity.point (primal J L x y) y)
  have hH := (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).1
  have hv : ‖H h‖ ≤ L * ‖h‖ :=
    (H.le_opNorm h).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
  have hi := abs_le.mp (abs_real_inner_le_norm (H h) h)
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg h)
  change L * ‖h‖ ^ 2 ≤ inner ℝ (H h + (2 * L) • h) h ∧
    inner ℝ (H h + (2 * L) • h) h ≤ 3 * L * ‖h‖ ^ 2
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith only [hi.1, hi.2, hm]

theorem primalHessian_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : ‖primalHessian J L x y‖ ≤ 3 * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 3 * L)
  intro h
  change ‖blockUU J (JointSliceRegularity.point (primal J L x y) y) h + (2 * L) • h‖ ≤ _
  have hH := (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).1
  calc
    _ ≤ ‖blockUU J (JointSliceRegularity.point (primal J L x y) y) h‖ + ‖(2 * L) • h‖ := norm_add_le _ _
    _ ≤ L * ‖h‖ + (2 * L) * ‖h‖ := by
      gcongr
      · exact (ContinuousLinearMap.le_opNorm _ h).trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)]
    _ = 3 * L * ‖h‖ := by ring

theorem primalHessian_inverse_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    (primalHessian J L x y).IsInvertible ∧ ‖(primalHessian J L x y).inverse‖ ≤ 1 / L := by
  have hc := fun h => (primalHessian_quadratic_bounds J L hL hC2 hLip x y h).1
  let A := OriginalCoerciveOperator.equivalenceOfCoercive (primalHessian J L x y) L hL hc
  have hA : A.toContinuousLinearMap = primalHessian J L x y := rfl
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  exact OriginalCoerciveOperator.inverse_norm_le (primalHessian J L x y) L hL hc

theorem primalHessian_condition_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    ‖primalHessian J L x y‖ * ‖(primalHessian J L x y).inverse‖ ≤ 3 := by
  have h1 := primalHessian_norm_bound J L hL hC2 hLip x y
  have h2 := (primalHessian_inverse_bound J L hL hC2 hLip x y).2
  calc
    _ ≤ (3 * L) * (1 / L) := by gcongr
    _ = 3 := by field_simp


noncomputable def residualDerivative (J : Joint E F → ℝ) (L : ℝ) (p : F × E) : F × E →L[ℝ] E :=
  (blockUY J (JointSliceRegularity.point p.2 p.1)).comp (ContinuousLinearMap.fst ℝ F E) +
    (blockUU J (JointSliceRegularity.point p.2 p.1) + (2 * L) • ContinuousLinearMap.id ℝ E).comp
      (ContinuousLinearMap.snd ℝ F E)

theorem residual_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (x : E) (hC2 : ContDiff ℝ 2 J) :
    ContDiff ℝ 1 (residual J L x) := by
  have hemb : ContDiff ℝ 1 (fun p : F × E => JointSliceRegularity.point p.2 p.1) :=
    ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp contDiff_snd).add
      ((JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.contDiff.comp contDiff_fst)
  have hgrad := (WithLp.fstL 2 ℝ E F).contDiff.comp
    ((contDiff_gradient_of_contDiff2 J hC2).comp hemb)
  have hlin : ContDiff ℝ 1 (fun p : F × E => p.2 - x) := contDiff_snd.sub contDiff_const
  exact hgrad.add (hlin.const_smul (2 * L))

theorem residual_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (x : E) (hC2 : ContDiff ℝ 2 J) (p : F × E) :
    HasFDerivAt (residual J L x) (residualDerivative J L p) p := by
  let emb : F × E →L[ℝ] Joint E F :=
    (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
        (ContinuousLinearMap.snd ℝ F E) +
      (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℝ F E)
  have hemb : HasFDerivAt (fun p : F × E => JointSliceRegularity.point p.2 p.1) emb p :=
    emb.hasFDerivAt
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point p.2 p.1)).hasFDerivAt
  have hc := (WithLp.fstL 2 ℝ E F).hasFDerivAt.comp p (hgrad.comp p hemb)
  have hlin : HasFDerivAt (fun p : F × E => (2 * L) • (p.2 - x))
      ((2 * L) • ContinuousLinearMap.snd ℝ F E) p :=
    ((ContinuousLinearMap.snd ℝ F E).hasFDerivAt.sub_const x).const_smul (2 * L)
  convert! hc.add hlin using 1
  ext q <;>
    simp only [residualDerivative, blockUU, blockUY, emb,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      map_add] <;>
    module

theorem residual_zero_at_primal
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : residual J L x (y, primal J L x y) = 0 := by
  have hfoc := primal_first_order J L hL hJ hLip x y
  unfold residual
  rw [← JointSliceRegularity.gradient_x_slice_eq_projection J hJ, hfoc]
  module

theorem primal_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 1 (primal J L x) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpl : LipschitzWith 1 (primal J L x) := by
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using primal_lipschitz J L hL hJ hLip x y y'
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hinv : (fderiv ℝ (residual J L x) (y, primal J L x y) ∘L
      ContinuousLinearMap.inr ℝ F E).IsInvertible := by
    rw [(residual_hasFDerivAt J L x hC2 (y, primal J L x y)).fderiv]
    have heq : (residualDerivative J L (y, primal J L x y)).comp
        (ContinuousLinearMap.inr ℝ F E) = primalHessian J L x y := by
      ext h
      simp [residualDerivative, primalHessian]
    rw [heq]
    exact (primalHessian_inverse_bound J L hL hC2 hLip x y).1
  exact actual_selection_contDiffAt (residual J L x) (primal J L x) y
    (residual_contDiff J L x hC2).contDiffAt hinv hpl.continuous.continuousAt
    (residual_zero_at_primal J L hL hJ hLip x)

theorem primal_derivative_formula
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    fderiv ℝ (primal J L x) y = -(primalHessian J L x y).inverse.comp
      (blockUY J (JointSliceRegularity.point (primal J L x y) y)) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  have hc := (residual_hasFDerivAt J L x hC2 (y, primal J L x y)).comp y
    ((hasFDerivAt_id y).prodMk hu)
  have heq : (fun t : F => residual J L x (t, primal J L x t)) = fun _ => (0 : E) := by
    funext t
    exact residual_zero_at_primal J L hL hJ hLip x t
  change HasFDerivAt (fun t : F => residual J L x (t, primal J L x t)) _ y at hc
  rw [heq] at hc
  have hd := hc.unique (hasFDerivAt_const (c := (0 : E)) y)
  have hi := (primalHessian_inverse_bound J L hL hC2 hLip x y).1
  ext h
  have hh := DFunLike.congr_fun hd h
  change blockUY J (JointSliceRegularity.point (primal J L x y) y) h +
    primalHessian J L x y (fderiv ℝ (primal J L x) y h) = 0 at hh
  have hneg : primalHessian J L x y (fderiv ℝ (primal J L x) y h) =
      -blockUY J (JointSliceRegularity.point (primal J L x y) y) h := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_comm] using hh
  have hhInv := congrArg (primalHessian J L x y).inverse hneg
  simpa only [hi.inverse_apply_self, map_neg, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply] using hhInv

theorem primal_derivative_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : ‖fderiv ℝ (primal J L x) y‖ ≤ 1 := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  exact hu.le_of_lip' (by norm_num)
    (Filter.Eventually.of_forall (fun t => by
      simpa only [one_mul] using primal_lipschitz J L hL hJ hLip x t y))

theorem primalHessian_selfadjoint
    (J : Joint E F → ℝ) (L : ℝ) (hC2 : ContDiff ℝ 2 J) (x : E) (y : F) :
    (primalHessian J L x y).adjoint = primalHessian J L x y := by
  have hs := OriginalSaddleTangent.gradient_derivative_selfadjoint
    (fun t => JointSliceRegularity.curry J t y)
    (JointSliceRegularity.contDiff2_x_slice J hC2 y) (primal J L x y)
  rw [(gradient_x_hasFDerivAt_x J hC2 (primal J L x y) y).fderiv] at hs
  simp only [primalHessian, map_add, map_smul, hs, ContinuousLinearMap.adjoint_id]


noncomputable def regularizedHessian (J : Joint E F → ℝ) (L : ℝ) (u : E) (y : F) : E →L[ℝ] E :=
  blockUU J (JointSliceRegularity.point u y) + (2 * L) • ContinuousLinearMap.id ℝ E

theorem regularizedHessian_quadratic_bounds
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) (h : E) :
    L * ‖h‖ ^ 2 ≤ inner ℝ (regularizedHessian J L u y h) h ∧
      inner ℝ (regularizedHessian J L u y h) h ≤ 3 * L * ‖h‖ ^ 2 := by
  let H := blockUU J (JointSliceRegularity.point u y)
  have hH := (block_norm_bounds J L hL hC2 hLip u y).1
  have hv : ‖H h‖ ≤ L * ‖h‖ :=
    (H.le_opNorm h).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
  have hi := abs_le.mp (abs_real_inner_le_norm (H h) h)
  have hm := mul_le_mul_of_nonneg_right hv (norm_nonneg h)
  change L * ‖h‖ ^ 2 ≤ inner ℝ (H h + (2 * L) • h) h ∧
    inner ℝ (H h + (2 * L) • h) h ≤ 3 * L * ‖h‖ ^ 2
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith only [hi.1, hi.2, hm]

theorem regularizedHessian_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) : ‖regularizedHessian J L u y‖ ≤ 3 * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 3 * L)
  intro h
  change ‖blockUU J (JointSliceRegularity.point u y) h + (2 * L) • h‖ ≤ _
  have hH := (block_norm_bounds J L hL hC2 hLip u y).1
  calc
    _ ≤ ‖blockUU J (JointSliceRegularity.point u y) h‖ + ‖(2 * L) • h‖ := norm_add_le _ _
    _ ≤ L * ‖h‖ + (2 * L) * ‖h‖ := by
      gcongr
      · exact (ContinuousLinearMap.le_opNorm _ h).trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg h))
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)]
    _ = 3 * L * ‖h‖ := by ring

theorem regularizedHessian_inverse_and_condition
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) :
    (regularizedHessian J L u y).IsInvertible ∧
      ‖(regularizedHessian J L u y).inverse‖ ≤ 1 / L ∧
      ‖regularizedHessian J L u y‖ * ‖(regularizedHessian J L u y).inverse‖ ≤ 3 := by
  have hc := fun h => (regularizedHessian_quadratic_bounds J L hL hC2 hLip u y h).1
  let A := OriginalCoerciveOperator.equivalenceOfCoercive (regularizedHessian J L u y) L hL hc
  have hA : A.toContinuousLinearMap = regularizedHessian J L u y := rfl
  have hi : ‖(regularizedHessian J L u y).inverse‖ ≤ 1 / L := by
    rw [← hA, ContinuousLinearMap.inverse_equiv]
    exact OriginalCoerciveOperator.inverse_norm_le _ L hL hc
  refine ⟨⟨A, hA⟩, hi, ?_⟩
  have hn := regularizedHessian_norm_bound J L hL hC2 hLip u y
  calc
    _ ≤ (3 * L) * (1 / L) := by gcongr
    _ = 3 := by field_simp

/-- This principal contains all original conclusions for the actual selected minimizer,
plus existence/C1/invertibility certificates and uniform conditioning at all primal points. -/
theorem primal_elimination_from_standing_joint
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) :
    (∀ y : F,
      (∀ u : E, JointSliceRegularity.curry J (primal J L x y) y +
        L * ‖primal J L x y - x‖ ^ 2 ≤ JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2) ∧
      (∀ u : E, (∀ v : E, JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2 ≤
        JointSliceRegularity.curry J v y + L * ‖v - x‖ ^ 2) → u = primal J L x y)) ∧
    (∀ y : F, (primalHessian J L x y).adjoint = primalHessian J L x y) ∧
    (∀ y : F, ∀ h : E, L * ‖h‖ ^ 2 ≤ inner ℝ (primalHessian J L x y h) h ∧
      inner ℝ (primalHessian J L x y h) h ≤ 3 * L * ‖h‖ ^ 2) ∧
    (∀ y : F, ‖primalHessian J L x y‖ * ‖(primalHessian J L x y).inverse‖ ≤ 3) ∧
    ContDiff ℝ 1 (primal J L x) ∧
    (∀ y : F, fderiv ℝ (primal J L x) y = -(primalHessian J L x y).inverse.comp
      (blockUY J (JointSliceRegularity.point (primal J L x y) y))) ∧
    (∀ y : F, ‖fderiv ℝ (primal J L x) y‖ ≤ 1) ∧
    (∀ y y' : F, ‖JointSliceRegularity.point (primal J L x y) y -
      JointSliceRegularity.point (primal J L x y') y'‖ ≤ Real.sqrt 2 * ‖y - y'‖) ∧
    (∀ u : E, ∀ y : F, ∀ h : E,
      L * ‖h‖ ^ 2 ≤ inner ℝ (regularizedHessian J L u y h) h ∧
      inner ℝ (regularizedHessian J L u y h) h ≤ 3 * L * ‖h‖ ^ 2) ∧
    (∀ u : E, ∀ y : F, (regularizedHessian J L u y).IsInvertible ∧
      ‖(regularizedHessian J L u y).inverse‖ ≤ 1 / L ∧
      ‖regularizedHessian J L u y‖ * ‖(regularizedHessian J L u y).inverse‖ ≤ 3) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  exact ⟨primal_is_unique_minimizer J L hL hJ hLip x,
    primalHessian_selfadjoint J L hC2 x,
    primalHessian_quadratic_bounds J L hL hC2 hLip x,
    primalHessian_condition_bound J L hL hC2 hLip x,
    primal_contDiff J L hL hC2 hLip x,
    primal_derivative_formula J L hL hC2 hLip x,
    primal_derivative_norm_bound J L hL hC2 hLip x,
    primal_graph_lipschitz J L hL hJ hLip x,
    regularizedHessian_quadratic_bounds J L hL hC2 hLip,
    regularizedHessian_inverse_and_condition J L hL hC2 hLip⟩

end OriginalPrimalElimination


namespace OriginalDualCurvature

open OriginalSaddleImplicit
open OriginalPrimalElimination

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def graph (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : Joint E F :=
  JointSliceRegularity.point (primal J L x y) y

noncomputable def psi (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : ℝ :=
  -sInf (Set.range (fun u : E => JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2))

noncomputable def blockYU (J : Joint E F → ℝ) (w : Joint E F) : E →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap)

noncomputable def blockYY (J : Joint E F → ℝ) (w : Joint E F) : F →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp
    ((fderiv ℝ (gradient J) w).comp (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap)

noncomputable def schur (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) : F →L[ℝ] F :=
  -blockYY J (graph J L x y) + (blockYU J (graph J L x y)).comp
    ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))

theorem psi_eq_value_at_primal
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    psi J L x y = -(J (graph J L x y) + L * ‖primal J L x y - x‖ ^ 2) := by
  change -MoreauTransfer.envelope (fun u => JointSliceRegularity.curry J u y) L x = _
  rw [MoreauTransfer.envelope_eq_prox_objective _ L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (slice_weak_convex J L hL hJ hLip y) x]
  rfl

theorem graph_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 1 (graph J L x) := by
  exact ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.contDiff.comp
    (primal_contDiff J L hL hC2 hLip x)).add
      (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.contDiff

theorem graph_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    HasFDerivAt (graph J L x)
      ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.comp
        (fderiv ℝ (primal J L x) y) +
          (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap) y := by
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  exact ((JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.comp y hu).add
    (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt

theorem psi_hasGradientAt
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    HasGradientAt (psi J L x) (-(gradient J (graph J L x y)).snd) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hu := ((primal_contDiff J L hL hC2 hLip x).differentiable (by norm_num) y).hasFDerivAt
  have hjcomp := (hJ (graph J L x y)).hasFDerivAt.comp y (graph_hasFDerivAt J L hL hC2 hLip x y)
  have hquad := ((hu.sub_const x).norm_sq).const_mul L
  have heq : psi J L x = fun t => -(J (graph J L x t) + L * ‖primal J L x t - x‖ ^ 2) := by
    funext t
    exact psi_eq_value_at_primal J L hL hJ hLip x t
  have hfoc := primal_first_order J L hL hJ hLip x y
  rw [JointSliceRegularity.gradient_x_slice_eq_projection J hJ] at hfoc
  change (gradient J (graph J L x y)).fst = (2 * L) • (x - primal J L x y) at hfoc
  rw [heq]
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! (hjcomp.add hquad).neg using 1
  ext h
  simp only [InnerProductSpace.toDual_apply_apply, neg_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply, two_smul, smul_eq_mul]
  change inner ℝ (-(gradient J (graph J L x y)).snd) h =
    -((fderiv ℝ J (graph J L x y))
      (JointSliceRegularity.axisX (fderiv ℝ (primal J L x) y h) + JointSliceRegularity.axisY h) +
        L * (inner ℝ (primal J L x y - x) (fderiv ℝ (primal J L x) y h) +
          inner ℝ (primal J L x y - x) (fderiv ℝ (primal J L x) y h)))
  rw [← inner_gradient_left, inner_add_right, JointSliceRegularity.inner_axisX,
    JointSliceRegularity.inner_axisY, hfoc, real_inner_smul_left, inner_neg_left]
  rw [show primal J L x y - x = -(x - primal J L x y) by abel, inner_neg_left]
  ring

theorem psi_gradient
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : gradient (psi J L x) = fun y => -(gradient J (graph J L x y)).snd := by
  funext y
  exact (psi_hasGradientAt J L hL hC2 hLip x y).gradient

theorem psi_gradient_contDiff
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 1 (gradient (psi J L x)) := by
  rw [psi_gradient J L hL hC2 hLip x]
  exact ((WithLp.sndL 2 ℝ E F).contDiff.comp
    ((contDiff_gradient_of_contDiff2 J hC2).comp (graph_contDiff J L hL hC2 hLip x))).neg


theorem psi_gradient_hasFDerivAt
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    HasFDerivAt (gradient (psi J L x)) (schur J L x y) y := by
  have hg := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (graph J L x y)).hasFDerivAt
  have hc := ((WithLp.sndL 2 ℝ E F).hasFDerivAt.comp y
    (hg.comp y (graph_hasFDerivAt J L hL hC2 hLip x y))).neg
  rw [psi_gradient J L hL hC2 hLip x]
  convert! hc using 1
  ext h
  rw [primal_derivative_formula J L hL hC2 hLip x y]
  simp only [schur, blockYY, blockYU, graph, ContinuousLinearMap.comp_apply,
    add_apply, neg_apply, map_add, map_neg]
  module

theorem psi_hessian_formula
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : fderiv ℝ (gradient (psi J L x)) y = schur J L x y :=
  (psi_gradient_hasFDerivAt J L hL hC2 hLip x y).fderiv

theorem psi_contDiff2
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ContDiff ℝ 2 (psi J L x) := by
  have hdiff : Differentiable ℝ (psi J L x) :=
    fun y => (psi_hasGradientAt J L hL hC2 hLip x y).differentiableAt
  have hfd : fderiv ℝ (psi J L x) = fun y =>
      InnerProductSpace.toDual ℝ F (gradient (psi J L x) y) := by
    funext y
    exact toDual_gradient.symm
  have hc : ContDiff ℝ 1 (fderiv ℝ (psi J L x)) := by
    rw [hfd]
    exact (InnerProductSpace.toDual ℝ F).toContinuousLinearEquiv.contDiff.comp
      (psi_gradient_contDiff J L hL hC2 hLip x)
  exact contDiff_succ_iff_fderiv.mpr ⟨hdiff, by simp, hc⟩

theorem cross_blocks_adjoint
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (w : Joint E F) :
    blockYU J w = (blockUY J w).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro e f
  let H := fderiv ℝ (gradient J) w
  have hself : H.adjoint = H := OriginalSaddleTangent.gradient_derivative_selfadjoint J hC2 w
  change inner ℝ (H (JointSliceRegularity.axisX e)).snd f =
    inner ℝ e (H (JointSliceRegularity.axisY f)).fst
  calc
    inner ℝ (H (JointSliceRegularity.axisX e)).snd f =
        inner ℝ (H (JointSliceRegularity.axisX e)) (JointSliceRegularity.axisY f) :=
      (JointSliceRegularity.inner_axisY _ _).symm
    _ = inner ℝ (JointSliceRegularity.axisX e) (H (JointSliceRegularity.axisY f)) := by
      rw [← H.adjoint_inner_right, hself]
    _ = inner ℝ (H (JointSliceRegularity.axisY f)) (JointSliceRegularity.axisX e) := real_inner_comm _ _
    _ = inner ℝ (H (JointSliceRegularity.axisY f)).fst e := JointSliceRegularity.inner_axisX _ _
    _ = inner ℝ e (H (JointSliceRegularity.axisY f)).fst := real_inner_comm _ _

theorem gradient_y_hasFDerivAt_y
    (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) (u : E) (y : F) :
    HasFDerivAt (gradient (JointSliceRegularity.curry J u))
      (blockYY J (JointSliceRegularity.point u y)) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgrad := ((contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
    (JointSliceRegularity.point u y)).hasFDerivAt
  have hc := (WithLp.sndL 2 ℝ E F).hasFDerivAt.comp y
    (hgrad.comp y (JointSliceRegularity.point_hasFDerivAt_y u y))
  have heq : gradient (JointSliceRegularity.curry J u) =
      (fun z => (gradient J (JointSliceRegularity.point u z)).snd) := by
    funext z
    exact JointSliceRegularity.gradient_y_slice_eq_projection J hJ u z
  rw [heq]
  exact hc

theorem blockYY_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (u : E) (y : F) : ‖blockYY J (JointSliceRegularity.point u y)‖ ≤ L := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  exact (gradient_y_hasFDerivAt_y J hC2 u y).le_of_lip' hL.le
    (Filter.Eventually.of_forall (fun z =>
      JointSliceRegularity.gradient_y_lipschitz_in_y J hJ L hLip u z y))


theorem negative_blockYY_lower_bound
    (J : Joint E F → ℝ) (μ : ℝ) (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (u : E) (y h : F) :
    μ * ‖h‖ ^ 2 ≤ inner ℝ (-(blockYY J (JointSliceRegularity.point u y) h)) h := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hd := JointSliceRegularity.differentiable_y_slice J hJ u
  have hneg : gradient (fun t => -JointSliceRegularity.curry J u t) =
      fun t => -gradient (JointSliceRegularity.curry J u) t := by
    funext t
    exact OriginalSaddleRegularity.gradient_neg_of_differentiable _ hd t
  have hD : HasFDerivAt (gradient (fun t => -JointSliceRegularity.curry J u t))
      (-blockYY J (JointSliceRegularity.point u y)) y := by
    rw [hneg]
    exact (gradient_y_hasFDerivAt_y J hC2 u y).neg
  exact OriginalCoerciveOperator.derivative_coercive_of_strong_monotonicity _ μ
    (PacketCore.gradient_strong_monotone _ μ (hsc u) hd.neg) y _ hD h

theorem schur_quadratic_lower_bound
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (y h : F) : μ * ‖h‖ ^ 2 ≤ inner ℝ (schur J L x y h) h := by
  let A := primalHessian J L x y
  let U := blockUY J (graph J L x y)
  let a := A.inverse (U h)
  have hi := (primalHessian_inverse_bound J L hL hC2 hLip x y).1
  have hAa : A a = U h := hi.self_apply_inverse _
  have ha := (primalHessian_quadratic_bounds J L hL hC2 hLip x y a).1
  have hpos : 0 ≤ inner ℝ (blockYU J (graph J L x y) a) h := by
    rw [cross_blocks_adjoint J hC2]
    change 0 ≤ inner ℝ (U.adjoint a) h
    rw [U.adjoint_inner_left, ← hAa]
    have heq : inner ℝ a (A a) = inner ℝ (A a) a := real_inner_comm _ _
    rw [heq]
    exact (by positivity : 0 ≤ L * ‖a‖ ^ 2).trans ha
  have hy := negative_blockYY_lower_bound J μ hC2 hsc (primal J L x y) y h
  change μ * ‖h‖ ^ 2 ≤ inner ℝ (-(blockYY J (graph J L x y) h) +
    blockYU J (graph J L x y) a) h
  rw [inner_add_left]
  exact hy.trans (le_add_of_nonneg_right hpos)

theorem schur_norm_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) : ‖schur J L x y‖ ≤ 2 * L := by
  have huu : ‖blockUY J (graph J L x y)‖ ≤ L :=
    (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).2
  have hyy : ‖blockYY J (graph J L x y)‖ ≤ L :=
    blockYY_norm_bound J L hL hC2 hLip (primal J L x y) y
  have hyu : ‖blockYU J (graph J L x y)‖ ≤ L := by
    rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]
    exact huu
  have hi := (primalHessian_inverse_bound J L hL hC2 hLip x y).2
  have ht : ‖(blockYU J (graph J L x y)).comp
      ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))‖ ≤ L := by
    calc
      _ ≤ ‖blockYU J (graph J L x y)‖ *
          (‖(primalHessian J L x y).inverse‖ * ‖blockUY J (graph J L x y)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ L * ((1 / L) * L) := by gcongr
      _ = L := by field_simp
  calc
    _ ≤ ‖-blockYY J (graph J L x y)‖ + ‖(blockYU J (graph J L x y)).comp
        ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))‖ := norm_add_le _ _
    _ ≤ L + L := add_le_add (by rw [norm_neg]; exact hyy) ht
    _ = 2 * L := by ring

theorem psi_hessian_quadratic_bounds
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (y h : F) :
    μ * ‖h‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ∧
      inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ≤ 2 * L * ‖h‖ ^ 2 := by
  rw [psi_hessian_formula J L hL hC2 hLip]
  refine ⟨schur_quadratic_lower_bound J L μ hL hC2 hLip hsc x y h, ?_⟩
  have hn := schur_norm_bound J L hL hC2 hLip x y
  calc
    _ ≤ ‖schur J L x y h‖ * ‖h‖ := real_inner_le_norm _ _
    _ ≤ (2 * L * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.le_opNorm _ h).trans
        (mul_le_mul_of_nonneg_right hn (norm_nonneg h))) (norm_nonneg h)
    _ = 2 * L * ‖h‖ ^ 2 := by ring


theorem contracted_operator_norm
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : Z →L[ℝ] X) (Q : Y →L[ℝ] Z) (D : Z →L[ℝ] Z)
    (hP : ∀ z : Z, ‖P z‖ ≤ ‖z‖) (hQ : ∀ y : Y, ‖Q y‖ ≤ ‖y‖) :
    ‖P.comp (D.comp Q)‖ ≤ ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
  intro h
  exact (hP _).trans ((D.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hQ h) (norm_nonneg D)))

theorem contracted_operator_difference_norm
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : Z →L[ℝ] X) (Q : Y →L[ℝ] Z) (D D' : Z →L[ℝ] Z)
    (hP : ∀ z : Z, ‖P z‖ ≤ ‖z‖) (hQ : ∀ y : Y, ‖Q y‖ ≤ ‖y‖) :
    ‖P.comp (D.comp Q) - P.comp (D'.comp Q)‖ ≤ ‖D - D'‖ := by
  have heq : P.comp (D.comp Q) - P.comp (D'.comp Q) = P.comp ((D - D').comp Q) := by
    ext h
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [heq]
  exact contracted_operator_norm P Q (D - D') hP hQ

theorem block_difference_bounds
    (J : Joint E F → ℝ) (w w' : Joint E F) :
    ‖blockUU J w - blockUU J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ ∧
    ‖blockUY J w - blockUY J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ ∧
    ‖blockYU J w - blockYU J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ ∧
    ‖blockYY J w - blockYY J w'‖ ≤ ‖fderiv ℝ (gradient J) w - fderiv ℝ (gradient J) w'‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_fst_projection) (fun h => le_of_eq ((JointSliceRegularity.axisX (E := E) (F := F)).norm_map h))
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_fst_projection) (fun h => le_of_eq ((JointSliceRegularity.axisY (E := E) (F := F)).norm_map h))
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_snd_projection) (fun h => le_of_eq ((JointSliceRegularity.axisX (E := E) (F := F)).norm_map h))
  · exact contracted_operator_difference_norm _ _ _ _
      (JointSliceRegularity.norm_snd_projection) (fun h => le_of_eq ((JointSliceRegularity.axisY (E := E) (F := F)).norm_map h))

theorem inverse_difference_norm_of_isInvertible
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (hB : B.IsInvertible) :
    ‖A.inverse - B.inverse‖ ≤ ‖A.inverse‖ * ‖B - A‖ * ‖B.inverse‖ := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [← ha, ← hb, ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.inverse_equiv]
  exact OriginalCoerciveOperator.inverse_difference_norm a b

theorem three_factor_norm
    (P : E →L[ℝ] F) (A : E →L[ℝ] E) (Q : F →L[ℝ] E) :
    ‖P.comp (A.comp Q)‖ ≤ ‖P‖ * ‖A‖ * ‖Q‖ := by
  calc
    _ ≤ ‖P‖ * (‖A‖ * ‖Q‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by ring

theorem three_factor_difference
    (P P' : E →L[ℝ] F) (A A' : E →L[ℝ] E) (Q Q' : F →L[ℝ] E) :
    P.comp (A.comp Q) - P'.comp (A'.comp Q') =
      (P - P').comp (A.comp Q) + P'.comp ((A - A').comp Q) +
        P'.comp (A'.comp (Q - Q')) := by
  ext h
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel


theorem schur_lipschitz_before_graph
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖schur J L x y - schur J L x y'‖ ≤ 4 * ρ * ‖graph J L x y - graph J L x y'‖ := by
  let d := ρ * ‖graph J L x y - graph J L x y'‖
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let P := blockYU J (graph J L x y)
  let P' := blockYU J (graph J L x y')
  let Q := blockUY J (graph J L x y)
  let Q' := blockUY J (graph J L x y')
  let A := primalHessian J L x y
  let A' := primalHessian J L x y'
  have hQ : ‖Q‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (primal J L x y) y).2
  have hQ' : ‖Q'‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (primal J L x y') y').2
  have hP : ‖P‖ ≤ L := by
    dsimp [P]; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ
  have hP' : ‖P'‖ ≤ L := by
    dsimp [P']; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ'
  have hAi := primalHessian_inverse_bound J L hL hC2 hLip x y
  have hAi' := primalHessian_inverse_bound J L hL hC2 hLip x y'
  have hAiNorm : ‖A.inverse‖ ≤ 1 / L := hAi.2
  have hAiNorm' : ‖A'.inverse‖ ≤ 1 / L := hAi'.2
  have hblocks := block_difference_bounds J (graph J L x y) (graph J L x y')
  have hH := hHess (graph J L x y) (graph J L x y')
  have hPdiff : ‖P - P'‖ ≤ d := hblocks.2.2.1.trans hH
  have hQdiff : ‖Q - Q'‖ ≤ d := hblocks.2.1.trans hH
  have hYYdiff : ‖blockYY J (graph J L x y) - blockYY J (graph J L x y')‖ ≤ d :=
    hblocks.2.2.2.trans hH
  have hAdiff : ‖A - A'‖ ≤ d := by
    have heq : A - A' = blockUU J (graph J L x y) - blockUU J (graph J L x y') := by
      dsimp [A, A', primalHessian, graph]
      abel
    rw [heq]
    exact hblocks.1.trans hH
  have hAiDiff : ‖A.inverse - A'.inverse‖ ≤ d / L ^ 2 := by
    calc
      _ ≤ ‖A.inverse‖ * ‖A' - A‖ * ‖A'.inverse‖ :=
        inverse_difference_norm_of_isInvertible A A' hAi.1 hAi'.1
      _ ≤ (1 / L) * d * (1 / L) := by
        rw [norm_sub_rev A' A]
        gcongr
      _ = d / L ^ 2 := by field_simp <;> ring
  have ht1 : ‖(P - P').comp (A.inverse.comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P - P'‖ * ‖A.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ d * (1 / L) * L := by gcongr
      _ = d := by field_simp
  have ht2 : ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A.inverse - A'.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ L * (d / L ^ 2) * L := by gcongr
      _ = d := by field_simp <;> ring
  have ht3 : ‖P'.comp (A'.inverse.comp (Q - Q'))‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A'.inverse‖ * ‖Q - Q'‖ := three_factor_norm _ _ _
      _ ≤ L * (1 / L) * d := by gcongr
      _ = d := by field_simp
  have hterms : ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ ≤ 3 * d := by
    rw [three_factor_difference]
    calc
      _ ≤ ‖(P - P').comp (A.inverse.comp Q)‖ +
          ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ +
          ‖P'.comp (A'.inverse.comp (Q - Q'))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ d + d + d := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * d := by ring
  have heq : schur J L x y - schur J L x y' =
      -(blockYY J (graph J L x y) - blockYY J (graph J L x y')) +
        (P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')) := by
    dsimp [schur, P, P', Q, Q', A, A']
    abel
  rw [heq]
  calc
    _ ≤ ‖-(blockYY J (graph J L x y) - blockYY J (graph J L x y'))‖ +
        ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ := norm_add_le _ _
    _ ≤ d + 3 * d := add_le_add (by rw [norm_neg]; exact hYYdiff) hterms
    _ = 4 * ρ * ‖graph J L x y - graph J L x y'‖ := by dsimp [d]; ring

theorem psi_hessian_lipschitz
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖fderiv ℝ (gradient (psi J L x)) y - fderiv ℝ (gradient (psi J L x)) y'‖ ≤
      (4 * Real.sqrt 2) * ρ * ‖y - y'‖ := by
  rw [psi_hessian_formula J L hL hC2 hLip x y, psi_hessian_formula J L hL hC2 hLip x y']
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hgraph := primal_graph_lipschitz J L hL hJ hLip x y y'
  calc
    _ ≤ 4 * ρ * ‖graph J L x y - graph J L x y'‖ :=
      schur_lipschitz_before_graph J L ρ hL hρ hC2 hLip hHess x y y'
    _ ≤ 4 * ρ * (Real.sqrt 2 * ‖y - y'‖) :=
      mul_le_mul_of_nonneg_left hgraph (by positivity : 0 ≤ 4 * ρ)
    _ = (4 * Real.sqrt 2) * ρ * ‖y - y'‖ := by ring


theorem psi_gradient_slice
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y : F) :
    gradient (psi J L x) y = -gradient (JointSliceRegularity.curry J (primal J L x y)) y := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  rw [psi_gradient J L hL hC2 hLip x,
    JointSliceRegularity.gradient_y_slice_eq_projection J hJ]
  rfl

theorem psi_gradient_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) : ∀ y y' : F,
    ‖gradient (psi J L x) y - gradient (psi J L x) y'‖ ≤ 2 * L * ‖y - y'‖ := by
  apply OriginalAudit.lipschitz_gradient_of_bounded_fderiv_gradient
  · exact (psi_gradient_contDiff J L hL hC2 hLip x).differentiable (by norm_num)
  · intro y
    rw [psi_hessian_formula J L hL hC2 hLip x y]
    exact schur_norm_bound J L hL hC2 hLip x y

theorem psi_strongConvex
    (J : Joint E F → ℝ) (L μ : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) μ
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) : StrongConvexOn (Set.univ : Set F) μ (psi J L x) := by
  let g : F → E → ℝ := fun y u => -(JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2)
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hw : ∀ u : E, StrongConvexOn (Set.univ : Set F) (-(-μ)) (fun y => g y u) := by
    intro u
    apply strongConvexOn_iff_convex.mpr
    have hc := (strongConvexOn_iff_convex.mp (hsc u)).add_const (-L * ‖u - x‖ ^ 2)
    convert hc using 1 <;> (first | rfl | (funext y; dsimp [g]; ring))
  have hmax : ∀ y : F, ∀ u : E, g y u ≤ g y (primal J L x y) := by
    intro y u
    exact neg_le_neg ((primal_is_unique_minimizer J L hL hJ hLip x y).1 u)
  have hv := OriginalSaddleRegularity.value_weakly_convex_from_actual_maxima
    g (-μ) hw (primal J L x) hmax
  have heq : OriginalSaddleRegularity.value g (primal J L x) = psi J L x := by
    funext y
    exact (psi_eq_value_at_primal J L hL hJ hLip x y).symm
  rw [heq] at hv
  simpa only [neg_neg] using hv

/-- All original reduced-dual curvature conclusions refer to the genuine negative minimum,
with actual gradients/Hessians and no value-function or Schur formula assumptions. -/
theorem dual_curvature_from_standing_joint
    (J : Joint E F → ℝ) (L μ ρ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) μ
      (fun y => J (WithLp.toLp 2 (u, y))))
    (x : E) :
    ContDiff ℝ 2 (psi J L x) ∧
    (∀ y : F, gradient (psi J L x) y = -gradient (JointSliceRegularity.curry J (primal J L x y)) y) ∧
    (∀ y : F, fderiv ℝ (gradient (psi J L x)) y =
      -blockYY J (graph J L x y) + (blockYU J (graph J L x y)).comp
        ((primalHessian J L x y).inverse.comp (blockUY J (graph J L x y)))) ∧
    (∀ y : F, ∀ h : F,
      μ * ‖h‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ∧
      inner ℝ (fderiv ℝ (gradient (psi J L x)) y h) h ≤ 2 * L * ‖h‖ ^ 2) ∧
    (∀ y y' : F,
      ‖fderiv ℝ (gradient (psi J L x)) y - fderiv ℝ (gradient (psi J L x)) y'‖ ≤
        (4 * Real.sqrt 2) * ρ * ‖y - y'‖) ∧
    StrongConvexOn (Set.univ : Set F) μ (psi J L x) ∧
    (∀ y y' : F, ‖gradient (psi J L x) y - gradient (psi J L x) y'‖ ≤ 2 * L * ‖y - y'‖) := by
  have hconcave' : ∀ u : E, StrongConcaveOn (Set.univ : Set F) μ (JointSliceRegularity.curry J u) := by
    intro u
    have heq : JointSliceRegularity.curry J u = (fun y : F => J (WithLp.toLp 2 (u, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp u y)
    rw [heq]
    exact hconcave u
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J μ hconcave'
  exact ⟨psi_contDiff2 J L hL hC2 hLip x,
    psi_gradient_slice J L hL hC2 hLip x,
    psi_hessian_formula J L hL hC2 hLip x,
    psi_hessian_quadratic_bounds J L μ hL hC2 hLip hsc x,
    psi_hessian_lipschitz J L ρ hL hρ hC2 hLip hHess x,
    psi_strongConvex J L μ hL hC2 hLip hsc x,
    psi_gradient_lipschitz J L hL hC2 hLip x⟩

end OriginalDualCurvature


namespace OriginalDualOracleEstimates

open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualCurvature

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def schurAt (J : Joint E F → ℝ) (L : ℝ) (u : E) (y : F) : F →L[ℝ] F :=
  -blockYY J (JointSliceRegularity.point u y) + (blockYU J (JointSliceRegularity.point u y)).comp
    ((regularizedHessian J L u y).inverse.comp (blockUY J (JointSliceRegularity.point u y)))

theorem off_solution_schur_lipschitz
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (u u' : E) (y y' : F) :
    ‖schurAt J L u y - schurAt J L u' y'‖ ≤ 4 * ρ * ‖JointSliceRegularity.point u y - JointSliceRegularity.point u' y'‖ := by
  let d := ρ * ‖JointSliceRegularity.point u y - JointSliceRegularity.point u' y'‖
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let P := blockYU J (JointSliceRegularity.point u y)
  let P' := blockYU J (JointSliceRegularity.point u' y')
  let Q := blockUY J (JointSliceRegularity.point u y)
  let Q' := blockUY J (JointSliceRegularity.point u' y')
  let A := regularizedHessian J L u y
  let A' := regularizedHessian J L u' y'
  have hQ : ‖Q‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (u) y).2
  have hQ' : ‖Q'‖ ≤ L := (block_norm_bounds J L hL hC2 hLip (u') y').2
  have hP : ‖P‖ ≤ L := by
    dsimp [P]; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ
  have hP' : ‖P'‖ ≤ L := by
    dsimp [P']; rw [cross_blocks_adjoint J hC2, ContinuousLinearMap.adjoint.norm_map]; exact hQ'
  have hAi := regularizedHessian_inverse_and_condition J L hL hC2 hLip u y
  have hAi' := regularizedHessian_inverse_and_condition J L hL hC2 hLip u' y'
  have hAiNorm : ‖A.inverse‖ ≤ 1 / L := hAi.2.1
  have hAiNorm' : ‖A'.inverse‖ ≤ 1 / L := hAi'.2.1
  have hblocks := block_difference_bounds J (JointSliceRegularity.point u y) (JointSliceRegularity.point u' y')
  have hH := hHess (JointSliceRegularity.point u y) (JointSliceRegularity.point u' y')
  have hPdiff : ‖P - P'‖ ≤ d := hblocks.2.2.1.trans hH
  have hQdiff : ‖Q - Q'‖ ≤ d := hblocks.2.1.trans hH
  have hYYdiff : ‖blockYY J (JointSliceRegularity.point u y) - blockYY J (JointSliceRegularity.point u' y')‖ ≤ d :=
    hblocks.2.2.2.trans hH
  have hAdiff : ‖A - A'‖ ≤ d := by
    have heq : A - A' = blockUU J (JointSliceRegularity.point u y) - blockUU J (JointSliceRegularity.point u' y') := by
      dsimp [A, A', regularizedHessian]
      abel
    rw [heq]
    exact hblocks.1.trans hH
  have hAiDiff : ‖A.inverse - A'.inverse‖ ≤ d / L ^ 2 := by
    calc
      _ ≤ ‖A.inverse‖ * ‖A' - A‖ * ‖A'.inverse‖ :=
        inverse_difference_norm_of_isInvertible A A' hAi.1 hAi'.1
      _ ≤ (1 / L) * d * (1 / L) := by
        rw [norm_sub_rev A' A]
        gcongr
      _ = d / L ^ 2 := by field_simp <;> ring
  have ht1 : ‖(P - P').comp (A.inverse.comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P - P'‖ * ‖A.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ d * (1 / L) * L := by gcongr
      _ = d := by field_simp
  have ht2 : ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A.inverse - A'.inverse‖ * ‖Q‖ := three_factor_norm _ _ _
      _ ≤ L * (d / L ^ 2) * L := by gcongr
      _ = d := by field_simp <;> ring
  have ht3 : ‖P'.comp (A'.inverse.comp (Q - Q'))‖ ≤ d := by
    calc
      _ ≤ ‖P'‖ * ‖A'.inverse‖ * ‖Q - Q'‖ := three_factor_norm _ _ _
      _ ≤ L * (1 / L) * d := by gcongr
      _ = d := by field_simp
  have hterms : ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ ≤ 3 * d := by
    rw [three_factor_difference]
    calc
      _ ≤ ‖(P - P').comp (A.inverse.comp Q)‖ +
          ‖P'.comp ((A.inverse - A'.inverse).comp Q)‖ +
          ‖P'.comp (A'.inverse.comp (Q - Q'))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ d + d + d := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * d := by ring
  have heq : schurAt J L u y - schurAt J L u' y' =
      -(blockYY J (JointSliceRegularity.point u y) - blockYY J (JointSliceRegularity.point u' y')) +
        (P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')) := by
    dsimp [schurAt, P, P', Q, Q', A, A']
    abel
  rw [heq]
  calc
    _ ≤ ‖-(blockYY J (JointSliceRegularity.point u y) - blockYY J (JointSliceRegularity.point u' y'))‖ +
        ‖P.comp (A.inverse.comp Q) - P'.comp (A'.inverse.comp Q')‖ := norm_add_le _ _
    _ ≤ d + 3 * d := add_le_add (by rw [norm_neg]; exact hYYdiff) hterms
    _ = 4 * ρ * ‖JointSliceRegularity.point u y - JointSliceRegularity.point u' y'‖ := by dsimp [d]; ring



noncomputable def valueEstimate (J : Joint E F → ℝ) (L : ℝ) (x u : E) (y : F) : ℝ :=
  -(JointSliceRegularity.curry J u y + L * ‖u - x‖ ^ 2)

noncomputable def gradientEstimate (J : Joint E F → ℝ) (u : E) (y : F) : F :=
  -gradient (JointSliceRegularity.curry J u) y

theorem value_estimate_error
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * ‖u - primal J L x y‖ ^ 2 := by
  let p := primal J L x y
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hs := OriginalAudit.smooth_descent_upper (fun t => f t y) L hL
    (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun t t' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip t t' y)
    p (u - p)
  rw [show p + (u - p) = u by abel] at hs
  have hfoc := primal_first_order J L hL hJ hLip x y
  change gradient (fun t => f t y) p = (2 * L) • (x - p) at hfoc
  rw [hfoc, real_inner_smul_left] at hs
  have hquad := OriginalSaddleStability.norm_square_center_change x p u
  have hquadL := congrArg (fun t : ℝ => L * t) hquad
  have hupper : f u y + L * ‖u - x‖ ^ 2 - (f p y + L * ‖p - x‖ ^ 2) ≤
      3 * L / 2 * ‖u - p‖ ^ 2 := by
    nlinarith only [hs, hquadL]
  have hmin := (primal_is_unique_minimizer J L hL hJ hLip x y).1 u
  have hnonneg : 0 ≤ f u y + L * ‖u - x‖ ^ 2 - (f p y + L * ‖p - x‖ ^ 2) := sub_nonneg.mpr hmin
  have heq : valueEstimate J L x u y - psi J L x y =
      -(f u y + L * ‖u - x‖ ^ 2 - (f p y + L * ‖p - x‖ ^ 2)) := by
    rw [psi_eq_value_at_primal J L hL hJ hLip x y]
    dsimp [valueEstimate, f, p, graph, JointSliceRegularity.curry]
    ring
  rw [heq, abs_neg, abs_of_nonneg hnonneg]
  exact hupper

theorem gradient_estimate_error
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * ‖u - primal J L x y‖ := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  rw [psi_gradient_slice J L hL hC2 hLip x y]
  change ‖-gradient (JointSliceRegularity.curry J u) y -
    -gradient (JointSliceRegularity.curry J (primal J L x y)) y‖ ≤ _
  have heq : -gradient (JointSliceRegularity.curry J u) y -
      -gradient (JointSliceRegularity.curry J (primal J L x y)) y =
    gradient (JointSliceRegularity.curry J (primal J L x y)) y -
      gradient (JointSliceRegularity.curry J u) y := by abel
  rw [heq]
  calc
    _ ≤ L * ‖primal J L x y - u‖ :=
      JointSliceRegularity.gradient_y_lipschitz_in_x J hJ L hLip (primal J L x y) u y
    _ = L * ‖u - primal J L x y‖ := by rw [norm_sub_rev]

theorem hessian_estimate_error
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u : E) (y : F) :
    ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * ‖u - primal J L x y‖ := by
  rw [psi_hessian_formula J L hL hC2 hLip x y]
  have heq : schur J L x y = schurAt J L (primal J L x y) y := rfl
  rw [heq]
  have hb := off_solution_schur_lipschitz J L ρ hL hρ hC2 hLip hHess
    u (primal J L x y) y y
  rw [JointSliceRegularity.norm_point_sub_same_y] at hb
  exact hb

theorem plug_in_errors_at_tolerance
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u : E) (y : F) (e : ℝ) (he : ‖u - primal J L x y‖ ≤ e) :
    |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
    ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * e ∧
    ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e := by
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  refine ⟨(value_estimate_error J L hL hC2 hLip x u y).trans ?_,
    (gradient_estimate_error J L hL hC2 hLip x u y).trans ?_,
    (hessian_estimate_error J L ρ hL hρ hC2 hLip hHess x u y).trans ?_⟩
  · exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) he0).mpr he) (by positivity)
  · exact mul_le_mul_of_nonneg_left he hL.le
  · exact mul_le_mul_of_nonneg_left he (by positivity)


theorem residual_strong_pairing
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    L * ‖u - primal J L x y‖ ^ 2 ≤
      inner ℝ (OriginalPrimalElimination.residual J L x (y, u)) (u - primal J L x y) := by
  let p := primal J L x y
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hs := OriginalSaddleRegularity.smooth_function_weakly_convex
    (fun t => f t y) L hL (JointSliceRegularity.differentiable_x_slice J hJ y)
    (fun t t' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip t t' y)
  have he := PacketCore.gradient_strong_monotone (fun t => f t y) (-L) hs
    (JointSliceRegularity.differentiable_x_slice J hJ y) u p
  have hfoc := primal_first_order J L hL hJ hLip x y
  change gradient (fun t => f t y) p = (2 * L) • (x - p) at hfoc
  have hr : OriginalPrimalElimination.residual J L x (y, u) =
      gradient (fun t => f t y) u - gradient (fun t => f t y) p + (2 * L) • (u - p) := by
    dsimp only [OriginalPrimalElimination.residual]
    rw [← JointSliceRegularity.gradient_x_slice_eq_projection J hJ]
    change gradient (fun t => f t y) u + (2 * L) • (u - x) = _
    rw [hfoc]
    module
  rw [hr, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith only [he]

theorem observable_residual_distance
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖u - primal J L x y‖ ≤ ‖OriginalPrimalElimination.residual J L x (y, u)‖ / L := by
  have hc := residual_strong_pairing J L hL hC2 hLip x u y
  have hi := real_inner_le_norm (OriginalPrimalElimination.residual J L x (y, u)) (u - primal J L x y)
  apply (le_div_iff₀ hL).mpr
  by_cases hz : ‖u - primal J L x y‖ = 0
  · rw [hz, zero_mul]; exact norm_nonneg _
  · have hp : 0 < ‖u - primal J L x y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [hc, hi])

theorem residual_norm_upper
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖OriginalPrimalElimination.residual J L x (y, u)‖ ≤ 3 * L * ‖u - primal J L x y‖ := by
  let p := primal J L x y
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hfoc := primal_first_order J L hL hJ hLip x y
  change gradient (fun t => f t y) p = (2 * L) • (x - p) at hfoc
  have hr : OriginalPrimalElimination.residual J L x (y, u) =
      gradient (fun t => f t y) u - gradient (fun t => f t y) p + (2 * L) • (u - p) := by
    dsimp only [OriginalPrimalElimination.residual]
    rw [← JointSliceRegularity.gradient_x_slice_eq_projection J hJ]
    change gradient (fun t => f t y) u + (2 * L) • (u - x) = _
    rw [hfoc]
    module
  have hg := JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u p y
  rw [hr]
  calc
    _ ≤ ‖gradient (fun t => f t y) u - gradient (fun t => f t y) p‖ + ‖(2 * L) • (u - p)‖ := norm_add_le _ _
    _ ≤ L * ‖u - p‖ + (2 * L) * ‖u - p‖ := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)]
    _ = 3 * L * ‖u - p‖ := by ring

end OriginalDualOracleEstimates


namespace OriginalDualOracleGD

open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualCurvature
open OriginalDualOracleEstimates

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def step (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) (u : E) : E :=
  u - (1 / (9 * L)) • OriginalPrimalElimination.residual J L x (y, u)

noncomputable def iterate (J : Joint E F → ℝ) (L : ℝ) (x : E) (y : F) (u0 : E) : ℕ → E :=
  Nat.rec u0 (fun _ u => step J L x y u)

noncomputable def logBudget (D e : ℝ) : ℕ := Nat.ceil (18 * Real.log (1 + 3 * D / e))

theorem step_squared_contraction
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u : E) (y : F) :
    ‖step J L x y u - primal J L x y‖ ^ 2 ≤ (8 / 9 : ℝ) * ‖u - primal J L x y‖ ^ 2 := by
  let p := primal J L x y
  let r := OriginalPrimalElimination.residual J L x (y, u)
  let a : ℝ := 1 / (9 * L)
  have ha : 0 < a := by dsimp [a]; positivity
  have hc := residual_strong_pairing J L hL hC2 hLip x u y
  have hr := residual_norm_upper J L hL hC2 hLip x u y
  have hr2 : ‖r‖ ^ 2 ≤ (3 * L * ‖u - p‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * L * ‖u - p‖)).mpr hr
  have hn : step J L x y u - p = (u - p) - a • r := by dsimp [step, a, r]; abel
  rw [hn, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    real_inner_smul_right, real_inner_comm r (u - p)]
  have hpos := mul_le_mul_of_nonneg_left hr2 (sq_nonneg a)
  have hneg := mul_le_mul_of_nonpos_left hc (by nlinarith only [ha] : -2 * a ≤ 0)
  calc
    _ ≤ ‖u - p‖ ^ 2 + a ^ 2 * (3 * L * ‖u - p‖) ^ 2 -
        2 * a * (L * ‖u - p‖ ^ 2) := by nlinarith only [hpos, hneg]
    _ = (8 / 9 : ℝ) * ‖u - p‖ ^ 2 := by dsimp [a]; field_simp <;> ring

theorem iterate_squared_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y : F) (n : ℕ) :
    ‖iterate J L x y u0 n - primal J L x y‖ ^ 2 ≤
      (8 / 9 : ℝ) ^ n * ‖u0 - primal J L x y‖ ^ 2 := by
  induction n with
  | zero => simp only [iterate, Nat.rec_zero, pow_zero, one_mul, le_refl]
  | succ n ih =>
    change ‖step J L x y (iterate J L x y u0 n) - primal J L x y‖ ^ 2 ≤ _
    calc
      _ ≤ (8 / 9 : ℝ) * ‖iterate J L x y u0 n - primal J L x y‖ ^ 2 :=
        step_squared_contraction J L hL hC2 hLip x _ y
      _ ≤ (8 / 9 : ℝ) * ((8 / 9 : ℝ) ^ n * ‖u0 - primal J L x y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (8 / 9 : ℝ) ^ (n + 1) * ‖u0 - primal J L x y‖ ^ 2 := by rw [pow_succ]; ring

theorem geometric_exponential_bound (n : ℕ) :
    (8 / 9 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 9) := by
  have hq : (8 / 9 : ℝ) ≤ Real.exp (-1 / 9) := by
    nlinarith only [Real.add_one_le_exp (-1 / 9)]
  calc
    _ ≤ (Real.exp (-1 / 9)) ^ n := pow_le_pow_left₀ (by norm_num) hq n
    _ = Real.exp (-(n : ℝ) / 9) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem logarithmic_geometric_accuracy (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e) :
    (8 / 9 : ℝ) ^ logBudget D e * D ^ 2 ≤ (e / 3) ^ 2 := by
  let t := 1 + 3 * D / e
  have ht : 0 < t := by dsimp [t]; positivity
  have hceil : 18 * Real.log t ≤ (logBudget D e : ℝ) := Nat.le_ceil _
  have hpow : (8 / 9 : ℝ) ^ logBudget D e ≤ (t ^ 2)⁻¹ := by
    calc
      _ ≤ Real.exp (-(logBudget D e : ℝ) / 9) := geometric_exponential_bound _
      _ ≤ Real.exp (-(2 * Real.log t)) := Real.exp_le_exp.mpr (by linarith only [hceil])
      _ = (t ^ 2)⁻¹ := by
        rw [Real.exp_neg, show 2 * Real.log t = Real.log t + Real.log t by ring,
          Real.exp_add, Real.exp_log ht]
        ring
  have hratio : D / t ≤ e / 3 := by
    apply (div_le_iff₀ ht).mpr
    dsimp [t]
    have he0 : e ≠ 0 := ne_of_gt he
    field_simp
    nlinarith only [he]
  have hsquare : (D / t) ^ 2 ≤ (e / 3) ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ D / t) (by positivity : 0 ≤ e / 3)).mpr hratio
  calc
    _ ≤ (t ^ 2)⁻¹ * D ^ 2 := mul_le_mul_of_nonneg_right hpow (sq_nonneg D)
    _ = (D / t) ^ 2 := by field_simp
    _ ≤ (e / 3) ^ 2 := hsquare

theorem logBudget_query_bound (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e) :
    (logBudget D e : ℝ) + 1 ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  have ht : 1 ≤ 1 + 3 * D / e := by
    have hp : 0 ≤ 3 * D / e := by positivity
    linarith
  have hl : 0 ≤ 18 * Real.log (1 + 3 * D / e) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg ht)
  have hc := Nat.ceil_lt_add_one hl
  change (logBudget D e : ℝ) < 18 * Real.log (1 + 3 * D / e) + 1 at hc
  linarith


theorem iterate_at_budget_certified
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y : F) (D e : ℝ) (hD : 0 ≤ D) (he : 0 < e)
    (hinit : ‖u0 - primal J L x y‖ ≤ D) :
    ‖iterate J L x y u0 (logBudget D e) - primal J L x y‖ ≤ e / 3 ∧
    ‖OriginalPrimalElimination.residual J L x
      (y, iterate J L x y u0 (logBudget D e))‖ ≤ L * e := by
  let u := iterate J L x y u0 (logBudget D e)
  have hiter := iterate_squared_bound J L hL hC2 hLip x u0 y (logBudget D e)
  have hsq : ‖u - primal J L x y‖ ^ 2 ≤ (e / 3) ^ 2 := by
    calc
      _ ≤ (8 / 9 : ℝ) ^ logBudget D e * ‖u0 - primal J L x y‖ ^ 2 := hiter
      _ ≤ (8 / 9 : ℝ) ^ logBudget D e * D ^ 2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hD).mpr hinit) (by positivity)
      _ ≤ (e / 3) ^ 2 := logarithmic_geometric_accuracy D e hD he
  have hu : ‖u - primal J L x y‖ ≤ e / 3 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ e / 3)).mp hsq
  refine ⟨hu, ?_⟩
  calc
    _ ≤ 3 * L * ‖u - primal J L x y‖ := residual_norm_upper J L hL hC2 hLip x u y
    _ ≤ 3 * L * (e / 3) := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 3 * L)
    _ = L * e := by ring

theorem observed_initial_residual_simulation
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) (e : ℝ) (he : 0 < e) :
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    let n := logBudget D e
    let u := iterate J L x y u0 n
    ‖OriginalPrimalElimination.residual J L x (y, u)‖ ≤ L * e ∧
    ‖u - primal J L x y‖ ≤ e ∧
    |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
    ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * e ∧
    ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e ∧
    (n : ℝ) + 1 ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hinit : ‖u0 - primal J L x y‖ ≤ D := observable_residual_distance J L hL hC2 hLip x u0 y
  have hu := iterate_at_budget_certified J L hL hC2 hLip x u0 y D e hD he hinit
  have hdist : ‖iterate J L x y u0 (logBudget D e) - primal J L x y‖ ≤ e :=
    hu.1.trans (by linarith only [he])
  have herr := plug_in_errors_at_tolerance J L ρ hL hρ hC2 hLip hHess x
    (iterate J L x y u0 (logBudget D e)) y e hdist
  exact ⟨hu.2, hdist, herr.1, herr.2.1, herr.2.2, logBudget_query_bound D e hD he⟩


theorem primal_center_lipschitz
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y : F) :
    ‖primal J L x y - primal J L x' y‖ ≤ 2 * ‖x - x'‖ := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hzero := residual_zero_at_primal J L hL hJ hLip x y
  have hr : OriginalPrimalElimination.residual J L x' (y, primal J L x y) =
      (2 * L) • (x - x') := by
    have heq : OriginalPrimalElimination.residual J L x' (y, primal J L x y) =
        OriginalPrimalElimination.residual J L x (y, primal J L x y) + (2 * L) • (x - x') := by
      dsimp [OriginalPrimalElimination.residual]
      module
    rw [heq, hzero, zero_add]
  have hb := observable_residual_distance J L hL hC2 hLip x' (primal J L x y) y
  rw [hr, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * L)] at hb
  have heq : (2 * L * ‖x - x'‖) / L = 2 * ‖x - x'‖ := by field_simp
  rwa [heq] at hb

theorem warm_initial_residual_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y y' : F) :
    ‖OriginalPrimalElimination.residual J L x (y, primal J L x' y')‖ / L ≤
      3 * (2 * ‖x' - x‖ + ‖y' - y‖) := by
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hx := primal_center_lipschitz J L hL hC2 hLip x' x y'
  have hy := primal_lipschitz J L hL hJ hLip x y' y
  have htri := dist_triangle (primal J L x' y') (primal J L x y') (primal J L x y)
  simp only [dist_eq_norm] at htri
  have hd : ‖primal J L x' y' - primal J L x y‖ ≤ 2 * ‖x' - x‖ + ‖y' - y‖ :=
    htri.trans (add_le_add hx hy)
  have hr := residual_norm_upper J L hL hC2 hLip x (primal J L x' y') y
  apply (div_le_iff₀ hL).mpr
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 3 * L)
  nlinarith only [hr, hm]

end OriginalDualOracleGD


namespace OriginalDualOracleProgram

open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualCurvature
open OriginalDualOracleEstimates
open OriginalDualOracleGD

inductive QueryProgram (Z A V : Type*) where
  | pure (value : V)
  | ask (point : Z) (next : A → QueryProgram Z A V)

noncomputable def execute {Z A V : Type*} (oracle : Z → A) : QueryProgram Z A V → V × ℕ
  | .pure v => (v, 0)
  | .ask z next => let r := execute oracle (next (oracle z)); (r.1, r.2 + 1)

structure OracleAnswer (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] where
  value : ℝ
  grad : Z
  hess : Z →L[ℝ] Z

structure QueryState (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  u : E
  answer : OracleAnswer (Joint E F)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def actualOracle (J : Joint E F → ℝ) (w : Joint E F) : OracleAnswer (Joint E F) :=
  ⟨J w, gradient J w, fderiv ℝ (gradient J) w⟩

noncomputable def actualState (J : Joint E F → ℝ) (y : F) (u : E) : QueryState E F :=
  ⟨u, actualOracle J (JointSliceRegularity.point u y)⟩

noncomputable def answerResidual (L : ℝ) (x : E) (s : QueryState E F) : E :=
  s.answer.grad.fst + (2 * L) • (s.u - x)

noncomputable def nextPoint (L : ℝ) (x : E) (s : QueryState E F) : E :=
  s.u - (1 / (9 * L)) • answerResidual L x s

noncomputable def loop (L : ℝ) (x : E) (y : F) : ℕ → QueryState E F →
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (QueryState E F)
  | 0, s => .pure s
  | n + 1, s => .ask (JointSliceRegularity.point (nextPoint L x s) y)
      (fun a => loop L x y n ⟨nextPoint L x s, a⟩)

/-- The initial oracle response is cached for both the initial radius certificate and first step.
Each subsequent query supplies the gradient for the next step and the final plug-in Hessian/value. -/
noncomputable def simulator (L : ℝ) (x : E) (y : F) (u0 : E) (e : ℝ) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (QueryState E F) :=
  .ask (JointSliceRegularity.point u0 y) (fun a0 =>
    let s0 : QueryState E F := ⟨u0, a0⟩
    loop L x y (logBudget (‖answerResidual L x s0‖ / L) e) s0)

theorem loop_query_count
    (oracle : Joint E F → OracleAnswer (Joint E F)) (L : ℝ) (x : E) (y : F)
    (n : ℕ) (s : QueryState E F) : (execute oracle (loop L x y n s)).2 = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [loop, execute, ih]

theorem iterate_shift (J : Joint E F → ℝ) (L : ℝ) (x u : E) (y : F) (n : ℕ) :
    iterate J L x y u (n + 1) = iterate J L x y (step J L x y u) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step J L x y (iterate J L x y u (n + 1)) =
      step J L x y (iterate J L x y (step J L x y u) n)
    rw [ih]

theorem loop_actual_state
    (J : Joint E F → ℝ) (L : ℝ) (x u : E) (y : F) (n : ℕ) :
    (execute (actualOracle J) (loop L x y n (actualState J y u))).1 =
      actualState J y (iterate J L x y u n) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    change (execute (actualOracle J)
      (loop L x y n (actualState J y (step J L x y u)))).1 = _
    rw [ih, ← iterate_shift]

theorem simulator_actual_execution
    (J : Joint E F → ℝ) (L : ℝ) (x u0 : E) (y : F) (e : ℝ) :
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    let n := logBudget D e
    execute (actualOracle J) (simulator L x y u0 e) =
      (actualState J y (iterate J L x y u0 n), n + 1) := by
  dsimp only [simulator, execute]
  apply Prod.ext
  · exact loop_actual_state J L x u0 y _
  · exact congrArg (fun k : ℕ => k + 1) (loop_query_count (actualOracle J) L x y _ _)

noncomputable def valueOutput (L : ℝ) (x : E) (s : QueryState E F) : ℝ :=
  -(s.answer.value + L * ‖s.u - x‖ ^ 2)

noncomputable def gradientOutput (s : QueryState E F) : F := -s.answer.grad.snd

noncomputable def hessianOutput (L : ℝ) (s : QueryState E F) : F →L[ℝ] F :=
  let X := (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap
  let Y := (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap
  let A := (WithLp.fstL 2 ℝ E F).comp (s.answer.hess.comp X) +
    (2 * L) • ContinuousLinearMap.id ℝ E
  let U := (WithLp.fstL 2 ℝ E F).comp (s.answer.hess.comp Y)
  let V := (WithLp.sndL 2 ℝ E F).comp (s.answer.hess.comp X)
  let W := (WithLp.sndL 2 ℝ E F).comp (s.answer.hess.comp Y);
  -W + V.comp (A.inverse.comp U)

theorem actual_state_outputs
    (J : Joint E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ) (x u : E) (y : F) :
    valueOutput L x (actualState J y u) = valueEstimate J L x u y ∧
    gradientOutput (actualState J y u) = gradientEstimate J u y ∧
    hessianOutput L (actualState J y u) = schurAt J L u y := by
  refine ⟨rfl, ?_, rfl⟩
  change -(gradient J (JointSliceRegularity.point u y)).snd =
    -gradient (JointSliceRegularity.curry J u) y
  rw [JointSliceRegularity.gradient_y_slice_eq_projection J hJ]

/-- The algorithm itself only sees oracle answers. This theorem proves its actual errors,
observable certificate and exact query budget against the original second-order oracle. -/
theorem reduced_dual_oracle_simulation
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) (e : ℝ) (he : 0 < e) :
    let run := execute (actualOracle J) (simulator L x y u0 e)
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    ‖answerResidual L x run.1‖ ≤ L * e ∧
    ‖run.1.u - primal J L x y‖ ≤ e ∧
    |valueOutput L x run.1 - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
    ‖gradientOutput run.1 - gradient (psi J L x) y‖ ≤ L * e ∧
    ‖hessianOutput L run.1 - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e ∧
    (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  rw [simulator_actual_execution]
  dsimp only
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hout := actual_state_outputs J hJ L x
    (iterate J L x y u0 (logBudget (‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L) e)) y
  rw [hout.1, hout.2.1, hout.2.2]
  simpa only [Nat.cast_add, Nat.cast_one, answerResidual, actualState, actualOracle,
    OriginalPrimalElimination.residual] using
    observed_initial_residual_simulation J L ρ hL hρ hC2 hLip hHess x u0 y e he


theorem arbitrary_accuracy_simulation
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) (δ : ℝ) (hδ : 0 < δ) :
    let e := min 1 (δ / (1 + 3 * L + 4 * ρ))
    let run := execute (actualOracle J) (simulator L x y u0 e)
    let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
    0 < e ∧
    |valueOutput L x run.1 - psi J L x y| ≤ δ ∧
    ‖gradientOutput run.1 - gradient (psi J L x) y‖ ≤ δ ∧
    ‖hessianOutput L run.1 - fderiv ℝ (gradient (psi J L x)) y‖ ≤ δ ∧
    (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 3 * D / e) := by
  let c := 1 + 3 * L + 4 * ρ
  let e := min 1 (δ / c)
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := lt_min (by norm_num) (div_pos hδ hc)
  have he1 : e ≤ 1 := min_le_left _ _
  have heδ : e ≤ δ / c := min_le_right _ _
  have hce : c * e ≤ δ := by
    have hh := (le_div_iff₀ hc).mp heδ
    nlinarith only [hh]
  have he2 : e ^ 2 ≤ e := by nlinarith only [he, he1]
  have hv : 3 * L / 2 * e ^ 2 ≤ δ := by
    calc
      _ ≤ 3 * L / 2 * e := mul_le_mul_of_nonneg_left he2 (by positivity)
      _ ≤ c * e := mul_le_mul_of_nonneg_right (by dsimp [c]; linarith only [hL, hρ]) he.le
      _ ≤ δ := hce
  have hg : L * e ≤ δ :=
    (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith only [hL, hρ]) he.le).trans hce
  have hH : 4 * ρ * e ≤ δ :=
    (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith only [hL]) he.le).trans hce
  have hs := reduced_dual_oracle_simulation J L ρ hL hρ hC2 hLip hHess x u0 y e he
  exact ⟨he, hs.2.2.1.trans hv, hs.2.2.2.1.trans hg,
    hs.2.2.2.2.1.trans hH, hs.2.2.2.2.2⟩


theorem dual_oracle_from_standing_joint
    (J : Joint E F → ℝ) (L ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ ρ * ‖z - w‖)
    (x u0 : E) (y : F) :
    (∀ u : E, ∀ e : ℝ, ‖u - primal J L x y‖ ≤ e →
      |valueEstimate J L x u y - psi J L x y| ≤ 3 * L / 2 * e ^ 2 ∧
      ‖gradientEstimate J u y - gradient (psi J L x) y‖ ≤ L * e ∧
      ‖schurAt J L u y - fderiv ℝ (gradient (psi J L x)) y‖ ≤ 4 * ρ * e) ∧
    (∀ δ : ℝ, 0 < δ →
      let e := min 1 (δ / (1 + 3 * L + 4 * ρ))
      let run := execute (actualOracle J) (simulator L x y u0 e)
      let D := ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L
      0 < e ∧
      |valueOutput L x run.1 - psi J L x y| ≤ δ ∧
      ‖gradientOutput run.1 - gradient (psi J L x) y‖ ≤ δ ∧
      ‖hessianOutput L run.1 - fderiv ℝ (gradient (psi J L x)) y‖ ≤ δ ∧
      (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 3 * D / e)) := by
  exact ⟨fun u e he => plug_in_errors_at_tolerance J L ρ hL hρ hC2 hLip hHess x u y e he,
    arbitrary_accuracy_simulation J L ρ hL hρ hC2 hLip hHess x u0 y⟩

end OriginalDualOracleProgram


namespace OriginalDualResidualQueryBound
open OriginalSaddleImplicit
open OriginalPrimalElimination
open OriginalDualOracleGD
open OriginalDualOracleProgram

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def observedRadius (J : Joint E F → ℝ) (L : ℝ) (x u0 : E) (y : F) : ℝ :=
  ‖OriginalPrimalElimination.residual J L x (y, u0)‖ / L

theorem actual_residual_lipschitz_in_dual
    (J : Joint E F → ℝ) (L : ℝ)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) :
    ‖OriginalPrimalElimination.residual J L x (y, u0) - OriginalPrimalElimination.residual J L x (y0, u0)‖ ≤ L * ‖y - y0‖ := by
  have heq : OriginalPrimalElimination.residual J L x (y, u0) - OriginalPrimalElimination.residual J L x (y0, u0) =
      (gradient J (JointSliceRegularity.point u0 y)).fst -
        (gradient J (JointSliceRegularity.point u0 y0)).fst := by
    dsimp [OriginalPrimalElimination.residual]
    abel
  rw [heq]
  calc
    _ ≤ ‖gradient J (JointSliceRegularity.point u0 y) - gradient J (JointSliceRegularity.point u0 y0)‖ :=
      JointSliceRegularity.norm_fst_projection_sub _ _
    _ ≤ L * ‖JointSliceRegularity.point u0 y - JointSliceRegularity.point u0 y0‖ := hLip _ _
    _ = L * ‖y - y0‖ := by rw [JointSliceRegularity.norm_point_sub_same_x]

theorem observed_radius_at_query
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) :
    observedRadius J L x u0 y ≤ observedRadius J L x u0 y0 + ‖y - y0‖ := by
  have hr := actual_residual_lipschitz_in_dual J L hLip x u0 y y0
  have ht := norm_le_norm_sub_add (OriginalPrimalElimination.residual J L x (y, u0)) (OriginalPrimalElimination.residual J L x (y0, u0))
  unfold observedRadius
  apply (div_le_iff₀ hL).mpr
  have hdiv : (‖OriginalPrimalElimination.residual J L x (y0, u0)‖ / L) * L = ‖OriginalPrimalElimination.residual J L x (y0, u0)‖ :=
    div_mul_cancel₀ _ (ne_of_gt hL)
  nlinarith only [hr, ht, hdiv]

theorem observed_radius_difference_bound
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) :
    |observedRadius J L x u0 y - observedRadius J L x u0 y0| ≤ ‖y - y0‖ := by
  have h1 := observed_radius_at_query J L hL hLip x u0 y y0
  have h2 := observed_radius_at_query J L hL hLip x u0 y0 y
  rw [norm_sub_rev y0 y] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

theorem actual_simulator_cost_on_query_ball
    (J : Joint E F → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) (B e : ℝ) (he : 0 < e) (hball : ‖y - y0‖ ≤ B) :
    ((execute (actualOracle J) (simulator L x y u0 e)).2 : ℝ) ≤
      2 + 18 * Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / e) := by
  have hobs : 0 ≤ observedRadius J L x u0 y := by unfold observedRadius; positivity
  have hquery : observedRadius J L x u0 y ≤ observedRadius J L x u0 y0 + B :=
    (observed_radius_at_query J L hL hLip x u0 y y0).trans (add_le_add le_rfl hball)
  have hc := logBudget_query_bound (observedRadius J L x u0 y) e hobs he
  rw [simulator_actual_execution]
  simp only [Nat.cast_add, Nat.cast_one]
  apply hc.trans
  have hpositive : 0 < 1 + 3 * observedRadius J L x u0 y / e := by positivity
  have hlog : Real.log (1 + 3 * observedRadius J L x u0 y / e) ≤
      Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / e) := Real.log_le_log hpositive
    (by have hm := mul_le_mul_of_nonneg_left hquery (by norm_num : (0 : ℝ) ≤ 3)
        have hd := div_le_div_of_nonneg_right hm he.le
        linarith only [hd])
  nlinarith only [hlog]

end OriginalDualResidualQueryBound


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


namespace OriginalCoupledBetaAlgebra

noncomputable def lambda (A b : ℝ) : ℝ := A * b ^ 2 / (1 - b)
noncomputable def weight (A b : ℝ) : ℝ := A * b / (1 - b)

noncomputable def center {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y : E) (b : ℝ) : E := (1 - b) • y + b • x

theorem coupled_weights (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (hb1 : b < 1) :
    0 < lambda A b ∧ 0 < weight A b ∧
    weight A b ^ 2 = lambda A b * (A + weight A b) ∧
    A / (A + weight A b) = 1 - b ∧
    weight A b / (A + weight A b) = b := by
  have hden : 0 < 1 - b := sub_pos.mpr hb1
  have htotal : A + weight A b = A / (1 - b) := by
    dsimp [weight]
    field_simp <;> ring
  refine ⟨by dsimp [lambda]; positivity, by dsimp [weight]; positivity, ?_, ?_, ?_⟩
  · rw [htotal]
    dsimp [lambda, weight]
    field_simp <;> ring
  · rw [htotal]
    field_simp
  · rw [htotal]
    dsimp [weight]
    field_simp

theorem coupled_square_root_formula (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (hb1 : b < 1) :
    weight A b = (lambda A b + Real.sqrt (lambda A b ^ 2 + 4 * lambda A b * A)) / 2 := by
  have hw := coupled_weights A b hA hb hb1
  have hrel : lambda A b = b * weight A b := by dsimp [lambda, weight]; ring
  have htwo : 0 < 2 * weight A b - lambda A b := by
    rw [hrel]
    nlinarith only [hw.2.1, hb1]
  have hs : (2 * weight A b - lambda A b) ^ 2 = lambda A b ^ 2 + 4 * lambda A b * A := by
    nlinarith only [hw.2.2.1]
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_pos htwo]
  ring

theorem coupled_center {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (hb1 : b < 1) (x y : E) :
    (A / (A + weight A b)) • y + (weight A b / (A + weight A b)) • x = center x y b := by
  have hw := coupled_weights A b hA hb hb1
  rw [hw.2.2.2.1, hw.2.2.2.2]
  rfl

theorem zero_weight_first_step {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lam : ℝ) (hlam : 0 < lam) (x y : E) :
    (lam + Real.sqrt (lam ^ 2 + 4 * lam * 0)) / 2 = lam ∧
    (0 / (0 + lam)) • y + (lam / (0 + lam)) • x = x := by
  constructor
  · simp only [mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hlam]
    ring
  · simp [ne_of_gt hlam]

theorem center_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (b c : ℝ) : ‖center x y b - center x y c‖ = |b - c| * ‖x - y‖ := by
  have heq : center x y b - center x y c = (b - c) • (x - y) := by dsimp [center]; module
  rw [heq, norm_smul, Real.norm_eq_abs]

theorem lambda_difference (A b c : ℝ) (hb : b ≠ 1) (hc : c ≠ 1) :
    lambda A b - lambda A c = A * (b - c) * (b + c - b * c) / ((1 - b) * (1 - c)) := by
  have hb' : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hc' : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  dsimp [lambda]
  field_simp <;> ring

theorem lambda_lipschitz_on_compact
    (A t b c : ℝ) (hA : 0 < A) (ht : 0 < t)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |lambda A b - lambda A c| ≤ (2 * A / t ^ 2) * |b - c| := by
  have hb1 : b < 1 := by linarith
  have hc1 : c < 1 := by linarith
  have hden : 0 < (1 - b) * (1 - c) := by positivity
  have hdenlo : t ^ 2 ≤ (1 - b) * (1 - c) := by
    have hh := mul_le_mul (show t ≤ 1 - b by linarith) (show t ≤ 1 - c by linarith)
      ht.le (by linarith : 0 ≤ 1 - b)
    nlinarith only [hh]
  have hf0 : 0 ≤ b + c - b * c := by
    have hh := mul_nonneg hb (by linarith : 0 ≤ 1 - c)
    nlinarith only [hh, hc]
  have hf2 : b + c - b * c ≤ 2 := by
    have hh := mul_nonneg hb hc
    linarith only [hb1, hc1, hh]
  rw [lambda_difference A b c (ne_of_lt hb1) (ne_of_lt hc1), abs_div,
    abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hf0, abs_of_pos hden]
  have hnum : A * |b - c| * (b + c - b * c) ≤ A * |b - c| * 2 :=
    mul_le_mul_of_nonneg_left hf2 (by positivity)
  have hinv : 1 / ((1 - b) * (1 - c)) ≤ 1 / t ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ht) hdenlo
  calc
    _ = (A * |b - c| * (b + c - b * c)) * (1 / ((1 - b) * (1 - c))) := by ring
    _ ≤ (A * |b - c| * 2) * (1 / t ^ 2) :=
      mul_le_mul hnum hinv (by positivity) (by positivity)
    _ = (2 * A / t ^ 2) * |b - c| := by ring

end OriginalCoupledBetaAlgebra


namespace OriginalTaylorProxStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def proxGradient (v : E) (H : E →L[ℝ] E) (M lam : ℝ) (d : E) : E :=
  v + CertifiedATS.sympart H d + (M / 2 * ‖d‖) • d + lam⁻¹ • d

noncomputable def exactStep (v : E) (H : E →L[ℝ] E) (M lam : ℝ) : E :=
  Classical.epsilon (fun d => ∀ w, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w)

theorem model_strongConvex_with_prox
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) (mu + lam⁻¹) (CertifiedATS.model v H M lam) := by
  let K := H + lam⁻¹ • ContinuousLinearMap.id ℝ E
  have hK : ∀ d : E, (mu + lam⁻¹) * ‖d‖ ^ 2 ≤ inner ℝ (K d) d := by
    intro d
    change (mu + lam⁻¹) * ‖d‖ ^ 2 ≤ inner ℝ (H d + lam⁻¹ • d) d
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith only [hcoer d]
  have hlin : ConvexOn ℝ (Set.univ : Set E) (fun d => inner ℝ v d) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul, le_refl]
  have hcub : ConvexOn ℝ (Set.univ : Set E) (fun d => M / 6 * ‖d‖ ^ 3) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ M / 6)
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 3)
  have hq := strongConvexOn_iff_convex.mp (CertifiedATS.quadratic_strongConvex K (mu + lam⁻¹) hK)
  have hh := (hq.add hlin).add hcub
  apply strongConvexOn_iff_convex.mpr
  convert! hh using 1
  funext d
  simp only [Pi.add_apply, CertifiedATS.model, K, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  field_simp <;> ring

theorem exactStep_minimizes
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    ∀ w : E, CertifiedATS.model v H M lam (exactStep v H M lam) ≤ CertifiedATS.model v H M lam w := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun d => (CertifiedATS.model_hasGradientAt v H M lam d).differentiableAt
  obtain ⟨d, hdmin⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    (CertifiedATS.model v H M lam) (mu + lam⁻¹) 0 0 0 0 hm
    (by simpa using model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd (0 : E)
  have hex : ∃ d : E, ∀ w : E, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w :=
    ⟨d, fun w => by simpa [PacketCore.saddleValue] using hdmin w⟩
  exact Classical.epsilon_spec hex

theorem exactStep_first_order
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    proxGradient v H M lam (exactStep v H M lam) = 0 := by
  exact CertifiedATS.model_minimum_first_order v H M lam _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer)

theorem distance_from_scaled_residual
    (v : E) (H : E →L[ℝ] E) (M lam mu sigma : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hres : ‖lam • proxGradient v H M lam d‖ ≤ sigma * ‖d‖) :
    ‖d - exactStep v H M lam‖ ≤ sigma * ‖d‖ := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d
  rw [(CertifiedATS.model_hasGradientAt v H M lam d).gradient] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hlam.le
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hres
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hlam)
  have hnonneg : 0 ≤ lam * mu * ‖d - exactStep v H M lam‖ := by positivity
  change lam * ((mu + lam⁻¹) * ‖d - exactStep v H M lam‖) ≤
    lam * ‖proxGradient v H M lam d‖ at hscaled
  change lam * ‖proxGradient v H M lam d‖ ≤ sigma * ‖d‖ at hres
  have hcoeff : lam * (mu + lam⁻¹) = lam * mu + 1 := by rw [mul_add, hinv]
  rw [← mul_assoc, hcoeff] at hscaled
  nlinarith only [hscaled, hres, hnonneg]

theorem approximate_norm_bracket
    (v : E) (H : E →L[ℝ] E) (M lam mu sigma : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hres : ‖lam • proxGradient v H M lam d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * ‖d‖ ≤ ‖exactStep v H M lam‖ ∧
      ‖exactStep v H M lam‖ ≤ (1 + sigma) * ‖d‖ := by
  have hd := distance_from_scaled_residual v H M lam mu sigma hM hlam hmu hcoer d hres
  have h1 := norm_le_norm_sub_add d (exactStep v H M lam)
  have h2 := norm_le_norm_sub_add (exactStep v H M lam) d
  rw [norm_sub_rev (exactStep v H M lam) d] at h2
  constructor <;> nlinarith only [hd, h1, h2]

theorem exactStep_size_bound
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    (mu + lam⁻¹) * ‖exactStep v H M lam‖ ≤ ‖v‖ := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) (0 : E)
  rw [(CertifiedATS.model_hasGradientAt v H M lam 0).gradient] at hs
  simpa only [zero_sub, norm_neg, map_zero, norm_zero, zero_smul, smul_zero, mul_zero, add_zero] using hs


theorem parameter_stability
    (v v' : E) (H H' : E →L[ℝ] E) (M lam lam' mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hlam' : 0 < lam') (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (hcoer' : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H' d) d) :
    (mu + lam⁻¹) * ‖exactStep v H M lam - exactStep v' H' M lam'‖ ≤
      ‖v - v'‖ + (‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ + |lam⁻¹ - lam'⁻¹|) *
        ‖exactStep v' H' M lam'‖ := by
  let d' := exactStep v' H' M lam'
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d'
  rw [(CertifiedATS.model_hasGradientAt v H M lam d').gradient, norm_sub_rev d'] at hs
  have hz := exactStep_first_order v' H' M lam' mu hM hlam' hmu hcoer'
  have heq : proxGradient v H M lam d' = (v - v') +
      (CertifiedATS.sympart H - CertifiedATS.sympart H') d' + (lam⁻¹ - lam'⁻¹) • d' := by
    have heq0 : proxGradient v H M lam d' - proxGradient v' H' M lam' d' =
        (v - v') + (CertifiedATS.sympart H - CertifiedATS.sympart H') d' +
          (lam⁻¹ - lam'⁻¹) • d' := by
      dsimp [proxGradient]
      simp only [sub_apply, sub_smul]
      abel
    rw [hz, sub_zero] at heq0
    exact heq0
  change (mu + lam⁻¹) * ‖exactStep v H M lam - d'‖ ≤ ‖proxGradient v H M lam d'‖ at hs
  rw [heq] at hs
  have hnorm : ‖(v - v') + (CertifiedATS.sympart H - CertifiedATS.sympart H') d' +
      (lam⁻¹ - lam'⁻¹) • d'‖ ≤
      ‖v - v'‖ + (‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ + |lam⁻¹ - lam'⁻¹|) * ‖d'‖ := by
    calc
      _ ≤ ‖v - v'‖ + ‖(CertifiedATS.sympart H - CertifiedATS.sympart H') d'‖ +
          ‖(lam⁻¹ - lam'⁻¹) • d'‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖v - v'‖ + ‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ * ‖d'‖ +
          |lam⁻¹ - lam'⁻¹| * ‖d'‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact ContinuousLinearMap.le_opNorm (CertifiedATS.sympart H - CertifiedATS.sympart H') d' 
      _ = _ := by ring
  exact hs.trans hnorm

end OriginalTaylorProxStability


namespace OriginalBetaCurveBounds

open OriginalCoupledBetaAlgebra
open OriginalTaylorProxStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem lambda_compact_bounds
    (A s t b : ℝ) (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hsb : s ≤ b) (hbt : b ≤ 1 - t) :
    A * s ^ 2 ≤ lambda A b ∧ lambda A b ≤ A / t := by
  have hb : 0 ≤ b := hs.le.trans hsb
  have hb1 : b < 1 := by linarith
  have hden : 0 < 1 - b := by linarith
  have hsquare : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.le hb).mpr hsb
  have hbSquare : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  constructor
  · apply (le_div_iff₀ hden).mpr
    have h1 := mul_le_mul_of_nonneg_left (show 1 - b ≤ 1 by linarith) (by positivity : 0 ≤ A * s ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hsquare hA.le
    nlinarith only [h1, h2]
  · have hnum : A * b ^ 2 ≤ A := by nlinarith only [mul_le_mul_of_nonneg_left hbSquare hA.le]
    have hinv : 1 / (1 - b) ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith)
    change A * b ^ 2 / (1 - b) ≤ A / t
    calc
      _ = (A * b ^ 2) * (1 / (1 - b)) := by ring
      _ ≤ A * (1 / t) := mul_le_mul hnum hinv (by positivity) hA.le
      _ = A / t := by ring

theorem reciprocal_lipschitz (a b m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |a⁻¹ - b⁻¹| ≤ |a - b| / m ^ 2 := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a]
  have hprod : m ^ 2 ≤ a * b := by nlinarith only [mul_le_mul ha hb hm.le ha0.le]
  have hinv : 1 / (a * b) ≤ 1 / m ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hm) hprod
  calc
    _ = |a - b| * (1 / (a * b)) := by ring
    _ ≤ |a - b| * (1 / m ^ 2) := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
    _ = |a - b| / m ^ 2 := by ring

theorem inverse_lambda_lipschitz_on_compact
    (A s t b c : ℝ) (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hsb : s ≤ b) (hsc : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |(lambda A b)⁻¹ - (lambda A c)⁻¹| ≤
      ((2 * A / t ^ 2) / (A * s ^ 2) ^ 2) * |b - c| := by
  have hb := lambda_compact_bounds A s t b hA hs ht hsb hbt
  have hc := lambda_compact_bounds A s t c hA hs ht hsc hct
  have hdiff := lambda_lipschitz_on_compact A t b c hA ht (hs.le.trans hsb) (hs.le.trans hsc) hbt hct
  calc
    _ ≤ |lambda A b - lambda A c| / (A * s ^ 2) ^ 2 :=
      reciprocal_lipschitz _ _ _ (by positivity) hb.1 hc.1
    _ ≤ ((2 * A / t ^ 2) * |b - c|) / (A * s ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hdiff (by positivity)
    _ = _ := by ring

noncomputable def gradientBound (g : E → ℝ) (Lg : ℝ) (x y : E) : ℝ :=
  ‖gradient g y‖ + Lg * ‖x - y‖

noncomputable def actualStep (g : E → ℝ) (M : ℝ) (z : E) (lam : ℝ) : E :=
  exactStep (gradient g z) (fderiv ℝ (gradient g) z) M lam

noncomputable def betaStep (g : E → ℝ) (M A : ℝ) (x y : E) (b : ℝ) : E :=
  actualStep g M (center x y b) (lambda A b)

noncomputable def betaSize (g : E → ℝ) (M A : ℝ) (x y : E) (b : ℝ) : ℝ :=
  lambda A b * ‖betaStep g M A x y b‖

theorem center_gradient_bound
    (g : E → ℝ) (Lg : ℝ) (hLg : 0 ≤ Lg)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y : E) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖gradient g (center x y b)‖ ≤ gradientBound g Lg x y := by
  have hz : ‖center x y b - y‖ ≤ ‖x - y‖ := by
    have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    nlinarith only [mul_le_mul_of_nonneg_right hb1 (norm_nonneg (x - y))]
  have ht := norm_le_norm_sub_add (gradient g (center x y b)) (gradient g y)
  have hh := (hlip (center x y b) y).trans (mul_le_mul_of_nonneg_left hz hLg)
  dsimp [gradientBound]
  linarith only [ht, hh]

theorem actualStep_uniform_bound
    (g : E → ℝ) (mu Lg M lam : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hC2 : ContDiff ℝ 2 g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y : E) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖actualStep g M (center x y b) lam‖ ≤ gradientBound g Lg x y / mu := by
  have hs := exactStep_size_bound (gradient g (center x y b)) (fderiv ℝ (gradient g) (center x y b))
    M lam mu hM hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc (center x y b))
  have hg := center_gradient_bound g Lg hLg hlip x y b hb hb1
  have hnonneg : 0 ≤ lam⁻¹ * ‖actualStep g M (center x y b) lam‖ := by positivity
  apply (le_div_iff₀ hmu).mpr
  change (mu + lam⁻¹) * ‖actualStep g M (center x y b) lam‖ ≤ _ at hs
  nlinarith only [hs, hg, hnonneg]


noncomputable def inverseLambdaModulus (A s t : ℝ) : ℝ := (2 * A / t ^ 2) / (A * s ^ 2) ^ 2

noncomputable def stepModulus (mu Lg M A s t G D : ℝ) : ℝ :=
  (Lg * D + (M * D + inverseLambdaModulus A s t) * (G / mu)) / mu

noncomputable def sizeModulus (mu Lg M A s t G D : ℝ) : ℝ :=
  (2 * A / t ^ 2) * (G / mu) + (A / t) * stepModulus mu Lg M A s t G D

theorem betaStep_lipschitz
    (g : E → ℝ) (mu Lg M A s t G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (x y : E) (hG : gradientBound g Lg x y ≤ G)
    (b c : ℝ) (hsb : s ≤ b) (hsc' : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
      stepModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by
  have hb0 : 0 ≤ b := hs.le.trans hsb
  have hc0 : 0 ≤ c := hs.le.trans hsc'
  have hb1 : b < 1 := by linarith
  have hc1 : c < 1 := by linarith
  have hblam := (coupled_weights A b hA (hs.trans_le hsb) hb1).1
  have hclam := (coupled_weights A c hA (hs.trans_le hsc') hc1).1
  have hcRadius : ‖betaStep g M A x y c‖ ≤ G / mu :=
    (actualStep_uniform_bound g mu Lg M _ hmu hLg hM hclam hC2 hsc hlip x y c hc0 hc1.le).trans
      (div_le_div_of_nonneg_right hG hmu.le)
  have hraw := parameter_stability (gradient g (center x y b)) (gradient g (center x y c))
    (fderiv ℝ (gradient g) (center x y b)) (fderiv ℝ (gradient g) (center x y c)) M
    (lambda A b) (lambda A c) mu hM hblam hclam hmu.le
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc _)
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc _)
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 _),
    CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 _)] at hraw
  have hz := center_lipschitz x y b c
  have hv : ‖gradient g (center x y b) - gradient g (center x y c)‖ ≤ Lg * ‖x - y‖ * |b - c| := by
    calc
      _ ≤ Lg * ‖center x y b - center x y c‖ := hlip _ _
      _ = _ := by rw [hz]; ring
  have hH : ‖fderiv ℝ (gradient g) (center x y b) - fderiv ℝ (gradient g) (center x y c)‖ ≤
      M * ‖x - y‖ * |b - c| := by
    calc
      _ ≤ M * ‖center x y b - center x y c‖ := hHlip _ _
      _ = _ := by rw [hz]; ring
  have hi := inverse_lambda_lipschitz_on_compact A s t b c hA hs ht hsb hsc' hbt hct
  have hG0 : 0 ≤ G := (by dsimp [gradientBound]; positivity : 0 ≤ gradientBound g Lg x y).trans hG
  have hbound : mu * ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
      (Lg * ‖x - y‖ + (M * ‖x - y‖ + inverseLambdaModulus A s t) * (G / mu)) * |b - c| := by
    have hnonneg : 0 ≤ (lambda A b)⁻¹ * ‖betaStep g M A x y b - betaStep g M A x y c‖ := by positivity
    have h1 : mu * ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
        (mu + (lambda A b)⁻¹) * ‖betaStep g M A x y b - betaStep g M A x y c‖ := by
      nlinarith only [hnonneg]
    refine h1.trans (hraw.trans ?_)
    have hcoef0 : 0 ≤ (M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c| := by
      dsimp [inverseLambdaModulus]
      positivity
    have hsum : ‖fderiv ℝ (gradient g) (center x y b) - fderiv ℝ (gradient g) (center x y c)‖ +
        |(lambda A b)⁻¹ - (lambda A c)⁻¹| ≤
        (M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c| := by
      calc
        _ ≤ M * ‖x - y‖ * |b - c| + ((2 * A / t ^ 2) / (A * s ^ 2) ^ 2) * |b - c| := add_le_add hH hi
        _ = _ := by dsimp [inverseLambdaModulus]; ring
    calc
      _ ≤ (Lg * ‖x - y‖ * |b - c|) +
          ((M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c|) * (G / mu) := by
        exact add_le_add hv (mul_le_mul hsum hcRadius (norm_nonneg _) hcoef0)
      _ = _ := by ring
  calc
    _ ≤ ((Lg * ‖x - y‖ + (M * ‖x - y‖ + inverseLambdaModulus A s t) * (G / mu)) * |b - c|) / mu :=
      (le_div_iff₀ hmu).mpr (by nlinarith only [hbound])
    _ = stepModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by dsimp [stepModulus]; ring

theorem betaSize_lipschitz
    (g : E → ℝ) (mu Lg M A s t G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (x y : E) (hG : gradientBound g Lg x y ≤ G)
    (b c : ℝ) (hsb : s ≤ b) (hsc' : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |betaSize g M A x y b - betaSize g M A x y c| ≤
      sizeModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by
  have hb0 : 0 ≤ b := hs.le.trans hsb
  have hb1 : b < 1 := by linarith
  have hblam := (coupled_weights A b hA (hs.trans_le hsb) hb1).1
  have hclam := (coupled_weights A c hA (hs.trans_le hsc') (by linarith)).1
  have hG0 : 0 ≤ G := (by dsimp [gradientBound]; positivity : 0 ≤ gradientBound g Lg x y).trans hG
  have hRadius : ‖betaStep g M A x y b‖ ≤ G / mu :=
    (actualStep_uniform_bound g mu Lg M _ hmu hLg hM hblam hC2 hsc hlip x y b hb0 hb1.le).trans
      (div_le_div_of_nonneg_right hG hmu.le)
  have hlamDiff := lambda_lipschitz_on_compact A t b c hA ht hb0 (hs.le.trans hsc') hbt hct
  have hlamUpper := (lambda_compact_bounds A s t c hA hs ht hsc' hct).2
  have hStepDiff := betaStep_lipschitz g mu Lg M A s t G hmu hLg hM hA hs ht
    hC2 hsc hlip hHlip x y hG b c hsb hsc' hbt hct
  have hNormDiff := (abs_norm_sub_norm_le (betaStep g M A x y b) (betaStep g M A x y c)).trans hStepDiff
  unfold betaSize
  calc
    _ = |(lambda A b - lambda A c) * ‖betaStep g M A x y b‖ +
        lambda A c * (‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖)| := by congr 1; ring
    _ ≤ |(lambda A b - lambda A c) * ‖betaStep g M A x y b‖| +
        |lambda A c * (‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖)| := abs_add_le _ _
    _ = |lambda A b - lambda A c| * ‖betaStep g M A x y b‖ +
        lambda A c * |‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_pos hclam]
    _ ≤ ((2 * A / t ^ 2) * |b - c|) * (G / mu) +
        (A / t) * (stepModulus mu Lg M A s t G ‖x - y‖ * |b - c|) := by gcongr
    _ = sizeModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by dsimp [sizeModulus]; ring

end OriginalBetaCurveBounds


namespace OriginalBetaATSUniform

noncomputable def uniformStepFloor (mu Lg M lo rho : ℝ) : ℝ :=
  CertifiedATS.stepFloor rho (Lg + mu / 4 + lo⁻¹) M

noncomputable def uniformTolerance (mu Lg M lo up sigma rho : ℝ) : ℝ :=
  min (rho / 8) (min (mu / 4)
    (min (sigma * uniformStepFloor mu Lg M lo rho / (2 * up)) (sigma / (2 * up))))

theorem uniformStepFloor_positive
    (mu Lg M lo rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hrho : 0 < rho) :
    0 < uniformStepFloor mu Lg M lo rho := by
  exact CertifiedATS.stepFloor_positive rho _ M hrho (by positivity) hM

theorem uniformTolerance_positive
    (mu Lg M lo up sigma rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hup : 0 < up) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    0 < uniformTolerance mu Lg M lo up sigma rho := by
  have hell := uniformStepFloor_positive mu Lg M lo rho hmu hLg hM hlo hrho
  unfold uniformTolerance
  positivity

theorem uniformStepFloor_le
    (mu Lg M lo lam rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hrho : 0 < rho) :
    uniformStepFloor mu Lg M lo rho ≤ CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hinv : lam⁻¹ ≤ lo⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlo hlolam
  have hden : 0 < 8 * (Lg + mu / 4 + lam⁻¹ + M / 2) := by positivity
  have hdenle : 8 * (Lg + mu / 4 + lam⁻¹ + M / 2) ≤ 8 * (Lg + mu / 4 + lo⁻¹ + M / 2) := by linarith
  change min 1 (rho / (8 * (Lg + mu / 4 + lo⁻¹ + M / 2))) ≤
    min 1 (rho / (8 * (Lg + mu / 4 + lam⁻¹ + M / 2)))
  exact min_le_min le_rfl (div_le_div_of_nonneg_left hrho.le hden hdenle)

theorem uniformTolerance_le_refinementTolerance
    (mu Lg M lo up lam sigma rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hlamup : lam ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    uniformTolerance mu Lg M lo up sigma rho ≤
      CertifiedATS.refinementTolerance mu Lg M lam sigma rho := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hup : 0 < up := hlam.trans_le hlamup
  have hfloor := uniformStepFloor_le mu Lg M lo lam rho hmu hLg hM hlo hlolam hrho
  have hell : 0 < CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M :=
    CertifiedATS.stepFloor_positive rho _ M hrho (by positivity) hM
  have hterm3 : sigma * uniformStepFloor mu Lg M lo rho / (2 * up) ≤
      sigma * CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M / (2 * lam) := by
    calc
      _ ≤ sigma * CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M / (2 * up) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor hsigma.le) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hterm4 : sigma / (2 * up) ≤ sigma / (2 * lam) :=
    div_le_div_of_nonneg_left hsigma.le (by positivity) (by linarith)
  have h1 : uniformTolerance mu Lg M lo up sigma rho ≤ rho / 8 := min_le_left _ _
  have h2 : uniformTolerance mu Lg M lo up sigma rho ≤ mu / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h3 : uniformTolerance mu Lg M lo up sigma rho ≤ sigma * uniformStepFloor mu Lg M lo rho / (2 * up) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : uniformTolerance mu Lg M lo up sigma rho ≤ sigma / (2 * up) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact le_min h1 (le_min h2 (le_min (h3.trans hterm3) (h4.trans hterm4)))

theorem uniform_geometric_refinement
    (mu Lg M lo up lam sigma rho error0 : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hlamup : lam ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    error0 / (2 : ℝ) ^ CertifiedATS.halvingCount error0
      (uniformTolerance mu Lg M lo up sigma rho) ≤
        CertifiedATS.refinementTolerance mu Lg M lam sigma rho := by
  have hup : 0 < up := (hlo.trans_le hlolam).trans_le hlamup
  have ht := uniformTolerance_positive mu Lg M lo up sigma rho hmu hLg hM hlo hup hsigma hrho
  exact (CertifiedATS.halving_precision error0 _ ht).trans
    (uniformTolerance_le_refinementTolerance mu Lg M lo up lam sigma rho
      hmu hLg hM hlo hlolam hlamup hsigma hrho)

end OriginalBetaATSUniform


namespace OriginalBetaATSTrial

open OriginalTaylorProxStability
open OriginalBetaATSUniform

inductive GetterProgram (Q A R : Type*) where
  | pure (result : R)
  | ask (request : Q) (next : A → GetterProgram Q A R)

noncomputable def execute {Q A R : Type*} (getter : Q → A) : GetterProgram Q A R → R × ℕ
  | .pure r => (r, 0)
  | .ask q next => let r := execute getter (next (getter q)); (r.1, r.2 + 1)

structure Answer (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  grad : E
  hess : E →L[ℝ] E

inductive TrialResult (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | stop (point : E)
  | step (displacement : E) (outputAnswer : Answer E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def trialProgram (M lam delta rho deltaY : ℝ) (z : E) :
    GetterProgram (E × ℝ) (Answer E) (TrialResult E) := by
  classical
  exact .ask (z, delta) (fun a =>
    if ‖a.grad‖ + delta ≤ rho then .pure (.stop z) else
      let d := exactStep a.grad a.hess M lam
      .ask (z + d, deltaY) (fun aY =>
        if ‖aY.grad‖ + deltaY ≤ rho then .pure (.stop (z + d)) else .pure (.step d aY)))

noncomputable def trial (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) : TrialResult E :=
  (execute getter (trialProgram M lam delta rho deltaY z)).1

def TrialSpec (g : E → ℝ) (M lam sigma rho deltaY : ℝ) (z : E) : TrialResult E → Prop
  | .stop w => ‖gradient g w‖ ≤ rho
  | .step d aY =>
      ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (z + d)‖ ≤ deltaY ∧ rho / 2 < ‖gradient g (z + d)‖

theorem exactStep_unique
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hmin : ∀ w : E, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w) :
    d = exactStep v H M lam := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d
  rw [PacketCore.gradient_eq_zero_at_global_min _ _ hmin, norm_zero] at hs
  have hn : ‖d - exactStep v H M lam‖ ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [mul_zero] using hs
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

theorem selected_approximate_step_accepts
    (g : E → ℝ) (mu Lg M lam sigma rho delta : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (z v : E) (H : E →L[ℝ] E)
    (hgerr : ‖v - gradient g z‖ ≤ delta) (hHerr : ‖H - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hsmall : delta ≤ CertifiedATS.refinementTolerance mu Lg M lam sigma rho)
    (haway : rho / 2 ≤ ‖gradient g z‖) :
    ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M (exactStep v H M lam) +
      exactStep v H M lam‖ ≤ sigma * ‖exactStep v H M lam‖ := by
  obtain ⟨d, hmin, hfloor, hcert, hATS⟩ := CertifiedATS.model_acceptance_at_accuracy g hC2
    mu Lg M lam sigma rho hmu hLg hM hlam hsigma hrho hsc hlip z v H delta hgerr hHerr hsmall haway
  have hdmu : delta ≤ mu / 4 := hsmall.trans (CertifiedATS.refinementTolerance_bounds mu Lg M lam sigma rho).2.1
  have hcoer : ∀ w : E, (3 * mu / 4) * ‖w‖ ^ 2 ≤ inner ℝ (H w) w := by
    intro w
    simpa only [CertifiedATS.sympart_same_quadratic] using
      CertifiedATS.approximate_hessian_coercive g hC2 mu hsc z H delta hHerr hdmu w
  have heq := exactStep_unique v H M lam (3 * mu / 4) hM hlam (by positivity) hcoer d hmin
  rwa [heq] at hATS

theorem trial_getter_calls
    (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) :
    (execute getter (trialProgram M lam delta rho deltaY z)).2 ≤ 2 := by
  classical
  by_cases hc : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simp [trialProgram, execute, hc]
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    by_cases ho : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · dsimp only [d] at ho
      simp [trialProgram, execute, hc, d, ho]
    · dsimp only [d] at ho
      simp [trialProgram, execute, hc, d, ho]

theorem trial_spec_at_accuracy
    (g : E → ℝ) (mu Lg M lam sigma rho delta deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) (hsmall : delta ≤ CertifiedATS.refinementTolerance mu Lg M lam sigma rho) :
    TrialSpec g M lam sigma rho deltaY z (trial getter M lam delta rho deltaY z) := by
  classical
  have herr := hgetter z delta hdelta
  have hdeltaSmall := hsmall.trans (CertifiedATS.refinementTolerance_bounds mu Lg M lam sigma rho).1
  by_cases hcenter : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simpa only [trial, trialProgram, execute, if_pos hcenter, TrialSpec] using
      CertifiedATS.center_stop_certifies _ _ delta rho herr.1 hcenter
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    have herrY := (hgetter (z + d) deltaY hdeltaY).1
    by_cases hout : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · dsimp only [d] at hout
      simpa only [trial, trialProgram, execute, d, if_neg hcenter, if_pos hout, TrialSpec] using
        CertifiedATS.center_stop_certifies _ _ deltaY rho herrY hout
    · dsimp only [d] at hout
      have hcenterAway : rho / 2 ≤ ‖gradient g z‖ := by
        have hn := norm_le_norm_sub_add (getter (z, delta)).grad (gradient g z)
        have hnot : rho < ‖(getter (z, delta)).grad‖ + delta := lt_of_not_ge hcenter
        linarith only [hn, herr.1, hdeltaSmall, hnot, hrho]
      have hATS := selected_approximate_step_accepts g mu Lg M lam sigma rho delta
        hmu hLg hM hlam hsigma hrho hC2 hsc hlip z _ _ herr.1 herr.2 hsmall hcenterAway
      have hawayY : rho / 2 < ‖gradient g (z + d)‖ := by
        have hn := norm_le_norm_sub_add (getter (z + d, deltaY)).grad (gradient g (z + d))
        have hnot : rho < ‖(getter (z + d, deltaY)).grad‖ + deltaY := lt_of_not_ge hout
        linarith only [hn, herrY, hdeltaYsmall, hnot, hrho]
      have hs : TrialSpec g M lam sigma rho deltaY z (.step d (getter (z + d, deltaY))) :=
        ⟨hATS, herrY, hawayY⟩
      simpa only [trial, trialProgram, execute, d, if_neg hcenter, if_neg hout] using hs

theorem trial_uniform_spec
    (g : E → ℝ) (mu Lg M lo up lam sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlo : 0 < lo)
    (hlolam : lo ≤ lam) (hlamup : lam ≤ up) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) :
    TrialSpec g M lam sigma rho deltaY z
      (trial getter M lam (uniformTolerance mu Lg M lo up sigma rho) rho deltaY z) := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hup : 0 < up := hlam.trans_le hlamup
  exact trial_spec_at_accuracy g mu Lg M lam sigma rho _ deltaY
    hmu hLg hM hlam hsigma hrho
    (uniformTolerance_positive mu Lg M lo up sigma rho hmu hLg hM hlo hup hsigma hrho)
    hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter z
    (uniformTolerance_le_refinementTolerance mu Lg M lo up lam sigma rho hmu hLg hM hlo hlolam hlamup hsigma hrho)

end OriginalBetaATSTrial


namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_differentiable (F : E → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : gradient F = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) := rfl
  rw [heq]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder).differentiable (by norm_num)


theorem scalarization_hasGradientAt (T : E → E) (hdiff : Differentiable ℝ T) (w x : E) :
    HasGradientAt (fun u : E => inner ℝ w (T u)) ((fderiv ℝ T x).adjoint w) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (InnerProductSpace.toDual ℝ E w).hasFDerivAt.comp x (hdiff x).hasFDerivAt
  convert! hh using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem scalarization_gradient_lipschitz (T : E → E) (hdiff : Differentiable ℝ T)
    (M : ℝ) (hT : ∀ x y : E, ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * ‖x - y‖)
    (w x y : E) :
    ‖gradient (fun u : E => inner ℝ w (T u)) x - gradient (fun u : E => inner ℝ w (T u)) y‖ ≤
      (M * ‖w‖) * ‖x - y‖ := by
  rw [(scalarization_hasGradientAt T hdiff w x).gradient,
    (scalarization_hasGradientAt T hdiff w y).gradient]
  have he : (fderiv ℝ T x).adjoint w - (fderiv ℝ T y).adjoint w =
      (fderiv ℝ T x - fderiv ℝ T y).adjoint w := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [he]
  have hn := ContinuousLinearMap.le_opNorm (fderiv ℝ T x - fderiv ℝ T y).adjoint w
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  have hm := mul_le_mul_of_nonneg_right (hT x y) (norm_nonneg w)
  nlinarith only [hn, hm]

theorem vector_taylor_remainder (T : E → E) (hdiff : Differentiable ℝ T)
    (M : ℝ) (hM : 0 < M)
    (hT : ∀ x y : E, ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖T (z + d) - T z - fderiv ℝ T z d‖ ≤ M / 2 * ‖d‖ ^ 2 := by
  let R := T (z + d) - T z - fderiv ℝ T z d
  by_cases hz : R = 0
  · change ‖R‖ ≤ M / 2 * ‖d‖ ^ 2
    rw [hz, norm_zero]
    positivity
  · have hR : 0 < ‖R‖ := norm_pos_iff.mpr hz
    let p : E → ℝ := fun u => inner ℝ R (T u)
    have hp : Differentiable ℝ p := fun u => (scalarization_hasGradientAt T hdiff R u).differentiableAt
    have hupper := OriginalAudit.smooth_descent_upper p (M * ‖R‖) (by positivity) hp
      (scalarization_gradient_lipschitz T hdiff M hT R) z d
    have hgrad : gradient p z = (fderiv ℝ T z).adjoint R :=
      (scalarization_hasGradientAt T hdiff R z).gradient
    rw [hgrad, ContinuousLinearMap.adjoint_inner_left] at hupper
    have hi : inner ℝ R (T (z + d)) - inner ℝ R (T z) - inner ℝ R (fderiv ℝ T z d) = ‖R‖ ^ 2 := by
      rw [← inner_sub_right, ← inner_sub_right]
      exact real_inner_self_eq_norm_sq R
    dsimp only [p] at hupper
    have hsq : ‖R‖ * ‖R‖ ≤ ‖R‖ * (M / 2 * ‖d‖ ^ 2) := by
      nlinarith only [hupper, hi]
    change ‖R‖ ≤ M / 2 * ‖d‖ ^ 2
    exact (mul_le_mul_iff_right₀ hR).mp (by nlinarith only [hsq])

theorem gradient_taylor_remainder (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d‖ ≤
      M / 2 * ‖d‖ ^ 2 :=
  vector_taylor_remainder (gradient g) (gradient_differentiable g hC2) M hM hH z d

end RobustAHPE

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def trueModelVector (g : E → ℝ) (z : E) (Mbar : ℝ) (d : E) : E :=
  gradient g z + fderiv ℝ (gradient g) z d + (Mbar / 2 * ‖d‖) • d

theorem gradient_minus_modelVector_bound (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M Mbar : ℝ) (hM : 0 < M) (hMbar : 0 ≤ Mbar)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖gradient g (z + d) - trueModelVector g z Mbar d‖ ≤
      (M + Mbar) / 2 * ‖d‖ ^ 2 := by
  have ht := gradient_taylor_remainder g hC2 M hM hH z d
  have he : gradient g (z + d) - trueModelVector g z Mbar d =
      (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) - (Mbar / 2 * ‖d‖) • d := by
    dsimp only [trueModelVector]
    abel
  rw [he]
  have hn : ‖(Mbar / 2 * ‖d‖) • d‖ = (Mbar / 2) * ‖d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have htri := norm_sub_le
    (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) ((Mbar / 2 * ‖d‖) • d)
  rw [hn] at htri
  nlinarith only [ht, htri]

theorem true_gradient_residual_from_ATS (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖lam • gradient g (z + d) + d‖ ≤ (sigmaHat + sigmaU) * ‖d‖ := by
  have hm := gradient_minus_modelVector_bound g hC2 M M hM hM.le hH z d
  have he : lam • gradient g (z + d) + d =
      (lam • trueModelVector g z M d + d) + lam • (gradient g (z + d) - trueModelVector g z M d) := by
    module
  rw [he]
  have htri := norm_add_le (lam • trueModelVector g z M d + d)
    (lam • (gradient g (z + d) - trueModelVector g z M d))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at htri
  have hmul := mul_le_mul_of_nonneg_left hm hlam.le
  have hw := (le_div_iff₀ hM).mp hwindow
  have hwmul := mul_le_mul_of_nonneg_right hw (norm_nonneg d)
  nlinarith only [htri, hATS, hmul, hwmul]

theorem new_gradient_bound_from_ATS (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * ‖d‖ / lam := by
  have hr := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindow
  have ht := norm_sub_le (lam • gradient g (z + d) + d) d
  have he : (lam • gradient g (z + d) + d) - d = lam • gradient g (z + d) := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
  apply (le_div_iff₀ hlam).mpr
  nlinarith only [ht, hr]

theorem large_lambda_gradient_endpoint (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaU : 0 ≤ sigmaU)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * sigmaU / (M * lam ^ 2) := by
  have hg := new_gradient_bound_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindow
  have hw : ‖d‖ ≤ sigmaU / (M * lam) := by
    apply (le_div_iff₀ (mul_pos hM hlam)).mpr
    have hh := (le_div_iff₀ hM).mp hwindow
    nlinarith only [hh]
  calc
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * ‖d‖ / lam := hg
    _ ≤ (1 + sigmaHat + sigmaU) * (sigmaU / (M * lam)) / lam := by gcongr
    _ = (1 + sigmaHat + sigmaU) * sigmaU / (M * lam ^ 2) := by field_simp <;> ring

end RobustAHPE


namespace OriginalBetaSearchEndpoints

open OriginalCoupledBetaAlgebra
open OriginalTaylorProxStability
open OriginalBetaCurveBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_upper_from_certificate
    (g : E → ℝ) (Lg : ℝ) (x y v : E) (delta : ℝ)
    (herr : ‖v - gradient g y‖ ≤ delta) :
    gradientBound g Lg x y ≤ ‖v‖ + delta + Lg * ‖x - y‖ := by
  have hn := norm_le_norm_sub_add (gradient g y) v
  rw [norm_sub_rev (gradient g y) v] at hn
  dsimp [gradientBound]
  linarith only [hn, herr]

theorem actual_scaled_residual
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (M lam : ℝ) (hlam : 0 < lam) (z d : E) :
    lam • proxGradient (gradient g z) (fderiv ℝ (gradient g) z) M lam d =
      lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d := by
  dsimp [proxGradient, CertifiedATS.trueVector]
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 z)]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]

theorem actual_approximate_norm_bracket
    (g : E → ℝ) (mu M lam sigma : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * (lam * ‖d‖) ≤ lam * ‖actualStep g M z lam‖ ∧
      lam * ‖actualStep g M z lam‖ ≤ (1 + sigma) * (lam * ‖d‖) := by
  have hr : ‖lam • proxGradient (gradient g z) (fderiv ℝ (gradient g) z) M lam d‖ ≤ sigma * ‖d‖ := by
    rw [actual_scaled_residual g hC2 M lam hlam z d]
    exact hATS
  have hn := approximate_norm_bracket (gradient g z) (fderiv ℝ (gradient g) z) M lam mu sigma
    hM hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z) d hr
  change (1 - sigma) * ‖d‖ ≤ ‖actualStep g M z lam‖ ∧
    ‖actualStep g M z lam‖ ≤ (1 + sigma) * ‖d‖ at hn
  constructor
  · have hh := mul_le_mul_of_nonneg_left hn.1 hlam.le
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left hn.2 hlam.le
    nlinarith only [hh]

theorem exact_step_lambda_bound
    (g : E → ℝ) (mu M lam G : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (hG : ‖gradient g z‖ ≤ G) : ‖actualStep g M z lam‖ ≤ lam * G := by
  have hh := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) M lam mu hM hlam hmu.le
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hm := mul_le_mul_of_nonneg_left (hh.trans hG) hlam.le
  have hinv : lam * (mu + lam⁻¹) = lam * mu + 1 := by
    rw [mul_add, mul_inv_cancel₀ (ne_of_gt hlam)]
  change lam * ((mu + lam⁻¹) * ‖actualStep g M z lam‖) ≤ lam * G at hm
  rw [← mul_assoc, hinv] at hm
  have hn : 0 ≤ lam * mu * ‖actualStep g M z lam‖ := by positivity
  nlinarith only [hm, hn]

theorem approximate_small_lambda_bound
    (g : E → ℝ) (mu M lam sigma G : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * (lam * ‖d‖) ≤ lam ^ 2 * G := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM hlam hC2 hsc z d hATS).1
  have hs := exact_step_lambda_bound g mu M lam G hmu hM hlam hC2 hsc z hG
  have hm := mul_le_mul_of_nonneg_left hs hlam.le
  nlinarith only [hb, hm]

noncomputable def lambdaLow (M sigmaLow sigma G : ℝ) : ℝ :=
  min 1 (sigmaLow * (1 - sigma) / (2 * M * (1 + G)))

noncomputable def lambdaHigh (M rho sigma sigmaUp : ℝ) : ℝ :=
  1 + 2 * ((1 + sigma + sigmaUp) * sigmaUp) / (M * rho)

noncomputable def betaLow (A ell : ℝ) : ℝ := min (1 / 4) (ell / (4 * (1 + A)))
noncomputable def highMargin (A H : ℝ) : ℝ := min (1 / 4) (A / (8 * (1 + H)))
noncomputable def betaHigh (A H : ℝ) : ℝ := 1 - highMargin A H

theorem lambdaLow_positive
    (M sigmaLow sigma G : ℝ) (hM : 0 < M) (hLow : 0 < sigmaLow) (hsigma : sigma < 1) (hG : 0 ≤ G) :
    0 < lambdaLow M sigmaLow sigma G ∧ lambdaLow M sigmaLow sigma G ≤ 1 := by
  exact ⟨lt_min zero_lt_one (by positivity), min_le_left _ _⟩

theorem betaLow_properties
    (A ell : ℝ) (hA : 0 < A) (hell : 0 < ell) :
    0 < betaLow A ell ∧ betaLow A ell ≤ 1 / 4 ∧ lambda A (betaLow A ell) ≤ ell := by
  let b := betaLow A ell
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb4 : b ≤ 1 / 4 := min_le_left _ _
  have hbell : b ≤ ell / (4 * (1 + A)) := min_le_right _ _
  have hden : 0 < 1 - b := by linarith
  have hinv : 1 / (1 - b) ≤ 2 := by apply (div_le_iff₀ hden).mpr; linarith
  have hb2 : b ^ 2 ≤ b := by nlinarith only [hb, hb4]
  refine ⟨hb, hb4, ?_⟩
  change A * b ^ 2 / (1 - b) ≤ ell
  calc
    _ = (A * b ^ 2) * (1 / (1 - b)) := by ring
    _ ≤ (A * b) * 2 := mul_le_mul (mul_le_mul_of_nonneg_left hb2 hA.le) hinv (by positivity) (by positivity)
    _ ≤ (A * (ell / (4 * (1 + A)))) * 2 := by gcongr
    _ ≤ ell := by
      have heq : (A * (ell / (4 * (1 + A)))) * 2 = (2 * A * ell) / (4 * (1 + A)) := by ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + A))).mpr
      nlinarith only [hA, hell]

theorem betaHigh_properties
    (A H : ℝ) (hA : 0 < A) (hH : 0 ≤ H) :
    0 < highMargin A H ∧ highMargin A H ≤ 1 / 4 ∧
    3 / 4 ≤ betaHigh A H ∧ betaHigh A H < 1 ∧ H ≤ lambda A (betaHigh A H) := by
  let t := highMargin A H
  let b := betaHigh A H
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht4 : t ≤ 1 / 4 := min_le_left _ _
  have htA : t ≤ A / (8 * (1 + H)) := min_le_right _ _
  have hb : 3 / 4 ≤ b := by dsimp [b, betaHigh]; linarith only [ht4]
  have hb1 : b < 1 := by dsimp [b, betaHigh]; linarith only [ht]
  refine ⟨ht, ht4, hb, hb1, ?_⟩
  have hb2 : (1 / 4 : ℝ) ≤ b ^ 2 := by nlinarith only [hb]
  have hAprod := (le_div_iff₀ (by positivity : 0 < 8 * (1 + H))).mp htA
  have hlow : H ≤ (A / 4) / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith only [hAprod, ht, hH]
  have hquad := mul_le_mul_of_nonneg_left hb2 hA.le
  have heq : 1 - b = t := by dsimp [b, betaHigh, t]; ring
  change H ≤ A * b ^ 2 / (1 - b)
  rw [heq]
  exact hlow.trans (div_le_div_of_nonneg_right (by nlinarith only [hquad]) ht.le)


theorem low_endpoint_is_low
    (g : E → ℝ) (mu Lg M A sigmaLow sigma G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 < M) (hA : 0 < A)
    (hLow : 0 < sigmaLow) (hsigma : sigma < 1) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y d : E) (hG : gradientBound g Lg x y ≤ G)
    (hATS : let b := betaLow A (lambdaLow M sigmaLow sigma G)
      ‖lambda A b • CertifiedATS.trueVector (gradient g (center x y b))
        (fderiv ℝ (gradient g) (center x y b)) M d + d‖ ≤ sigma * ‖d‖) :
    lambda A (betaLow A (lambdaLow M sigmaLow sigma G)) * ‖d‖ < sigmaLow / M := by
  let ell := lambdaLow M sigmaLow sigma G
  let b := betaLow A ell
  let lam := lambda A b
  have hell := lambdaLow_positive M sigmaLow sigma G hM hLow hsigma hG0
  have hb := betaLow_properties A ell hA hell.1
  have hb1 : b < 1 := by linarith only [hb.2.1]
  have hlam : 0 < lam := (coupled_weights A b hA hb.1 hb1).1
  have hlamEll : lam ≤ ell := hb.2.2
  have hlamOne : lam ≤ 1 := hlamEll.trans hell.2
  have hprod := mul_nonneg hlam.le (sub_nonneg.mpr hlamOne)
  have hsq : lam ^ 2 ≤ ell := by nlinarith only [hprod, hlamEll]
  have hgrad : ‖gradient g (center x y b)‖ ≤ G :=
    (center_gradient_bound g Lg hLg hlip x y b hb.1.le hb1.le).trans hG
  have hsmall := approximate_small_lambda_bound g mu M lam sigma G hmu hM.le hlam hC2 hsc
    (center x y b) d hgrad hATS
  have hratio : ell ≤ sigmaLow * (1 - sigma) / (2 * M * (1 + G)) := min_le_right _ _
  have hr := (le_div_iff₀ (by positivity : 0 < 2 * M * (1 + G))).mp hratio
  have hellG : ell * G ≤ sigmaLow * (1 - sigma) / (2 * M) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * M)).mpr
    have hn : 0 ≤ 2 * M * ell := mul_nonneg (by positivity) hell.1.le
    nlinarith only [hr, hn]
  have hscale : (1 - sigma) * (lam * ‖d‖) ≤ (1 - sigma) * (sigmaLow / (2 * M)) := by
    calc
      _ ≤ lam ^ 2 * G := hsmall
      _ ≤ ell * G := mul_le_mul_of_nonneg_right hsq hG0
      _ ≤ sigmaLow * (1 - sigma) / (2 * M) := hellG
      _ = _ := by ring
  have hs : lam * ‖d‖ ≤ sigmaLow / (2 * M) :=
    (mul_le_mul_iff_right₀ (show 0 < 1 - sigma by linarith)).mp hscale
  have hhalf : sigmaLow / (2 * M) < sigmaLow / M := by
    have hp : 0 < sigmaLow / M := div_pos hLow hM
    have heq : sigmaLow / (2 * M) = (sigmaLow / M) / 2 := by ring
    rw [heq]
    linarith only [hp]
  exact hs.trans_lt hhalf

theorem large_lambda_upper_is_small
    (g : E → ℝ) (M rho sigma sigmaUp lam : ℝ)
    (hM : 0 < M) (hrho : 0 < rho) (hsigma : 0 ≤ sigma) (hUp : 0 ≤ sigmaUp)
    (hlam : 0 < lam) (hlarge : lambdaHigh M rho sigma sigmaUp ≤ lam)
    (hC2 : ContDiff ℝ 2 g)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaUp / M) : ‖gradient g (z + d)‖ ≤ rho / 2 := by
  let C := (1 + sigma + sigmaUp) * sigmaUp
  let q := 2 * C / (M * rho)
  have hq : 0 ≤ q := by dsimp [q, C]; positivity
  have hlarge' : 1 + q ≤ lam := hlarge
  have hsquare : q ≤ lam ^ 2 := by nlinarith only [hlarge', hq, sq_nonneg q]
  have hmul := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ M * rho)
  have heq : (M * rho) * q = 2 * C := by dsimp [q]; field_simp
  rw [heq] at hmul
  have hfinal : C / (M * lam ^ 2) ≤ rho / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < M * lam ^ 2)).mpr
    nlinarith only [hmul]
  have hb := RobustAHPE.large_lambda_gradient_endpoint g hC2 M lam sigma sigmaUp
    hM hlam hsigma hUp hHlip z d hATS hwindow
  exact hb.trans hfinal

theorem low_failure_exact_threshold
    (g : E → ℝ) (mu M lam sigma sigmaLow : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : 0 ≤ sigma)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hlow : lam * ‖d‖ < sigmaLow / M) :
    lam * ‖actualStep g M z lam‖ ≤ sigmaLow * (1 + sigma) / M := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).2
  have hm := mul_le_mul_of_nonneg_left hlow.le (by positivity : 0 ≤ 1 + sigma)
  have heq : (1 + sigma) * (sigmaLow / M) = sigmaLow * (1 + sigma) / M := by ring
  exact hb.trans (by simpa only [heq] using hm)

theorem high_failure_exact_threshold
    (g : E → ℝ) (mu M lam sigma sigmaUp : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : sigma < 1)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hhigh : sigmaUp / M < lam * ‖d‖) :
    sigmaUp * (1 - sigma) / M ≤ lam * ‖actualStep g M z lam‖ := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).1
  have hm := mul_le_mul_of_nonneg_left hhigh.le (show 0 ≤ 1 - sigma by linarith)
  have heq : (1 - sigma) * (sigmaUp / M) = sigmaUp * (1 - sigma) / M := by ring
  have hm' : sigmaUp * (1 - sigma) / M ≤ (1 - sigma) * (lam * ‖d‖) := by
    simpa only [heq] using hm
  exact hm'.trans hb

end OriginalBetaSearchEndpoints


namespace FangqingHysteresis

inductive Decision (R : Type*) where
  | accept (value : R)
  | low
  | high

inductive Outcome (R : Type*) where
  | found (value : R)
  | bracket (left right : ℝ)

inductive Program (Reply Result : Type*) where
  | pure (value : Result)
  | ask (point : ℝ) (next : Reply → Program Reply Result)

noncomputable def execute {Reply Result : Type*} (oracle : ℝ → Reply) :
    Program Reply Result → Result × ℕ
  | .pure value => (value, 0)
  | .ask x next => let r := execute oracle (next (oracle x)); (r.1, r.2 + 1)

noncomputable def bisect {R : Type*} : ℕ → ℝ → ℝ → Program (Decision R) (Outcome R)
  | 0, l, r => .pure (.bracket l r)
  | n + 1, l, r =>
      let m := (l + r) / 2
      .ask m (fun answer => match answer with
        | .accept value => .pure (.found value)
        | .low => bisect n m r
        | .high => bisect n l m)

def Bracket (F : ℝ → ℝ) (a b L U l r : ℝ) : Prop :=
  L ≤ l ∧ l ≤ r ∧ r ≤ U ∧ F l ≤ a ∧ b ≤ F r

def Spec {R : Type*} (F : ℝ → ℝ) (P : R → Prop) (a b L U : ℝ)
    (fuel : ℕ) (l r : ℝ) : Outcome R → Prop
  | .found value => P value
  | .bracket l' r' => Bracket F a b L U l' r' ∧ r' - l' = (r - l) / (2 : ℝ) ^ fuel

theorem execution_calls_le_fuel {R : Type*} (trial : ℝ → Decision R)
    (fuel : ℕ) (l r : ℝ) : (execute trial (bisect fuel l r)).2 ≤ fuel := by
  induction fuel generalizing l r with
  | zero => simp [bisect, execute]
  | succ n ih =>
    cases htrial : trial ((l + r) / 2) with
    | accept value => simp [bisect, execute, htrial]
    | low =>
      simpa only [bisect, execute, htrial] using Nat.add_le_add_right (ih ((l + r) / 2) r) 1
    | high =>
      simpa only [bisect, execute, htrial] using Nat.add_le_add_right (ih l ((l + r) / 2)) 1

theorem run_spec {R : Type*} (trial : ℝ → Decision R) (F : ℝ → ℝ) (P : R → Prop)
    (a b L U : ℝ)
    (haccept : ∀ x ∈ Set.Icc L U, ∀ value, trial x = .accept value → P value)
    (hlow : ∀ x ∈ Set.Icc L U, trial x = .low → F x ≤ a)
    (hhigh : ∀ x ∈ Set.Icc L U, trial x = .high → b ≤ F x)
    (fuel : ℕ) (l r : ℝ) (hbracket : Bracket F a b L U l r) :
    Spec F P a b L U fuel l r (execute trial (bisect fuel l r)).1 := by
  induction fuel generalizing l r with
  | zero =>
    simp only [bisect, execute, Spec, pow_zero, div_one]
    exact ⟨hbracket, True.intro⟩
  | succ n ih =>
    rcases hbracket with ⟨hl, hlr, hr, hFl, hFr⟩
    let m := (l + r) / 2
    have hm : m ∈ Set.Icc L U := ⟨by dsimp only [m]; linarith, by dsimp only [m]; linarith⟩
    cases htrial : trial ((l + r) / 2) with
    | accept value =>
      simp only [bisect, execute, htrial, Spec]
      exact haccept m hm value htrial
    | low =>
      have hnew : Bracket F a b L U m r :=
        ⟨hm.1, by dsimp only [m]; linarith, hr, hlow m hm htrial, hFr⟩
      have hi := ih m r hnew
      simp only [bisect, execute, htrial]
      cases hres : (execute trial (bisect n m r)).1 with
      | found value => simpa only [hres, Spec] using hi
      | bracket l' r' =>
        simp only [hres, Spec] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [hi.2]
        dsimp only [m]
        rw [pow_succ]
        field_simp
        <;> ring
    | high =>
      have hnew : Bracket F a b L U l m :=
        ⟨hl, by dsimp only [m]; linarith, hm.2, hFl, hhigh m hm htrial⟩
      have hi := ih l m hnew
      simp only [bisect, execute, htrial]
      cases hres : (execute trial (bisect n l m)).1 with
      | found value => simpa only [hres, Spec] using hi
      | bracket l' r' =>
        simp only [hres, Spec] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [hi.2]
        dsimp only [m]
        rw [pow_succ]
        field_simp
        <;> ring

noncomputable def halvingCount (a tau : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 1 (a / tau)))

theorem halving_precision (a tau : ℝ) (htau : 0 < tau) :
    a / (2 : ℝ) ^ halvingCount a tau ≤ tau := by
  have hm : 0 < max 1 (a / tau) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : Real.logb 2 (max 1 (a / tau)) ≤ (halvingCount a tau : ℝ) := Nat.le_ceil _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hm,
    Real.rpow_natCast] at hp
  have hh := le_trans (le_max_right 1 (a / tau)) hp
  have hmul := (div_le_iff₀ htau).mp hh
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith only [hmul]

noncomputable def searchFuel (K L U a b : ℝ) : ℕ :=
  halvingCount (K * (U - L)) ((b - a) / 2)

theorem bisection_success_and_calls {R : Type*}
    (trial : ℝ → Decision R) (F : ℝ → ℝ) (P : R → Prop)
    (a b L U K : ℝ) (hgap : a < b) (hK : 0 ≤ K)
    (hLU : L ≤ U) (hL : F L ≤ a) (hU : b ≤ F U)
    (hLip : ∀ x ∈ Set.Icc L U, ∀ y ∈ Set.Icc L U, |F x - F y| ≤ K * |x - y|)
    (haccept : ∀ x ∈ Set.Icc L U, ∀ value, trial x = .accept value → P value)
    (hlow : ∀ x ∈ Set.Icc L U, trial x = .low → F x ≤ a)
    (hhigh : ∀ x ∈ Set.Icc L U, trial x = .high → b ≤ F x) :
    ∃ value : R,
      (execute trial (bisect (searchFuel K L U a b) L U)).1 = .found value ∧ P value ∧
      (execute trial (bisect (searchFuel K L U a b) L U)).2 ≤ searchFuel K L U a b := by
  let n := searchFuel K L U a b
  have hspec := run_spec trial F P a b L U haccept hlow hhigh n L U
    ⟨le_rfl, hLU, le_rfl, hL, hU⟩
  cases hout : (execute trial (bisect n L U)).1 with
  | found value =>
    refine ⟨value, rfl, ?_, execution_calls_le_fuel trial n L U⟩
    simpa only [hout, Spec] using hspec
  | bracket l r =>
    simp only [hout, Spec, Bracket] at hspec
    rcases hspec with ⟨⟨hl, hlr, hr, hFl, hFr⟩, hwidth⟩
    have hlI : l ∈ Set.Icc L U := ⟨hl, le_trans hlr hr⟩
    have hrI : r ∈ Set.Icc L U := ⟨le_trans hl hlr, hr⟩
    have hdiff := hLip r hrI l hlI
    rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hdiff
    have hfg : b - a ≤ F r - F l := by linarith only [hFl, hFr]
    have hg : b - a ≤ K * (r - l) := hfg.trans ((le_abs_self _).trans hdiff)
    have hsmall := halving_precision (K * (U - L)) ((b - a) / 2) (by linarith only [hgap])
    change K * (U - L) / (2 : ℝ) ^ n ≤ (b - a) / 2 at hsmall
    have heq : K * (r - l) = K * (U - L) / (2 : ℝ) ^ n := by rw [hwidth]; ring
    rw [heq] at hg
    exfalso
    linarith only [hg, hsmall, hgap]

theorem searchFuel_log_bound (K L U a b : ℝ) :
    (searchFuel K L U a b : ℝ) ≤
      1 + Real.logb 2 (max 1 ((K * (U - L)) / ((b - a) / 2))) := by
  unfold searchFuel halvingCount
  have h0 : 0 ≤ Real.logb 2 (max 1 ((K * (U - L)) / ((b - a) / 2))) :=
    Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have h := Nat.ceil_lt_add_one h0
  linarith only [h]

end FangqingHysteresis


namespace OriginalCoupledBetaSearch

open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalBetaATSUniform
open OriginalBetaATSTrial (Answer TrialResult)
open FangqingHysteresis (Decision Outcome)

structure Settings where
  mu : ℝ
  Lg : ℝ
  M : ℝ
  A : ℝ
  sigma : ℝ
  sigmaLow : ℝ
  sigmaUp : ℝ
  rho : ℝ

structure Legal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_pos : 0 < c.M
  A_pos : 0 < c.A
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

noncomputable def lower (c : Settings) (G : ℝ) : ℝ :=
  betaLow c.A (lambdaLow c.M c.sigmaLow c.sigma G)
noncomputable def margin (c : Settings) : ℝ :=
  highMargin c.A (lambdaHigh c.M c.rho c.sigma c.sigmaUp)
noncomputable def upper (c : Settings) : ℝ := 1 - margin c
noncomputable def lambdaMin (c : Settings) (G : ℝ) : ℝ := c.A * lower c G ^ 2
noncomputable def lambdaMax (c : Settings) : ℝ := c.A / margin c
noncomputable def tolerance (c : Settings) (G : ℝ) : ℝ :=
  uniformTolerance c.mu c.Lg c.M (lambdaMin c G) (lambdaMax c) c.sigma c.rho
noncomputable def thresholdLow (c : Settings) : ℝ := c.sigmaLow * (1 + c.sigma) / c.M
noncomputable def thresholdHigh (c : Settings) : ℝ := c.sigmaUp * (1 - c.sigma) / c.M

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def modulus (c : Settings) (G : ℝ) (x y : E) : ℝ :=
  sizeModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G ‖x - y‖

noncomputable def observedGradientBound (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  ‖(getter (y, 1)).grad‖ + 1 + c.Lg * ‖x - y‖

inductive Result (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | stop (point : E)
  | window (beta : ℝ) (displacement : E) (outputAnswer : Answer E)

noncomputable def classifiedTrial (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) (b : ℝ) : Decision (Result E) := by
  classical
  exact match OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
    | .stop w => .accept (.stop w)
    | .step d aY =>
        if c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M then
          .accept (.window b d aY)
        else if lambda c.A b * ‖d‖ < c.sigmaLow / c.M then .low else .high

def ValidResult (g : E → ℝ) (c : Settings) (G deltaY : ℝ) (x y : E) : Result E → Prop
  | .stop w => ‖gradient g w‖ ≤ c.rho
  | .window b d aY =>
      b ∈ Set.Icc (lower c G) (upper c) ∧ 0 < b ∧ b < 1 ∧
      0 < lambda c.A b ∧
      c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖lambda c.A b • CertifiedATS.trueVector (gradient g (center x y b))
        (fderiv ℝ (gradient g) (center x y b)) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (center x y b + d)‖ ≤ deltaY ∧
      weight c.A b = (lambda c.A b + Real.sqrt (lambda c.A b ^ 2 + 4 * lambda c.A b * c.A)) / 2 ∧
      center x y b = (c.A / (c.A + weight c.A b)) • y +
        (weight c.A b / (c.A + weight c.A b)) • x

theorem compact_properties (c : Settings) (hc : Legal c) (G : ℝ) (hG : 0 ≤ G) :
    0 < lower c G ∧ lower c G ≤ 1 / 4 ∧ 0 < margin c ∧ margin c ≤ 1 / 4 ∧
    3 / 4 ≤ upper c ∧ upper c < 1 ∧ lower c G ≤ upper c ∧
    0 < lambdaMin c G ∧ 0 < lambdaMax c := by
  have hLow := lambdaLow_positive c.M c.sigmaLow c.sigma G hc.M_pos hc.low_pos hc.sigma_lt_one hG
  have hlo := betaLow_properties c.A _ hc.A_pos hLow.1
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hHigh : 0 ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
    dsimp [lambdaHigh]
    have hm := hc.M_pos
    have hr := hc.rho_pos
    have hs := hc.sigma_pos
    positivity
  have hhi := betaHigh_properties c.A _ hc.A_pos hHigh
  have hrange : lower c G ≤ upper c := by
    change betaLow c.A _ ≤ betaHigh c.A _
    linarith only [hlo.2.1, hhi.2.2.1]
  refine ⟨hlo.1, hlo.2.1, hhi.1, hhi.2.1, hhi.2.2.1, hhi.2.2.2.1, hrange, ?_, ?_⟩
  · exact mul_pos hc.A_pos (sq_pos_of_pos hlo.1)
  · exact div_pos hc.A_pos hhi.1

theorem interval_lambda_bounds (c : Settings) (hc : Legal c) (G : ℝ) (hG : 0 ≤ G)
    (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c)) :
    0 < b ∧ b < 1 ∧ 0 < lambda c.A b ∧
      lambdaMin c G ≤ lambda c.A b ∧ lambda c.A b ≤ lambdaMax c := by
  have hp := compact_properties c hc G hG
  have hb0 : 0 < b := hp.1.trans_le hb.1
  have hb1 : b < 1 := hb.2.trans_lt hp.2.2.2.2.2.1
  have hlam := (coupled_weights c.A b hc.A_pos hb0 hb1).1
  have hh := lambda_compact_bounds c.A (lower c G) (margin c) b hc.A_pos hp.1 hp.2.2.1 hb.1 hb.2
  exact ⟨hb0, hb1, hlam, hh.1, hh.2⟩

theorem observed_bound_is_valid
    (g : E → ℝ) (c : Settings) (hc : Legal c) (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    0 ≤ observedGradientBound getter c x y ∧
      gradientBound g c.Lg x y ≤ observedGradientBound getter c x y := by
  refine ⟨?_, ?_⟩
  · dsimp [observedGradientBound]
    have hLg := hc.Lg_nonneg
    positivity
  · exact gradient_upper_from_certificate g c.Lg x y _ 1 (hgetter y 1 (by norm_num)).1

theorem interval_trial_spec
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c)) :
    OriginalBetaATSTrial.TrialSpec g c.M (lambda c.A b) c.sigma c.rho deltaY (center x y b)
      (OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b)) := by
  have hp := compact_properties c hc G hG
  have hl := interval_lambda_bounds c hc G hG b hb
  exact OriginalBetaATSTrial.trial_uniform_spec g c.mu c.Lg c.M (lambdaMin c G) (lambdaMax c)
    (lambda c.A b) c.sigma c.rho deltaY hc.mu_pos hc.Lg_nonneg hc.M_pos.le
    hp.2.2.2.2.2.2.2.1 hl.2.2.2.1 hl.2.2.2.2 hc.sigma_pos hc.rho_pos
    hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter (center x y b)


theorem actual_modulus_spec
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G : ℝ) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    0 ≤ modulus c G x y ∧
    (∀ b ∈ Set.Icc (lower c G) (upper c), ∀ d ∈ Set.Icc (lower c G) (upper c),
      |betaSize g c.M c.A x y b - betaSize g c.M c.A x y d| ≤ modulus c G x y * |b - d|) := by
  have hp := compact_properties c hc G hG0
  have hmu := hc.mu_pos
  have hLg := hc.Lg_nonneg
  have hM := hc.M_pos
  have hA := hc.A_pos
  have hlo := hp.1
  have ht := hp.2.2.1
  refine ⟨?_, ?_⟩
  · dsimp [modulus, sizeModulus, stepModulus, inverseLambdaModulus]
    positivity
  · intro b hb d hd
    exact betaSize_lipschitz g c.mu c.Lg c.M c.A (lower c G) (margin c) G
      hc.mu_pos hc.Lg_nonneg hc.M_pos.le hc.A_pos hp.1 hp.2.2.1 hC2 hsc hlip hHlip
      x y hG b d hb.1 hd.1 hb.2 hd.2

theorem threshold_gap (c : Settings) (hc : Legal c) : thresholdLow c < thresholdHigh c :=
  div_lt_div_of_pos_right hc.gap hc.M_pos

theorem classified_accept_valid
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    ValidResult g c G deltaY x y value := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w =>
    simp only [classifiedTrial, hr] at haccept
    have hv := Decision.accept.inj haccept
    rw [← hv]
    rw [hr] at ht
    exact ht
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at haccept
      have hv := Decision.accept.inj haccept
      rw [← hv]
      exact ⟨hb, hl.1, hl.2.1, hl.2.2.1, hw.1, hw.2, ht.1, ht.2.1,
        coupled_square_root_formula c.A b hc.A_pos hl.1 hl.2.1,
        (coupled_center c.A b hc.A_pos hl.1 hl.2.1 x y).symm⟩
    · simp only [classifiedTrial, hr, if_neg hw] at haccept
      split_ifs at haccept <;> cases haccept

theorem classified_low_threshold
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (hlow : classifiedTrial getter c G deltaY x y b = .low) :
    betaSize g c.M c.A x y b ≤ thresholdLow c := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w => simp only [classifiedTrial, hr] at hlow; cases hlow
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at hlow; cases hlow
    · by_cases hm : lambda c.A b * ‖d‖ < c.sigmaLow / c.M
      · exact low_failure_exact_threshold g c.mu c.M (lambda c.A b) c.sigma c.sigmaLow
          hc.mu_pos hc.M_pos hl.2.2.1 hc.sigma_pos.le hC2 hsc (center x y b) d ht.1 hm
      · simp only [classifiedTrial, hr, if_neg hw, if_neg hm] at hlow; cases hlow

theorem classified_high_threshold
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (hhigh : classifiedTrial getter c G deltaY x y b = .high) :
    thresholdHigh c ≤ betaSize g c.M c.A x y b := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w => simp only [classifiedTrial, hr] at hhigh; cases hhigh
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at hhigh; cases hhigh
    · by_cases hm : lambda c.A b * ‖d‖ < c.sigmaLow / c.M
      · simp only [classifiedTrial, hr, if_neg hw, if_pos hm] at hhigh; cases hhigh
      · have hbound : c.sigmaUp / c.M < lambda c.A b * ‖d‖ := by
          apply lt_of_not_ge
          intro hle
          exact hw ⟨le_of_not_gt hm, hle⟩
        exact high_failure_exact_threshold g c.mu c.M (lambda c.A b) c.sigma c.sigmaUp
          hc.mu_pos hc.M_pos hl.2.2.1 hc.sigma_lt_one hC2 hsc (center x y b) d ht.1 hbound


theorem lower_endpoint_not_high
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    classifiedTrial getter c G deltaY x y (lower c G) ≠ .high := by
  classical
  intro hhigh
  have hp := compact_properties c hc G hG0
  have hb : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A (lower c G)) (tolerance c G)
      c.rho deltaY (center x y (lower c G)) with
  | stop w => simp only [classifiedTrial, hr] at hhigh; cases hhigh
  | step d aY =>
    rw [hr] at ht
    have hs := low_endpoint_is_low g c.mu c.Lg c.M c.A c.sigmaLow c.sigma G
      hc.mu_pos hc.Lg_nonneg hc.M_pos hc.A_pos hc.low_pos hc.sigma_lt_one hG0 hC2 hsc hlip x y d hG ht.1
    change lambda c.A (lower c G) * ‖d‖ < c.sigmaLow / c.M at hs
    have hn : ¬(c.sigmaLow / c.M ≤ lambda c.A (lower c G) * ‖d‖ ∧
        lambda c.A (lower c G) * ‖d‖ ≤ c.sigmaUp / c.M) := by
      intro hw
      exact not_le_of_gt hs hw.1
    simp only [classifiedTrial, hr, if_neg hn, if_pos hs] at hhigh
    cases hhigh

theorem upper_endpoint_not_low
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) : classifiedTrial getter c G deltaY x y (upper c) ≠ .low := by
  classical
  intro hlow
  have hp := compact_properties c hc G hG0
  have hb : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hb
  have hl := interval_lambda_bounds c hc G hG0 (upper c) hb
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hHigh0 : 0 ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
    dsimp [lambdaHigh]
    have hM := hc.M_pos
    have hRho := hc.rho_pos
    have hSigma := hc.sigma_pos
    positivity
  have hlarge := (betaHigh_properties c.A (lambdaHigh c.M c.rho c.sigma c.sigmaUp) hc.A_pos hHigh0).2.2.2.2
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A (upper c)) (tolerance c G)
      c.rho deltaY (center x y (upper c)) with
  | stop w => simp only [classifiedTrial, hr] at hlow; cases hlow
  | step d aY =>
    rw [hr] at ht
    have hs : c.sigmaUp / c.M < lambda c.A (upper c) * ‖d‖ := by
      apply lt_of_not_ge
      intro hwindow
      have hg := large_lambda_upper_is_small g c.M c.rho c.sigma c.sigmaUp (lambda c.A (upper c))
        hc.M_pos hc.rho_pos hc.sigma_pos.le hUp.le hl.2.2.1 hlarge hC2 hHlip (center x y (upper c)) d ht.1 hwindow
      exact not_lt_of_ge hg ht.2.2
    have hn : ¬(c.sigmaLow / c.M ≤ lambda c.A (upper c) * ‖d‖ ∧
        lambda c.A (upper c) * ‖d‖ ≤ c.sigmaUp / c.M) := by
      intro hw
      exact not_le_of_gt hs hw.2
    have hLowUp : c.sigmaLow / c.M < c.sigmaUp / c.M := div_lt_div_of_pos_right hc.low_lt_up hc.M_pos
    have hnotlow : ¬lambda c.A (upper c) * ‖d‖ < c.sigmaLow / c.M :=
      not_lt_of_ge (hLowUp.le.trans hs.le)
    simp only [classifiedTrial, hr, if_neg hn, if_neg hnotlow] at hlow
    cases hlow

noncomputable def fuel (c : Settings) (G : ℝ) (x y : E) : ℕ :=
  FangqingHysteresis.searchFuel (modulus c G x y) (lower c G) (upper c) (thresholdLow c) (thresholdHigh c)

noncomputable def searchProgram (c : Settings) (G : ℝ) (x y : E) :
    FangqingHysteresis.Program (Decision (Result E)) (Outcome (Result E)) :=
  .ask (lower c G) (fun left => match left with
    | .accept value => .pure (.found value)
    | _ => .ask (upper c) (fun right => match right with
      | .accept value => .pure (.found value)
      | _ => FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c)))

theorem bisection_after_endpoints
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G)
    (hleft : classifiedTrial getter c G deltaY x y (lower c G) = .low)
    (hright : classifiedTrial getter c G deltaY x y (upper c) = .high) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).1 = .found value ∧
      ValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).2 ≤ fuel c G x y := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have hK := actual_modulus_spec g c hc G hG0 hC2 hsc hlip hHlip x y hG
  exact FangqingHysteresis.bisection_success_and_calls
    (classifiedTrial getter c G deltaY x y) (betaSize g c.M c.A x y) (ValidResult g c G deltaY x y)
    (thresholdLow c) (thresholdHigh c) (lower c G) (upper c) (modulus c G x y)
    (threshold_gap c hc) hK.1 hp.2.2.2.2.2.2.1
    (classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL hleft)
    (classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU hright)
    hK.2
    (fun b hb value hv => classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value hv)
    (fun b hb hv => classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)
    (fun b hb hv => classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)


noncomputable def classifyResult (c : Settings) (b : ℝ) : TrialResult E → Decision (Result E) := by
  classical
  exact fun raw => match raw with
    | .stop w => .accept (.stop w)
    | .step d aY =>
        if c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M then
          .accept (.window b d aY)
        else if lambda c.A b * ‖d‖ < c.sigmaLow / c.M then .low else .high

theorem classifiedTrial_factor (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) (b : ℝ) :
    classifiedTrial getter c G deltaY x y b = classifyResult c b
      (OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b)) := rfl

theorem positive_search_success_and_calls
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).1 = .found value ∧
      ValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).2 ≤ fuel c G x y + 2 := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  cases hleft : classifiedTrial getter c G deltaY x y (lower c G) with
  | accept value =>
    refine ⟨value, ?_, ?_, ?_⟩
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
    · exact classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL value hleft
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
      omega
  | high => exact False.elim (lower_endpoint_not_high g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y hG hleft)
  | low =>
    cases hright : classifiedTrial getter c G deltaY x y (upper c) with
    | accept value =>
      refine ⟨value, ?_, ?_, ?_⟩
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
      · exact classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU value hright
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
        omega
    | low => exact False.elim (upper_endpoint_not_low g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter x y hright)
    | high =>
      obtain ⟨value, hrun, hvalid, hcount⟩ := bisection_after_endpoints g c hc G deltaY hG0 hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter x y hG hleft hright
      refine ⟨value, ?_, hvalid, ?_⟩
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright] using hrun
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright, Nat.add_assoc] using Nat.add_le_add_right hcount 2

theorem positive_search_log_bound (c : Settings) (G : ℝ) (x y : E) :
    (fuel c G x y : ℝ) + 2 ≤
      3 + Real.logb 2 (max 1 (((modulus c G x y) * (upper c - lower c G)) /
        ((thresholdHigh c - thresholdLow c) / 2))) := by
  have h := FangqingHysteresis.searchFuel_log_bound (modulus c G x y) (lower c G) (upper c) (thresholdLow c) (thresholdHigh c)
  change (fuel c G x y : ℝ) ≤ _ at h
  linarith only [h]

end OriginalCoupledBetaSearch


namespace FangqingGetterComposition

open OriginalBetaATSTrial

noncomputable def bind {Q A R S : Type*} :
    GetterProgram Q A R → (R → GetterProgram Q A S) → GetterProgram Q A S
  | .pure r, next => next r
  | .ask q cont, next => .ask q (fun answer => bind (cont answer) next)

noncomputable def map {Q A R S : Type*} (f : R → S) (program : GetterProgram Q A R) :
    GetterProgram Q A S := bind program (fun r => .pure (f r))

theorem execute_bind {Q A R S : Type*} (getter : Q → A)
    (program : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    execute getter (bind program next) =
      ((execute getter (next (execute getter program).1)).1,
        (execute getter program).2 + (execute getter (next (execute getter program).1)).2) := by
  induction program with
  | pure r => simp only [bind, execute, zero_add]
  | ask q cont ih =>
    simp only [bind, execute, ih]
    exact Prod.ext rfl (by omega)

theorem execute_map {Q A R S : Type*} (getter : Q → A) (f : R → S)
    (program : GetterProgram Q A R) :
    execute getter (map f program) = (f (execute getter program).1, (execute getter program).2) := by
  simp only [map, execute_bind, execute, add_zero]

noncomputable def derivedReply {Q A Reply : Type*} (getter : Q → A)
    (trials : ℝ → GetterProgram Q A Reply) (point : ℝ) : Reply := (execute getter (trials point)).1

noncomputable def lower {Q A Reply Result : Type*} (trials : ℝ → GetterProgram Q A Reply) :
    FangqingHysteresis.Program Reply Result → GetterProgram Q A Result
  | .pure r => .pure r
  | .ask point cont => bind (trials point) (fun reply => lower trials (cont reply))

theorem lower_result_and_count {Q A Reply Result : Type*}
    (getter : Q → A) (trials : ℝ → GetterProgram Q A Reply) (K : ℕ)
    (htrial : ∀ point : ℝ, (execute getter (trials point)).2 ≤ K)
    (program : FangqingHysteresis.Program Reply Result) :
    (execute getter (lower trials program)).1 =
      (FangqingHysteresis.execute (derivedReply getter trials) program).1 ∧
    (execute getter (lower trials program)).2 ≤
      K * (FangqingHysteresis.execute (derivedReply getter trials) program).2 := by
  induction program with
  | pure r => simp only [lower, execute, FangqingHysteresis.execute, mul_zero, le_refl, and_self]
  | ask point cont ih =>
    have hi := ih (derivedReply getter trials point)
    have hc := htrial point
    simp only [lower, execute_bind, FangqingHysteresis.execute]
    constructor
    · exact hi.1
    · change (execute getter (trials point)).2 +
        (execute getter (lower trials (cont (derivedReply getter trials point)))).2 ≤
          K * ((FangqingHysteresis.execute (derivedReply getter trials)
            (cont (derivedReply getter trials point))).2 + 1)
      have hm := add_le_add hc hi.2
      nlinarith only [hm]

noncomputable def withInitial {Q A Reply Result : Type*} (request : Q)
    (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) : GetterProgram Q A Result :=
  .ask request (fun answer => lower (trials answer) (program answer))

theorem withInitial_result_and_count {Q A Reply Result : Type*}
    (getter : Q → A) (request : Q) (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) (K : ℕ)
    (htrial : ∀ answer point, (execute getter (trials answer point)).2 ≤ K) :
    (execute getter (withInitial request trials program)).1 =
      (FangqingHysteresis.execute (derivedReply getter (trials (getter request))) (program (getter request))).1 ∧
    (execute getter (withInitial request trials program)).2 ≤
      1 + K * (FangqingHysteresis.execute
        (derivedReply getter (trials (getter request))) (program (getter request))).2 := by
  have hi := lower_result_and_count getter (trials (getter request)) K (htrial (getter request))
    (program (getter request))
  simp only [withInitial, execute]
  exact ⟨hi.1, by omega⟩

section ActualTaylorTrials
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def mappedTaylorTrial {Reply : Type*}
    (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    GetterProgram (E × ℝ) (Answer E) Reply :=
  map (classify point) (trialProgram M (lam point) delta rho deltaY (center point))

theorem mappedTaylorTrial_calls {Reply : Type*}
    (getter : E × ℝ → Answer E) (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    (execute getter (mappedTaylorTrial classify M delta rho deltaY lam center point)).2 ≤ 2 := by
  rw [mappedTaylorTrial, execute_map]
  exact trial_getter_calls getter M (lam point) delta rho deltaY (center point)

theorem lowered_actual_trials_result_and_count {Reply Result : Type*}
    (getter : E × ℝ → Answer E) (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E)
    (program : FangqingHysteresis.Program Reply Result) :
    (execute getter (lower (mappedTaylorTrial classify M delta rho deltaY lam center) program)).1 =
      (FangqingHysteresis.execute
        (derivedReply getter (mappedTaylorTrial classify M delta rho deltaY lam center)) program).1 ∧
    (execute getter (lower (mappedTaylorTrial classify M delta rho deltaY lam center) program)).2 ≤
      2 * (FangqingHysteresis.execute
        (derivedReply getter (mappedTaylorTrial classify M delta rho deltaY lam center)) program).2 :=
  lower_result_and_count getter _ 2 (mappedTaylorTrial_calls getter classify M delta rho deltaY lam center) program

end ActualTaylorTrials
end FangqingGetterComposition

namespace FangqingGetterComposition
open OriginalBetaATSTrial

noncomputable def trace {Q A R : Type*} (getter : Q → A) : GetterProgram Q A R → List Q
  | .pure _ => []
  | .ask q next => q :: trace getter (next (getter q))

noncomputable def baseCost {Q A R : Type*} (getter : Q → A) (cost : Q → ℕ) : GetterProgram Q A R → ℕ
  | .pure _ => 0
  | .ask q next => cost q + baseCost getter cost (next (getter q))

def AllRequests {Q A R : Type*} (P : Q → Prop) : GetterProgram Q A R → Prop
  | .pure _ => True
  | .ask q next => P q ∧ ∀ answer : A, AllRequests P (next answer)

theorem trace_length_eq_count {Q A R : Type*} (getter : Q → A) (program : GetterProgram Q A R) :
    (trace getter program).length = (execute getter program).2 := by
  induction program with
  | pure r => rfl
  | ask q next ih => simp only [trace, execute, List.length_cons, ih]

theorem baseCost_eq_trace_sum {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (program : GetterProgram Q A R) :
    baseCost getter cost program = ((trace getter program).map cost).sum := by
  induction program with
  | pure r => rfl
  | ask q next ih => simp only [baseCost, trace, List.map_cons, List.sum_cons, ih]

theorem allRequests_trace {Q A R : Type*} (getter : Q → A) (P : Q → Prop)
    (program : GetterProgram Q A R) (hprogram : AllRequests P program) :
    ∀ q ∈ trace getter program, P q := by
  induction program with
  | pure r => simp only [trace, List.not_mem_nil, false_implies, implies_true]
  | ask q next ih =>
    intro req hmem
    simp only [trace, List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact hprogram.1
    · exact ih (getter q) (hprogram.2 (getter q)) req htail

theorem allRequests_bind {Q A R S : Type*} (P : Q → Prop)
    (program : GetterProgram Q A R) (next : R → GetterProgram Q A S)
    (hprogram : AllRequests P program) (hnext : ∀ r : R, AllRequests P (next r)) :
    AllRequests P (bind program next) := by
  induction program with
  | pure r => exact hnext r
  | ask q cont ih =>
    exact ⟨hprogram.1, fun answer => ih answer (hprogram.2 answer)⟩

theorem allRequests_map {Q A R S : Type*} (P : Q → Prop) (f : R → S)
    (program : GetterProgram Q A R) (hprogram : AllRequests P program) : AllRequests P (map f program) :=
  allRequests_bind P program _ hprogram (fun _ => True.intro)

theorem allRequests_lower {Q A Reply Result : Type*}
    (P : Q → Prop) (trials : ℝ → GetterProgram Q A Reply)
    (htrials : ∀ point : ℝ, AllRequests P (trials point))
    (program : FangqingHysteresis.Program Reply Result) : AllRequests P (lower trials program) := by
  induction program with
  | pure r => exact True.intro
  | ask point cont ih => exact allRequests_bind P (trials point) _ (htrials point) ih

theorem trace_withInitial_requests {Q A Reply Result : Type*}
    (getter : Q → A) (request : Q) (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) (P : Q → Prop)
    (hinitial : P request) (htrials : ∀ point : ℝ, AllRequests P (trials (getter request) point)) :
    ∀ q ∈ trace getter (withInitial request trials program), P q := by
  intro q hq
  simp only [withInitial, trace, List.mem_cons] at hq
  rcases hq with rfl | htail
  · exact hinitial
  · exact allRequests_trace getter P _ (allRequests_lower P _ htrials _) q htail

theorem list_cost_bound {Q : Type*} (requests : List Q) (cost : Q → ℕ) (C : ℕ)
    (hcost : ∀ q ∈ requests, cost q ≤ C) : (requests.map cost).sum ≤ C * requests.length := by
  induction requests with
  | nil => simp
  | cons q tail ih =>
    have hh := hcost q (by simp)
    have ht := ih (fun r hr => hcost r (by simp [hr]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith only [hh, ht]

theorem baseCost_le_mul_count {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (program : GetterProgram Q A R) (C : ℕ)
    (hcost : ∀ q ∈ trace getter program, cost q ≤ C) :
    baseCost getter cost program ≤ C * (execute getter program).2 := by
  rw [baseCost_eq_trace_sum]
  simpa only [trace_length_eq_count] using list_cost_bound (trace getter program) cost C hcost

section TaylorRequestPrecisions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem trialProgram_precision_set (M lam delta rho deltaY : ℝ) (z : E) :
    AllRequests (fun q : E × ℝ => q.2 = delta ∨ q.2 = deltaY)
      (trialProgram M lam delta rho deltaY z) := by
  classical
  unfold trialProgram
  change (delta = delta ∨ delta = deltaY) ∧ _
  refine ⟨Or.inl rfl, ?_⟩
  intro a
  dsimp only
  split_ifs
  · exact True.intro
  · change (deltaY = delta ∨ deltaY = deltaY) ∧ _
    refine ⟨Or.inr rfl, ?_⟩
    intro aY
    dsimp only
    split_ifs <;> exact True.intro

theorem mappedTaylorTrial_precision_set {Reply : Type*}
    (classify : ℝ → TrialResult E → Reply) (M delta rho deltaY : ℝ)
    (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    AllRequests (fun q : E × ℝ => q.2 = delta ∨ q.2 = deltaY)
      (mappedTaylorTrial classify M delta rho deltaY lam center point) :=
  allRequests_map _ _ _ (trialProgram_precision_set M (lam point) delta rho deltaY (center point))

end TaylorRequestPrecisions
end FangqingGetterComposition

namespace FangqingGetterComposition
open OriginalBetaATSTrial

theorem allRequests_mono {Q A R : Type*} (P S : Q → Prop)
    (hPS : ∀ q, P q → S q) (program : GetterProgram Q A R)
    (hp : AllRequests P program) : AllRequests S program := by
  induction program with
  | pure r => exact True.intro
  | ask q next ih => exact ⟨hPS q hp.1, fun a => ih a (hp.2 a)⟩

noncomputable def logarithmicAtomicBound (K eta : ℝ) : ℕ :=
  ⌈K * (1 + Real.log (1 + eta⁻¹))⌉₊

theorem logarithmicAtomicBound_antitone (K floor eta : ℝ)
    (hK : 0 ≤ K) (hfloor : 0 < floor) (heta : floor ≤ eta) :
    logarithmicAtomicBound K eta ≤ logarithmicAtomicBound K floor := by
  have hpos : 0 < eta := hfloor.trans_le heta
  have hinv : eta⁻¹ ≤ floor⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hfloor heta
  have hlog : Real.log (1 + eta⁻¹) ≤ Real.log (1 + floor⁻¹) :=
    Real.log_le_log (by positivity) (by linarith only [hinv])
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hK)

theorem logarithmic_baseCost_bound {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (accuracy : Q → ℝ)
    (program : GetterProgram Q A R) (K floor : ℝ)
    (hK : 0 ≤ K) (hfloor : 0 < floor)
    (hprecision : ∀ q ∈ trace getter program, floor ≤ accuracy q)
    (hatomic : ∀ q : Q, 0 < accuracy q → cost q ≤ logarithmicAtomicBound K (accuracy q)) :
    baseCost getter cost program ≤ logarithmicAtomicBound K floor * (execute getter program).2 := by
  apply baseCost_le_mul_count
  intro q hq
  exact (hatomic q (hfloor.trans_le (hprecision q hq))).trans
    (logarithmicAtomicBound_antitone K floor (accuracy q) hK hfloor (hprecision q hq))

end FangqingGetterComposition


namespace FangqingGetterComposition
open OriginalBetaATSTrial

noncomputable def primitiveLower {Q A BQ BA R : Type*}
    (oracle : Q → GetterProgram BQ BA A) : GetterProgram Q A R → GetterProgram BQ BA R
  | .pure r => .pure r
  | .ask q next => bind (oracle q) (fun a => primitiveLower oracle (next a))

noncomputable def implementedGetter {Q A BQ BA : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A) (q : Q) : A :=
  (execute baseAnswer (oracle q)).1

noncomputable def implementedCost {Q A BQ BA : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A) (q : Q) : ℕ :=
  (execute baseAnswer (oracle q)).2

theorem primitiveLower_execution {Q A BQ BA R : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A)
    (program : GetterProgram Q A R) :
    execute baseAnswer (primitiveLower oracle program) =
      ((execute (implementedGetter baseAnswer oracle) program).1,
        baseCost (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle) program) := by
  induction program with
  | pure r => rfl
  | ask q next ih =>
    simp only [primitiveLower, execute_bind, ih, execute, baseCost, implementedGetter, implementedCost]

end FangqingGetterComposition

namespace FangqingGetterComposition

theorem logarithmicAtomicBound_real_le (K eta : ℝ) (hK : 0 ≤ K) (heta : 0 < eta) :
    (logarithmicAtomicBound K eta : ℝ) ≤ K * (1 + Real.log (1 + eta⁻¹)) + 1 := by
  have hlog : 0 ≤ Real.log (1 + eta⁻¹) := Real.log_nonneg (by have h := inv_nonneg.mpr heta.le; linarith only [h])
  exact (Nat.ceil_lt_add_one (mul_nonneg hK (by linarith only [hlog]))).le

end FangqingGetterComposition


namespace OriginalCoupledGetterProgram

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def initialBound (c : Settings) (x y : E) (a : Answer E) : ℝ :=
  ‖a.grad‖ + 1 + c.Lg * ‖x - y‖

noncomputable def trials (c : Settings) (G deltaY : ℝ) (x y : E) :
    ℝ → GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Decision (Result E)) :=
  mappedTaylorTrial (classifyResult c) c.M (tolerance c G) c.rho deltaY
    (lambda c.A) (center x y)

noncomputable def positiveProgram (c : Settings) (deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  withInitial (y, 1) (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y)

theorem trials_derivedReply (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) :
    derivedReply getter (trials c G deltaY x y) = classifiedTrial getter c G deltaY x y := by
  funext b
  simp only [derivedReply, trials, mappedTaylorTrial, execute_map]
  rfl

theorem positiveProgram_result_and_count (getter : E × ℝ → Answer E) (c : Settings)
    (deltaY : ℝ) (x y : E) :
    (execute getter (positiveProgram c deltaY x y)).1 =
      (FangqingHysteresis.execute
        (classifiedTrial getter c (observedGradientBound getter c x y) deltaY x y)
        (searchProgram c (observedGradientBound getter c x y) x y)).1 ∧
    (execute getter (positiveProgram c deltaY x y)).2 ≤
      1 + 2 * (FangqingHysteresis.execute
        (classifiedTrial getter c (observedGradientBound getter c x y) deltaY x y)
        (searchProgram c (observedGradientBound getter c x y) x y)).2 := by
  have h := withInitial_result_and_count getter (y, 1)
    (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y) 2
    (fun a b => mappedTaylorTrial_calls getter (classifyResult c) c.M
      (tolerance c (initialBound c x y a)) c.rho deltaY (lambda c.A) (center x y) b)
  rw [trials_derivedReply] at h
  exact h

theorem positiveProgram_success_and_getter_calls
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (positiveProgram c deltaY x y)).1 = .found value ∧
      ValidResult g c (observedGradientBound getter c x y) deltaY x y value ∧
      (execute getter (positiveProgram c deltaY x y)).2 ≤
        2 * fuel c (observedGradientBound getter c x y) x y + 5 := by
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  obtain ⟨value, hrun, hvalid, hcount⟩ := positive_search_success_and_calls g c hc
    (observedGradientBound getter c x y) deltaY hbound.1 hdeltaY hdeltaYsmall
    hC2 hsc hlip hHlip getter hgetter x y hbound.2
  have hprogram := positiveProgram_result_and_count getter c deltaY x y
  exact ⟨value, hprogram.1.trans hrun, hvalid, by omega⟩

theorem positiveProgram_getter_log_bound
    (getter : E × ℝ → Answer E) (c : Settings) (deltaY : ℝ) (x y : E)
    (hcount : (execute getter (positiveProgram c deltaY x y)).2 ≤
      2 * fuel c (observedGradientBound getter c x y) x y + 5) :
    ((execute getter (positiveProgram c deltaY x y)).2 : ℝ) ≤
      7 + 2 * Real.logb 2 (max 1
        ((modulus c (observedGradientBound getter c x y) x y *
          (upper c - lower c (observedGradientBound getter c x y))) /
            ((thresholdHigh c - thresholdLow c) / 2))) := by
  have h := positive_search_log_bound c (observedGradientBound getter c x y) x y
  have hnat : ((execute getter (positiveProgram c deltaY x y)).2 : ℝ) ≤
      2 * (fuel c (observedGradientBound getter c x y) x y : ℝ) + 5 := by exact_mod_cast hcount
  linarith only [h, hnat]

end OriginalCoupledGetterProgram

namespace OriginalCoupledGetterProgram
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def precisionFloor (c : Settings) (G deltaY : ℝ) : ℝ :=
  min 1 (min (tolerance c G) deltaY)

theorem precisionFloor_positive (c : Settings) (hc : Legal c) (G deltaY : ℝ)
    (hG : 0 ≤ G) (hdeltaY : 0 < deltaY) : 0 < precisionFloor c G deltaY := by
  have hp := compact_properties c hc G hG
  have ht := OriginalBetaATSUniform.uniformTolerance_positive c.mu c.Lg c.M
    (lambdaMin c G) (lambdaMax c) c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2 hc.sigma_pos hc.rho_pos
  exact lt_min (by norm_num) (lt_min ht hdeltaY)

theorem positiveProgram_request_precision_floor
    (getter : E × ℝ → Answer E) (c : Settings) (deltaY : ℝ) (x y : E) :
    ∀ q ∈ trace getter (positiveProgram c deltaY x y),
      precisionFloor c (observedGradientBound getter c x y) deltaY ≤ q.2 := by
  apply trace_withInitial_requests getter (y, 1)
    (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y)
    (fun q : E × ℝ => precisionFloor c (observedGradientBound getter c x y) deltaY ≤ q.2)
  · exact min_le_left _ _
  · intro b
    apply allRequests_mono
      (fun q : E × ℝ => q.2 = tolerance c (observedGradientBound getter c x y) ∨ q.2 = deltaY)
    · intro q hq
      rcases hq with hq | hq
      · rw [hq]
        exact (min_le_right _ _).trans (min_le_left _ _)
      · rw [hq]
        exact (min_le_right _ _).trans (min_le_right _ _)
    · exact mappedTaylorTrial_precision_set (classifyResult c) c.M
        (tolerance c (observedGradientBound getter c x y)) c.rho deltaY (lambda c.A) (center x y) b

theorem positiveProgram_logarithmic_base_cost
    (getter : E × ℝ → Answer E) (cost : E × ℝ → ℕ) (c : Settings) (deltaY : ℝ) (x y : E)
    (K : ℝ) (hK : 0 ≤ K)
    (hfloor : 0 < precisionFloor c (observedGradientBound getter c x y) deltaY)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (hcount : (execute getter (positiveProgram c deltaY x y)).2 ≤
      2 * fuel c (observedGradientBound getter c x y) x y + 5) :
    baseCost getter cost (positiveProgram c deltaY x y) ≤
      logarithmicAtomicBound K (precisionFloor c (observedGradientBound getter c x y) deltaY) *
        (2 * fuel c (observedGradientBound getter c x y) x y + 5) := by
  exact (logarithmic_baseCost_bound getter cost Prod.snd (positiveProgram c deltaY x y) K _ hK hfloor
    (positiveProgram_request_precision_floor getter c deltaY x y) hatomic).trans
      (Nat.mul_le_mul_left _ hcount)

end OriginalCoupledGetterProgram


namespace OriginalFirstCoupledStep

open OriginalCoupledBetaAlgebra
open OriginalCoupledBetaSearch
open OriginalBetaATSTrial (Answer)
open FangqingHysteresis (Decision Outcome)

structure CommonLegal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_pos : 0 < c.M
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

noncomputable def proxySettings (c : Settings) : Settings := {c with A := 1}

theorem proxy_legal (c : Settings) (hc : CommonLegal c) : Legal (proxySettings c) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, by norm_num [proxySettings], hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

theorem positive_legal (c : Settings) (hc : CommonLegal c) (hA : 0 < c.A) : Legal c :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hA, hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem center_same (z : E) (b : ℝ) : center z z b = z := by dsimp [center]; module

noncomputable def fixedSearchProgram (c : Settings) (G : ℝ) (z : E) :
    FangqingHysteresis.Program (Decision (Result E)) (Outcome (Result E)) :=
  searchProgram (proxySettings c) G z z

noncomputable def fixedTrial (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (z : E) : ℝ → Decision (Result E) :=
  classifiedTrial getter (proxySettings c) G deltaY z z

def FixedValidResult (g : E → ℝ) (c : Settings) (deltaY : ℝ) (z : E) : Result E → Prop
  | .stop w => ‖gradient g w‖ ≤ c.rho
  | .window b d aY =>
      0 < b ∧ b < 1 ∧ 0 < lambda 1 b ∧
      c.sigmaLow / c.M ≤ lambda 1 b * ‖d‖ ∧ lambda 1 b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖lambda 1 b • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (z + d)‖ ≤ deltaY ∧
      (lambda 1 b + Real.sqrt (lambda 1 b ^ 2 + 4 * lambda 1 b * 0)) / 2 = lambda 1 b ∧
      (0 / (0 + lambda 1 b)) • z + (lambda 1 b / (0 + lambda 1 b)) • z = z ∧
      0 < 0 + lambda 1 b

theorem proxy_result_is_actual_first_step
    (g : E → ℝ) (c : Settings) (deltaY G : ℝ) (z : E) (value : Result E)
    (hvalid : ValidResult g (proxySettings c) G deltaY z z value) :
    FixedValidResult g c deltaY z value := by
  cases value with
  | stop w => exact hvalid
  | window b d aY =>
    rcases hvalid with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
    rw [center_same] at hATS herr
    have hzero := zero_weight_first_step (lambda 1 b) hlam z z
    exact ⟨hb0, hb1, hlam, hlow, hhigh, hATS, herr, hzero.1, hzero.2, by simpa only [zero_add, proxySettings] using hlam⟩

theorem first_step_success_and_calls
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ c.Lg * ‖x - y‖)
    (hHlip : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ c.M * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ x : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (x, eta)).grad - gradient g x‖ ≤ eta ∧
      ‖(getter (x, eta)).hess - fderiv ℝ (gradient g) x‖ ≤ eta)
    (z : E) (hG : ‖gradient g z‖ ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (fixedTrial getter c G deltaY z) (fixedSearchProgram c G z)).1 = .found value ∧
      FixedValidResult g c deltaY z value ∧
      (FangqingHysteresis.execute (fixedTrial getter c G deltaY z) (fixedSearchProgram c G z)).2 ≤
        fuel (proxySettings c) G z z + 2 := by
  have hG' : OriginalBetaCurveBounds.gradientBound g (proxySettings c).Lg z z ≤ G := by
    simpa only [OriginalBetaCurveBounds.gradientBound, sub_self, norm_zero, mul_zero, add_zero] using hG
  obtain ⟨value, hrun, hvalid, hcount⟩ := positive_search_success_and_calls g (proxySettings c)
    (proxy_legal c hc) G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter z z hG'
  exact ⟨value, hrun, proxy_result_is_actual_first_step g c deltaY G z value hvalid, hcount⟩

theorem first_step_log_bound (c : Settings) (G : ℝ) (z : E) :
    (fuel (proxySettings c) G z z : ℝ) + 2 ≤
      3 + Real.logb 2 (max 1 (((modulus (proxySettings c) G z z) *
        (upper (proxySettings c) - lower (proxySettings c) G)) /
          ((thresholdHigh (proxySettings c) - thresholdLow (proxySettings c)) / 2))) :=
  positive_search_log_bound (proxySettings c) G z z

end OriginalFirstCoupledStep


namespace OriginalZeroCurvatureSearch

open OriginalTaylorProxStability
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalBetaATSUniform
open OriginalBetaATSTrial (Answer TrialResult)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem zero_hessian_lipschitz_exact_taylor
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (z d : E) :
    CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) 0 d = gradient g (z + d) := by
  have hrem : ‖gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro e he
    let m := 2 * e / (‖d‖ ^ 2 + 1)
    have hm : 0 < m := by dsimp [m]; positivity
    have hHm : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ m * ‖x - y‖ := by
      intro x y
      have hh := hH0 x y
      simp only [zero_mul] at hh
      exact hh.trans (by positivity)
    have hb := RobustAHPE.gradient_taylor_remainder g hC2 m hm hHm z d
    calc
      _ ≤ m / 2 * ‖d‖ ^ 2 := hb
      _ ≤ 0 + e := by
        have heq : m / 2 * ‖d‖ ^ 2 = e * ‖d‖ ^ 2 / (‖d‖ ^ 2 + 1) := by dsimp [m]; ring
        rw [heq, zero_add]
        apply (div_le_iff₀ (by positivity : 0 < ‖d‖ ^ 2 + 1)).mpr
        nlinarith only [he]
  have hzero := norm_eq_zero.mp (le_antisymm hrem (norm_nonneg _))
  have heq : gradient g (z + d) = gradient g z + fderiv ℝ (gradient g) z d := by
    calc
      _ = (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) +
          (gradient g z + fderiv ℝ (gradient g) z d) := by abel
      _ = _ := by rw [hzero, zero_add]
  simpa only [CertifiedATS.trueVector, zero_div, zero_mul, zero_smul, add_zero] using heq.symm

noncomputable def largeLambda (mu sigma rho G : ℝ) : ℝ :=
  1 + 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho)

theorem zero_curvature_large_lambda_small_gradient
    (g : E → ℝ) (mu lam sigma rho G : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (hrho : 0 < rho) (hG0 : 0 ≤ G) (hlarge : largeLambda mu sigma rho G ≤ lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) 0 d + d‖ ≤ sigma * ‖d‖) :
    ‖gradient g (z + d)‖ ≤ rho / 2 := by
  have hsize := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) 0 lam mu
    (by norm_num) hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hRadius : ‖actualStep g 0 z lam‖ ≤ G / mu := by
    have hn : 0 ≤ lam⁻¹ * ‖actualStep g 0 z lam‖ := by positivity
    apply (le_div_iff₀ hmu).mpr
    change (mu + lam⁻¹) * ‖actualStep g 0 z lam‖ ≤ _ at hsize
    nlinarith only [hsize, hG, hn]
  have hbr := (actual_approximate_norm_bracket g mu 0 lam sigma hmu (by norm_num) hlam hC2 hsc z d hATS).1
  have hbr0 : (1 - sigma) * ‖d‖ ≤ ‖actualStep g 0 z lam‖ := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hbr]
  have hmuDiv : mu * (G / mu) = G := by field_simp
  have hd : ‖d‖ ≤ G / (mu * (1 - sigma)) := by
    have hh := mul_le_mul_of_nonneg_left (hbr0.trans hRadius) hmu.le
    rw [hmuDiv] at hh
    apply (le_div_iff₀ (by positivity : 0 < mu * (1 - sigma))).mpr
    nlinarith only [hh]
  have hgradATS : ‖lam • gradient g (z + d) + d‖ ≤ sigma * ‖d‖ := by
    rwa [zero_hessian_lipschitz_exact_taylor g hC2 hH0 z d] at hATS
  have ht := norm_sub_le (lam • gradient g (z + d) + d) d
  have heq : (lam • gradient g (z + d) + d) - d = lam • gradient g (z + d) := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
  have hgrad : ‖gradient g (z + d)‖ ≤ (1 + sigma) * (G / (mu * (1 - sigma))) / lam := by
    apply (le_div_iff₀ hlam).mpr
    have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 1 + sigma)
    nlinarith only [ht, hgradATS, hm]
  have hden : 0 < mu * (1 - sigma) * rho := by positivity
  have hl : 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho) ≤ lam := by
    change 1 + _ ≤ lam at hlarge
    linarith only [hlarge]
  have hmul := (div_le_iff₀ hden).mp hl
  have hfinal : (1 + sigma) * (G / (mu * (1 - sigma))) / lam ≤ rho / 2 := by
    have heq' : (1 + sigma) * (G / (mu * (1 - sigma))) / lam =
        ((1 + sigma) * G) / (mu * (1 - sigma) * lam) := by field_simp <;> ring
    rw [heq']
    apply (div_le_iff₀ (by positivity : 0 < mu * (1 - sigma) * lam)).mpr
    nlinarith only [hmul]
  exact hgrad.trans hfinal

theorem zero_curvature_trial_stops
    (g : E → ℝ) (mu Lg lam sigma rho G deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hlam : 0 < lam) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hrho : 0 < rho) (hG0 : 0 ≤ G) (hlarge : largeLambda mu sigma rho G ≤ lam)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) (hG : ‖gradient g z‖ ≤ G) :
    ∃ w : E, OriginalBetaATSTrial.trial getter 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (OriginalBetaATSTrial.execute getter
        (OriginalBetaATSTrial.trialProgram 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z)).2 ≤ 2 := by
  have ht := OriginalBetaATSTrial.trial_uniform_spec g mu Lg 0 lam lam lam sigma rho deltaY
    hmu hLg (by norm_num) hlam le_rfl le_rfl hsigma0 hrho hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter z
  cases hout : OriginalBetaATSTrial.trial getter 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z with
  | stop w =>
    rw [hout] at ht
    exact ⟨w, rfl, ht, OriginalBetaATSTrial.trial_getter_calls getter 0 lam _ rho deltaY z⟩
  | step d aY =>
    rw [hout] at ht
    have hg := zero_curvature_large_lambda_small_gradient g mu lam sigma rho G hmu hlam hsigma0.le hsigma1
      hrho hG0 hlarge hC2 hsc hH0 z d hG ht.1
    exact False.elim (not_lt_of_ge hg ht.2.2)


noncomputable def observedBound (getter : E × ℝ → Answer E) (Lg : ℝ) (x y : E) : ℝ :=
  ‖(getter (y, 1)).grad‖ + 1 + Lg * ‖x - y‖

noncomputable def chosenBeta (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho : ℝ) (x y : E) : ℝ :=
  betaHigh A (largeLambda mu sigma rho (observedBound getter Lg x y))

theorem zero_curvature_observable_coupled_stop
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    let b := chosenBeta getter mu Lg A sigma rho x y
    let lam := OriginalCoupledBetaAlgebra.lambda A b
    let z := OriginalCoupledBetaAlgebra.center x y b
    0 < b ∧ b < 1 ∧ 0 < lam ∧
    (∃ w : E, OriginalBetaATSTrial.trial getter 0 lam
      (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (OriginalBetaATSTrial.execute getter
        (OriginalBetaATSTrial.trialProgram 0 lam
          (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z)).2 ≤ 2) := by
  let G := observedBound getter Lg x y
  have hG0 : 0 ≤ G := by dsimp [G, observedBound]; positivity
  have hG : gradientBound g Lg x y ≤ G :=
    gradient_upper_from_certificate g Lg x y _ 1 (hgetter y 1 (by norm_num)).1
  have hH0' : 0 ≤ largeLambda mu sigma rho G := by dsimp [largeLambda]; positivity
  have hb := betaHigh_properties A (largeLambda mu sigma rho G) hA hH0'
  have hb0 : 0 < betaHigh A (largeLambda mu sigma rho G) := by linarith only [hb.2.2.1]
  have hb1 := hb.2.2.2.1
  have hlam := (OriginalCoupledBetaAlgebra.coupled_weights A _ hA hb0 hb1).1
  refine ⟨hb0, hb1, hlam, ?_⟩
  apply zero_curvature_trial_stops g mu Lg _ sigma rho G deltaY hmu hLg hlam
    hsigma0 hsigma1 hrho hG0 hb.2.2.2.2 hdeltaY hdeltaYsmall hC2 hsc hlip hH0 getter hgetter
  exact (center_gradient_bound g Lg hLg hlip x y _ hb0.le hb1.le).trans hG

end OriginalZeroCurvatureSearch


namespace OriginalCoupledSearchComplete

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def effectiveSettings (c : Settings) : Settings :=
  if 0 < c.A then c else proxySettings c

noncomputable def effectiveY (c : Settings) (x y : E) : E := if 0 < c.A then y else x

noncomputable def coupledProgram (c : Settings) (deltaY : ℝ) (x y : E) :=
  positiveProgram (effectiveSettings c) deltaY x (effectiveY c x y)

def ActualValid (g : E → ℝ) (c : Settings) (getter : E × ℝ → Answer E)
    (deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  if 0 < c.A then ValidResult g c (observedGradientBound getter c x y) deltaY x y value
  else FixedValidResult g c deltaY x value

theorem effective_legal (c : Settings) (hc : CommonLegal c) : Legal (effectiveSettings c) := by
  by_cases hA : 0 < c.A
  · simpa only [effectiveSettings, if_pos hA] using positive_legal c hc hA
  · simpa only [effectiveSettings, if_neg hA] using proxy_legal c hc

theorem effective_fields (c : Settings) :
    (effectiveSettings c).mu = c.mu ∧ (effectiveSettings c).Lg = c.Lg ∧
    (effectiveSettings c).M = c.M ∧ (effectiveSettings c).rho = c.rho := by
  by_cases hA : 0 < c.A <;> simp [effectiveSettings, hA, proxySettings]

theorem coupled_search_from_certified_getters
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    let e := effectiveSettings c
    let y' := effectiveY c x y
    let G := observedGradientBound getter e x y'
    ∃ value : Result E,
      (execute getter (coupledProgram c deltaY x y)).1 = .found value ∧
      ActualValid g c getter deltaY x y value ∧
      (0 < c.A ∨ c.A = 0) ∧
      (FangqingHysteresis.execute (classifiedTrial getter e G deltaY x y')
        (searchProgram e G x y')).2 ≤ fuel e G x y' + 2 ∧
      ((fuel e G x y' : ℕ) : ℝ) + 2 ≤
        3 + Real.logb 2 (max 1 ((modulus e G x y' * (upper e - lower e G)) /
          ((thresholdHigh e - thresholdLow e) / 2))) ∧
      (execute getter (coupledProgram c deltaY x y)).2 ≤ 2 * fuel e G x y' + 5 ∧
      0 < precisionFloor e G deltaY ∧
      (∀ q ∈ trace getter (coupledProgram c deltaY x y), precisionFloor e G deltaY ≤ q.2) ∧
      baseCost getter cost (coupledProgram c deltaY x y) ≤
        logarithmicAtomicBound K (precisionFloor e G deltaY) * (2 * fuel e G x y' + 5) := by
  let e := effectiveSettings c
  let y' := effectiveY c x y
  let G := observedGradientBound getter e x y'
  have he := effective_legal c hc
  have hf := effective_fields c
  have hde : deltaY ≤ e.rho / 8 := by simpa only [e, hf.2.2.2] using hdeltaYsmall
  have hsce : StrongConvexOn (Set.univ : Set E) e.mu g := by simpa only [e, hf.1] using hsc
  have hlipe : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ e.Lg * ‖z - w‖ := by
    simpa only [e, hf.2.1] using hlip
  have hHlipe : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ e.M * ‖z - w‖ := by
    simpa only [e, hf.2.2.1] using hHlip
  obtain ⟨value, hrun, hvalid, hcount⟩ := positiveProgram_success_and_getter_calls g e he deltaY
    hdeltaY hde hC2 hsce hlipe hHlipe getter hgetter x y'
  have hbound := observed_bound_is_valid g e he getter hgetter x y'
  obtain ⟨_, _, _, hATSCount⟩ := positive_search_success_and_calls g e he G deltaY hbound.1
    hdeltaY hde hC2 hsce hlipe hHlipe getter hgetter x y' hbound.2
  have hfloor := precisionFloor_positive e he G deltaY hbound.1 hdeltaY
  have hv : ActualValid g c getter deltaY x y value := by
    by_cases hpos : 0 < c.A
    · simpa only [ActualValid, if_pos hpos, e, effectiveSettings, y', effectiveY] using hvalid
    · apply (if_neg hpos).mpr
      apply proxy_result_is_actual_first_step g c deltaY G x value
      simpa only [G, e, effectiveSettings, y', effectiveY, if_neg hpos] using hvalid
  have hcases : 0 < c.A ∨ c.A = 0 := by
    by_cases hp : 0 < c.A
    · exact Or.inl hp
    · exact Or.inr (le_antisymm (le_of_not_gt hp) hA)
  exact ⟨value, hrun, hv, hcases, hATSCount, positive_search_log_bound e G x y', hcount,
    hfloor, positiveProgram_request_precision_floor getter e deltaY x y',
    positiveProgram_logarithmic_base_cost getter cost e deltaY x y' K hK hfloor hatomic hcount⟩

end OriginalCoupledSearchComplete


namespace OriginalZeroCurvatureSearch
open OriginalBetaATSTrial
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def initialBeta (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  OriginalBetaSearchEndpoints.betaHigh A (largeLambda mu sigma rho (‖a.grad‖ + 1 + Lg * ‖x - y‖))
noncomputable def initialLambda (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  lambda A (initialBeta mu Lg A sigma rho x y a)
noncomputable def initialCenter (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : E :=
  center x y (initialBeta mu Lg A sigma rho x y a)
noncomputable def initialTolerance (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  OriginalBetaATSUniform.uniformTolerance mu Lg 0
    (initialLambda mu Lg A sigma rho x y a) (initialLambda mu Lg A sigma rho x y a) sigma rho
noncomputable def zeroProgram (mu Lg A sigma rho deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (TrialResult E) :=
  .ask (y, 1) (fun a => trialProgram 0 (initialLambda mu Lg A sigma rho x y a)
    (initialTolerance mu Lg A sigma rho x y a) rho deltaY (initialCenter mu Lg A sigma rho x y a))
noncomputable def zeroPrecisionFloor (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho deltaY : ℝ) (x y : E) : ℝ :=
  min 1 (min (initialTolerance mu Lg A sigma rho x y (getter (y, 1))) deltaY)

theorem zeroProgram_trace_floor (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho deltaY : ℝ) (x y : E) :
    ∀ q ∈ trace getter (zeroProgram mu Lg A sigma rho deltaY x y),
      zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ≤ q.2 := by
  intro q hq
  simp only [zeroProgram, trace, List.mem_cons] at hq
  rcases hq with rfl | htail
  · exact min_le_left _ _
  · apply allRequests_trace getter
      (fun q : E × ℝ => zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ≤ q.2)
      _ _ q htail
    apply allRequests_mono _ _ _ _ (trialProgram_precision_set 0 _ _ rho deltaY _)
    intro r hr
    rcases hr with hr | hr
    · rw [hr]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [hr]
      exact (min_le_right _ _).trans (min_le_right _ _)

theorem zeroProgram_small_gradient_and_logarithmic_cost
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ w : E, (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).1 = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).2 ≤ 3 ∧
      0 < zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ∧
      baseCost getter cost (zeroProgram mu Lg A sigma rho deltaY x y) ≤
        3 * logarithmicAtomicBound K (zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y) := by
  obtain ⟨hb, hb1, hlam, w, hw, hgrad, hcalls⟩ := zero_curvature_observable_coupled_stop g mu Lg A sigma rho deltaY
    hmu hLg hA hsigma0 hsigma1 hrho hdeltaY hdeltaYsmall hC2 hsc hlip hH0 getter hgetter x y
  have hrun : (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).1 = .stop w := hw
  have hcount : (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).2 ≤ 3 := by
    change (execute getter (trialProgram 0 _ _ rho deltaY _)).2 + 1 ≤ 3
    exact Nat.add_le_add_right hcalls 1
  have hlam' : 0 < initialLambda mu Lg A sigma rho x y (getter (y, 1)) := hlam
  have ht : 0 < initialTolerance mu Lg A sigma rho x y (getter (y, 1)) := by
    exact OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 _ _ sigma rho
      hmu hLg (by norm_num) hlam' hlam' hsigma0 hrho
  have hfloor : 0 < zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y :=
    lt_min (by norm_num) (lt_min ht hdeltaY)
  have hcost := logarithmic_baseCost_bound getter cost Prod.snd
    (zeroProgram mu Lg A sigma rho deltaY x y) K _ hK hfloor
    (zeroProgram_trace_floor getter mu Lg A sigma rho deltaY x y) hatomic
  refine ⟨w, hrun, hgrad, hcount, hfloor, hcost.trans ?_⟩
  calc
    _ ≤ logarithmicAtomicBound K (zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y) * 3 :=
      Nat.mul_le_mul_left _ hcount
    _ = _ := Nat.mul_comm _ _

end OriginalZeroCurvatureSearch


namespace OriginalCoupledSearchComplete
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open OriginalZeroCurvatureSearch
open FangqingGetterComposition

structure NonnegativeLegal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_nonneg : 0 ≤ c.M
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

theorem positive_common (c : Settings) (hc : NonnegativeLegal c) (hM : 0 < c.M) : CommonLegal c :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hM, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def zeroAsOutcome : TrialResult E → FangqingHysteresis.Outcome (Result E)
  | .stop w => .found (.stop w)
  | .step _ _ => .bracket 0 1

noncomputable def allCurvatureProgram (c : Settings) (deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  if 0 < c.M then coupledProgram c deltaY x y
  else FangqingGetterComposition.map zeroAsOutcome
    (zeroProgram c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY x (effectiveY c x y))

noncomputable def allPrecisionFloor (getter : E × ℝ → Answer E)
    (c : Settings) (deltaY : ℝ) (x y : E) : ℝ :=
  if 0 < c.M then precisionFloor (effectiveSettings c)
    (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) deltaY
  else zeroPrecisionFloor getter c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY x (effectiveY c x y)

noncomputable def allGetterBudget (getter : E × ℝ → Answer E)
    (c : Settings) (x y : E) : ℕ :=
  if 0 < c.M then 2 * fuel (effectiveSettings c)
    (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) x (effectiveY c x y) + 5
  else 3

noncomputable def allATSCalls (getter : E × ℝ → Answer E)
    (c : Settings) (deltaY : ℝ) (x y : E) : ℕ :=
  if 0 < c.M then (FangqingHysteresis.execute
    (classifiedTrial getter (effectiveSettings c)
      (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) deltaY x (effectiveY c x y))
    (searchProgram (effectiveSettings c)
      (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) x (effectiveY c x y))).2
  else 1

noncomputable def allATSLogBound (getter : E × ℝ → Answer E)
    (c : Settings) (x y : E) : ℝ :=
  if 0 < c.M then 3 + Real.logb 2 (max 1
    ((modulus (effectiveSettings c) (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y))
      x (effectiveY c x y) * (upper (effectiveSettings c) -
        lower (effectiveSettings c) (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)))) /
      ((thresholdHigh (effectiveSettings c) - thresholdLow (effectiveSettings c)) / 2)))
  else 1

def AllValid (g : E → ℝ) (c : Settings) (getter : E × ℝ → Answer E)
    (deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  if 0 < c.M then ActualValid g c getter deltaY x y value
  else match value with
    | .stop w => ‖gradient g w‖ ≤ c.rho
    | .window _ _ _ => False

theorem baseCost_map_actual {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ)
    (f : R → S) (p : GetterProgram Q A R) :
    baseCost getter cost (FangqingGetterComposition.map f p) = baseCost getter cost p := by
  induction p with
  | pure r => rfl
  | ask q next ih =>
    change cost q + baseCost getter cost (FangqingGetterComposition.map f (next (getter q))) =
      cost q + baseCost getter cost (next (getter q))
    rw [ih]

theorem coupled_search_all_nonnegative_curvatures
    (g : E → ℝ) (c : Settings) (hc : NonnegativeLegal c) (hA : 0 ≤ c.A)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (allCurvatureProgram c deltaY x y)).1 = .found value ∧
      AllValid g c getter deltaY x y value ∧
      (allATSCalls getter c deltaY x y : ℝ) ≤ allATSLogBound getter c x y ∧
      (execute getter (allCurvatureProgram c deltaY x y)).2 ≤ allGetterBudget getter c x y ∧
      0 < allPrecisionFloor getter c deltaY x y ∧
      baseCost getter cost (allCurvatureProgram c deltaY x y) ≤
        logarithmicAtomicBound K (allPrecisionFloor getter c deltaY x y) * allGetterBudget getter c x y := by
  classical
  by_cases hM : 0 < c.M
  · obtain ⟨value, hrun, hvalid, _, hATS, hlog, hcount, hfloor, _, hcost⟩ :=
      coupled_search_from_certified_getters g c (positive_common c hc hM) hA deltaY hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter cost K hK hatomic x y
    have hreal := Nat.cast_le (α := ℝ).mpr hATS
    simp only [Nat.cast_add, Nat.cast_ofNat] at hreal
    have hb : (allATSCalls getter c deltaY x y : ℝ) ≤ allATSLogBound getter c x y := by
      simp only [allATSCalls, allATSLogBound, if_pos hM]
      exact hreal.trans hlog
    exact ⟨value, by simpa only [allCurvatureProgram, if_pos hM] using hrun,
      by simpa only [AllValid, if_pos hM] using hvalid, hb,
      by simpa only [allCurvatureProgram, allGetterBudget, if_pos hM] using hcount,
      by simpa only [allPrecisionFloor, if_pos hM] using hfloor,
      by simpa only [allCurvatureProgram, allPrecisionFloor, allGetterBudget, if_pos hM] using hcost⟩
  · have hM0 : c.M = 0 := le_antisymm (le_of_not_gt hM) hc.M_nonneg
    have hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
      simpa only [hM0] using hHlip
    have hAe : 0 < (effectiveSettings c).A := by
      by_cases hpos : 0 < c.A
      · simpa only [effectiveSettings, if_pos hpos] using hpos
      · simp only [effectiveSettings, if_neg hpos, proxySettings]; norm_num
    obtain ⟨w, hrun, hg, hcount, hfloor, hcost⟩ :=
      zeroProgram_small_gradient_and_logarithmic_cost g c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY
        hc.mu_pos hc.Lg_nonneg hAe hc.sigma_pos hc.sigma_lt_one hc.rho_pos hdeltaY hdeltaYsmall
        hC2 hsc hlip hH0 getter hgetter cost K hK hatomic x (effectiveY c x y)
    refine ⟨.stop w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [allCurvatureProgram, if_neg hM, execute_map, hrun, zeroAsOutcome]
    · simpa only [AllValid, if_neg hM] using hg
    · simp only [allATSCalls, allATSLogBound, if_neg hM, Nat.cast_one, le_refl]
    · simpa only [allCurvatureProgram, allGetterBudget, if_neg hM, execute_map] using hcount
    · simpa only [allPrecisionFloor, if_neg hM] using hfloor
    · simpa only [allCurvatureProgram, allPrecisionFloor, allGetterBudget, if_neg hM,
        baseCost_map_actual, Nat.mul_comm] using hcost

end OriginalCoupledSearchComplete


namespace OriginalTrialQueryGeometry
open OriginalBetaATSTrial
open OriginalTaylorProxStability
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem observable_model_step_norm_bound
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam delta G : ℝ)
    (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (a : Answer E) (hgrad : ‖a.grad - gradient g z‖ ≤ delta)
    (hhess : ‖a.hess - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hdelta : delta ≤ mu / 4) (hG : ‖gradient g z‖ ≤ G) :
    ‖exactStep a.grad a.hess M lam‖ ≤ 2 * (G + delta) / mu := by
  have hcoer : ∀ d : E, mu / 2 * ‖d‖ ^ 2 ≤ inner ℝ (a.hess d) d := by
    intro d
    have hh := CertifiedATS.approximate_hessian_coercive g hC2 mu hsc z a.hess delta hhess hdelta d
    rw [CertifiedATS.sympart_same_quadratic] at hh
    have hn := sq_nonneg ‖d‖
    nlinarith only [hh, hn, hmu]
  have hsize := exactStep_size_bound a.grad a.hess M lam (mu / 2) hM hlam (by positivity) hcoer
  have ha : ‖a.grad‖ ≤ G + delta := by
    have ht := norm_le_norm_sub_add a.grad (gradient g z)
    linarith only [ht, hgrad, hG]
  have hn : 0 ≤ lam⁻¹ * ‖exactStep a.grad a.hess M lam‖ := by positivity
  apply (le_div_iff₀ hmu).mpr
  nlinarith only [hsize, ha, hn]

theorem trial_trace_query_points
    (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) :
    ∀ q ∈ trace getter (trialProgram M lam delta rho deltaY z),
      q.1 = z ∨ q.1 = z + exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam := by
  classical
  intro q hq
  by_cases hs : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simp only [trialProgram, trace, hs, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hq
    exact Or.inl (congrArg Prod.fst hq)
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    by_cases hy : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · simp only [trialProgram, trace, hs, ↓reduceIte, d, hy, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq
      · exact Or.inl (congrArg Prod.fst hq)
      · exact Or.inr (congrArg Prod.fst hq)
    · simp only [trialProgram, trace, hs, ↓reduceIte, d, hy, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq
      · exact Or.inl (congrArg Prod.fst hq)
      · exact Or.inr (congrArg Prod.fst hq)

theorem actual_trial_query_distance_bound
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam delta rho deltaY G Bz : ℝ)
    (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (getter : E × ℝ → Answer E) (z w : E)
    (hgrad : ‖(getter (z, delta)).grad - gradient g z‖ ≤ delta)
    (hhess : ‖(getter (z, delta)).hess - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hdelta : delta ≤ mu / 4) (hG : ‖gradient g z‖ ≤ G) (hcenter : ‖z - w‖ ≤ Bz) :
    ∀ q ∈ trace getter (trialProgram M lam delta rho deltaY z),
      ‖q.1 - w‖ ≤ Bz + 2 * (G + delta) / mu := by
  let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
  have hd : ‖d‖ ≤ 2 * (G + delta) / mu :=
    observable_model_step_norm_bound g hC2 mu M lam delta G hmu hM hlam hsc z _ hgrad hhess hdelta hG
  have hb : 0 ≤ 2 * (G + delta) / mu := (norm_nonneg d).trans hd
  intro q hq
  rcases trial_trace_query_points getter M lam delta rho deltaY z q hq with heq | heq
  · rw [heq]
    exact hcenter.trans (le_add_of_nonneg_right hb)
  · rw [heq]
    have hsplit : z + d - w = (z - w) + d := by abel
    change ‖z + d - w‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hcenter hd)

end OriginalTrialQueryGeometry


namespace OriginalCoupledQueryGeometry
open OriginalBetaATSTrial
open OriginalTaylorProxStability
open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalCoupledBetaSearch
open OriginalCoupledGetterProgram
open OriginalTrialQueryGeometry
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def AllAsks {Reply R : Type*} (P : ℝ → Prop) : FangqingHysteresis.Program Reply R → Prop
  | .pure _ => True
  | .ask b next => P b ∧ ∀ reply, AllAsks P (next reply)

theorem bisect_allAsks_interval {R : Type*} (n : ℕ) (L U l r : ℝ)
    (hL : L ≤ l) (hlr : l ≤ r) (hU : r ≤ U) :
    AllAsks (fun b => b ∈ Set.Icc L U) (FangqingHysteresis.bisect (R := R) n l r) := by
  induction n generalizing l r with
  | zero => exact True.intro
  | succ n ih =>
    change ((l + r) / 2 ∈ Set.Icc L U) ∧ _
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    intro reply
    cases reply with
    | accept v => exact True.intro
    | low => exact ih _ _ (by linarith) (by linarith) hU
    | high => exact ih _ _ hL (by linarith) (by linarith)

theorem search_allAsks_interval (c : Settings) (G : ℝ) (x y : E)
    (hLU : lower c G ≤ upper c) :
    AllAsks (fun b => b ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) (searchProgram c G x y) := by
  change (lower c G ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) ∧ _
  refine ⟨⟨le_rfl, hLU⟩, ?_⟩
  intro left
  cases left with
  | accept v => exact True.intro
  | low | high =>
    change (upper c ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) ∧ _
    refine ⟨⟨hLU, le_rfl⟩, ?_⟩
    intro right
    cases right with
    | accept v => exact True.intro
    | low | high => exact bisect_allAsks_interval _ _ _ _ _ le_rfl hLU le_rfl

theorem trace_bind_actual {Q A R S : Type*} (getter : Q → A)
    (p : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    trace getter (bind p next) = trace getter p ++ trace getter (next (execute getter p).1) := by
  induction p with
  | pure r => rfl
  | ask q cont ih => simp only [FangqingGetterComposition.bind, trace, execute, ih, List.cons_append]

theorem trace_map_actual {Q A R S : Type*} (getter : Q → A)
    (f : R → S) (p : GetterProgram Q A R) : trace getter (FangqingGetterComposition.map f p) = trace getter p := by
  simp only [FangqingGetterComposition.map, trace_bind_actual, trace, List.append_nil]

theorem actual_lower_trace_on_domain {Q A Reply R : Type*}
    (getter : Q → A) (trials : ℝ → GetterProgram Q A Reply)
    (domain : ℝ → Prop) (P : Q → Prop)
    (p : FangqingHysteresis.Program Reply R) (hp : AllAsks domain p)
    (htrials : ∀ b, domain b → ∀ q ∈ trace getter (trials b), P q) :
    ∀ q ∈ trace getter (FangqingGetterComposition.lower trials p), P q := by
  induction p with
  | pure v => simp only [FangqingGetterComposition.lower, trace, List.not_mem_nil, false_implies, implies_true]
  | ask b next ih =>
    intro q hq
    rw [FangqingGetterComposition.lower, trace_bind_actual, List.mem_append] at hq
    rcases hq with hq | hq
    · exact htrials b hp.1 q hq
    · exact ih (execute getter (trials b)).1 (hp.2 _) q hq

noncomputable def queryRadius (c : Settings) (G : ℝ) (x y : E) : ℝ :=
  ‖x - y‖ + 2 * (G + c.mu / 4) / c.mu

theorem positiveProgram_actual_query_ball
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (positiveProgram c deltaY x y),
      ‖q.1 - y‖ ≤ queryRadius c (observedGradientBound getter c x y) x y := by
  let G := observedGradientBound getter c x y
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  have hp := compact_properties c hc G hbound.1
  have ht := precisionFloor_positive c hc G 1 hbound.1 (by norm_num)
  have htol : 0 < tolerance c G :=
    ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : tolerance c G ≤ c.mu / 4 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hG0 : 0 ≤ G := hbound.1
  have hR : 0 ≤ queryRadius c G x y := by
    dsimp [queryRadius]
    have hmu := hc.mu_pos
    positivity
  intro q hq
  change q ∈ trace getter (.ask (y, 1) (fun a =>
    FangqingGetterComposition.lower (trials c (initialBound c x y a) deltaY x y)
      (searchProgram c (initialBound c x y a) x y))) at hq
  simp only [trace, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [sub_self, norm_zero] using hR
  · apply actual_lower_trace_on_domain getter (trials c G deltaY x y)
      (fun b => b ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c))
      (fun q : E × ℝ => ‖q.1 - y‖ ≤ queryRadius c G x y)
      (searchProgram c G x y)
      (search_allAsks_interval c G x y hp.2.2.2.2.2.2.1) _ q hq
    intro b hb r hr
    have hinterval := interval_lambda_bounds c hc G hbound.1 b hb
    have hcenter : ‖center x y b - y‖ ≤ ‖x - y‖ := by
      have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hinterval.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hinterval.2.1.le
    have hG : ‖gradient g (center x y b)‖ ≤ G :=
      (center_gradient_bound g c.Lg hc.Lg_nonneg hlip x y b hinterval.1.le hinterval.2.1.le).trans hbound.2
    have herrors := hgetter (center x y b) (tolerance c G) htol
    have htrace : r ∈ trace getter (trialProgram c.M (lambda c.A b) (tolerance c G)
        c.rho deltaY (center x y b)) := by
      simpa only [trials, mappedTaylorTrial, trace_map_actual] using hr
    have hh := actual_trial_query_distance_bound g hC2 c.mu c.M (lambda c.A b) (tolerance c G)
      c.rho deltaY G ‖x - y‖ hc.mu_pos hc.M_pos.le hinterval.2.2.1 hsc getter
      (center x y b) y herrors.1 herrors.2 hsmall hG hcenter r htrace
    have hfrac : 2 * (G + tolerance c G) / c.mu ≤ 2 * (G + c.mu / 4) / c.mu :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hsmall) (by norm_num)) hc.mu_pos.le
    exact hh.trans (add_le_add le_rfl hfrac)

end OriginalCoupledQueryGeometry


namespace OriginalZeroQueryGeometry
open OriginalBetaATSTrial
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalCoupledBetaAlgebra
open OriginalZeroCurvatureSearch
open OriginalTrialQueryGeometry
open OriginalCoupledQueryGeometry
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem zeroProgram_actual_query_ball
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (zeroProgram mu Lg A sigma rho deltaY x y),
      ‖q.1 - y‖ ≤ ‖x - y‖ + 2 * (observedBound getter Lg x y + mu / 4) / mu := by
  let G := observedBound getter Lg x y
  let b := initialBeta mu Lg A sigma rho x y (getter (y, 1))
  let lam := initialLambda mu Lg A sigma rho x y (getter (y, 1))
  let delta := initialTolerance mu Lg A sigma rho x y (getter (y, 1))
  have hG0 : 0 ≤ G := by dsimp [G, observedBound]; positivity
  have hG : gradientBound g Lg x y ≤ G :=
    gradient_upper_from_certificate g Lg x y _ 1 (hgetter y 1 (by norm_num)).1
  have hH : 0 ≤ largeLambda mu sigma rho G := by dsimp [largeLambda]; positivity
  have hb := betaHigh_properties A (largeLambda mu sigma rho G) hA hH
  have hb0 : 0 < b := by change 0 < betaHigh A (largeLambda mu sigma rho G); linarith only [hb.2.2.1]
  have hb1 : b < 1 := hb.2.2.2.1
  have hlam : 0 < lam := (coupled_weights A b hA hb0 hb1).1
  have hd : 0 < delta := OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 lam lam sigma rho
    hmu hLg (by norm_num) hlam hlam hsigma hrho
  have hsmall : delta ≤ mu / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcenter : ‖center x y b - y‖ ≤ ‖x - y‖ := by
    have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
    exact mul_le_of_le_one_left (norm_nonneg _) hb1.le
  have hgrad : ‖gradient g (center x y b)‖ ≤ G :=
    (center_gradient_bound g Lg hLg hlip x y b hb0.le hb1.le).trans hG
  have herrors := hgetter (center x y b) delta hd
  have hR : 0 ≤ ‖x - y‖ + 2 * (G + mu / 4) / mu := by positivity
  intro q hq
  simp only [zeroProgram, trace, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [sub_self, norm_zero] using hR
  · have hh := actual_trial_query_distance_bound g hC2 mu 0 lam delta rho deltaY G ‖x - y‖
      hmu (by norm_num) hlam hsc getter (center x y b) y herrors.1 herrors.2 hsmall hgrad hcenter q hq
    exact hh.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsmall) (by norm_num)) hmu.le))

end OriginalZeroQueryGeometry

namespace OriginalZeroQueryGeometry
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledSearchComplete
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open OriginalCoupledQueryGeometry
open FangqingGetterComposition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def allQueryRadius (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  let y' := effectiveY c x y
  ‖x - y'‖ + 2 * (observedGradientBound getter (effectiveSettings c) x y' + c.mu / 4) / c.mu

theorem allProgram_actual_query_ball
    (g : E → ℝ) (c : Settings) (hc : NonnegativeLegal c) (deltaY : ℝ)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (allCurvatureProgram c deltaY x y),
      ‖q.1 - effectiveY c x y‖ ≤ allQueryRadius getter c x y := by
  classical
  have hf := effective_fields c
  by_cases hM : 0 < c.M
  · have he := effective_legal c (positive_common c hc hM)
    have hsce : StrongConvexOn (Set.univ : Set E) (effectiveSettings c).mu g := by
      simpa only [hf.1] using hsc
    have hlipe : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ (effectiveSettings c).Lg * ‖z - w‖ := by
      simpa only [hf.2.1] using hlip
    have hh := positiveProgram_actual_query_ball g (effectiveSettings c) he deltaY hC2 hsce hlipe getter hgetter
      x (effectiveY c x y)
    simpa only [allCurvatureProgram, if_pos hM, coupledProgram, queryRadius, allQueryRadius, hf.1] using hh
  · have hAe : 0 < (effectiveSettings c).A := by
      by_cases hpos : 0 < c.A
      · simpa only [effectiveSettings, if_pos hpos] using hpos
      · simp only [effectiveSettings, if_neg hpos, proxySettings]; norm_num
    have hh := zeroProgram_actual_query_ball g c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY
      hc.mu_pos hc.Lg_nonneg hAe hc.sigma_pos hc.sigma_lt_one hc.rho_pos hC2 hsc hlip getter hgetter
      x (effectiveY c x y)
    simpa only [allCurvatureProgram, if_neg hM, trace_map_actual, allQueryRadius,
      OriginalZeroCurvatureSearch.observedBound, observedGradientBound, hf.2.1] using hh

end OriginalZeroQueryGeometry


namespace OriginalDualGetterImplementation
open OriginalSaddleImplicit
open OriginalDualCurvature
open OriginalDualResidualQueryBound
open OriginalBetaATSTrial
open FangqingGetterComposition

noncomputable def liftQuery {Q A R : Type*} : OriginalDualOracleProgram.QueryProgram Q A R → GetterProgram Q A R
  | .pure r => .pure r
  | .ask q next => .ask q (fun a => liftQuery (next a))

theorem execute_liftQuery {Q A R : Type*} (oracle : Q → A)
    (p : OriginalDualOracleProgram.QueryProgram Q A R) :
    OriginalBetaATSTrial.execute oracle (liftQuery p) = OriginalDualOracleProgram.execute oracle p := by
  induction p with
  | pure r => rfl
  | ask q next ih => simp only [liftQuery, OriginalBetaATSTrial.execute, OriginalDualOracleProgram.execute, ih]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def accuracyRadius (L rho eta : ℝ) : ℝ := min 1 (eta / (1 + 3 * L + 4 * rho))

noncomputable def oracleProgram (L rho : ℝ) (x u0 : E) (q : F × ℝ) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Answer F) :=
  FangqingGetterComposition.map
    (fun s : OriginalDualOracleProgram.QueryState E F =>
      ⟨OriginalDualOracleProgram.gradientOutput s, OriginalDualOracleProgram.hessianOutput L s⟩)
    (liftQuery (OriginalDualOracleProgram.simulator L x q.1 u0 (accuracyRadius L rho q.2)))

noncomputable def actualGetter (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) : F × ℝ → Answer F :=
  implementedGetter (OriginalDualOracleProgram.actualOracle J) (oracleProgram L rho x u0)
noncomputable def actualCost (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) : F × ℝ → ℕ :=
  implementedCost (OriginalDualOracleProgram.actualOracle J) (oracleProgram L rho x u0)

theorem actual_getter_accuracy
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (x u0 : E) (y : F) (eta : ℝ) (heta : 0 < eta) :
    ‖(actualGetter J L rho x u0 (y, eta)).grad - gradient (psi J L x) y‖ ≤ eta ∧
    ‖(actualGetter J L rho x u0 (y, eta)).hess - fderiv ℝ (gradient (psi J L x)) y‖ ≤ eta := by
  have hh := OriginalDualOracleProgram.arbitrary_accuracy_simulation J L rho hL hrho hC2 hLip hHess x u0 y eta heta
  simpa only [actualGetter, implementedGetter, oracleProgram, execute_map, execute_liftQuery,
    accuracyRadius] using And.intro hh.2.2.1 hh.2.2.2.1

theorem actual_cost_is_original_bundled_queries
    (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) (q : F × ℝ) :
    actualCost J L rho x u0 q =
      (OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalDualOracleProgram.simulator L x q.1 u0 (accuracyRadius L rho q.2))).2 := by
  simp only [actualCost, implementedCost, oracleProgram, execute_map, execute_liftQuery]

theorem accuracyRadius_positive (L rho eta : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho) (heta : 0 < eta) :
    0 < accuracyRadius L rho eta := by unfold accuracyRadius; positivity

theorem accuracyRadius_mono (L rho floor eta : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho) (hfloor : floor ≤ eta) :
    accuracyRadius L rho floor ≤ accuracyRadius L rho eta := by
  exact min_le_min le_rfl (div_le_div_of_nonneg_right hfloor (by positivity))

noncomputable def queryBallBudget (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E)
    (y0 : F) (B floor : ℝ) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho floor))

theorem actual_cost_on_query_ball_with_precision_floor
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) (B floor eta : ℝ)
    (hfloor : 0 < floor) (hprecision : floor ≤ eta) (hball : ‖y - y0‖ ≤ B) :
    actualCost J L rho x u0 (y, eta) ≤ queryBallBudget J L rho x u0 y0 B floor := by
  have hf := accuracyRadius_positive L rho floor hL hrho hfloor
  have he := accuracyRadius_positive L rho eta hL hrho (hfloor.trans_le hprecision)
  have hb : 0 ≤ B := (norm_nonneg _).trans hball
  have hobs : 0 ≤ observedRadius J L x u0 y0 := by unfold observedRadius; positivity
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x u0 y y0 B
    (accuracyRadius L rho eta) he hball
  rw [← actual_cost_is_original_bundled_queries J L rho x u0 (y, eta)] at hc
  have heFloor := accuracyRadius_mono L rho floor eta hL hrho hprecision
  have hfrac := div_le_div_of_nonneg_left (show 0 ≤ 3 * (observedRadius J L x u0 y0 + B) by positivity)
    hf heFloor
  have hlog : Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho eta) ≤
      Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho floor) :=
    Real.log_le_log (by positivity) (add_le_add le_rfl hfrac)
  apply (Nat.cast_le (α := ℝ)).mp
  exact (hc.trans (by linarith only [hlog])).trans (Nat.le_ceil _)

end OriginalDualGetterImplementation


namespace OriginalActualDualCoupledSearch
open OriginalSaddleImplicit
open OriginalDualCurvature
open OriginalDualGetterImplementation
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledSearchComplete
open OriginalZeroQueryGeometry
open OriginalCoupledQueryGeometry
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def actualOriginalProgram (L rho : ℝ) (proxCenter uInit : E)
    (c : Settings) (deltaY : ℝ) (X Y : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (FangqingHysteresis.Outcome (Result F)) :=
  primitiveLower (oracleProgram L rho proxCenter uInit) (allCurvatureProgram c deltaY X Y)

noncomputable def originalQueryBudget (J : Joint E F → ℝ) (L rho : ℝ) (proxCenter uInit : E)
    (c : Settings) (deltaY : ℝ) (X Y : F) : ℕ :=
  let getter := actualGetter J L rho proxCenter uInit
  queryBallBudget J L rho proxCenter uInit (effectiveY c X Y) (allQueryRadius getter c X Y)
    (allPrecisionFloor getter c deltaY X Y) * allGetterBudget getter c X Y

theorem coupled_search_with_actual_original_oracle
    (J : Joint E F → ℝ) (L mu rho : ℝ) (hL : 0 < L) (hmu : 0 < mu) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u, y))))
    (proxCenter uInit : E) (c : Settings) (hc : NonnegativeLegal c) (hA : 0 ≤ c.A)
    (hmuField : c.mu = mu) (hLgField : c.Lg = 2 * L) (hMField : c.M = (4 * Real.sqrt 2) * rho)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (X Y : F) :
    let getter := actualGetter J L rho proxCenter uInit
    ∃ value : Result F,
      (OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
        (actualOriginalProgram L rho proxCenter uInit c deltaY X Y)).1 = .found value ∧
      AllValid (psi J L proxCenter) c getter deltaY X Y value ∧
      (allATSCalls getter c deltaY X Y : ℝ) ≤ allATSLogBound getter c X Y ∧
      0 < allPrecisionFloor getter c deltaY X Y ∧
      (OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
        (actualOriginalProgram L rho proxCenter uInit c deltaY X Y)).2 ≤
          originalQueryBudget J L rho proxCenter uInit c deltaY X Y := by
  let getter := actualGetter J L rho proxCenter uInit
  let p := allCurvatureProgram c deltaY X Y
  let floor := allPrecisionFloor getter c deltaY X Y
  let B := allQueryRadius getter c X Y
  let budget := queryBallBudget J L rho proxCenter uInit (effectiveY c X Y) B floor
  have hd := dual_curvature_from_standing_joint J L mu rho hL hmu hrho hC2 hLip hHess hconcave proxCenter
  have hgsc : StrongConvexOn (Set.univ : Set F) c.mu (psi J L proxCenter) := by
    simpa only [hmuField] using hd.2.2.2.2.2.1
  have hglip : ∀ z w : F, ‖gradient (psi J L proxCenter) z - gradient (psi J L proxCenter) w‖ ≤ c.Lg * ‖z - w‖ := by
    simpa only [hLgField] using hd.2.2.2.2.2.2
  have hgHess : ∀ z w : F,
      ‖fderiv ℝ (gradient (psi J L proxCenter)) z - fderiv ℝ (gradient (psi J L proxCenter)) w‖ ≤ c.M * ‖z - w‖ := by
    simpa only [hMField] using hd.2.2.2.2.1
  have hgetter : ∀ z : F, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient (psi J L proxCenter) z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient (psi J L proxCenter)) z‖ ≤ eta :=
    actual_getter_accuracy J L rho hL hrho hC2 hLip hHess proxCenter uInit
  obtain ⟨value, hrun, hvalid, hATS, hcount, hfloor, _⟩ :=
    coupled_search_all_nonnegative_curvatures (psi J L proxCenter) c hc hA deltaY hdeltaY hdeltaYsmall
      hd.1 hgsc hglip hgHess getter hgetter (fun _ => 0) 0 (by norm_num)
      (fun _ _ => Nat.zero_le _) X Y
  have hpoints := allProgram_actual_query_ball (psi J L proxCenter) c hc deltaY hd.1 hgsc hglip getter hgetter X Y
  have hprecisions : ∀ q ∈ trace getter p, floor ≤ q.2 := by
    by_cases hM : 0 < c.M
    · simpa only [p, floor, allCurvatureProgram, if_pos hM, coupledProgram, allPrecisionFloor] using
        OriginalCoupledGetterProgram.positiveProgram_request_precision_floor getter (effectiveSettings c) deltaY X (effectiveY c X Y)
    · simpa only [p, floor, allCurvatureProgram, if_neg hM, trace_map_actual, allPrecisionFloor] using
        OriginalZeroCurvatureSearch.zeroProgram_trace_floor getter c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY X (effectiveY c X Y)
  have hcost : baseCost getter (actualCost J L rho proxCenter uInit) p ≤ budget * (execute getter p).2 := by
    apply baseCost_le_mul_count
    intro q hq
    exact actual_cost_on_query_ball_with_precision_floor J L rho hL hrho hLip proxCenter uInit q.1
      (effectiveY c X Y) B floor q.2 hfloor (hprecisions q hq) (hpoints q hq)
  have hbase := primitiveLower_execution (OriginalDualOracleProgram.actualOracle J)
    (oracleProgram L rho proxCenter uInit) p
  have hbase' : execute (OriginalDualOracleProgram.actualOracle J)
      (actualOriginalProgram L rho proxCenter uInit c deltaY X Y) =
      ((execute getter p).1, baseCost getter (actualCost J L rho proxCenter uInit) p) := hbase
  refine ⟨value, ?_, hvalid, hATS, hfloor, ?_⟩
  · rw [hbase']
    exact hrun
  · rw [hbase']
    exact hcost.trans (Nat.mul_le_mul_left _ hcount)

end OriginalActualDualCoupledSearch


namespace OriginalDualGetterResourceComposition
open OriginalSaddleImplicit
open OriginalDualGetterImplementation
open OriginalBetaATSTrial
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_original_queries_from_realized_geometry {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x uInit : E) (y0 : F) (B floor : ℝ) (hfloor : 0 < floor)
    (p : GetterProgram (F × ℝ) (Answer F) R)
    (hpoint : ∀ q ∈ trace (actualGetter J L rho x uInit) p, ‖q.1 - y0‖ ≤ B)
    (hprecision : ∀ q ∈ trace (actualGetter J L rho x uInit) p, floor ≤ q.2) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).2 ≤
      queryBallBudget J L rho x uInit y0 B floor * (execute (actualGetter J L rho x uInit) p).2 := by
  rw [primitiveLower_execution]
  apply baseCost_le_mul_count
  intro q hq
  exact actual_cost_on_query_ball_with_precision_floor J L rho hL hrho hLip x uInit q.1 y0
    B floor q.2 hfloor (hprecision q hq) (hpoint q hq)

theorem actual_original_queries_from_checked_getter_budget {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x uInit : E) (y0 : F) (B floor : ℝ) (hfloor : 0 < floor)
    (p : GetterProgram (F × ℝ) (Answer F) R) (N : ℕ)
    (hpoint : ∀ q ∈ trace (actualGetter J L rho x uInit) p, ‖q.1 - y0‖ ≤ B)
    (hprecision : ∀ q ∈ trace (actualGetter J L rho x uInit) p, floor ≤ q.2)
    (hcount : (execute (actualGetter J L rho x uInit) p).2 ≤ N) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).2 ≤
      queryBallBudget J L rho x uInit y0 B floor * N :=
  (actual_original_queries_from_realized_geometry J L rho hL hrho hLip x uInit y0 B floor hfloor p
    hpoint hprecision).trans (Nat.mul_le_mul_left _ hcount)

theorem actual_original_program_result {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (x uInit : E)
    (p : GetterProgram (F × ℝ) (Answer F) R) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).1 =
      (execute (actualGetter J L rho x uInit) p).1 := by
  rw [primitiveLower_execution]
  rfl

end OriginalDualGetterResourceComposition


namespace OriginalDualMinimizer

open OriginalSaddleImplicit OriginalPrimalElimination OriginalDualCurvature
open OriginalSaddleTransfer

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem primal_at_actual_dual_saddle
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) :
    primal J L x (vStar (JointSliceRegularity.curry J) L x) =
      uStar (JointSliceRegularity.curry J) L x := by
  let f := JointSliceRegularity.curry J
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx : ∀ y : F, ∀ u u' : E,
      ‖gradient (fun t => f t y) u - gradient (fun t => f t y) u'‖ ≤ L * ‖u - u'‖ :=
    fun y u u' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u u' y
  have hxy : ∀ u : E, ∀ y y' : F,
      ‖gradient (fun t => f t y) u - gradient (fun t => f t y') u‖ ≤ L * ‖y - y'‖ :=
    fun u y y' => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y y'
  apply ((primal_is_unique_minimizer J L hL hJ hLip x (vStar f L x)).2 (uStar f L x) ?_).symm
  intro u
  have hh := OriginalSaddleStability.fixed_dual_quadratic_growth f L mu hL hmu
    hdiffX hdiffY hsc hxx hxy x u
  change f (uStar f L x) (vStar f L x) + L * ‖uStar f L x - x‖ ^ 2 +
      L / 2 * ‖u - uStar f L x‖ ^ 2 ≤ f u (vStar f L x) + L * ‖u - x‖ ^ 2 at hh
  have hn : 0 ≤ L / 2 * ‖u - uStar f L x‖ ^ 2 := by positivity
  linarith only [hh, hn]

theorem actual_dual_saddle_minimizes
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) :
    ∀ y : F, psi J L x (vStar (JointSliceRegularity.curry J) L x) ≤ psi J L x y := by
  intro y
  let f := JointSliceRegularity.curry J
  let u := uStar f L x
  let v := vStar f L x
  have hprimal := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hmin := (primal_is_unique_minimizer J L hL hJ hLip x y).1 u
  have hmax := yStar_maximizes f mu hmu hsc
    (JointSliceRegularity.differentiable_y_slice J hJ) u y
  change f u y ≤ f u v at hmax
  rw [psi_eq_value_at_primal J L hL hJ hLip, psi_eq_value_at_primal J L hL hJ hLip]
  simp only [graph, hprimal]
  change -(f u v + L * ‖u - x‖ ^ 2) ≤
    -(f (primal J L x y) y + L * ‖primal J L x y - x‖ ^ 2)
  linarith only [hmin, hmax]

end OriginalDualMinimizer


namespace FrozenAudit

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

theorem gradient_enlargement
    (g : E → ℝ) (μ δ : ℝ) (y v : E)
    (hμ : 0 < μ) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (herror : ‖v - gradient g y‖ ≤ δ) :
    EpsilonSubgradient g y v (δ ^ 2 / (2 * μ)) := by
  constructor
  · positivity
  · intro w
    have hs := strongConvex_support g μ hsc hdiff y w
    have he : inner ℝ (v - gradient g y) (w - y) ≤ δ * ‖w - y‖ := by
      calc
        inner ℝ (v - gradient g y) (w - y) ≤
            ‖v - gradient g y‖ * ‖w - y‖ := real_inner_le_norm _ _
        _ ≤ δ * ‖w - y‖ :=
          mul_le_mul_of_nonneg_right herror (norm_nonneg _)
    rw [inner_sub_left] at he
    have hden : 0 < 2 * μ := by positivity
    have hcancel : (δ ^ 2 / (2 * μ)) * (2 * μ) = δ ^ 2 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : δ * ‖w - y‖ ≤
        μ / 2 * ‖w - y‖ ^ 2 + δ ^ 2 / (2 * μ) := by
      apply (mul_le_mul_iff_right₀ hμ).mp
      nlinarith only [hcancel, sq_nonneg (μ * ‖w - y‖ - δ)]
    nlinarith only [hs, he, hquad]

end FrozenAudit

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def chosenSlack (gamma sigma0 : ℝ) : ℝ := (sigma0 - gamma) / 4
noncomputable def outputGradientTolerance (mu lam eta r : ℝ) : ℝ :=
  eta * r * min lam⁻¹ (min 1 (mu / lam))

theorem chosenSlack_properties (gamma sigma0 : ℝ) (hgamma : 0 ≤ gamma) (hmargin : gamma < sigma0) :
    0 < chosenSlack gamma sigma0 ∧
    (gamma + chosenSlack gamma sigma0) ^ 2 + (chosenSlack gamma sigma0) ^ 2 < sigma0 ^ 2 := by
  have hg : 0 < sigma0 - gamma := sub_pos.mpr hmargin
  have hp := mul_nonneg hgamma hg.le
  have hs := sq_pos_of_pos hg
  unfold chosenSlack
  constructor <;> nlinarith only [hg, hp, hs]

theorem outputGradientTolerance_positive (mu lam eta r : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (heta : 0 < eta) (hr : 0 < r) :
    0 < outputGradientTolerance mu lam eta r := by
  unfold outputGradientTolerance
  positivity

theorem outputGradientTolerance_suffices (mu lam eta r delta : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (heta : 0 ≤ eta) (hr : 0 ≤ r) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ outputGradientTolerance mu lam eta r) :
    lam * delta ≤ eta * r ∧ lam * delta ^ 2 / mu ≤ eta ^ 2 * r ^ 2 := by
  let c := min lam⁻¹ (min 1 (mu / lam))
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hc1 : c ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc2 : c ≤ mu / lam := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcLam : c * lam ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left lam⁻¹ (min 1 (mu / lam))) hlam.le
    rw [inv_mul_cancel₀ (ne_of_gt hlam)] at hh
    exact hh
  have hsmall' : delta ≤ eta * r * c := hsmall
  have hcsq : c ^ 2 ≤ mu / lam := by
    have hh : c ^ 2 ≤ c := by nlinarith only [hc0.le, hc1]
    exact le_trans hh hc2
  constructor
  · have hm := mul_le_mul_of_nonneg_left hsmall' hlam.le
    have hc := mul_le_mul_of_nonneg_left hcLam (mul_nonneg heta hr)
    nlinarith only [hm, hc]
  · have hsq : delta ^ 2 ≤ (eta * r * c) ^ 2 :=
      (sq_le_sq₀ hdelta (by positivity)).mpr hsmall'
    have hm := mul_le_mul_of_nonneg_left hsq hlam.le
    have hc := (le_div_iff₀ hlam).mp hcsq
    have hcmul := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ eta ^ 2 * r ^ 2)
    apply (div_le_iff₀ hmu).mpr
    nlinarith only [hm, hcmul]

theorem enlarged_gradient_relative_certificate
    (g : E → ℝ) (mu lam gamma eta sigma0 delta : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (hgamma : 0 ≤ gamma) (heta : 0 ≤ eta)
    (hslack : (gamma + eta) ^ 2 + eta ^ 2 ≤ sigma0 ^ 2)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (y d v : E) (herror : ‖v - gradient g y‖ ≤ delta)
    (hres : ‖lam • gradient g y + d‖ ≤ gamma * ‖d‖)
    (htol1 : lam * delta ≤ eta * ‖d‖)
    (htol2 : lam * delta ^ 2 / mu ≤ eta ^ 2 * ‖d‖ ^ 2) :
    FrozenAudit.EpsilonSubgradient g y v (delta ^ 2 / (2 * mu)) ∧
      ‖lam • v + d‖ ^ 2 + 2 * lam * (delta ^ 2 / (2 * mu)) ≤ sigma0 ^ 2 * ‖d‖ ^ 2 := by
  refine ⟨FrozenAudit.gradient_enlargement g mu delta y v hmu hdiff hsc herror, ?_⟩
  have he : lam • v + d = (lam • gradient g y + d) + lam • (v - gradient g y) := by module
  have hn : ‖lam • v + d‖ ≤ (gamma + eta) * ‖d‖ := by
    have ht := norm_add_le (lam • gradient g y + d) (lam • (v - gradient g y))
    rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
    have hm := mul_le_mul_of_nonneg_left herror hlam.le
    nlinarith only [ht, hm, hres, htol1]
  have hsq := (sq_le_sq₀ (norm_nonneg (lam • v + d)) (by positivity : 0 ≤ (gamma + eta) * ‖d‖)).mpr hn
  have hc := mul_le_mul_of_nonneg_right hslack (sq_nonneg ‖d‖)
  have heps : 2 * lam * (delta ^ 2 / (2 * mu)) = lam * delta ^ 2 / mu := by field_simp <;> ring
  rw [heps]
  nlinarith only [hsq, hc, htol2]

theorem small_gradient_contracts_distance (g : E → ℝ) (mu D : ℝ) (hmu : 0 < mu)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (xstar y : E) (hmin : ∀ w : E, g xstar ≤ g w) (hsmall : ‖gradient g y‖ ≤ mu * D / 2) :
    ‖y - xstar‖ ≤ D / 2 := by
  have hs := PacketCore.strongConvex_gradient_distance g mu hmu hsc hdiff xstar hmin y
  nlinarith only [hs, hsmall, hmu]

theorem output_tolerance_lower_bound_from_window (mu M lam eta sigmaL r : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hwindow : sigmaL / M ≤ lam * r) :
    eta * sigmaL * min lam⁻¹ (min 1 (mu / lam)) / (M * lam) ≤
      outputGradientTolerance mu lam eta r := by
  have hc : 0 ≤ min lam⁻¹ (min 1 (mu / lam)) := by positivity
  have hw : sigmaL / (M * lam) ≤ r := by
    apply (div_le_iff₀ (mul_pos hM hlam)).mpr
    have hh := (div_le_iff₀ hM).mp hwindow
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg heta hc)
  dsimp only [outputGradientTolerance]
  convert! hm using 1 <;> field_simp <;> ring

end RobustAHPE

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_search_output_to_relative_tuple
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam sigmaHat sigmaL sigmaU sigma0 : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaL : 0 < sigmaL) (hsigmaU : 0 ≤ sigmaU)
    (hmargin : sigmaHat + sigmaU < sigma0)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindowLower : sigmaL / M ≤ lam * ‖d‖) (hwindowUpper : lam * ‖d‖ ≤ sigmaU / M) :
    let eta := chosenSlack (sigmaHat + sigmaU) sigma0
    let tol := outputGradientTolerance mu lam eta ‖d‖
    0 < tol ∧
    eta * sigmaL * min lam⁻¹ (min 1 (mu / lam)) / (M * lam) ≤ tol ∧
    (∀ v : E, ‖v - gradient g (z + d)‖ ≤ tol →
      FrozenAudit.EpsilonSubgradient g (z + d) v (tol ^ 2 / (2 * mu)) ∧
      ‖lam • v + d‖ ^ 2 + 2 * lam * (tol ^ 2 / (2 * mu)) ≤ sigma0 ^ 2 * ‖d‖ ^ 2 ∧
      sigmaL / M ≤ lam * ‖d‖) := by
  dsimp only
  have hgamma : 0 ≤ sigmaHat + sigmaU := add_nonneg hsigmaHat hsigmaU
  have heta := chosenSlack_properties (sigmaHat + sigmaU) sigma0 hgamma hmargin
  have hd : 0 < ‖d‖ := by
    by_contra hf
    have hz : ‖d‖ = 0 := le_antisymm (le_of_not_gt hf) (norm_nonneg d)
    rw [hz, mul_zero] at hwindowLower
    exact not_le_of_gt (div_pos hsigmaL hM) hwindowLower
  have htol := outputGradientTolerance_positive mu lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖ hmu hlam heta.1 hd
  refine ⟨htol, output_tolerance_lower_bound_from_window mu M lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL ‖d‖ hmu hM hlam heta.1.le hwindowLower, ?_⟩
  intro v hv
  have hacc := outputGradientTolerance_suffices mu lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖
    (outputGradientTolerance mu lam (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖)
    hmu hlam heta.1.le (norm_nonneg d) htol.le le_rfl
  have hres := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindowUpper
  have hr := enlarged_gradient_relative_certificate g mu lam (sigmaHat + sigmaU)
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigma0
    (outputGradientTolerance mu lam (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖)
    hmu hlam hgamma heta.1.le heta.2.le (hC2.differentiable (by norm_num)) hsc
    (z + d) d v hv hres hacc.1 hacc.2
  exact ⟨hr.1, hr.2, hwindowLower⟩

end RobustAHPE

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def globalMinimizer (g : E → ℝ) : E :=
  Classical.epsilon (fun z => ∀ w : E, g z ≤ g w)

theorem globalMinimizer_is_actual [FiniteDimensional ℝ E]
    (g : E → ℝ) (mu : ℝ) (hmu : 0 < mu) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g) :
    ∀ w : E, g (globalMinimizer g) ≤ g w := by
  have hex : ∃ z : E, ∀ w : E, g z ≤ g w := by
    obtain ⟨z, hz⟩ := PacketCore.exists_inner_maximizer_finiteDimensional g mu 0 0 0 0
      hmu (by simpa using hsc) hdiff (0 : E)
    exact ⟨z, fun w => by simpa [PacketCore.saddleValue] using hz w⟩
  exact Classical.epsilon_spec hex

theorem globalMinimizer_unique [FiniteDimensional ℝ E]
    (g : E → ℝ) (mu : ℝ) (hmu : 0 < mu) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g) (y : E) (hy : ∀ w : E, g y ≤ g w) :
    y = globalMinimizer g := by
  have hz := globalMinimizer_is_actual g mu hmu hdiff hsc
  have hzero := PacketCore.gradient_eq_zero_at_global_min g (globalMinimizer g) hz
  have hs := PacketCore.strongConvex_support g mu hsc hdiff (globalMinimizer g) y
  rw [hzero, inner_zero_left, add_zero] at hs
  have hym := hy (globalMinimizer g)
  have hsq : ‖y - globalMinimizer g‖ ^ 2 ≤ 0 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < mu / 2)).mp
    nlinarith only [hs, hym]
  have hn : ‖y - globalMinimizer g‖ = 0 := by
    nlinarith only [hsq, norm_nonneg (y - globalMinimizer g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem small_gradient_actual_minimizer_contract [FiniteDimensional ℝ E]
    (g : E → ℝ) (mu D : ℝ) (hmu : 0 < mu) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (y : E) (hsmall : ‖gradient g y‖ ≤ mu * D / 2) :
    ‖y - globalMinimizer g‖ ≤ D / 2 :=
  small_gradient_contracts_distance g mu D hmu hdiff hsc (globalMinimizer g) y
    (globalMinimizer_is_actual g mu hmu hdiff hsc) hsmall

end RobustAHPE

namespace RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def uniformOutputGradientTolerance (mu M lamHi eta sigmaL : ℝ) : ℝ :=
  eta * sigmaL * min lamHi⁻¹ (min 1 (mu / lamHi)) / (M * lamHi)

theorem uniformOutputGradientTolerance_positive (mu M lamHi eta sigmaL : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hHi : 0 < lamHi) (heta : 0 < eta) (hL : 0 < sigmaL) :
    0 < uniformOutputGradientTolerance mu M lamHi eta sigmaL := by
  unfold uniformOutputGradientTolerance
  positivity

theorem output_tolerance_coefficient_antitone (mu lam lamHi : ℝ)
    (hmu : 0 ≤ mu) (hlam : 0 < lam) (hbound : lam ≤ lamHi) :
    min lamHi⁻¹ (min 1 (mu / lamHi)) ≤ min lam⁻¹ (min 1 (mu / lam)) := by
  exact min_le_min (inv_anti₀ hlam hbound)
    (min_le_min le_rfl (div_le_div_of_nonneg_left hmu hlam hbound))

theorem uniform_output_tolerance_le_actual (mu M lam lamHi eta sigmaL r : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (heta : 0 ≤ eta) (hL : 0 ≤ sigmaL)
    (hbound : lam ≤ lamHi) (hwindow : sigmaL / M ≤ lam * r) :
    uniformOutputGradientTolerance mu M lamHi eta sigmaL ≤ outputGradientTolerance mu lam eta r := by
  have hHi : 0 < lamHi := lt_of_lt_of_le hlam hbound
  have hc := output_tolerance_coefficient_antitone mu lam lamHi hmu.le hlam hbound
  have hcHi : 0 ≤ min lamHi⁻¹ (min 1 (mu / lamHi)) := by positivity
  have htop := output_tolerance_lower_bound_from_window mu M lam eta sigmaL r hmu hM hlam heta hwindow
  unfold uniformOutputGradientTolerance
  calc
    eta * sigmaL * min lamHi⁻¹ (min 1 (mu / lamHi)) / (M * lamHi)
      ≤ eta * sigmaL * min lamHi⁻¹ (min 1 (mu / lamHi)) / (M * lam) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hM hlam)
          (mul_le_mul_of_nonneg_left hbound hM.le)
    _ ≤ eta * sigmaL * min lam⁻¹ (min 1 (mu / lam)) / (M * lam) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (mul_nonneg heta hL)) (by positivity)
    _ ≤ outputGradientTolerance mu lam eta r := htop

theorem actual_search_output_to_uniform_relative_tuple
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam lamHi sigmaHat sigmaL sigmaU sigma0 : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hlamHi : lam ≤ lamHi)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaL : 0 < sigmaL) (hsigmaU : 0 ≤ sigmaU)
    (hmargin : sigmaHat + sigmaU < sigma0)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindowLower : sigmaL / M ≤ lam * ‖d‖) (hwindowUpper : lam * ‖d‖ ≤ sigmaU / M) :
    let eta := chosenSlack (sigmaHat + sigmaU) sigma0
    let tol := uniformOutputGradientTolerance mu M lamHi eta sigmaL
    0 < tol ∧
    (∀ v : E, ‖v - gradient g (z + d)‖ ≤ tol →
      FrozenAudit.EpsilonSubgradient g (z + d) v (tol ^ 2 / (2 * mu)) ∧
      ‖lam • v + d‖ ^ 2 + 2 * lam * (tol ^ 2 / (2 * mu)) ≤ sigma0 ^ 2 * ‖d‖ ^ 2 ∧
      sigmaL / M ≤ lam * ‖d‖) := by
  dsimp only
  have hgamma : 0 ≤ sigmaHat + sigmaU := add_nonneg hsigmaHat hsigmaU
  have heta := chosenSlack_properties (sigmaHat + sigmaU) sigma0 hgamma hmargin
  have hHi : 0 < lamHi := lt_of_lt_of_le hlam hlamHi
  have htol := uniformOutputGradientTolerance_positive mu M lamHi
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL hmu hM hHi heta.1 hsigmaL
  have hbound := uniform_output_tolerance_le_actual mu M lam lamHi
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL ‖d‖ hmu hM hlam heta.1.le hsigmaL.le hlamHi hwindowLower
  refine ⟨htol, ?_⟩
  intro v hv
  have hacc := outputGradientTolerance_suffices mu lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖
    (uniformOutputGradientTolerance mu M lamHi (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL)
    hmu hlam heta.1.le (norm_nonneg d) htol.le hbound
  have hres := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindowUpper
  have hr := enlarged_gradient_relative_certificate g mu lam (sigmaHat + sigmaU)
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigma0
    (uniformOutputGradientTolerance mu M lamHi (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL)
    hmu hlam hgamma heta.1.le heta.2.le (hC2.differentiable (by norm_num)) hsc
    (z + d) d v hv hres hacc.1 hacc.2
  exact ⟨hr.1, hr.2, hwindowLower⟩

end RobustAHPE


namespace OriginalCertifiedCoupledAHPE

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

noncomputable def effective (c : Settings) : Settings :=
  if c.A = 0 then proxySettings c else c

noncomputable def effectiveY {E : Type*} (c : Settings) (x y : E) : E :=
  if c.A = 0 then x else y

theorem effective_mu (c : Settings) : (effective c).mu = c.mu := by
  unfold effective
  split_ifs <;> rfl

theorem effective_Lg (c : Settings) : (effective c).Lg = c.Lg := by
  unfold effective
  split_ifs <;> rfl

theorem effective_M (c : Settings) : (effective c).M = c.M := by
  unfold effective
  split_ifs <;> rfl

theorem effective_sigma (c : Settings) : (effective c).sigma = c.sigma := by
  unfold effective
  split_ifs <;> rfl

theorem effective_low (c : Settings) : (effective c).sigmaLow = c.sigmaLow := by
  unfold effective
  split_ifs <;> rfl

theorem effective_up (c : Settings) : (effective c).sigmaUp = c.sigmaUp := by
  unfold effective
  split_ifs <;> rfl

theorem effective_rho (c : Settings) : (effective c).rho = c.rho := by
  unfold effective
  split_ifs <;> rfl

theorem effective_legal (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A) : Legal (effective c) := by
  unfold effective
  split_ifs with hzero
  · exact proxy_legal c hc
  · exact positive_legal c hc (lt_of_le_of_ne hA (Ne.symm hzero))

noncomputable def outputTolerance (c : Settings) (sigma0 : ℝ) : ℝ :=
  RobustAHPE.uniformOutputGradientTolerance c.mu c.M (lambdaMax c)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow

noncomputable def outputQueryPrecision (c : Settings) (sigma0 : ℝ) : ℝ :=
  min (c.rho / 8) (outputTolerance c sigma0)

theorem outputTolerance_positive (c : Settings) (hc : Legal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0) : 0 < outputTolerance c sigma0 := by
  have hup : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hslack := RobustAHPE.chosenSlack_properties (c.sigma + c.sigmaUp) sigma0
    (add_nonneg hc.sigma_pos.le hup.le) hmargin
  have hp := compact_properties c hc 0 (by norm_num)
  exact RobustAHPE.uniformOutputGradientTolerance_positive c.mu c.M (lambdaMax c)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
    hc.mu_pos hc.M_pos hp.2.2.2.2.2.2.2.2 hslack.1 hc.low_pos

theorem outputQueryPrecision_positive (c : Settings) (hc : Legal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0) : 0 < outputQueryPrecision c sigma0 :=
  lt_min (by exact div_pos hc.rho_pos (by norm_num)) (outputTolerance_positive c hc sigma0 hmargin)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def program (c : Settings) (sigma0 : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  positiveProgram (effective c) (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y)

noncomputable def actualLambda (c : Settings) (b : ℝ) : ℝ := lambda (effective c).A b
noncomputable def actualWeight (c : Settings) (b : ℝ) : ℝ :=
  (actualLambda c b + Real.sqrt (actualLambda c b ^ 2 + 4 * actualLambda c b * c.A)) / 2
noncomputable def actualCenter (c : Settings) (x y : E) (b : ℝ) : E :=
  center x (effectiveY c x y) b

noncomputable def getterBound (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  observedGradientBound getter (effective c) x (effectiveY c x y)

noncomputable def queryFloor (getter : E × ℝ → Answer E) (c : Settings)
    (sigma0 : ℝ) (x y : E) : ℝ :=
  precisionFloor (effective c) (getterBound getter c x y) (outputQueryPrecision (effective c) sigma0)

noncomputable def trialFuel (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℕ :=
  fuel (effective c) (getterBound getter c x y) x (effectiveY c x y)

theorem actual_coupled_center (c : Settings) (hA : 0 ≤ c.A) (x y : E) (b : ℝ)
    (hb : 0 < b) (hb1 : b < 1) :
    0 < actualLambda c b ∧ 0 < actualWeight c b ∧ 0 < c.A + actualWeight c b ∧
      actualCenter c x y b =
        (c.A / (c.A + actualWeight c b)) • y +
          (actualWeight c b / (c.A + actualWeight c b)) • x := by
  by_cases hzero : c.A = 0
  · have hpos : 0 < actualLambda c b := by
      simpa only [actualLambda, effective, if_pos hzero, proxySettings] using
        (coupled_weights 1 b (by norm_num) hb hb1).1
    have hw : actualWeight c b = actualLambda c b := by
      simpa only [actualWeight, hzero] using (zero_weight_first_step (actualLambda c b) hpos x y).1
    have hc : actualCenter c x y b = x := by
      simp only [actualCenter, effectiveY, if_pos hzero]
      exact center_same x b
    refine ⟨hpos, by rwa [hw], by simpa only [hzero, zero_add, hw] using hpos, ?_⟩
    rw [hc, hzero, hw]
    exact (zero_weight_first_step (actualLambda c b) hpos x y).2.symm
  · have hApos : 0 < c.A := lt_of_le_of_ne hA (Ne.symm hzero)
    have hlam : actualLambda c b = lambda c.A b := by simp only [actualLambda, effective, if_neg hzero]
    have hw : actualWeight c b = weight c.A b := by
      rw [actualWeight, hlam]
      exact (coupled_square_root_formula c.A b hApos hb hb1).symm
    have hp := coupled_weights c.A b hApos hb hb1
    refine ⟨by rw [hlam]; exact hp.1, by rw [hw]; exact hp.2.1,
      by rw [hw]; exact add_pos hApos hp.2.1, ?_⟩
    rw [hw]
    change center x (effectiveY c x y) b = _
    rw [effectiveY, if_neg hzero]
    exact (coupled_center c.A b hApos hb hb1 x y).symm

noncomputable def ValidOutput (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (x y : E) : Result E → Prop
  | .stop w => ‖w - RobustAHPE.globalMinimizer g‖ ≤ D / 2
  | .window b d aY =>
      0 < actualLambda c b ∧ 0 < actualWeight c b ∧ 0 < c.A + actualWeight c b ∧
      actualCenter c x y b =
        (c.A / (c.A + actualWeight c b)) • y +
          (actualWeight c b / (c.A + actualWeight c b)) • x ∧
      FrozenAudit.EpsilonSubgradient g (actualCenter c x y b + d) aY.grad
        ((outputTolerance (effective c) sigma0) ^ 2 / (2 * c.mu)) ∧
      ‖actualLambda c b • aY.grad + d‖ ^ 2 +
        2 * actualLambda c b * ((outputTolerance (effective c) sigma0) ^ 2 / (2 * c.mu)) ≤
          sigma0 ^ 2 * ‖d‖ ^ 2 ∧
      c.sigmaLow / c.M ≤ actualLambda c b * ‖d‖

theorem valid_search_gives_original_tuple
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (sigma0 D G : ℝ) (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hrho : c.rho = c.mu * D / 2) (hG : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hH : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (x y : E) (value : Result E)
    (hvalid : ValidResult g (effective c) G (outputQueryPrecision (effective c) sigma0)
      x (effectiveY c x y) value) : ValidOutput g c sigma0 D x y value := by
  have he := effective_legal c hc hA
  cases value with
  | stop w =>
    apply RobustAHPE.small_gradient_actual_minimizer_contract g c.mu D hc.mu_pos
      (hC2.differentiable (by norm_num)) hsc w
    simpa only [ValidResult, effective_rho, hrho] using hvalid
  | window b d aY =>
    rcases hvalid with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
    have hbounds := interval_lambda_bounds (effective c) he G hG b hb
    have htuple := RobustAHPE.actual_search_output_to_uniform_relative_tuple g hC2
      (effective c).mu (effective c).M (lambda (effective c).A b) (lambdaMax (effective c))
      (effective c).sigma (effective c).sigmaLow (effective c).sigmaUp sigma0
      he.mu_pos he.M_pos hlam hbounds.2.2.2.2 he.sigma_pos.le he.low_pos
      (he.low_pos.trans he.low_lt_up).le
      (by simpa only [effective_sigma, effective_up] using hmargin)
      (by simpa only [effective_mu] using hsc)
      (by simpa only [effective_M] using hH)
      (center x (effectiveY c x y) b) d hATS hlow hhigh
    have herrTol : ‖aY.grad - gradient g (center x (effectiveY c x y) b + d)‖ ≤
        outputTolerance (effective c) sigma0 :=
      herr.trans (min_le_right _ _)
    have hcert := htuple.2 aY.grad herrTol
    have hcouple := actual_coupled_center c hA x y b hb0 hb1
    exact ⟨hcouple.1, hcouple.2.1, hcouple.2.2.1, hcouple.2.2.2,
      by simpa only [actualCenter, outputTolerance, effective_mu] using hcert.1,
      by simpa only [actualLambda, outputTolerance, effective_mu] using hcert.2.1,
      by simpa only [actualLambda, effective_low, effective_M] using hcert.2.2⟩

end OriginalCertifiedCoupledAHPE

namespace OriginalCertifiedCoupledAHPE
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem original_certified_coupled_ahpe_step
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (sigma0 D : ℝ) (hmargin : c.sigma + c.sigmaUp < sigma0) (hsigma0 : sigma0 < 1)
    (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (program c sigma0 x y)).1 = .found value ∧
      ValidOutput g c sigma0 D x y value ∧
      0 < queryFloor getter c sigma0 x y ∧
      (∀ q ∈ trace getter (program c sigma0 x y), queryFloor getter c sigma0 x y ≤ q.2) ∧
      (execute getter (program c sigma0 x y)).2 ≤ 2 * trialFuel getter c x y + 5 ∧
      baseCost getter cost (program c sigma0 x y) ≤
        logarithmicAtomicBound K (queryFloor getter c sigma0 x y) * (2 * trialFuel getter c x y + 5) ∧
      ((execute getter (program c sigma0 x y)).2 : ℝ) ≤
        7 + 2 * Real.logb 2 (max 1
          ((modulus (effective c) (getterBound getter c x y) x (effectiveY c x y) *
            (upper (effective c) - lower (effective c) (getterBound getter c x y))) /
              ((thresholdHigh (effective c) - thresholdLow (effective c)) / 2))) := by
  have he := effective_legal c hc hA
  have hmarginE : (effective c).sigma + (effective c).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up] using hmargin
  have hprecision := outputQueryPrecision_positive (effective c) he sigma0 hmarginE
  have hbound := observed_bound_is_valid g (effective c) he getter hgetter x (effectiveY c x y)
  obtain ⟨value, hrun, hvalid, hcount⟩ := positiveProgram_success_and_getter_calls g
    (effective c) he (outputQueryPrecision (effective c) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu] using hsc)
    (by simpa only [effective_Lg] using hlip) (by simpa only [effective_M] using hHlip)
    getter hgetter x (effectiveY c x y)
  have hfloor := precisionFloor_positive (effective c) he _ _ hbound.1 hprecision
  have hcost := positiveProgram_logarithmic_base_cost getter cost (effective c)
    (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y) K hK hfloor hatomic hcount
  have hlog := positiveProgram_getter_log_bound getter (effective c)
    (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y) hcount
  refine ⟨value, hrun,
    valid_search_gives_original_tuple g c hc hA sigma0 D _ hmargin hrho hbound.1 hC2 hsc hHlip x y value hvalid,
    hfloor, positiveProgram_request_precision_floor getter (effective c)
      (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y), hcount, hcost, hlog⟩

end OriginalCertifiedCoupledAHPE

namespace OriginalCertifiedCoupledAHPE
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem original_certified_step_actual_base_program
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (sigma0 D : ℝ) (hmargin : c.sigma + c.sigmaUp < sigma0) (hsigma0 : sigma0 < 1)
    (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(implementedGetter baseAnswer oracle (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(implementedGetter baseAnswer oracle (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 →
      (execute baseAnswer (oracle q)).2 ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute baseAnswer (primitiveLower oracle (program c sigma0 x y))).1 = .found value ∧
      ValidOutput g c sigma0 D x y value ∧
      0 < queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y ∧
      (execute baseAnswer (primitiveLower oracle (program c sigma0 x y))).2 ≤
        logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) *
          (2 * trialFuel (implementedGetter baseAnswer oracle) c x y + 5) ∧
      ((execute baseAnswer (primitiveLower oracle (program c sigma0 x y))).2 : ℝ) ≤
        (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) : ℝ) *
          (7 + 2 * Real.logb 2 (max 1
            ((modulus (effective c) (getterBound (implementedGetter baseAnswer oracle) c x y) x (effectiveY c x y) *
              (upper (effective c) - lower (effective c) (getterBound (implementedGetter baseAnswer oracle) c x y))) /
                ((thresholdHigh (effective c) - thresholdLow (effective c)) / 2)))) := by
  obtain ⟨value, hrun, hvalid, hfloor, hprecision, hcount, hcost, hlog⟩ :=
    original_certified_coupled_ahpe_step g c hc hA sigma0 D hmargin hsigma0 hrho hC2 hsc hlip hHlip
      (implementedGetter baseAnswer oracle) hgetter (implementedCost baseAnswer oracle) K hK hatomic x y
  have hlocal := logarithmic_baseCost_bound (implementedGetter baseAnswer oracle)
    (implementedCost baseAnswer oracle) Prod.snd (program c sigma0 x y) K _ hK hfloor hprecision hatomic
  have hcast : (baseCost (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
      (program c sigma0 x y) : ℝ) ≤
        (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) : ℝ) *
          ((execute (implementedGetter baseAnswer oracle) (program c sigma0 x y)).2 : ℝ) := by
    exact_mod_cast hlocal
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (Nat.cast_nonneg (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y)) :
      (0 : ℝ) ≤ (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) : ℝ))
  rw [primitiveLower_execution]
  exact ⟨value, hrun, hvalid, hfloor, hcost, hcast.trans hscaled⟩

end OriginalCertifiedCoupledAHPE


namespace LargeStepAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (g : E → ℝ) (A : ℝ) (x y xstar : E) : ℝ :=
  A * (g y - g xstar) + ‖x - xstar‖ ^ 2 / 2

def EpsilonSubgradient (g : E → ℝ) (y v : E) (eps : ℝ) : Prop :=
  0 ≤ eps ∧ ∀ w : E, g y + inner ℝ v (w - y) - eps ≤ g w

theorem a_formula_properties (A lam : ℝ) (hA : 0 ≤ A) (hlam : 0 < lam) :
    let a := (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2
    0 < a ∧ 0 < A + a ∧ a ^ 2 = lam * (A + a) := by
  dsimp only
  have hrad : 0 ≤ lam ^ 2 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (lam ^ 2 + 4 * lam * A)
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith only [hs]

theorem one_step_potential
    (g : E → ℝ) (Aold Anew a lam sigma eps : ℝ)
    (xold yold xnew ynew z v xstar : E)
    (hAold : 0 ≤ Aold) (hAnew : 0 < Anew) (ha : 0 ≤ a) (hlam : 0 < lam)
    (hAsum : Anew = Aold + a) (hasquare : a ^ 2 = lam * Anew)
    (hz : Anew • z = Aold • yold + a • xold)
    (hx : xnew = xold - a • v)
    (hsubgrad : EpsilonSubgradient g ynew v eps)
    (hrelative : ‖lam • v + (ynew - z)‖ ^ 2 + 2 * lam * eps ≤ sigma ^ 2 * ‖ynew - z‖ ^ 2) :
    potential g Anew xnew ynew xstar ≤ potential g Aold xold yold xstar -
      ((1 - sigma ^ 2) / 2) * (Anew / lam) * ‖ynew - z‖ ^ 2 := by
  have hold := mul_le_mul_of_nonneg_left (hsubgrad.2 yold) hAold
  have hstar := mul_le_mul_of_nonneg_left (hsubgrad.2 xstar) ha
  have hi : Aold * inner ℝ v (yold - ynew) + a * inner ℝ v (xstar - ynew) =
      -Anew * inner ℝ v (ynew - z) - a * inner ℝ v (xold - xstar) := by
    have hh := congrArg (fun t : E => inner ℝ v t) hz
    simp only [inner_smul_right, inner_add_right] at hh
    simp only [inner_sub_right]
    rw [hAsum] at hh ⊢
    nlinarith only [hh]
  have hsupport : Anew * (g ynew - g xstar) ≤
      Aold * (g yold - g xstar) + Anew * eps + Anew * inner ℝ v (ynew - z) +
        a * inner ℝ v (xold - xstar) := by
    rw [hAsum] at hi ⊢
    nlinarith only [hold, hstar, hi]
  have hxnorm : ‖xnew - xstar‖ ^ 2 = ‖xold - xstar‖ ^ 2 -
      2 * a * inner ℝ v (xold - xstar) + a ^ 2 * ‖v‖ ^ 2 := by
    rw [hx]
    have he : xold - a • v - xstar = (xold - xstar) - a • v := by abel
    rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right, real_inner_comm (xold - xstar) v]
    ring
  have hr := hrelative
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hlam,
    mul_pow, real_inner_smul_left] at hr
  have hbase : 2 * lam * eps + 2 * lam * inner ℝ v (ynew - z) + lam ^ 2 * ‖v‖ ^ 2 ≤
      -(1 - sigma ^ 2) * ‖ynew - z‖ ^ 2 := by nlinarith only [hr]
  have hm := mul_le_mul_of_nonneg_left hbase hAnew.le
  have hR : Anew * eps + Anew * inner ℝ v (ynew - z) + (a ^ 2 / 2) * ‖v‖ ^ 2 ≤
      -((1 - sigma ^ 2) / 2) * (Anew / lam) * ‖ynew - z‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * lam)).mp
    convert! hm using 1
    · rw [hasquare]
      ring
    · field_simp
      <;> ring
  dsimp only [potential]
  nlinarith only [hsupport, hxnorm, hR]

end LargeStepAHPE

namespace LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem prefix_parameter_properties
    (A a lam : ℕ → ℝ) (n : ℕ) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k) :
    (∀ k ≤ n, 0 ≤ A k) ∧
    (∀ k < n, 0 < a k ∧ 0 < A (k + 1) ∧ (a k) ^ 2 = lam k * A (k + 1)) := by
  have hAnonneg : ∀ k ≤ n, 0 ≤ A k := by
    intro k
    induction k with
    | zero => intro _; rw [hA0]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hp := a_formula_properties (A k) (lam k) (ih (by omega)) (hlam k hkn)
      dsimp only at hp
      rw [← haformula k hkn] at hp
      rw [hrec k hkn]
      exact hp.2.1.le
  refine ⟨hAnonneg, ?_⟩
  intro k hk
  have hp := a_formula_properties (A k) (lam k) (hAnonneg k (by omega)) (hlam k hk)
  dsimp only at hp
  rw [← haformula k hk] at hp
  rw [hrec k hk]
  exact hp

theorem prefix_energy_balance
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma : ℝ) (xstar : E) (n : ℕ) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2) :
    potential g (A n) (x n) (y n) xstar +
      (1 - sigma ^ 2) / 2 *
        (∑ k ∈ Finset.range n, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) ≤
      potential g (A 0) (x 0) (y 0) xstar := by
  have hp := prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have hstep : ∀ k < n,
      potential g (A (k + 1)) (x (k + 1)) (y (k + 1)) xstar ≤
        potential g (A k) (x k) (y k) xstar -
          (1 - sigma ^ 2) / 2 * ((A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) := by
    intro k hk
    have hpos := hp.2 k hk
    have hcenter : A (k + 1) • z k = A k • y k + a k • x k := by
      rw [hz k hk]
      have h1 : A (k + 1) * (A k / A (k + 1)) = A k := by field_simp [ne_of_gt hpos.2.1]
      have h2 : A (k + 1) * (a k / A (k + 1)) = a k := by field_simp [ne_of_gt hpos.2.1]
      simp only [smul_add, smul_smul, h1, h2]
    have hs := one_step_potential g (A k) (A (k + 1)) (a k) (lam k) sigma (err k)
      (x k) (y k) (x (k + 1)) (y (k + 1)) (z k) (v k) xstar
      (hp.1 k (by omega)) hpos.2.1 hpos.1.le (hlam k hk) (hrec k hk) hpos.2.2
      hcenter (hx k hk) (hsubgrad k hk) (hrelative k hk)
    simpa only [mul_assoc] using hs
  have hpartial : ∀ j ≤ n,
      potential g (A j) (x j) (y j) xstar + (1 - sigma ^ 2) / 2 *
        (∑ k ∈ Finset.range j, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) ≤
        potential g (A 0) (x 0) (y 0) xstar := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjs : j < n := by omega
      have hh := hstep j hjs
      have hi := ih (by omega)
      rw [Finset.sum_range_succ]
      nlinarith only [hh, hi]
  exact hpartial n le_rfl

theorem prefix_energy_and_step_budget
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma D : ℝ) (xstar : E) (n : ℕ) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hmin : ∀ w : E, g xstar ≤ g w) (hD : ‖x 0 - xstar‖ ≤ D) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2) :
    potential g (A n) (x n) (y n) xstar ≤ D ^ 2 / 2 ∧
    2 * A n * (g (y n) - g xstar) ≤ D ^ 2 ∧
    (∑ k ∈ Finset.range n, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) ≤
      D ^ 2 / (1 - sigma ^ 2) := by
  have hp := prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have hb := prefix_energy_balance g A a lam x y z v err sigma xstar n hA0 hlam haformula hrec hz hx hsubgrad hrelative
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  have hP0 : potential g (A 0) (x 0) (y 0) xstar ≤ D ^ 2 / 2 := by
    simp only [potential, hA0, zero_mul, zero_add]
    have hn := norm_nonneg (x 0 - xstar)
    nlinarith only [hD, hn]
  have hPnonneg : 0 ≤ potential g (A n) (x n) (y n) xstar := by
    unfold potential
    exact add_nonneg (mul_nonneg (hp.1 n le_rfl) (sub_nonneg.mpr (hmin _))) (by positivity)
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact mul_nonneg (div_nonneg (hp.2 k hkn).2.1.le (hlam k hkn).le) (sq_nonneg _)
  have hupper : potential g (A n) (x n) (y n) xstar ≤ D ^ 2 / 2 := by
    nlinarith only [hb, hP0, mul_nonneg halpha.le hsum]
  refine ⟨hupper, ?_, ?_⟩
  · dsimp only [potential] at hupper
    have hn := sq_nonneg ‖x n - xstar‖
    nlinarith only [hupper, hn]
  · apply (le_div_iff₀ halpha).mpr
    nlinarith only [hb, hP0, hPnonneg]

end LargeStepAHPE

namespace LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem large_step_ratio_bound (A lam M theta r : ℝ)
    (hA : 0 ≤ A) (hlam : 0 < lam) (hM : 0 < M) (htheta : 0 < theta) (hr : 0 ≤ r)
    (hlarge : theta / M ≤ lam * r) :
    (theta ^ 2 / M ^ 2) * (A / lam ^ 3) ≤ (A / lam) * r ^ 2 := by
  have hs := (div_le_iff₀ hM).mp hlarge
  have hsq : theta ^ 2 ≤ ((lam * r) * M) ^ 2 :=
    (sq_le_sq₀ htheta.le (by positivity)).mpr hs
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ A / (M ^ 2 * lam ^ 3))
  convert! hm using 1 <;> field_simp <;> ring

theorem reciprocal_budget_from_weighted_budget (A lam r : ℕ → ℝ) (n : ℕ)
    (alpha M theta D : ℝ) (halpha : 0 < alpha) (hM : 0 < M) (htheta : 0 < theta)
    (hA : ∀ k < n, 0 ≤ A (k + 1)) (hlam : ∀ k < n, 0 < lam k)
    (hr : ∀ k < n, 0 ≤ r k) (hlarge : ∀ k < n, theta / M ≤ lam k * r k)
    (hbudget : (∑ k ∈ Finset.range n, (A (k + 1) / lam k) * (r k) ^ 2) ≤ D ^ 2 / alpha) :
    (∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3) ≤ M ^ 2 * D ^ 2 / (theta ^ 2 * alpha) := by
  have hsum : (theta ^ 2 / M ^ 2) * (∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3) ≤
      ∑ k ∈ Finset.range n, (A (k + 1) / lam k) * (r k) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact large_step_ratio_bound (A (k + 1)) (lam k) M theta (r k)
      (hA k hkn) (hlam k hkn) hM htheta (hr k hkn) (hlarge k hkn)
  have hh := le_trans hsum hbudget
  apply (le_div_iff₀ (by positivity : 0 < theta ^ 2 * alpha)).mpr
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ M ^ 2 * alpha)
  convert! hm using 1 <;> field_simp <;> ring

end LargeStepAHPE


namespace OriginalAHPEWeightGrowth

open scoped BigOperators

theorem rpow_pow_nat (x p : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x ^ p) ^ n = x ^ (p * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem reciprocal_sixth_moment_bound
    {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) :
    (s.card : ℝ) ^ 7 ≤ (∑ i ∈ s, b i) ^ 6 * ∑ i ∈ s, 1 / (b i) ^ 6 := by
  let f := fun i => (b i) ^ (6 / 7 : ℝ)
  let g := fun i => (b i) ^ (-6 / 7 : ℝ)
  have hpq : Real.HolderConjugate (7 / 6) 7 := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := f) (g := g) (fun i hi => Real.rpow_nonneg (hb i hi).le _)
    (fun i hi => Real.rpow_nonneg (hb i hi).le _)
  have hfg : ∑ i ∈ s, f i * g i = (s.card : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [f, g]
        rw [← Real.rpow_add (hb i hi)]
        norm_num
      _ = _ := by simp
  have hfp : ∑ i ∈ s, (f i) ^ (7 / 6 : ℝ) = ∑ i ∈ s, b i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    rw [← Real.rpow_mul (hb i hi).le]
    norm_num
  have hgp : ∑ i ∈ s, (g i) ^ (7 : ℝ) = ∑ i ∈ s, 1 / (b i) ^ 6 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [g]
    rw [← Real.rpow_mul (hb i hi).le]
    norm_num [Real.rpow_neg, Real.rpow_natCast] <;> rfl
  rw [hfg, hfp, hgp] at hh
  have hexp : (1 : ℝ) / (7 / 6) = 6 / 7 := by norm_num
  rw [hexp] at hh
  have hs : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i hi => (hb i hi).le)
  have ht : 0 ≤ ∑ i ∈ s, 1 / (b i) ^ 6 := by positivity
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (s.card : ℝ)) hh 7
  rw [mul_pow, rpow_pow_nat _ _ hs, rpow_pow_nat _ _ ht] at hpow
  norm_num [Real.rpow_natCast] at hpow
  simpa only [one_div] using hpow

theorem cube_root_increment_bound
    (x y a : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hrec : y = x + a) :
    a / y ^ (2 / 3 : ℝ) ≤ 3 * (y ^ (1 / 3 : ℝ) - x ^ (1 / 3 : ℝ)) := by
  let u := y ^ (1 / 3 : ℝ)
  let v := x ^ (1 / 3 : ℝ)
  have hu : 0 ≤ u := Real.rpow_nonneg hy.le _
  have hv : 0 ≤ v := Real.rpow_nonneg hx _
  have hu3 : u ^ 3 = y := by
    dsimp only [u]
    rw [rpow_pow_nat y _ hy.le]
    norm_num
  have hv3 : v ^ 3 = x := by
    dsimp only [v]
    rw [rpow_pow_nat x _ hx]
    norm_num
  have hu2 : u ^ 2 = y ^ (2 / 3 : ℝ) := by
    dsimp only [u]
    rw [rpow_pow_nat y _ hy.le]
    congr 1
    norm_num
  have hp := mul_nonneg (sq_nonneg (u - v)) (by positivity : 0 ≤ 2 * u + v)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hy _)).mpr
  rw [← hu2]
  change a ≤ 3 * (u - v) * u ^ 2
  nlinarith only [hp, hu3, hv3, hrec]

theorem sum_range_differences (c : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (c (k + 1) - c k)) = c n - c 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sum_weight_bound
    (A a : ℕ → ℝ) (n : ℕ) (hA0 : A 0 = 0)
    (hA : ∀ k ≤ n, 0 ≤ A k)
    (hAp : ∀ k < n, 0 < A (k + 1))
    (hrec : ∀ k < n, A (k + 1) = A k + a k) :
    (∑ k ∈ Finset.range n, a k / (A (k + 1)) ^ (2 / 3 : ℝ)) ≤
      3 * (A n) ^ (1 / 3 : ℝ) := by
  have hsum : (∑ k ∈ Finset.range n, a k / (A (k + 1)) ^ (2 / 3 : ℝ)) ≤
      ∑ k ∈ Finset.range n, 3 * ((A (k + 1)) ^ (1 / 3 : ℝ) - (A k) ^ (1 / 3 : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact cube_root_increment_bound (A k) (A (k + 1)) (a k)
      (hA k (by omega)) (hAp k hkn) (hrec k hkn)
  rw [← Finset.mul_sum] at hsum
  rw [sum_range_differences (fun k => (A k) ^ (1 / 3 : ℝ)) n, hA0] at hsum
  norm_num at hsum
  exact hsum

theorem reciprocal_weight_identity
    (A a lam : ℝ) (hA : 0 < A) (ha : 0 < a) (hlam : 0 < lam)
    (hrel : a ^ 2 = lam * A) :
    1 / (a / A ^ (2 / 3 : ℝ)) ^ 6 = A / lam ^ 3 := by
  have hApow : (A ^ (2 / 3 : ℝ)) ^ 6 = A ^ 4 := by
    rw [rpow_pow_nat A _ hA.le]
    norm_num [Real.rpow_natCast]
  have ha6 : a ^ 6 = lam ^ 3 * A ^ 3 := by
    calc
      a ^ 6 = (a ^ 2) ^ 3 := by ring
      _ = (lam * A) ^ 3 := by rw [hrel]
      _ = _ := by ring
  rw [div_pow, hApow, ha6]
  field_simp
  <;> ring

theorem ahpe_weight_growth_squared
    (A a lam : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hA0 : A 0 = 0) (hA : ∀ k ≤ n, 0 ≤ A k)
    (ha : ∀ k < n, 0 < a k) (hlam : ∀ k < n, 0 < lam k)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hrel : ∀ k < n, (a k) ^ 2 = lam k * A (k + 1))
    (hB : 0 ≤ B)
    (hbudget : ∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3 ≤ B) :
    (n : ℝ) ^ 7 ≤ 3 ^ 6 * B * (A n) ^ 2 := by
  let b := fun k => a k / (A (k + 1)) ^ (2 / 3 : ℝ)
  have hAp : ∀ k < n, 0 < A (k + 1) := by
    intro k hk
    rw [hrec k hk]
    exact add_pos_of_nonneg_of_pos (hA k (by omega)) (ha k hk)
  have hb : ∀ k ∈ Finset.range n, 0 < b k := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    dsimp only [b]
    exact div_pos (ha k hkn) (Real.rpow_pos_of_pos (hAp k hkn) _)
  have hi : (∑ k ∈ Finset.range n, 1 / (b k) ^ 6) =
      ∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact reciprocal_weight_identity (A (k + 1)) (a k) (lam k)
      (hAp k hkn) (ha k hkn) (hlam k hkn) (hrel k hkn)
  have ht : ∑ k ∈ Finset.range n, 1 / (b k) ^ 6 ≤ B := by rwa [hi]
  have hs := sum_weight_bound A a n hA0 hA hAp hrec
  have hs0 : 0 ≤ ∑ k ∈ Finset.range n, b k := Finset.sum_nonneg (fun k hk => (hb k hk).le)
  have hh := reciprocal_sixth_moment_bound (Finset.range n) b hb
  simp only [Finset.card_range] at hh
  have hs6 := pow_le_pow_left₀ hs0 hs 6
  have hr : ((A n) ^ (1 / 3 : ℝ)) ^ 6 = (A n) ^ 2 := by
    rw [rpow_pow_nat _ _ (hA n le_rfl)]
    norm_num [Real.rpow_natCast]
  calc
    (n : ℝ) ^ 7 ≤ (∑ k ∈ Finset.range n, b k) ^ 6 *
        ∑ k ∈ Finset.range n, 1 / (b k) ^ 6 := hh
    _ ≤ (∑ k ∈ Finset.range n, b k) ^ 6 * B :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg hs0 _)
    _ ≤ (3 * (A n) ^ (1 / 3 : ℝ)) ^ 6 * B := mul_le_mul_of_nonneg_right hs6 hB
    _ = 3 ^ 6 * B * (A n) ^ 2 := by rw [mul_pow, hr]; ring

end OriginalAHPEWeightGrowth

namespace LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rateConstant (sigma theta : ℝ) : ℝ :=
  1 + 729 / (4 * theta ^ 2 * (1 - sigma ^ 2))

theorem coarse_square_root_bound (q t K : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hbound : q ^ 2 ≤ K * t ^ 2) : q ≤ (K + 1) * t := by
  by_contra hfail
  have hc : 0 ≤ (K + 1) * t := by positivity
  have hs := (sq_lt_sq₀ hc hq).mpr (lt_of_not_ge hfail)
  have hk : K ≤ (K + 1) ^ 2 := by nlinarith only [sq_nonneg K, hK]
  have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg t)
  rw [mul_pow] at hs
  linarith only [hs, hm, hbound]

theorem gap_rate_from_energy_and_growth
    (G A D M theta sigma : ℝ) (n : ℕ)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 < M) (htheta : 0 < theta)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hn : 1 ≤ n)
    (henergy : 2 * A * G ≤ D ^ 2)
    (hgrowth : (n : ℝ) ^ 7 ≤ 3 ^ 6 * (M ^ 2 * D ^ 2 / (theta ^ 2 * (1 - sigma ^ 2))) * A ^ 2) :
    G ≤ rateConstant sigma theta * M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  have hden : 0 < theta ^ 2 * (1 - sigma ^ 2) := by positivity
  have hE := (sq_le_sq₀ (by positivity : 0 ≤ 2 * A * G) (sq_nonneg D)).mpr henergy
  have hGrowthClear : (theta ^ 2 * (1 - sigma ^ 2)) * (n : ℝ) ^ 7 ≤
      729 * M ^ 2 * D ^ 2 * A ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hgrowth hden.le
    convert! hh using 1 <;> field_simp <;> ring
  have h1 := mul_le_mul_of_nonneg_right hGrowthClear (by positivity : 0 ≤ 4 * G ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 729 * M ^ 2 * D ^ 2)
  have hcombined : 4 * (theta ^ 2 * (1 - sigma ^ 2)) * G ^ 2 * (n : ℝ) ^ 7 ≤
      729 * M ^ 2 * D ^ 6 := by
    nlinarith only [h1, h2]
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hnPow : 0 < (n : ℝ) ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos hnr _
  have hnSq : ((n : ℝ) ^ (7 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (7 / 2 : ℝ)) 2, ← Real.rpow_mul hnr.le]
    norm_num [Real.rpow_natCast]
  let K := 729 / (4 * theta ^ 2 * (1 - sigma ^ 2))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hsq : (G * (n : ℝ) ^ (7 / 2 : ℝ)) ^ 2 ≤ K * (M * D ^ 3) ^ 2 := by
    dsimp only [K]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * theta ^ 2 * (1 - sigma ^ 2))).mpr
    rw [mul_pow, hnSq]
    convert! hcombined using 1 <;> ring
  have hroot := coarse_square_root_bound (G * (n : ℝ) ^ (7 / 2 : ℝ)) (M * D ^ 3) K
    (by positivity) (by positivity) hK hsq
  apply (le_div_iff₀ hnPow).mpr
  convert! hroot using 1 <;> dsimp only [rateConstant, K] <;> ring

theorem large_step_ahpe_convergence
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma theta M D : ℝ) (xstar : E) (n : ℕ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (htheta : 0 < theta) (hM : 0 < M) (hn : 1 ≤ n)
    (hmin : ∀ w : E, g xstar ≤ g w) (hD : ‖x 0 - xstar‖ ≤ D) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2)
    (hlarge : ∀ k < n, theta / M ≤ lam k * ‖y (k + 1) - z k‖) :
    g (y n) - g xstar ≤ rateConstant sigma theta * M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  have hp := prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have he := prefix_energy_and_step_budget g A a lam x y z v err sigma D xstar n
    hsigma0 hsigma1 hmin hD hA0 hlam haformula hrec hz hx hsubgrad hrelative
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  have hb := reciprocal_budget_from_weighted_budget A lam (fun k => ‖y (k + 1) - z k‖) n
    (1 - sigma ^ 2) M theta D halpha hM htheta (fun k hk => (hp.2 k hk).2.1.le)
    hlam (fun k _ => norm_nonneg _) hlarge he.2.2
  have hg := OriginalAHPEWeightGrowth.ahpe_weight_growth_squared A a lam n
    (M ^ 2 * D ^ 2 / (theta ^ 2 * (1 - sigma ^ 2))) hA0 hp.1
    (fun k hk => (hp.2 k hk).1) hlam hrec (fun k hk => (hp.2 k hk).2.2) (by positivity) hb
  exact gap_rate_from_energy_and_growth (g (y n) - g xstar) (A n) D M theta sigma n
    (sub_nonneg.mpr (hmin _)) (hp.1 n le_rfl) (le_trans (norm_nonneg _) hD) hM htheta
    hsigma0 hsigma1 hn he.2.1 hg

end LargeStepAHPE

namespace LargeStepAHPE

theorem rateConstant_positive (sigma theta : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (htheta : 0 < theta) :
    0 < rateConstant sigma theta := by
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  unfold rateConstant
  positivity

end LargeStepAHPE

namespace LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def solutionSet (g : E → ℝ) : Set E := {w | ∀ u : E, g w ≤ g u}

theorem solutionSet_isClosed (g : E → ℝ)
    (hclosed : IsClosed {p : E × ℝ | g p.1 ≤ p.2}) : IsClosed (solutionSet g) := by
  have hlower : LowerSemicontinuous g := lowerSemicontinuous_iff_isClosed_epigraph.mpr hclosed
  have he : solutionSet g = ⋂ u : E, {w : E | g w ≤ g u} := by
    ext w
    simp only [solutionSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter (fun u => hlower.isClosed_preimage (g u))

theorem original_large_step_ahpe_blackbox
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma theta M D : ℝ) (xstar : E) (n : ℕ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (htheta : 0 < theta) (hM : 0 < M) (hn : 1 ≤ n)
    (hclosed : IsClosed {p : E × ℝ | g p.1 ≤ p.2})
    (hconvex : ConvexOn ℝ (Set.univ : Set E) g)
    (hmin : ∀ w : E, g xstar ≤ g w)
    (hD : Metric.infDist (x 0) (solutionSet g) ≤ D) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2)
    (hlarge : ∀ k < n, theta / M ≤ lam k * ‖y (k + 1) - z k‖) :
    g (y n) - g xstar ≤ rateConstant sigma theta * M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  have hne : (solutionSet g).Nonempty := ⟨xstar, hmin⟩
  obtain ⟨w, hw, hdistance⟩ := (solutionSet_isClosed g hclosed).exists_infDist_eq_dist hne (x 0)
  have hDpoint : ‖x 0 - w‖ ≤ D := by
    have he : ‖x 0 - w‖ = Metric.infDist (x 0) (solutionSet g) := by
      simpa only [dist_eq_norm] using hdistance.symm
    rw [he]
    exact hD
  have hminw : ∀ u : E, g w ≤ g u := hw
  have hvalue : g w = g xstar := le_antisymm (hminw xstar) (hmin w)
  have hr := large_step_ahpe_convergence g A a lam x y z v err sigma theta M D w n
    hsigma0 hsigma1 htheta hM hn hminw hDpoint hA0 hlam haformula hrec hz hx hsubgrad hrelative hlarge
  rw [hvalue] at hr
  exact hr

end LargeStepAHPE


namespace OriginalSecondOrderCount

noncomputable def iterations (C M D mu : ℝ) : ℕ :=
  max 1 (Nat.ceil ((8 * C * M * D / mu) ^ (2 / 7 : ℝ)))

theorem rounded_iteration_properties (C M D mu : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D) (hmu : 0 < mu) :
    1 ≤ iterations C M D mu ∧
    (iterations C M D mu : ℝ) ≤ 1 + (8 * C) ^ (2 / 7 : ℝ) * (M * D / mu) ^ (2 / 7 : ℝ) ∧
    8 * C * M * D / mu ≤ (iterations C M D mu : ℝ) ^ (7 / 2 : ℝ) := by
  let x := 8 * C * M * D / mu
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hr : 0 ≤ x ^ (2 / 7 : ℝ) := Real.rpow_nonneg hx _
  have hceil := (Nat.ceil_lt_add_one hr).le
  have hroot : x ^ (2 / 7 : ℝ) ≤ (iterations C M D mu : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 (Nat.ceil (x ^ (2 / 7 : ℝ))))
  have hupper : (iterations C M D mu : ℝ) ≤ 1 + x ^ (2 / 7 : ℝ) := by
    unfold iterations
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith only [hr]
    · linarith only [hceil]
  have hfactor : x ^ (2 / 7 : ℝ) =
      (8 * C) ^ (2 / 7 : ℝ) * (M * D / mu) ^ (2 / 7 : ℝ) := by
    have he : x = (8 * C) * (M * D / mu) := by dsimp only [x]; ring
    rw [he, Real.mul_rpow (by positivity) (by positivity)]
  have hpower := Real.rpow_le_rpow hr hroot (by norm_num : (0 : ℝ) ≤ 7 / 2)
  rw [← Real.rpow_mul hx] at hpower
  norm_num only [show (2 / 7 : ℝ) * (7 / 2) = 1 by norm_num, Real.rpow_one] at hpower
  refine ⟨le_max_left _ _, ?_, hpower⟩
  rw [hfactor] at hupper
  exact hupper

theorem contraction_gap_budget (C M D mu : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D) (hmu : 0 < mu) :
    C * M * D ^ 3 / (iterations C M D mu : ℝ) ^ (7 / 2 : ℝ) ≤ mu * D ^ 2 / 8 := by
  have hp := rounded_iteration_properties C M D mu hC hM hD hmu
  have hn : (0 : ℝ) < (iterations C M D mu : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hp.1
  have hnPow : 0 < (iterations C M D mu : ℝ) ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  have hm := (div_le_iff₀ hmu).mp hp.2.2
  have hDs := mul_le_mul_of_nonneg_right hm (sq_nonneg D)
  apply (div_le_iff₀ hnPow).mpr
  nlinarith only [hDs]

theorem distance_from_contracted_gap (mu D r G : ℝ)
    (hmu : 0 < mu) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hlower : mu / 2 * r ^ 2 ≤ G) (hgap : G ≤ mu * D ^ 2 / 8) :
    r ≤ D / 2 := by
  have hs : r ^ 2 ≤ (D / 2) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hmu).mp
    nlinarith only [hlower, hgap]
  exact (sq_le_sq₀ hr (by positivity)).mp hs

end OriginalSecondOrderCount


namespace OriginalRobustTrajectory

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure State (E : Type*) where
  weight : ℝ
  x : E
  y : E

noncomputable def settingsAt (c : Settings) (s : State E) : Settings := {c with A := s.weight}
noncomputable def stepProgram (c : Settings) (sigma0 : ℝ) (s : State E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  OriginalCertifiedCoupledAHPE.program (settingsAt c s) sigma0 s.x s.y

noncomputable def nextWindow (c : Settings) (s : State E) (b : ℝ) (d : E) (aY : Answer E) : State E :=
  ⟨s.weight + actualWeight (settingsAt c s) b,
    s.x - actualWeight (settingsAt c s) b • aY.grad,
    actualCenter (settingsAt c s) s.x s.y b + d⟩

noncomputable def advanceValue (c : Settings) (s : State E) : FangqingHysteresis.Outcome (Result E) → State E
  | .found (.window b d aY) => nextWindow c s b d aY
  | _ => s

noncomputable def choice (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) :
    FangqingHysteresis.Outcome (Result E) := (execute getter (stepProgram c sigma0 s)).1

noncomputable def advance (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) : State E :=
  advanceValue c s (choice getter c sigma0 s)

noncomputable def states (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : State E :=
  (advance getter c sigma0)^[k] s

theorem states_zero (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) :
    states getter c sigma0 s 0 = s := rfl

theorem states_succ (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) :
    states getter c sigma0 s (k + 1) = advance getter c sigma0 (states getter c sigma0 s k) :=
  Function.iterate_succ_apply' _ _ _

theorem states_shift (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) :
    states getter c sigma0 s (k + 1) = states getter c sigma0 (advance getter c sigma0 s) k :=
  Function.iterate_succ_apply _ _ _

inductive Outcome (E : Type*) where
  | stop (point : E)
  | finished (state : State E)
  | failure

noncomputable def loopProgram (c : Settings) (sigma0 : ℝ) : ℕ → State E → GetterProgram (E × ℝ) (Answer E) (Outcome E)
  | 0, s => .pure (.finished s)
  | n + 1, s => bind (stepProgram c sigma0 s) (fun result => match result with
      | .found (.stop w) => .pure (.stop w)
      | .found (.window b d aY) => loopProgram c sigma0 n (nextWindow c s b d aY)
      | .bracket _ _ => .pure .failure)

def WindowPrefix (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (n : ℕ) : Prop :=
  ∀ k < n, ∃ b d aY, choice getter c sigma0 (states getter c sigma0 s k) = .found (.window b d aY)

theorem settingsAt_common (c : Settings) (hc : CommonLegal c) (s : State E) : CommonLegal (settingsAt c s) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

theorem actual_step_is_valid
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 D : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0) (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (s : State E) (hs : 0 ≤ s.weight) :
    ∃ value : Result E, choice getter c sigma0 s = .found value ∧
      ValidOutput g (settingsAt c s) sigma0 D s.x s.y value := by
  let cs := settingsAt c s
  have hcs := settingsAt_common c hc s
  have he := effective_legal cs hcs hs
  have hmarginE : (effective cs).sigma + (effective cs).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up, cs, settingsAt] using hmargin
  have hprecision := outputQueryPrecision_positive (effective cs) he sigma0 hmarginE
  have hbound := OriginalCoupledBetaSearch.observed_bound_is_valid g (effective cs) he getter hgetter s.x (effectiveY cs s.x s.y)
  obtain ⟨value, hrun, hvalid, hcount⟩ := OriginalCoupledGetterProgram.positiveProgram_success_and_getter_calls g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu, cs, settingsAt] using hsc)
    (by simpa only [effective_Lg, cs, settingsAt] using hlip) (by simpa only [effective_M, cs, settingsAt] using hHlip)
    getter hgetter s.x (effectiveY cs s.x s.y)
  exact ⟨value, hrun, valid_search_gives_original_tuple g cs hcs hs sigma0 D _ hmargin hrho
    hbound.1 hC2 hsc hHlip s.x s.y value hvalid⟩

theorem all_states_nonnegative
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (s : State E) (hs : 0 ≤ s.weight) : ∀ k, 0 ≤ (states getter c sigma0 s k).weight := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [states_succ]
    obtain ⟨value, hv, hvalid⟩ := hstep _ ih
    cases value with
    | stop w => simpa only [advance, hv, advanceValue] using ih
    | window b d aY =>
      exact (by simpa only [advance, hv, advanceValue, nextWindow, settingsAt] using hvalid.2.2.1.le)

def LoopInvariant (g : E → ℝ) (getter : E × ℝ → Answer E) (c : Settings)
    (sigma0 D : ℝ) (s : State E) (n : ℕ) : Outcome E → Prop
  | .stop w => ‖w - RobustAHPE.globalMinimizer g‖ ≤ D / 2
  | .finished final => final = states getter c sigma0 s n ∧ WindowPrefix getter c sigma0 s n
  | .failure => False

theorem loop_actual_execution_prefix
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (n : ℕ) (s : State E) (hs : 0 ≤ s.weight) :
    LoopInvariant g getter c sigma0 D s n (execute getter (loopProgram c sigma0 n s)).1 := by
  induction n generalizing s with
  | zero => exact ⟨rfl, by intro k hk; omega⟩
  | succ n ih =>
    obtain ⟨value, hvalue, hvalid⟩ := hstep s hs
    have hrun := execute_bind getter (stepProgram c sigma0 s)
      (fun result => match result with
        | .found (.stop w) => GetterProgram.pure (.stop w)
        | .found (.window b d aY) => loopProgram c sigma0 n (nextWindow c s b d aY)
        | .bracket _ _ => GetterProgram.pure .failure)
    change (execute getter (stepProgram c sigma0 s)).1 = .found value at hvalue
    cases value with
    | stop w =>
      simpa only [loopProgram, execute_bind, hvalue, execute, LoopInvariant, ValidOutput] using hvalid
    | window b d aY =>
      have hnext : 0 ≤ (nextWindow c s b d aY).weight := hvalid.2.2.1.le
      have hi := ih (nextWindow c s b d aY) hnext
      have hadv : advance getter c sigma0 s = nextWindow c s b d aY := by
        unfold advance choice
        rw [hvalue]
        rfl
      simp only [loopProgram, execute_bind, hvalue] at hi ⊢
      cases hout : (execute getter (loopProgram c sigma0 n (nextWindow c s b d aY))).1 with
      | failure => simpa only [hout, LoopInvariant] using hi
      | stop w => simpa only [hout, LoopInvariant] using hi
      | finished final =>
        simp only [hout, LoopInvariant] at hi ⊢
        refine ⟨by rw [states_shift, hadv]; exact hi.1, ?_⟩
        intro k hk
        cases k with
        | zero => exact ⟨b, d, aY, hvalue⟩
        | succ k =>
          rw [states_shift, hadv]
          exact hi.2 k (by omega)

end OriginalRobustTrajectory

namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure Frame (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  beta : ℝ
  displacement : E
  answer : Answer E

noncomputable def record : FangqingHysteresis.Outcome (Result E) → Frame E
  | .found (.window b d aY) => ⟨b, d, aY⟩
  | _ => ⟨0, 0, ⟨0, 0⟩⟩

noncomputable def frames (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : Frame E :=
  record (choice getter c sigma0 (states getter c sigma0 s k))

noncomputable def weights (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  (states getter c sigma0 s k).weight
noncomputable def increments (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  actualWeight (settingsAt c (states getter c sigma0 s k)) (frames getter c sigma0 s k).beta
noncomputable def lambdas (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  actualLambda (settingsAt c (states getter c sigma0 s k)) (frames getter c sigma0 s k).beta
noncomputable def xpoints (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  (states getter c sigma0 s k).x
noncomputable def ypoints (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  (states getter c sigma0 s k).y
noncomputable def centers (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  actualCenter (settingsAt c (states getter c sigma0 s k)) (states getter c sigma0 s k).x
    (states getter c sigma0 s k).y (frames getter c sigma0 s k).beta
noncomputable def vectors (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  (frames getter c sigma0 s k).answer.grad
noncomputable def errors (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  outputTolerance (effective (settingsAt c (states getter c sigma0 s k))) sigma0 ^ 2 / (2 * c.mu)

theorem actual_prefix_is_ahpe
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (s : State E) (hs : 0 ≤ s.weight) (n : ℕ) (hp : WindowPrefix getter c sigma0 s n) :
    ∀ k < n,
      0 < lambdas getter c sigma0 s k ∧
      increments getter c sigma0 s k =
        (lambdas getter c sigma0 s k + Real.sqrt (lambdas getter c sigma0 s k ^ 2 +
          4 * lambdas getter c sigma0 s k * weights getter c sigma0 s k)) / 2 ∧
      weights getter c sigma0 s (k + 1) = weights getter c sigma0 s k + increments getter c sigma0 s k ∧
      centers getter c sigma0 s k =
        (weights getter c sigma0 s k / weights getter c sigma0 s (k + 1)) • ypoints getter c sigma0 s k +
          (increments getter c sigma0 s k / weights getter c sigma0 s (k + 1)) • xpoints getter c sigma0 s k ∧
      xpoints getter c sigma0 s (k + 1) = xpoints getter c sigma0 s k -
        increments getter c sigma0 s k • vectors getter c sigma0 s k ∧
      LargeStepAHPE.EpsilonSubgradient g (ypoints getter c sigma0 s (k + 1))
        (vectors getter c sigma0 s k) (errors getter c sigma0 s k) ∧
      ‖lambdas getter c sigma0 s k • vectors getter c sigma0 s k +
        (ypoints getter c sigma0 s (k + 1) - centers getter c sigma0 s k)‖ ^ 2 +
          2 * lambdas getter c sigma0 s k * errors getter c sigma0 s k ≤
            sigma0 ^ 2 * ‖ypoints getter c sigma0 s (k + 1) - centers getter c sigma0 s k‖ ^ 2 ∧
      c.sigmaLow / c.M ≤ lambdas getter c sigma0 s k *
        ‖ypoints getter c sigma0 s (k + 1) - centers getter c sigma0 s k‖ := by
  intro k hk
  obtain ⟨b, d, aY, hout⟩ := hp k hk
  obtain ⟨value, hvalue, hvalid⟩ := hstep (states getter c sigma0 s k)
    (all_states_nonnegative g c sigma0 D getter hstep s hs k)
  have heq : value = .window b d aY := FangqingHysteresis.Outcome.found.inj (hvalue.symm.trans hout)
  rw [heq] at hvalid
  rcases hvalid with ⟨hlam, ha, hAnew, hz, hsub, hrel, hlarge⟩
  have hnext : states getter c sigma0 s (k + 1) = nextWindow c (states getter c sigma0 s k) b d aY := by
    rw [states_succ]
    unfold advance
    rw [hout]
    rfl
  simp only [lambdas, increments, weights, centers, xpoints, ypoints, vectors, errors,
    frames, record, hout, hnext, nextWindow, settingsAt, add_sub_cancel_left]
  exact ⟨hlam, rfl, True.intro, hz, True.intro, hsub, hrel, hlarge⟩

end OriginalRobustTrajectory

namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def contractionIterations (c : Settings) (sigma0 D : ℝ) : ℕ :=
  OriginalSecondOrderCount.iterations (LargeStepAHPE.rateConstant sigma0 c.sigmaLow) c.M D c.mu

noncomputable def resultPoint : Outcome E → E
  | .stop w => w
  | .finished s => s.y
  | .failure => 0

theorem actual_prefix_gap_rate
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (hsigma0 : 0 < sigma0) (hsigma1 : sigma0 < 1)
    (htheta : 0 < c.sigmaLow) (hM : 0 < c.M)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (xstar start : E) (hmin : ∀ w : E, g xstar ≤ g w) (hD : ‖start - xstar‖ ≤ D)
    (n : ℕ) (hn : 1 ≤ n) (hp : WindowPrefix getter c sigma0 ⟨0, start, start⟩ n) :
    g (ypoints getter c sigma0 ⟨0, start, start⟩ n) - g xstar ≤
      LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  let initial : State E := ⟨0, start, start⟩
  have hpref := actual_prefix_is_ahpe g c sigma0 D getter hstep initial (by norm_num [initial]) n hp
  exact LargeStepAHPE.large_step_ahpe_convergence g
    (weights getter c sigma0 initial) (increments getter c sigma0 initial) (lambdas getter c sigma0 initial)
    (xpoints getter c sigma0 initial) (ypoints getter c sigma0 initial) (centers getter c sigma0 initial)
    (vectors getter c sigma0 initial) (errors getter c sigma0 initial)
    sigma0 c.sigmaLow c.M D xstar n hsigma0 hsigma1 htheta hM hn hmin hD rfl
    (fun k hk => (hpref k hk).1) (fun k hk => (hpref k hk).2.1)
    (fun k hk => (hpref k hk).2.2.1) (fun k hk => (hpref k hk).2.2.2.1)
    (fun k hk => (hpref k hk).2.2.2.2.1) (fun k hk => (hpref k hk).2.2.2.2.2.1)
    (fun k hk => (hpref k hk).2.2.2.2.2.2.1) (fun k hk => (hpref k hk).2.2.2.2.2.2.2)

theorem actual_finite_second_order_contraction
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 D : ℝ) (hD : 0 < D)
    (hmargin : c.sigma + c.sigmaUp < sigma0) (hsigma1 : sigma0 < 1)
    (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    ‖resultPoint (execute getter (loopProgram c sigma0 (contractionIterations c sigma0 D) ⟨0, start, start⟩)).1 -
        RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      (contractionIterations c sigma0 D : ℝ) ≤
        1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
          (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  have hstep := actual_step_is_valid g c hc sigma0 D hmargin hrho hC2 hsc hlip hHlip getter hgetter
  have hup : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hsigma0 : 0 < sigma0 := lt_trans (add_pos hc.sigma_pos hup) hmargin
  have hC := LargeStepAHPE.rateConstant_positive sigma0 c.sigmaLow hsigma0 hsigma1 hc.low_pos
  have hn := OriginalSecondOrderCount.rounded_iteration_properties
    (LargeStepAHPE.rateConstant sigma0 c.sigmaLow) c.M D c.mu hC.le hc.M_pos.le hD.le hc.mu_pos
  have hrun := loop_actual_execution_prefix g c sigma0 D getter hstep
    (contractionIterations c sigma0 D) ⟨0, start, start⟩ (by norm_num)
  refine ⟨?_, hn.2.1⟩
  generalize hout : (execute getter (loopProgram c sigma0 (contractionIterations c sigma0 D) ⟨0, start, start⟩)).1 = out at hrun ⊢
  cases out with
  | stop w => exact hrun
  | failure => exact False.elim hrun
  | finished final =>
    have hgap := actual_prefix_gap_rate g c sigma0 D hsigma0 hsigma1 hc.low_pos hc.M_pos getter hstep
      (RobustAHPE.globalMinimizer g) start
      (RobustAHPE.globalMinimizer_is_actual g c.mu hc.mu_pos (hC2.differentiable (by norm_num)) hsc)
      hstart (contractionIterations c sigma0 D) hn.1 hrun.2
    have hbudget := OriginalSecondOrderCount.contraction_gap_budget
      (LargeStepAHPE.rateConstant sigma0 c.sigmaLow) c.M D c.mu hC.le hc.M_pos.le hD.le hc.mu_pos
    have hmin := RobustAHPE.globalMinimizer_is_actual g c.mu hc.mu_pos (hC2.differentiable (by norm_num)) hsc
    have hzero := PacketCore.gradient_eq_zero_at_global_min g (RobustAHPE.globalMinimizer g) hmin
    have hlower := PacketCore.strongConvex_support g c.mu hsc (hC2.differentiable (by norm_num))
      (RobustAHPE.globalMinimizer g) final.y
    rw [hzero, inner_zero_left, add_zero] at hlower
    have hfinal : ypoints getter c sigma0 ⟨0, start, start⟩ (contractionIterations c sigma0 D) = final.y :=
      congrArg State.y hrun.1.symm
    rw [hfinal] at hgap
    exact OriginalSecondOrderCount.distance_from_contracted_gap c.mu D ‖final.y - RobustAHPE.globalMinimizer g‖
      (g final.y - g (RobustAHPE.globalMinimizer g)) hc.mu_pos hD.le (norm_nonneg _)
      (by linarith only [hlower]) (hgap.trans hbudget)

end OriginalRobustTrajectory


namespace OriginalCoupledSearchExtended
open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalCoupledBetaSearch
open OriginalBetaATSTrial (Answer TrialResult)
open FangqingHysteresis (Decision Outcome)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def NonterminalGradient (g : E → ℝ) (c : Settings) (x y : E) : Result E → Prop
  | .stop _ => True
  | .window b d _ => c.rho / 2 < ‖gradient g (center x y b + d)‖

def ExtendedValidResult (g : E → ℝ) (c : Settings) (G deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  ValidResult g c G deltaY x y value ∧ NonterminalGradient g c x y value

theorem classified_accept_nonterminal
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    NonterminalGradient g c x y value := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w =>
    simp only [classifiedTrial, hr] at haccept
    have hv := Decision.accept.inj haccept
    rw [← hv]
    rw [hr] at ht
    exact True.intro
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at haccept
      have hv := Decision.accept.inj haccept
      rw [← hv]
      exact ht.2.2
    · simp only [classifiedTrial, hr, if_neg hw] at haccept
      split_ifs at haccept <;> cases haccept

theorem classified_accept_valid_extended
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    ExtendedValidResult g c G deltaY x y value := by
  exact ⟨classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value haccept,
    classified_accept_nonterminal g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value haccept⟩

theorem bisection_after_endpoints_extended
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G)
    (hleft : classifiedTrial getter c G deltaY x y (lower c G) = .low)
    (hright : classifiedTrial getter c G deltaY x y (upper c) = .high) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).1 = .found value ∧
      ExtendedValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).2 ≤ fuel c G x y := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have hK := actual_modulus_spec g c hc G hG0 hC2 hsc hlip hHlip x y hG
  exact FangqingHysteresis.bisection_success_and_calls
    (classifiedTrial getter c G deltaY x y) (betaSize g c.M c.A x y) (ExtendedValidResult g c G deltaY x y)
    (thresholdLow c) (thresholdHigh c) (lower c G) (upper c) (modulus c G x y)
    (threshold_gap c hc) hK.1 hp.2.2.2.2.2.2.1
    (classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL hleft)
    (classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU hright)
    hK.2
    (fun b hb value hv => classified_accept_valid_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value hv)
    (fun b hb hv => classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)
    (fun b hb hv => classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)


theorem positive_search_success_and_calls_extended
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).1 = .found value ∧
      ExtendedValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).2 ≤ fuel c G x y + 2 := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  cases hleft : classifiedTrial getter c G deltaY x y (lower c G) with
  | accept value =>
    refine ⟨value, ?_, ?_, ?_⟩
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
    · exact classified_accept_valid_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL value hleft
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
      omega
  | high => exact False.elim (lower_endpoint_not_high g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y hG hleft)
  | low =>
    cases hright : classifiedTrial getter c G deltaY x y (upper c) with
    | accept value =>
      refine ⟨value, ?_, ?_, ?_⟩
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
      · exact classified_accept_valid_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU value hright
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
        omega
    | low => exact False.elim (upper_endpoint_not_low g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter x y hright)
    | high =>
      obtain ⟨value, hrun, hvalid, hcount⟩ := bisection_after_endpoints_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter x y hG hleft hright
      refine ⟨value, ?_, hvalid, ?_⟩
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright] using hrun
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright, Nat.add_assoc] using Nat.add_le_add_right hcount 2


theorem positiveProgram_found_window_has_nonterminal_gradient
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (d : E) (aY : Answer E)
    (hfound : (OriginalBetaATSTrial.execute getter
      (OriginalCoupledGetterProgram.positiveProgram c deltaY x y)).1 = .found (.window b d aY)) :
    c.rho / 2 < ‖gradient g (center x y b + d)‖ := by
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  obtain ⟨value, hrun, hv, _⟩ := positive_search_success_and_calls_extended g c hc
    (observedGradientBound getter c x y) deltaY hbound.1 hdeltaY hdeltaYsmall
    hC2 hsc hlip hHlip getter hgetter x y hbound.2
  have hp := (OriginalCoupledGetterProgram.positiveProgram_result_and_count getter c deltaY x y).1
  have heq := FangqingHysteresis.Outcome.found.inj ((hp.symm.trans hfound).symm.trans hrun)
  rw [← heq] at hv
  exact hv.2

end OriginalCoupledSearchExtended


namespace OriginalAcceptedLambdaLowerBound
open OriginalTaylorProxStability
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def lambdaFloor (mu M sigma sigmaLow G : ℝ) : ℝ :=
  sigmaLow * mu * (1 - sigma) / (M * (1 + G))

theorem lambdaFloor_positive (mu M sigma sigmaLow G : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hsigma : sigma < 1) (hLow : 0 < sigmaLow) (hG : 0 ≤ G) :
    0 < lambdaFloor mu M sigma sigmaLow G := by dsimp [lambdaFloor]; positivity

theorem accepted_lambda_lower_bound_from_gradient
    (g : E → ℝ) (mu M lam sigma sigmaLow G : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : sigma < 1) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : sigmaLow / M ≤ lam * ‖d‖) :
    lambdaFloor mu M sigma sigmaLow G ≤ lam := by
  have hsize := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) M lam mu
    hM.le hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hn : 0 ≤ lam⁻¹ * ‖actualStep g M z lam‖ := by positivity
  change (mu + lam⁻¹) * ‖actualStep g M z lam‖ ≤ _ at hsize
  have hexact : mu * ‖actualStep g M z lam‖ ≤ G := by nlinarith only [hsize, hG, hn]
  have hbr := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).1
  have hb : (1 - sigma) * ‖d‖ ≤ ‖actualStep g M z lam‖ := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hbr]
  have hnorm : mu * (1 - sigma) * ‖d‖ ≤ G := by
    have hh := mul_le_mul_of_nonneg_left hb hmu.le
    nlinarith only [hh, hexact]
  have hw := (div_le_iff₀ hM).mp hwindow
  have hwm := mul_le_mul_of_nonneg_left hw (show 0 ≤ mu * (1 - sigma) by positivity)
  have hnm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ lam * M by positivity)
  have hsmall : sigmaLow * mu * (1 - sigma) ≤ lam * M * G := by nlinarith only [hwm, hnm]
  unfold lambdaFloor
  apply (div_le_iff₀ (by positivity : 0 < M * (1 + G))).mpr
  have hp : 0 ≤ lam * M := by positivity
  nlinarith only [hsmall, hp]

theorem first_step_lambda_lower_bound_from_actual_minimizer
    (g : E → ℝ) (mu Lg M lam sigma sigmaLow D : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 < M) (hlam : 0 < lam)
    (hsigma : sigma < 1) (hD : 0 ≤ D)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (z zstar d : E) (hmin : ∀ w : E, g zstar ≤ g w) (hdist : ‖z - zstar‖ ≤ D)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : sigmaLow / M ≤ lam * ‖d‖) :
    lambdaFloor mu M sigma sigmaLow (Lg * D) ≤ lam := by
  have hz := PacketCore.gradient_eq_zero_at_global_min g zstar hmin
  have hG : ‖gradient g z‖ ≤ Lg * D := by
    have hh := (hlip z zstar).trans (mul_le_mul_of_nonneg_left hdist hLg)
    simpa only [hz, sub_zero] using hh
  exact accepted_lambda_lower_bound_from_gradient g mu M lam sigma sigmaLow (Lg * D)
    hmu hM hlam hsigma (mul_nonneg hLg hD) hC2 hsc z d hG hATS hwindow

end OriginalAcceptedLambdaLowerBound


namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_window_facts
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (s : State E) (hs : 0 ≤ s.weight) (b : ℝ) (d : E) (aY : Answer E)
    (hout : choice getter c sigma0 s = .found (.window b d aY)) :
    0 < b ∧ b < 1 ∧ 0 < actualLambda (settingsAt c s) b ∧
      c.sigmaLow / c.M ≤ actualLambda (settingsAt c s) b * ‖d‖ ∧
      actualLambda (settingsAt c s) b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖actualLambda (settingsAt c s) b • CertifiedATS.trueVector
        (gradient g (actualCenter (settingsAt c s) s.x s.y b))
        (fderiv ℝ (gradient g) (actualCenter (settingsAt c s) s.x s.y b)) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      c.rho / 2 < ‖gradient g (actualCenter (settingsAt c s) s.x s.y b + d)‖ := by
  let cs := settingsAt c s
  have hcs := settingsAt_common c hc s
  have he := effective_legal cs hcs hs
  have hmarginE : (effective cs).sigma + (effective cs).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up, cs, settingsAt] using hmargin
  have hprecision := outputQueryPrecision_positive (effective cs) he sigma0 hmarginE
  obtain ⟨value, hrun, hv, hcount⟩ := OriginalCoupledGetterProgram.positiveProgram_success_and_getter_calls g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu, cs, settingsAt] using hsc)
    (by simpa only [effective_Lg, cs, settingsAt] using hlip)
    (by simpa only [effective_M, cs, settingsAt] using hHlip)
    getter hgetter s.x (effectiveY cs s.x s.y)
  have hfound : (execute getter (OriginalCoupledGetterProgram.positiveProgram (effective cs)
      (outputQueryPrecision (effective cs) sigma0) s.x (effectiveY cs s.x s.y))).1 = .found (.window b d aY) := hout
  have heq : value = .window b d aY := FangqingHysteresis.Outcome.found.inj (hrun.symm.trans hfound)
  rw [heq] at hv
  have haway := OriginalCoupledSearchExtended.positiveProgram_found_window_has_nonterminal_gradient g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu, cs, settingsAt] using hsc)
    (by simpa only [effective_Lg, cs, settingsAt] using hlip)
    (by simpa only [effective_M, cs, settingsAt] using hHlip)
    getter hgetter s.x (effectiveY cs s.x s.y) b d aY hfound
  rcases hv with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
  refine ⟨hb0, hb1, hlam, ?_, ?_, ?_, ?_⟩
  · simpa only [actualLambda, effective_low, effective_M, cs, settingsAt] using hlow
  · simpa only [actualLambda, effective_up, effective_M, cs, settingsAt] using hhigh
  · simpa only [actualLambda, actualCenter, effective_M, effective_sigma, cs, settingsAt] using hATS
  · simpa only [actualCenter, effective_rho, cs, settingsAt] using haway

noncomputable def lambdaCap (c : Settings) : ℝ :=
  1 + 2 * ((1 + c.sigma + c.sigmaUp) * c.sigmaUp) / (c.M * c.rho)

theorem lambdaCap_positive (c : Settings) (hc : CommonLegal c) : 0 < lambdaCap c := by
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hM := hc.M_pos
  have hrho := hc.rho_pos
  have hsigma := hc.sigma_pos
  unfold lambdaCap
  positivity

theorem actual_window_lambda_cap
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (s : State E) (hs : 0 ≤ s.weight) (b : ℝ) (d : E) (aY : Answer E)
    (hout : choice getter c sigma0 s = .found (.window b d aY)) :
    actualLambda (settingsAt c s) b ≤ lambdaCap c := by
  have h := actual_window_facts g c hc sigma0 hmargin hC2 hsc hlip hHlip getter hgetter s hs b d aY hout
  let lam := actualLambda (settingsAt c s) b
  let K := 2 * ((1 + c.sigma + c.sigmaUp) * c.sigmaUp) / (c.M * c.rho)
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hM := hc.M_pos
  have hrho := hc.rho_pos
  have hsigma := hc.sigma_pos
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlam : 0 < lam := h.2.2.1
  have hend := RobustAHPE.large_lambda_gradient_endpoint g hC2 c.M lam c.sigma c.sigmaUp
    hc.M_pos hlam hc.sigma_pos.le hu.le hHlip
    (actualCenter (settingsAt c s) s.x s.y b) d h.2.2.2.2.2.1 h.2.2.2.2.1
  have he := (le_div_iff₀ (mul_pos hc.M_pos (sq_pos_of_pos hlam))).mp hend
  have haw := mul_lt_mul_of_pos_right h.2.2.2.2.2.2 (mul_pos hc.M_pos (sq_pos_of_pos hlam))
  have hsquare : lam ^ 2 < K := by
    apply (lt_div_iff₀ (mul_pos hc.M_pos hc.rho_pos)).mpr
    nlinarith only [he, haw]
  change lam ≤ 1 + K
  by_cases hsmall : lam ≤ 1
  · linarith only [hsmall, hK]
  · have hlarge : 1 < lam := lt_of_not_ge hsmall
    have hsq : lam ≤ lam ^ 2 := by nlinarith only [hlarge]
    linarith only [hsq, hsquare]

noncomputable def firstWeightFloor (c : Settings) (D : ℝ) : ℝ :=
  OriginalAcceptedLambdaLowerBound.lambdaFloor c.mu c.M c.sigma c.sigmaLow (c.Lg * D)

theorem firstWeightFloor_positive (c : Settings) (hc : CommonLegal c) (D : ℝ) (hD : 0 ≤ D) :
    0 < firstWeightFloor c D :=
  OriginalAcceptedLambdaLowerBound.lambdaFloor_positive c.mu c.M c.sigma c.sigmaLow (c.Lg * D)
    hc.mu_pos hc.M_pos hc.sigma_lt_one hc.low_pos (mul_nonneg hc.Lg_nonneg hD)

theorem actual_first_window_weight_lower
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 D : ℝ) (hD : 0 ≤ D)
    (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (start xstar : E) (hmin : ∀ w : E, g xstar ≤ g w) (hdist : ‖start - xstar‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hout : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY)) :
    firstWeightFloor c D ≤ (states getter c sigma0 ⟨0, start, start⟩ 1).weight := by
  let initial : State E := ⟨0, start, start⟩
  have hf := actual_window_facts g c hc sigma0 hmargin hC2 hsc hlip hHlip getter hgetter initial (by norm_num [initial]) b d aY hout
  have hcenter : actualCenter (settingsAt c initial) start start b = start := by
    unfold actualCenter effectiveY
    split_ifs <;> exact OriginalFirstCoupledStep.center_same start b
  have hATS := hf.2.2.2.2.2.1
  change ‖actualLambda (settingsAt c initial) b • CertifiedATS.trueVector
    (gradient g (actualCenter (settingsAt c initial) start start b))
    (fderiv ℝ (gradient g) (actualCenter (settingsAt c initial) start start b)) c.M d + d‖ ≤ c.sigma * ‖d‖ at hATS
  rw [hcenter] at hATS
  have hell := OriginalAcceptedLambdaLowerBound.first_step_lambda_lower_bound_from_actual_minimizer g
    c.mu c.Lg c.M (actualLambda (settingsAt c initial) b) c.sigma c.sigmaLow D
    hc.mu_pos hc.Lg_nonneg hc.M_pos hf.2.2.1 hc.sigma_lt_one hD hC2 hsc hlip
    start xstar d hmin hdist hATS hf.2.2.2.1
  have hweight : actualWeight (settingsAt c initial) b = actualLambda (settingsAt c initial) b := by
    exact (OriginalCoupledBetaAlgebra.zero_weight_first_step (actualLambda (settingsAt c initial) b)
      hf.2.2.1 start start).1
  rw [states_succ]
  simp only [states_zero, advance, hout, advanceValue, nextWindow, initial, zero_add]
  rw [hweight]
  exact hell

end OriginalRobustTrajectory


namespace FangqingGetterComposition
open OriginalBetaATSTrial

theorem baseCost_bind {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ)
    (p : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    baseCost getter cost (bind p next) =
      baseCost getter cost p + baseCost getter cost (next (execute getter p).1) := by
  induction p with
  | pure r => simp only [bind, baseCost, execute, Nat.zero_add]
  | ask q cont ih => simp only [bind, baseCost, execute, ih, Nat.add_assoc]

end FangqingGetterComposition

namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem loop_actual_weighted_cost_bound
    (getter : E × ℝ → Answer E) (cost : E × ℝ → ℕ) (c : Settings) (sigma0 : ℝ)
    (n C : ℕ) (s : State E)
    (hcost : ∀ k < n, baseCost getter cost (stepProgram c sigma0 (states getter c sigma0 s k)) ≤ C) :
    baseCost getter cost (loopProgram c sigma0 n s) ≤ C * n := by
  induction n generalizing s with
  | zero => simp only [loopProgram, baseCost, Nat.mul_zero, le_refl]
  | succ n ih =>
    have hfirst := hcost 0 (by omega)
    change baseCost getter cost (stepProgram c sigma0 s) ≤ C at hfirst
    rw [loopProgram, baseCost_bind]
    cases hout : (execute getter (stepProgram c sigma0 s)).1 with
    | bracket l r =>
      simp only [baseCost]
      nlinarith only [hfirst]
    | found value =>
      cases value with
      | stop w =>
        simp only [baseCost]
        nlinarith only [hfirst]
      | window b d aY =>
        have hadv : advance getter c sigma0 s = nextWindow c s b d aY := by
          unfold advance choice
          rw [hout]
          rfl
        have ht : ∀ k < n, baseCost getter cost
            (stepProgram c sigma0 (states getter c sigma0 (nextWindow c s b d aY) k)) ≤ C := by
          intro k hk
          have h := hcost (k + 1) (by omega)
          rw [states_shift, hadv] at h
          exact h
        have htail := ih (nextWindow c s b d aY) ht
        nlinarith only [hfirst, htail]

theorem all_state_weights_nondecreasing
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (s : State E) (hs : 0 ≤ s.weight) :
    Monotone (fun k => (states getter c sigma0 s k).weight) := by
  apply monotone_nat_of_le_succ
  intro k
  obtain ⟨value, hv, hvalid⟩ := hstep _ (all_states_nonnegative g c sigma0 D getter hstep s hs k)
  rw [states_succ]
  cases value with
  | stop w => simp only [advance, hv, advanceValue, le_refl]
  | window b d aY =>
    change (states getter c sigma0 s k).weight ≤ _
    simp only [advance, hv, advanceValue, nextWindow]
    exact le_add_of_nonneg_right hvalid.2.1.le

theorem window_energy_decreases
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (hsigma0 : 0 < sigma0) (hsigma1 : sigma0 < 1)
    (s : State E) (hs : 0 ≤ s.weight) (b : ℝ) (d : E) (aY : Answer E)
    (hvalid : ValidOutput g (settingsAt c s) sigma0 D s.x s.y (.window b d aY)) (xstar : E) :
    LargeStepAHPE.potential g (nextWindow c s b d aY).weight (nextWindow c s b d aY).x
      (nextWindow c s b d aY).y xstar ≤ LargeStepAHPE.potential g s.weight s.x s.y xstar := by
  rcases hvalid with ⟨hlam, ha, hAnew, hz, hsub, hrel, hlarge⟩
  let lam := actualLambda (settingsAt c s) b
  let a := actualWeight (settingsAt c s) b
  let z := actualCenter (settingsAt c s) s.x s.y b
  have htotal : 0 < s.weight + a := hAnew
  have hscaled : (s.weight + a) • z = s.weight • s.y + a • s.x := by
    have hcoef1 : (s.weight + a) * (s.weight / (s.weight + a)) = s.weight := by
      field_simp [ne_of_gt htotal]
    have hcoef2 : (s.weight + a) * (a / (s.weight + a)) = a := by
      field_simp [ne_of_gt htotal]
    change z = (s.weight / (s.weight + a)) • s.y + (a / (s.weight + a)) • s.x at hz
    rw [hz, smul_add, smul_smul, smul_smul, hcoef1, hcoef2]
  have haformula : a = (lam + Real.sqrt (lam ^ 2 + 4 * lam * s.weight)) / 2 := rfl
  have hsquare := LargeStepAHPE.a_formula_properties s.weight lam hs hlam
  dsimp only at hsquare
  rw [← haformula] at hsquare
  have hrelative : ‖lam • aY.grad + ((z + d) - z)‖ ^ 2 +
      2 * lam * (outputTolerance (effective (settingsAt c s)) sigma0 ^ 2 / (2 * c.mu)) ≤
        sigma0 ^ 2 * ‖(z + d) - z‖ ^ 2 := by simpa only [add_sub_cancel_left, settingsAt, lam] using hrel
  have hp := LargeStepAHPE.one_step_potential g s.weight (s.weight + a) a lam sigma0
    (outputTolerance (effective (settingsAt c s)) sigma0 ^ 2 / (2 * c.mu))
    s.x s.y (s.x - a • aY.grad) (z + d) z aY.grad xstar hs hAnew ha.le hlam rfl hsquare.2.2
    hscaled rfl hsub hrelative
  have hnonneg : 0 ≤ (1 - sigma0 ^ 2) / 2 * ((s.weight + a) / lam) * ‖(z + d) - z‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by nlinarith only [hsigma0, hsigma1]) (div_nonneg hAnew.le hlam.le)) (sq_nonneg _)
  exact le_trans hp (sub_le_self _ hnonneg)

theorem all_state_energy_bound
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (hsigma0 : 0 < sigma0) (hsigma1 : sigma0 < 1)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (xstar start : E) (hD : ‖start - xstar‖ ≤ D) :
    ∀ k, LargeStepAHPE.potential g (states getter c sigma0 ⟨0, start, start⟩ k).weight
      (states getter c sigma0 ⟨0, start, start⟩ k).x
      (states getter c sigma0 ⟨0, start, start⟩ k).y xstar ≤ D ^ 2 / 2 := by
  intro k
  induction k with
  | zero =>
    dsimp only [states, Function.iterate_zero, id_eq, LargeStepAHPE.potential]
    nlinarith only [hD, norm_nonneg (start - xstar)]
  | succ k ih =>
    have hs := all_states_nonnegative g c sigma0 D getter hstep ⟨0, start, start⟩ (by norm_num) k
    obtain ⟨value, hv, hvalid⟩ := hstep _ hs
    rw [states_succ]
    cases value with
    | stop w => simpa only [advance, hv, advanceValue] using ih
    | window b d aY =>
      have hp := window_energy_decreases g c sigma0 D hsigma0 hsigma1 _ hs b d aY hvalid xstar
      simpa only [advance, hv, advanceValue] using hp.trans ih

theorem x_radius_from_energy (g : E → ℝ) (A D : ℝ) (x y xstar : E)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hmin : ∀ w : E, g xstar ≤ g w)
    (henergy : LargeStepAHPE.potential g A x y xstar ≤ D ^ 2 / 2) : ‖x - xstar‖ ≤ D := by
  have hgap : 0 ≤ g y - g xstar := sub_nonneg.mpr (hmin y)
  have hprod := mul_nonneg hA hgap
  dsimp only [LargeStepAHPE.potential] at henergy
  have hsq : ‖x - xstar‖ ^ 2 ≤ D ^ 2 := by nlinarith only [henergy, hprod]
  exact (sq_le_sq₀ (norm_nonneg _) hD).mp hsq

noncomputable def geometryRadius (mu ell D : ℝ) : ℝ := D * (1 + (mu * ell)⁻¹)

theorem y_radius_from_energy (g : E → ℝ) (mu ell A D : ℝ)
    (hmu : 0 < mu) (hell : 0 < ell) (hA : ell ≤ A) (hD : 0 ≤ D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (x y xstar : E) (hmin : ∀ w : E, g xstar ≤ g w)
    (henergy : LargeStepAHPE.potential g A x y xstar ≤ D ^ 2 / 2) :
    ‖y - xstar‖ ≤ geometryRadius mu ell D := by
  have hg0 := PacketCore.gradient_eq_zero_at_global_min g xstar hmin
  have hlower := PacketCore.strongConvex_support g mu hsc hdiff xstar y
  rw [hg0, inner_zero_left, add_zero] at hlower
  have hm := mul_le_mul_of_nonneg_left hlower hell.le
  have hgap : 0 ≤ g y - g xstar := sub_nonneg.mpr (hmin y)
  have hprod := mul_le_mul_of_nonneg_right hA hgap
  dsimp only [LargeStepAHPE.potential] at henergy
  have hbase : mu * ell * ‖y - xstar‖ ^ 2 ≤ D ^ 2 := by
    nlinarith only [hm, hprod, henergy, sq_nonneg ‖x - xstar‖]
  have ht : 0 < mu * ell := mul_pos hmu hell
  have hinv : 0 < (mu * ell)⁻¹ := inv_pos.mpr ht
  have hid : mu * ell * (geometryRadius mu ell D) ^ 2 =
      D ^ 2 * (mu * ell + 2 + (mu * ell)⁻¹) := by
    unfold geometryRadius
    field_simp
    <;> ring
  have hR : D ≤ geometryRadius mu ell D := by
    unfold geometryRadius
    nlinarith only [hD, mul_nonneg hD hinv.le]
  have htarget : D ^ 2 ≤ mu * ell * (geometryRadius mu ell D) ^ 2 := by
    rw [hid]
    nlinarith only [sq_nonneg D, mul_nonneg (sq_nonneg D) (add_nonneg ht.le hinv.le)]
  have hsq : ‖y - xstar‖ ^ 2 ≤ geometryRadius mu ell D ^ 2 :=
    (mul_le_mul_iff_right₀ ht).mp (hbase.trans htarget)
  exact (sq_le_sq₀ (norm_nonneg _) (hD.trans hR)).mp hsq

end OriginalRobustTrajectory


namespace OriginalAHPEWeightUpper

theorem one_step_weight_upper (lam Lambda A : ℝ) (k : ℕ)
    (hlam : 0 < lam) (hLam : lam ≤ Lambda) (hA : 0 ≤ A)
    (hbound : A ≤ Lambda * (k : ℝ) ^ 2) :
    let a := (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2
    a ≤ Lambda * ((k : ℝ) + 1) ∧
      A + a ≤ Lambda * (((k + 1 : ℕ) : ℝ) ^ 2) := by
  dsimp only
  have hLambda : 0 < Lambda := lt_of_lt_of_le hlam hLam
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hrad : 0 ≤ lam ^ 2 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (lam ^ 2 + 4 * lam * A)
  have hprod := mul_le_mul hLam hbound hA hLambda.le
  have hsq := (sq_le_sq₀ hlam.le hLambda.le).mpr hLam
  have htarget : 0 ≤ Lambda * (2 * (k : ℝ) + 1) := by positivity
  have hradup : lam ^ 2 + 4 * lam * A ≤ (Lambda * (2 * (k : ℝ) + 1)) ^ 2 := by
    nlinarith only [hprod, hsq, mul_nonneg (sq_nonneg Lambda) hk]
  have hroot : Real.sqrt (lam ^ 2 + 4 * lam * A) ≤ Lambda * (2 * (k : ℝ) + 1) := by
    nlinarith only [hs, hn, htarget, hradup]
  have ha : (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2 ≤ Lambda * ((k : ℝ) + 1) := by
    linarith only [hroot, hLam]
  refine ⟨ha, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith only [ha, hbound, mul_nonneg hLambda.le hk]

theorem prefix_weight_upper_bound (A a lam : ℕ → ℝ) (n : ℕ) (Lambda : ℝ)
    (hLambda : 0 < Lambda) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k) (hlamUpper : ∀ k < n, lam k ≤ Lambda)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k) :
    (∀ k ≤ n, A k ≤ Lambda * (k : ℝ) ^ 2) ∧
      (∀ k < n, a k ≤ Lambda * ((k : ℝ) + 1)) := by
  have hp := LargeStepAHPE.prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have hweight : ∀ k ≤ n, A k ≤ Lambda * (k : ℝ) ^ 2 := by
    intro k
    induction k with
    | zero => intro _; norm_num [hA0]
    | succ k ih =>
        intro hk
        have hkn : k < n := by omega
        have hs := one_step_weight_upper (lam k) Lambda (A k) k (hlam k hkn) (hlamUpper k hkn)
          (hp.1 k (by omega)) (ih (by omega))
        dsimp only at hs
        rw [← haformula k hkn, ← hrec k hkn] at hs
        exact hs.2
  refine ⟨hweight, ?_⟩
  intro k hk
  have hs := one_step_weight_upper (lam k) Lambda (A k) k (hlam k hk) (hlamUpper k hk)
    (hp.1 k (by omega)) (hweight k (by omega))
  dsimp only at hs
  rw [← haformula k hk] at hs
  exact hs.1

end OriginalAHPEWeightUpper


namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure Hypotheses (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (getter : E × ℝ → Answer E) : Prop where
  common : CommonLegal c
  D_pos : 0 < D
  margin : c.sigma + c.sigmaUp < sigma0
  sigma_lt_one : sigma0 < 1
  rho_eq : c.rho = c.mu * D / 2
  C2 : ContDiff ℝ 2 g
  strongly_convex : StrongConvexOn (Set.univ : Set E) c.mu g
  gradient_lipschitz : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖
  hessian_lipschitz : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖
  getter_correct : ∀ z : E, ∀ eta : ℝ, 0 < eta →
    ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
    ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta

theorem Hypotheses.sigma_positive {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) : 0 < sigma0 :=
  lt_trans (add_pos H.common.sigma_pos (H.common.low_pos.trans H.common.low_lt_up)) H.margin

theorem Hypotheses.step_valid {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) : ∀ s : State E, 0 ≤ s.weight →
      ∃ value : Result E, choice getter c sigma0 s = .found value ∧
        ValidOutput g (settingsAt c s) sigma0 D s.x s.y value :=
  actual_step_is_valid g c H.common sigma0 D H.margin H.rho_eq H.C2 H.strongly_convex
    H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct

theorem Hypotheses.actual_minimum {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) : ∀ w : E, g (RobustAHPE.globalMinimizer g) ≤ g w :=
  RobustAHPE.globalMinimizer_is_actual g c.mu H.common.mu_pos (H.C2.differentiable (by norm_num)) H.strongly_convex

noncomputable def effectiveWeightFloor (c : Settings) (D : ℝ) : ℝ := min 1 (firstWeightFloor c D)
noncomputable def stateRadius (c : Settings) (D : ℝ) : ℝ := geometryRadius c.mu (firstWeightFloor c D) D
noncomputable def weightCeiling (c : Settings) (n : ℕ) : ℝ := 1 + lambdaCap c * (n : ℝ) ^ 2
noncomputable def observedCeiling (c : Settings) (D : ℝ) : ℝ := 2 + c.Lg * (D + 2 * stateRadius c D)

theorem stateRadius_ge_D (c : Settings) (hc : CommonLegal c) (D : ℝ) (hD : 0 ≤ D) : D ≤ stateRadius c D := by
  have hell := firstWeightFloor_positive c hc D hD
  have hinv : 0 ≤ (c.mu * firstWeightFloor c D)⁻¹ := inv_nonneg.mpr (mul_nonneg hc.mu_pos.le hell.le)
  unfold stateRadius geometryRadius
  nlinarith only [mul_nonneg hD hinv]

theorem actual_state_weight_upper
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E) :
    ∀ k, (states getter c sigma0 ⟨0, start, start⟩ k).weight ≤ lambdaCap c * (k : ℝ) ^ 2 := by
  intro k
  induction k with
  | zero => simp only [states_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, le_refl]
  | succ k ih =>
    let s := states getter c sigma0 ⟨0, start, start⟩ k
    have hs := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
    obtain ⟨value, hv, hvalid⟩ := H.step_valid s hs
    have hvalue := hv
    dsimp only [s] at hvalue
    rw [states_succ]
    cases value with
    | stop w =>
      simp only [advance, hvalue, advanceValue]
      have hm : (k : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        nlinarith only [(show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
      exact ih.trans (mul_le_mul_of_nonneg_left hm (lambdaCap_positive c H.common).le)
    | window b d aY =>
      have hcap := actual_window_lambda_cap g c H.common sigma0 H.margin H.C2 H.strongly_convex
        H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct s hs b d aY hv
      have hup := OriginalAHPEWeightUpper.one_step_weight_upper
        (actualLambda (settingsAt c s) b) (lambdaCap c) s.weight k hvalid.1 hcap hs ih
      dsimp only at hup
      simp only [advance, hvalue, advanceValue, nextWindow]
      exact hup.2

theorem actual_state_geometry_after_first_window
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hfirst : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY)) :
    ∀ k,
      ‖(states getter c sigma0 ⟨0, start, start⟩ k).x - RobustAHPE.globalMinimizer g‖ ≤ D ∧
      ‖(states getter c sigma0 ⟨0, start, start⟩ k).y - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D ∧
      (1 ≤ k → firstWeightFloor c D ≤ (states getter c sigma0 ⟨0, start, start⟩ k).weight) := by
  have hfloor := actual_first_window_weight_lower g c H.common sigma0 D H.D_pos.le H.margin H.C2 H.strongly_convex
    H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct start (RobustAHPE.globalMinimizer g)
    H.actual_minimum hstart b d aY hfirst
  have hmono := all_state_weights_nondecreasing g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num)
  have henergy := all_state_energy_bound g c sigma0 D H.sigma_positive H.sigma_lt_one getter H.step_valid
    (RobustAHPE.globalMinimizer g) start hstart
  have hell := firstWeightFloor_positive c H.common D H.D_pos.le
  intro k
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have hx := x_radius_from_energy g _ D _ _ (RobustAHPE.globalMinimizer g) hA H.D_pos.le H.actual_minimum (henergy k)
  have hweight : 1 ≤ k → firstWeightFloor c D ≤ (states getter c sigma0 ⟨0, start, start⟩ k).weight :=
    fun hk => hfloor.trans (hmono hk)
  refine ⟨hx, ?_, hweight⟩
  cases k with
  | zero => exact hstart.trans (stateRadius_ge_D c H.common D H.D_pos.le)
  | succ k =>
    exact y_radius_from_energy g c.mu (firstWeightFloor c D) _ D H.common.mu_pos hell (hweight (by omega)) H.D_pos.le
      (H.C2.differentiable (by norm_num)) H.strongly_convex _ _ (RobustAHPE.globalMinimizer g) H.actual_minimum (henergy _)

theorem effective_weight_interval
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hfirst : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY))
    (n k : ℕ) (hk : k ≤ n) :
    0 < effectiveWeightFloor c D ∧
      effectiveWeightFloor c D ≤ (effective (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))).A ∧
      (effective (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))).A ≤ weightCeiling c n := by
  have hell := firstWeightFloor_positive c H.common D H.D_pos.le
  have hgeometry := actual_state_geometry_after_first_window H start hstart b d aY hfirst k
  have hupper := actual_state_weight_upper H start k
  have hcap := lambdaCap_positive c H.common
  have hsq : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    apply (sq_le_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg n)).mpr
    exact_mod_cast hk
  refine ⟨lt_min (by norm_num) hell, ?_, ?_⟩
  · unfold effective
    split_ifs with hz
    · exact min_le_left _ _
    · have hkn : 1 ≤ k := by
        by_contra hbad
        have hk0 : k = 0 := by omega
        subst k
        exact hz rfl
      exact (min_le_right _ _).trans (hgeometry.2.2 hkn)
  · unfold effective
    split_ifs
    · change 1 ≤ 1 + lambdaCap c * (n : ℝ) ^ 2
      have hp := mul_nonneg hcap.le (sq_nonneg (n : ℝ))
      linarith only [hp]
    · exact hupper.trans ((mul_le_mul_of_nonneg_left hsq hcap.le).trans (by unfold weightCeiling; linarith))

theorem actual_observed_gradient_upper
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hfirst : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY)) (k : ℕ) :
    0 ≤ getterBound getter (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))
      (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y ∧
    getterBound getter (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))
      (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y ≤ observedCeiling c D := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let w := effectiveY (settingsAt c s) s.x s.y
  have hgeom := actual_state_geometry_after_first_window H start hstart b d aY hfirst k
  have hR := stateRadius_ge_D c H.common D H.D_pos.le
  have hw : ‖w - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D := by
    dsimp only [w, effectiveY]
    split_ifs
    · exact hgeom.1.trans hR
    · exact hgeom.2.1
  have hg0 := PacketCore.gradient_eq_zero_at_global_min g (RobustAHPE.globalMinimizer g) H.actual_minimum
  have hG : ‖gradient g w‖ ≤ c.Lg * stateRadius c D := by
    have hh := (H.gradient_lipschitz w (RobustAHPE.globalMinimizer g)).trans (mul_le_mul_of_nonneg_left hw H.common.Lg_nonneg)
    simpa only [hg0, sub_zero] using hh
  have herr := (H.getter_correct w 1 (by norm_num)).1
  have hnorm := (norm_le_norm_sub_add (getter (w, 1)).grad (gradient g w)).trans (add_le_add herr hG)
  have hxy : ‖s.x - w‖ ≤ D + stateRadius c D :=
    (norm_sub_le_norm_sub_add_norm_sub s.x (RobustAHPE.globalMinimizer g) w).trans
      (add_le_add hgeom.1 (by simpa only [norm_sub_rev] using hw))
  have hproduct := mul_le_mul_of_nonneg_left hxy H.common.Lg_nonneg
  have hLg := H.common.Lg_nonneg
  simp only [getterBound, OriginalCoupledBetaSearch.observedGradientBound, effective_Lg, settingsAt]
  constructor
  · change 0 ≤ ‖(getter (w, 1)).grad‖ + 1 + c.Lg * ‖s.x - w‖
    positivity
  · change ‖(getter (w, 1)).grad‖ + 1 + c.Lg * ‖s.x - w‖ ≤ observedCeiling c D
    unfold observedCeiling
    nlinarith only [hnorm, hproduct]

end OriginalRobustTrajectory

namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def ResourceScene (g : E → ℝ) (getter : E × ℝ → Answer E) (c : Settings)
    (D : ℝ) (n : ℕ) (s : State E) : Prop :=
  0 < effectiveWeightFloor c D ∧
    effectiveWeightFloor c D ≤ (effective (settingsAt c s)).A ∧
    (effective (settingsAt c s)).A ≤ weightCeiling c n ∧
    0 ≤ getterBound getter (settingsAt c s) s.x s.y ∧
    getterBound getter (settingsAt c s) s.x s.y ≤ observedCeiling c D ∧
    ‖s.x - RobustAHPE.globalMinimizer g‖ ≤ D ∧
    ‖s.y - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D

theorem actual_resources_on_stream
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    ∀ k ≤ n, ResourceScene g getter c D n (states getter c sigma0 ⟨0, start, start⟩ k) := by
  let initial : State E := ⟨0, start, start⟩
  obtain ⟨value, hv, hvalid⟩ := H.step_valid initial (by norm_num [initial])
  cases value with
  | window b d aY =>
    intro k hk
    have hA := effective_weight_interval H start hstart b d aY hv n k hk
    have hG := actual_observed_gradient_upper H start hstart b d aY hv k
    have hgeom := actual_state_geometry_after_first_window H start hstart b d aY hv k
    exact ⟨hA.1, hA.2.1, hA.2.2, hG.1, hG.2, hgeom.1, hgeom.2.1⟩
  | stop w =>
    have hadv : advance getter c sigma0 initial = initial := by
      unfold advance
      rw [hv]
      rfl
    have hfixed : ∀ k, states getter c sigma0 initial k = initial := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [states_succ, ih]; exact hadv
    have hell := firstWeightFloor_positive c H.common D H.D_pos.le
    have hR := stateRadius_ge_D c H.common D H.D_pos.le
    have hR0 : 0 ≤ stateRadius c D := H.D_pos.le.trans hR
    have hcap := lambdaCap_positive c H.common
    have hgradzero := PacketCore.gradient_eq_zero_at_global_min g (RobustAHPE.globalMinimizer g) H.actual_minimum
    have hGtrue : ‖gradient g start‖ ≤ c.Lg * D := by
      have h := (H.gradient_lipschitz start (RobustAHPE.globalMinimizer g)).trans
        (mul_le_mul_of_nonneg_left hstart H.common.Lg_nonneg)
      simpa only [hgradzero, sub_zero] using h
    have hnorm := (norm_le_norm_sub_add (getter (start, 1)).grad (gradient g start)).trans
      (add_le_add (H.getter_correct start 1 (by norm_num)).1 hGtrue)
    have hget : getterBound getter (settingsAt c initial) initial.x initial.y = ‖(getter (start, 1)).grad‖ + 1 := by
      simp only [getterBound, OriginalCoupledBetaSearch.observedGradientBound, effective_Lg,
        effectiveY, settingsAt, initial, ite_true, if_pos rfl, sub_self, norm_zero, mul_zero, add_zero]
    have hAeff : (effective (settingsAt c initial)).A = 1 := by
      simp only [effective, settingsAt, initial, ite_true, if_pos rfl, OriginalFirstCoupledStep.proxySettings]
    intro k hk
    change ResourceScene g getter c D n (states getter c sigma0 initial k)
    rw [hfixed]
    refine ⟨lt_min (by norm_num) hell, ?_, ?_, ?_, ?_, hstart, hstart.trans hR⟩
    · rw [hAeff]
      exact min_le_left _ _
    · rw [hAeff]
      change 1 ≤ 1 + lambdaCap c * (n : ℝ) ^ 2
      have hprod := mul_nonneg hcap.le (sq_nonneg (n : ℝ))
      linarith only [hprod]
    · rw [hget]
      positivity
    · rw [hget]
      unfold observedCeiling
      have hprod := mul_nonneg H.common.Lg_nonneg hR0
      nlinarith only [hnorm, hprod]

end OriginalRobustTrajectory


namespace OriginalUniformBetaResources

open OriginalCoupledBetaSearch OriginalBetaSearchEndpoints OriginalBetaATSUniform

noncomputable section

def betaFloor (c : Settings) (Amax Gmax : ℝ) : ℝ :=
  betaLow Amax (lambdaLow c.M c.sigmaLow c.sigma Gmax)

def marginFloor (c : Settings) (Amin : ℝ) : ℝ :=
  highMargin Amin (lambdaHigh c.M c.rho c.sigma c.sigmaUp)

def lambdaFloor (c : Settings) (Amin Amax Gmax : ℝ) : ℝ :=
  Amin * betaFloor c Amax Gmax ^ 2

def lambdaCeiling (c : Settings) (Amax : ℝ) : ℝ :=
  4 * Amax + 8 * (1 + lambdaHigh c.M c.rho c.sigma c.sigmaUp)

theorem endpoint_bounds (c : Settings) (hc : Legal c) (Amin Amax Gmax G : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) :
    0 < betaFloor c Amax Gmax ∧ betaFloor c Amax Gmax ≤ lower c G ∧
    0 < marginFloor c Amin ∧ marginFloor c Amin ≤ margin c ∧
    0 < lambdaFloor c Amin Amax Gmax ∧ lambdaFloor c Amin Amax Gmax ≤ lambdaMin c G ∧
    0 < lambdaCeiling c Amax ∧ lambdaMax c ≤ lambdaCeiling c Amax := by
  have hA := hc.A_pos
  have hM := hc.M_pos
  have hAmax : 0 < Amax := hc.A_pos.trans_le hAhi
  have hGmax : 0 ≤ Gmax := hG.trans hGhi
  let H := lambdaHigh c.M c.rho c.sigma c.sigmaUp
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hH : 0 ≤ H := by
    dsimp only [H, lambdaHigh]
    have hM := hc.M_pos
    have hrho := hc.rho_pos
    have hsigma := hc.sigma_pos
    positivity
  have hell := lambdaLow_positive c.M c.sigmaLow c.sigma Gmax hc.M_pos hc.low_pos hc.sigma_lt_one hGmax
  have hbeta := (betaLow_properties Amax _ hAmax hell.1).1
  have hellMono : lambdaLow c.M c.sigmaLow c.sigma Gmax ≤ lambdaLow c.M c.sigmaLow c.sigma G := by
    unfold lambdaLow
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_left (by
      have hh := hc.low_pos
      have hs := hc.sigma_lt_one
      positivity) (by
        have hh := hc.M_pos
        positivity)
    have hh := mul_le_mul_of_nonneg_left hGhi (by positivity : 0 ≤ 2 * c.M)
    nlinarith only [hh]
  have hbetaBound : betaFloor c Amax Gmax ≤ lower c G := by
    unfold betaFloor lower betaLow
    apply min_le_min le_rfl
    calc
      _ ≤ lambdaLow c.M c.sigmaLow c.sigma Gmax / (4 * (1 + c.A)) :=
        div_le_div_of_nonneg_left hell.1.le (by positivity) (by linarith only [hAhi])
      _ ≤ _ := div_le_div_of_nonneg_right hellMono (by positivity)
  have hmargin : 0 < marginFloor c Amin := by
    unfold marginFloor highMargin
    change 0 < min (1 / 4 : ℝ) (Amin / (8 * (1 + H)))
    positivity
  have hmarginBound : marginFloor c Amin ≤ margin c := by
    unfold marginFloor margin highMargin
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_right hAlo (by change 0 ≤ 8 * (1 + H); positivity)
  have hp := compact_properties c hc G hG
  have hsq := (sq_le_sq₀ hbeta.le hp.1.le).mpr hbetaBound
  have hlambdaFloor : 0 < lambdaFloor c Amin Amax Gmax := by
    unfold lambdaFloor
    exact mul_pos hAmin (sq_pos_of_pos hbeta)
  have hloBound : lambdaFloor c Amin Amax Gmax ≤ lambdaMin c G :=
    mul_le_mul hAlo hsq (sq_nonneg _) hc.A_pos.le
  have hceiling : 0 < lambdaCeiling c Amax := by
    change 0 < 4 * Amax + 8 * (1 + H)
    positivity
  have hmaxBound : lambdaMax c ≤ lambdaCeiling c Amax := by
    unfold lambdaMax margin highMargin
    change c.A / min (1 / 4 : ℝ) (c.A / (8 * (1 + H))) ≤ 4 * Amax + 8 * (1 + H)
    rcases le_total (1 / 4 : ℝ) (c.A / (8 * (1 + H))) with hleft | hright
    · rw [min_eq_left hleft]
      norm_num
      nlinarith only [hAhi, hH]
    · rw [min_eq_right hright]
      have hid : c.A / (c.A / (8 * (1 + H))) = 8 * (1 + H) := by
        field_simp [ne_of_gt hc.A_pos]
      rw [hid]
      linarith only [hAmax]
  exact ⟨hbeta, hbetaBound, hmargin, hmarginBound, hlambdaFloor, hloBound, hceiling, hmaxBound⟩

theorem uniform_tolerance_mono
    (mu Lg M lo up lo' up' sigma rho : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hlo : 0 < lo) (hlole : lo ≤ lo') (hup' : 0 < up') (huple : up' ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    uniformTolerance mu Lg M lo up sigma rho ≤ uniformTolerance mu Lg M lo' up' sigma rho := by
  have hstep := uniformStepFloor_le mu Lg M lo lo' rho hmu hLg hM hlo hlole hrho
  change uniformStepFloor mu Lg M lo rho ≤ uniformStepFloor mu Lg M lo' rho at hstep
  have hstep0 := (uniformStepFloor_positive mu Lg M lo rho hmu hLg hM hlo hrho).le
  have hterm : sigma * uniformStepFloor mu Lg M lo rho / (2 * up) ≤
      sigma * uniformStepFloor mu Lg M lo' rho / (2 * up') := by
    calc
      _ ≤ sigma * uniformStepFloor mu Lg M lo rho / (2 * up') :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [huple])
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hsigma.le) (by positivity)
  have hterm4 : sigma / (2 * up) ≤ sigma / (2 * up') :=
    div_le_div_of_nonneg_left hsigma.le (by positivity) (by linarith only [huple])
  exact min_le_min le_rfl (min_le_min le_rfl (min_le_min hterm hterm4))

def centerPrecisionFloor (c : Settings) (Amin Amax Gmax : ℝ) : ℝ :=
  uniformTolerance c.mu c.Lg c.M (lambdaFloor c Amin Amax Gmax) (lambdaCeiling c Amax) c.sigma c.rho

theorem center_precision_bounds (c : Settings) (hc : Legal c) (Amin Amax Gmax G : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) :
    0 < centerPrecisionFloor c Amin Amax Gmax ∧
      centerPrecisionFloor c Amin Amax Gmax ≤ tolerance c G := by
  have he := endpoint_bounds c hc Amin Amax Gmax G hAmin hAlo hAhi hG hGhi
  have hp := compact_properties c hc G hG
  refine ⟨uniformTolerance_positive c.mu c.Lg c.M _ _ c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le he.2.2.2.2.1 he.2.2.2.2.2.2.1 hc.sigma_pos hc.rho_pos, ?_⟩
  exact uniform_tolerance_mono c.mu c.Lg c.M _ _ _ _ c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le he.2.2.2.2.1 he.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2 he.2.2.2.2.2.2.2 hc.sigma_pos hc.rho_pos

theorem uniform_output_tolerance_antitone (mu M up up' eta sigmaL : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hup' : 0 < up') (huple : up' ≤ up)
    (heta : 0 ≤ eta) (hsigmaL : 0 ≤ sigmaL) :
    RobustAHPE.uniformOutputGradientTolerance mu M up eta sigmaL ≤
      RobustAHPE.uniformOutputGradientTolerance mu M up' eta sigmaL := by
  have hup : 0 < up := hup'.trans_le huple
  have hc := RobustAHPE.output_tolerance_coefficient_antitone mu up' up hmu.le hup' huple
  have hc0 : 0 ≤ min up⁻¹ (min 1 (mu / up)) := by positivity
  unfold RobustAHPE.uniformOutputGradientTolerance
  calc
    _ ≤ eta * sigmaL * min up⁻¹ (min 1 (mu / up)) / (M * up') :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left huple hM.le)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (mul_nonneg heta hsigmaL)) (by positivity)

def outputPrecisionFloor (c : Settings) (Amax sigma0 : ℝ) : ℝ :=
  min (c.rho / 8) (RobustAHPE.uniformOutputGradientTolerance c.mu c.M (lambdaCeiling c Amax)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow)

theorem output_precision_bounds (c : Settings) (hc : Legal c) (Amax sigma0 : ℝ)
    (hAhi : c.A ≤ Amax) (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < outputPrecisionFloor c Amax sigma0 ∧
      outputPrecisionFloor c Amax sigma0 ≤ OriginalCertifiedCoupledAHPE.outputQueryPrecision c sigma0 := by
  have he := endpoint_bounds c hc c.A Amax 0 0 hc.A_pos le_rfl hAhi le_rfl le_rfl
  have hp := compact_properties c hc 0 le_rfl
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have heta := (RobustAHPE.chosenSlack_properties (c.sigma + c.sigmaUp) sigma0
    (add_nonneg hc.sigma_pos.le hUp.le) hmargin).1
  have htol := RobustAHPE.uniformOutputGradientTolerance_positive c.mu c.M (lambdaCeiling c Amax)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
    hc.mu_pos hc.M_pos he.2.2.2.2.2.2.1 heta hc.low_pos
  refine ⟨lt_min (div_pos hc.rho_pos (by norm_num)) htol, ?_⟩
  exact min_le_min le_rfl (uniform_output_tolerance_antitone c.mu c.M (lambdaCeiling c Amax)
    (lambdaMax c) (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
    hc.mu_pos hc.M_pos hp.2.2.2.2.2.2.2.2 he.2.2.2.2.2.2.2 heta.le hc.low_pos.le)

def queryPrecisionFloor (c : Settings) (Amin Amax Gmax sigma0 : ℝ) : ℝ :=
  min 1 (min (centerPrecisionFloor c Amin Amax Gmax) (outputPrecisionFloor c Amax sigma0))

theorem all_query_precision_bounds (c : Settings) (hc : Legal c) (Amin Amax Gmax G sigma0 : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < queryPrecisionFloor c Amin Amax Gmax sigma0 ∧
      queryPrecisionFloor c Amin Amax Gmax sigma0 ≤
        OriginalCoupledGetterProgram.precisionFloor c G
          (OriginalCertifiedCoupledAHPE.outputQueryPrecision c sigma0) := by
  have hcTol := center_precision_bounds c hc Amin Amax Gmax G hAmin hAlo hAhi hG hGhi
  have hoTol := output_precision_bounds c hc Amax sigma0 hAhi hmargin
  exact ⟨lt_min zero_lt_one (lt_min hcTol.1 hoTol.1),
    min_le_min le_rfl (min_le_min hcTol.2 hoTol.2)⟩

def modulusCeiling (c : Settings) (Amin Amax Gmax Dmax : ℝ) : ℝ :=
  let T := 2 * Amax / marginFloor c Amin ^ 2
  let I := T / lambdaFloor c Amin Amax Gmax ^ 2
  T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
    ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)

theorem size_modulus_uniform_bound (c : Settings) (hc : Legal c) (Amin Amax Gmax G D Dmax : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) (hD : 0 ≤ D) (hDhi : D ≤ Dmax) :
    0 ≤ modulusCeiling c Amin Amax Gmax Dmax ∧
      OriginalBetaCurveBounds.sizeModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G D ≤
        modulusCeiling c Amin Amax Gmax Dmax := by
  have he := endpoint_bounds c hc Amin Amax Gmax G hAmin hAlo hAhi hG hGhi
  rcases he with ⟨hb0, hb, ht0, ht, hlo0, hlo, hup0, hup⟩
  have hp := compact_properties c hc G hG
  have hA := hc.A_pos
  have hmu := hc.mu_pos
  have hM := hc.M_pos
  have hLg := hc.Lg_nonneg
  have hAmax : 0 < Amax := hc.A_pos.trans_le hAhi
  have hGmax : 0 ≤ Gmax := hG.trans hGhi
  have hDmax : 0 ≤ Dmax := hD.trans hDhi
  have hm : 0 < margin c := hp.2.2.1
  have hl : 0 < lambdaMin c G := hp.2.2.2.2.2.2.2.1
  let T := 2 * Amax / marginFloor c Amin ^ 2
  let I := T / lambdaFloor c Amin Amax Gmax ^ 2
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hI0 : 0 ≤ I := by dsimp only [I]; positivity
  have hT : 2 * c.A / margin c ^ 2 ≤ T := by
    dsimp only [T]
    calc
      _ ≤ 2 * Amax / margin c ^ 2 := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        ((sq_le_sq₀ ht0.le hm.le).mpr ht)
  have hI : OriginalBetaCurveBounds.inverseLambdaModulus c.A (lower c G) (margin c) ≤ I := by
    change (2 * c.A / margin c ^ 2) / (lambdaMin c G) ^ 2 ≤ T / lambdaFloor c Amin Amax Gmax ^ 2
    calc
      _ ≤ T / (lambdaMin c G) ^ 2 := div_le_div_of_nonneg_right hT (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hT0 (by positivity)
        ((sq_le_sq₀ hlo0.le hl.le).mpr hlo)
  have hratio : c.A / margin c ≤ Amax / marginFloor c Amin := by
    calc
      _ ≤ Amax / margin c := div_le_div_of_nonneg_right hAhi hm.le
      _ ≤ _ := div_le_div_of_nonneg_left hAmax.le ht0 ht
  have hstep : OriginalBetaCurveBounds.stepModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G D ≤
      (c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu := by
    unfold OriginalBetaCurveBounds.stepModulus
    gcongr
  have hactualI0 : 0 ≤ OriginalBetaCurveBounds.inverseLambdaModulus c.A (lower c G) (margin c) := by
    unfold OriginalBetaCurveBounds.inverseLambdaModulus
    positivity
  have hactualStep0 : 0 ≤ OriginalBetaCurveBounds.stepModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G D := by
    unfold OriginalBetaCurveBounds.stepModulus
    positivity
  refine ⟨?_, ?_⟩
  · change 0 ≤ T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
      ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)
    positivity
  · unfold OriginalBetaCurveBounds.sizeModulus
    change _ ≤ T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
      ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)
    gcongr

theorem fuel_uniform_log_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (c : Settings) (hc : Legal c) (Amin Amax Gmax G Dmax : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) (x y : E) (hDhi : ‖x - y‖ ≤ Dmax) :
    let B := Real.logb 2 (max 1 (2 * modulusCeiling c Amin Amax Gmax Dmax /
      (thresholdHigh c - thresholdLow c)))
    (fuel c G x y : ℝ) + 2 ≤ 3 + B ∧
      2 * (fuel c G x y : ℝ) + 5 ≤ 7 + 2 * B := by
  dsimp only
  have hsize := size_modulus_uniform_bound c hc Amin Amax Gmax G ‖x - y‖ Dmax
    hAmin hAlo hAhi hG hGhi (norm_nonneg _) hDhi
  have hA := hc.A_pos
  have hmu := hc.mu_pos
  have hM := hc.M_pos
  have hLg := hc.Lg_nonneg
  have hp := compact_properties c hc G hG
  have hm := hp.2.2.1
  have hK0 : 0 ≤ modulus c G x y := by
    unfold modulus OriginalBetaCurveBounds.sizeModulus OriginalBetaCurveBounds.stepModulus
      OriginalBetaCurveBounds.inverseLambdaModulus
    positivity
  have hK : modulus c G x y ≤ modulusCeiling c Amin Amax Gmax Dmax := hsize.2
  have hwidth : upper c - lower c G ≤ 1 := by linarith only [hp.1, hp.2.2.2.2.2.1]
  have hgap := threshold_gap c hc
  have hnum : modulus c G x y * (upper c - lower c G) ≤ modulusCeiling c Amin Amax Gmax Dmax := by
    have hh := mul_le_mul_of_nonneg_left hwidth hK0
    nlinarith only [hh, hK]
  have hr : (modulus c G x y * (upper c - lower c G)) / ((thresholdHigh c - thresholdLow c) / 2) ≤
      2 * modulusCeiling c Amin Amax Gmax Dmax / (thresholdHigh c - thresholdLow c) := by
    calc
      _ ≤ modulusCeiling c Amin Amax Gmax Dmax / ((thresholdHigh c - thresholdLow c) / 2) :=
        div_le_div_of_nonneg_right hnum (by linarith only [hgap])
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le_max le_rfl hr)
  have hf := positive_search_log_bound c G x y
  constructor <;> linarith only [hf, hlog]

end
end OriginalUniformBetaResources


namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def uniformPrecisionFloor (c : Settings) (sigma0 D : ℝ) (n : ℕ) : ℝ :=
  OriginalUniformBetaResources.queryPrecisionFloor c (effectiveWeightFloor c D)
    (weightCeiling c n) (observedCeiling c D) sigma0

noncomputable def uniformModulusCeiling (c : Settings) (D : ℝ) (n : ℕ) : ℝ :=
  OriginalUniformBetaResources.modulusCeiling c (effectiveWeightFloor c D)
    (weightCeiling c n) (observedCeiling c D) (D + stateRadius c D)

noncomputable def getterLogCeiling (c : Settings) (D : ℝ) (n : ℕ) : ℝ :=
  7 + 2 * Real.logb 2 (max 1 (2 * uniformModulusCeiling c D n / (thresholdHigh c - thresholdLow c)))

noncomputable def getterCountCeiling (c : Settings) (D : ℝ) (n : ℕ) : ℕ := ⌈getterLogCeiling c D n⌉₊

noncomputable def stepCostCeiling (c : Settings) (K sigma0 D : ℝ) (n : ℕ) : ℕ :=
  logarithmicAtomicBound K (uniformPrecisionFloor c sigma0 D n) * getterCountCeiling c D n

theorem uniform_query_floor_effective (c : Settings) (s : State E) (Amin Amax Gmax sigma0 : ℝ) :
    OriginalUniformBetaResources.queryPrecisionFloor (effective (settingsAt c s)) Amin Amax Gmax sigma0 =
      OriginalUniformBetaResources.queryPrecisionFloor c Amin Amax Gmax sigma0 := by
  simp only [OriginalUniformBetaResources.queryPrecisionFloor, OriginalUniformBetaResources.centerPrecisionFloor,
    OriginalUniformBetaResources.outputPrecisionFloor, OriginalUniformBetaResources.lambdaFloor,
    OriginalUniformBetaResources.lambdaCeiling, OriginalUniformBetaResources.betaFloor,
    OriginalUniformBetaResources.marginFloor, effective_mu, effective_Lg, effective_M, effective_sigma,
    effective_low, effective_up, effective_rho, settingsAt]

theorem uniform_modulus_effective (c : Settings) (s : State E) (Amin Amax Gmax Dmax : ℝ) :
    OriginalUniformBetaResources.modulusCeiling (effective (settingsAt c s)) Amin Amax Gmax Dmax =
      OriginalUniformBetaResources.modulusCeiling c Amin Amax Gmax Dmax := by
  simp only [OriginalUniformBetaResources.modulusCeiling, OriginalUniformBetaResources.lambdaFloor,
    OriginalUniformBetaResources.betaFloor, OriginalUniformBetaResources.marginFloor,
    effective_mu, effective_Lg, effective_M, effective_sigma, effective_low, effective_up, effective_rho, settingsAt]

theorem scene_center_distance_bound
    {g : E → ℝ} {getter : E × ℝ → Answer E} {c : Settings} {D : ℝ} {n : ℕ}
    (hc : OriginalFirstCoupledStep.CommonLegal c) (hD : 0 ≤ D) (s : State E)
    (hscene : ResourceScene g getter c D n s) :
    ‖s.x - effectiveY (settingsAt c s) s.x s.y‖ ≤ D + stateRadius c D := by
  have hR := stateRadius_ge_D c hc D hD
  have hw : ‖effectiveY (settingsAt c s) s.x s.y - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D := by
    unfold effectiveY
    split_ifs
    · exact hscene.2.2.2.2.2.1.trans hR
    · exact hscene.2.2.2.2.2.2
  exact (norm_sub_le_norm_sub_add_norm_sub s.x (RobustAHPE.globalMinimizer g)
    (effectiveY (settingsAt c s) s.x s.y)).trans
      (add_le_add hscene.2.2.2.2.2.1 (by simpa only [norm_sub_rev] using hw))

theorem actual_uniform_step_resource_parameters
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n k : ℕ) (hk : k ≤ n) :
    0 < uniformPrecisionFloor c sigma0 D n ∧
      uniformPrecisionFloor c sigma0 D n ≤ queryFloor getter
        (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k)) sigma0
        (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y ∧
      2 * trialFuel getter (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))
        (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y + 5 ≤
          getterCountCeiling c D n := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have he := effective_legal cs (settingsAt_common c H.common s) hA
  have hscene := actual_resources_on_stream H start hstart n k hk
  have hprecision := OriginalUniformBetaResources.all_query_precision_bounds (effective cs) he
    (effectiveWeightFloor c D) (weightCeiling c n) (observedCeiling c D)
    (getterBound getter cs s.x s.y) sigma0 hscene.1 hscene.2.1 hscene.2.2.1 hscene.2.2.2.1 hscene.2.2.2.2.1
    (by simpa only [effective_sigma, effective_up, cs, settingsAt] using H.margin)
  rw [uniform_query_floor_effective] at hprecision
  have hfuel := (OriginalUniformBetaResources.fuel_uniform_log_bound (effective cs) he
    (effectiveWeightFloor c D) (weightCeiling c n) (observedCeiling c D) (getterBound getter cs s.x s.y)
    (D + stateRadius c D) hscene.1 hscene.2.1 hscene.2.2.1 hscene.2.2.2.1 hscene.2.2.2.2.1
    s.x (effectiveY cs s.x s.y) (scene_center_distance_bound H.common H.D_pos.le s hscene)).2
  rw [uniform_modulus_effective] at hfuel
  simp only [thresholdHigh, thresholdLow, effective_M, effective_sigma, effective_low, effective_up, cs, settingsAt] at hfuel
  have hcount : ((2 * trialFuel getter cs s.x s.y + 5 : ℕ) : ℝ) ≤ getterLogCeiling c D n := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, trialFuel, getterBound, getterLogCeiling,
      uniformModulusCeiling, thresholdHigh, thresholdLow, cs, settingsAt] using hfuel
  have hnat : 2 * trialFuel getter cs s.x s.y + 5 ≤ getterCountCeiling c D n := by
    exact_mod_cast hcount.trans (Nat.le_ceil (getterLogCeiling c D n))
  exact ⟨hprecision.1, hprecision.2, hnat⟩

theorem actual_uniform_step_base_cost
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (n k : ℕ) (hk : k ≤ n) :
    baseCost getter cost (stepProgram c sigma0 (states getter c sigma0 ⟨0, start, start⟩ k)) ≤
      stepCostCeiling c K sigma0 D n := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  obtain ⟨value, hrun, hvalid, hfloor, htrace, hcount, hcost, hlog⟩ :=
    original_certified_coupled_ahpe_step g cs (settingsAt_common c H.common s) hA sigma0 D H.margin H.sigma_lt_one
      H.rho_eq H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct cost K hK hatomic s.x s.y
  have hu := actual_uniform_step_resource_parameters H start hstart n k hk
  have hmono := logarithmicAtomicBound_antitone K (uniformPrecisionFloor c sigma0 D n)
    (queryFloor getter cs sigma0 s.x s.y) hK hu.1 hu.2.1
  exact hcost.trans (Nat.mul_le_mul hmono hu.2.2)

theorem actual_contraction_base_count
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (H : Hypotheses g c sigma0 D (implementedGetter baseAnswer oracle))
    (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → (execute baseAnswer (oracle q)).2 ≤ logarithmicAtomicBound K q.2)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let n := contractionIterations c sigma0 D
    let p := primitiveLower oracle (loopProgram c sigma0 n ⟨0, start, start⟩)
    ‖resultPoint (execute baseAnswer p).1 - RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      0 < uniformPrecisionFloor c sigma0 D n ∧
      (execute baseAnswer p).2 ≤ stepCostCeiling c K sigma0 D n * n ∧
      (n : ℝ) ≤ 1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
        (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  have hcontract := actual_finite_second_order_contraction g c H.common sigma0 D H.D_pos H.margin H.sigma_lt_one H.rho_eq
    H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz (implementedGetter baseAnswer oracle) H.getter_correct start hstart
  have hcost := loop_actual_weighted_cost_bound (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
    c sigma0 (contractionIterations c sigma0 D) (stepCostCeiling c K sigma0 D (contractionIterations c sigma0 D)) ⟨0, start, start⟩
    (fun k hk => actual_uniform_step_base_cost H start hstart (implementedCost baseAnswer oracle) K hK hatomic _ k (by omega))
  have hfloor := (actual_uniform_step_resource_parameters H start hstart (contractionIterations c sigma0 D) 0 (by omega)).1
  rw [primitiveLower_execution]
  exact ⟨hcontract.1, hfloor, hcost, hcontract.2⟩

end OriginalRobustTrajectory


namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def uniformQueryRadius (c : Settings) (D : ℝ) : ℝ :=
  D + 2 * stateRadius c D + 2 * (observedCeiling c D + c.mu / 4) / c.mu

theorem actual_uniform_step_query_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n k : ℕ) (hk : k ≤ n) :
    ∀ q ∈ trace getter (stepProgram c sigma0 (states getter c sigma0 ⟨0, start, start⟩ k)),
      uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧
        ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c D := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  let w := effectiveY cs s.x s.y
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have he := effective_legal cs (settingsAt_common c H.common s) hA
  have hscene := actual_resources_on_stream H start hstart n k hk
  have hu := actual_uniform_step_resource_parameters H start hstart n k hk
  have hp := OriginalCoupledGetterProgram.positiveProgram_request_precision_floor getter (effective cs)
    (outputQueryPrecision (effective cs) sigma0) s.x w
  have hb := OriginalCoupledQueryGeometry.positiveProgram_actual_query_ball g (effective cs) he
    (outputQueryPrecision (effective cs) sigma0) H.C2
    (by simpa only [effective_mu, cs, settingsAt] using H.strongly_convex)
    (by simpa only [effective_Lg, cs, settingsAt] using H.gradient_lipschitz)
    getter H.getter_correct s.x w
  have hR := stateRadius_ge_D c H.common D H.D_pos.le
  have hw : ‖w - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D := by
    dsimp only [w, effectiveY]
    split_ifs
    · exact hscene.2.2.2.2.2.1.trans hR
    · exact hscene.2.2.2.2.2.2
  have hdist := scene_center_distance_bound H.common H.D_pos.le s hscene
  have hG := hscene.2.2.2.2.1
  have hfrac := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add hG (le_refl (c.mu / 4))) (by norm_num : (0 : ℝ) ≤ 2)) H.common.mu_pos.le
  intro q hq
  have hq' : q ∈ trace getter (OriginalCoupledGetterProgram.positiveProgram (effective cs)
      (outputQueryPrecision (effective cs) sigma0) s.x w) := hq
  refine ⟨hu.2.1.trans (hp q hq'), ?_⟩
  have hbq := hb q hq'
  have htriangle := norm_sub_le_norm_sub_add_norm_sub q.1 w (RobustAHPE.globalMinimizer g)
  have hbd := add_le_add hbq hw
  have hbound := htriangle.trans hbd
  simp only [OriginalCoupledQueryGeometry.queryRadius, effective_mu, cs, settingsAt] at hbound
  simp only [getterBound, cs, settingsAt, w] at hfrac hdist hbound
  unfold uniformQueryRadius
  nlinarith only [hbound, hdist, hfrac]

theorem actual_uniform_step_getter_count
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n k : ℕ) (hk : k ≤ n) :
    (execute getter (stepProgram c sigma0 (states getter c sigma0 ⟨0, start, start⟩ k))).2 ≤ getterCountCeiling c D n := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have he := effective_legal cs (settingsAt_common c H.common s) hA
  have hmarginE : (effective cs).sigma + (effective cs).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up, cs, settingsAt] using H.margin
  have hprecision := outputQueryPrecision_positive (effective cs) he sigma0 hmarginE
  obtain ⟨value, hrun, hvalid, hcount⟩ := OriginalCoupledGetterProgram.positiveProgram_success_and_getter_calls g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    H.C2 (by simpa only [effective_mu, cs, settingsAt] using H.strongly_convex)
    (by simpa only [effective_Lg, cs, settingsAt] using H.gradient_lipschitz)
    (by simpa only [effective_M, cs, settingsAt] using H.hessian_lipschitz)
    getter H.getter_correct s.x (effectiveY cs s.x s.y)
  exact hcount.trans (actual_uniform_step_resource_parameters H start hstart n k hk).2.2

theorem loop_trace_from_step_traces
    (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ)
    (P : E × ℝ → Prop) (n : ℕ) (s : State E)
    (hsteps : ∀ k < n, ∀ q ∈ trace getter (stepProgram c sigma0 (states getter c sigma0 s k)), P q) :
    ∀ q ∈ trace getter (loopProgram c sigma0 n s), P q := by
  induction n generalizing s with
  | zero => simp only [loopProgram, trace, List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
    intro q hq
    rw [loopProgram, OriginalCoupledQueryGeometry.trace_bind_actual, List.mem_append] at hq
    rcases hq with hfirst | htail
    · exact hsteps 0 (by omega) q hfirst
    · cases hout : (execute getter (stepProgram c sigma0 s)).1 with
      | bracket l r => simpa only [hout, trace, List.not_mem_nil] using htail
      | found value =>
        cases value with
        | stop w => simpa only [hout, trace, List.not_mem_nil] using htail
        | window b d aY =>
          have hadv : advance getter c sigma0 s = nextWindow c s b d aY := by
            unfold advance choice
            rw [hout]
            rfl
          have hnext : ∀ k < n, ∀ r ∈ trace getter (stepProgram c sigma0
              (states getter c sigma0 (nextWindow c s b d aY) k)), P r := by
            intro k hk r hr
            have h := hsteps (k + 1) (by omega)
            rw [states_shift, hadv] at h
            exact h r hr
          exact ih (nextWindow c s b d aY) hnext q (by simpa only [hout] using htail)

theorem actual_contraction_getter_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    ∀ q ∈ trace getter (loopProgram c sigma0 n ⟨0, start, start⟩),
      uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧
        ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c D :=
  loop_trace_from_step_traces getter c sigma0 _ n ⟨0, start, start⟩
    (fun k hk => actual_uniform_step_query_trace H start hstart n k (by omega))

theorem actual_contraction_local_base_count
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (H : Hypotheses g c sigma0 D (implementedGetter baseAnswer oracle))
    (C : ℕ)
    (hatomic : ∀ q : E × ℝ,
      uniformPrecisionFloor c sigma0 D (contractionIterations c sigma0 D) ≤ q.2 →
      ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c D →
      (execute baseAnswer (oracle q)).2 ≤ C)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let n := contractionIterations c sigma0 D
    let p := primitiveLower oracle (loopProgram c sigma0 n ⟨0, start, start⟩)
    ‖resultPoint (execute baseAnswer p).1 - RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      0 < uniformPrecisionFloor c sigma0 D n ∧
      (execute baseAnswer p).2 ≤ C * getterCountCeiling c D n * n ∧
      (n : ℝ) ≤ 1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
        (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  have hcontract := actual_finite_second_order_contraction g c H.common sigma0 D H.D_pos H.margin H.sigma_lt_one H.rho_eq
    H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz (implementedGetter baseAnswer oracle) H.getter_correct start hstart
  have hcost := loop_actual_weighted_cost_bound (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
    c sigma0 (contractionIterations c sigma0 D) (C * getterCountCeiling c D (contractionIterations c sigma0 D)) ⟨0, start, start⟩ (by
      intro k hk
      have htr := actual_uniform_step_query_trace H start hstart (contractionIterations c sigma0 D) k (by omega)
      have hb := baseCost_le_mul_count (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
        (stepProgram c sigma0 (states (implementedGetter baseAnswer oracle) c sigma0 ⟨0, start, start⟩ k)) C
        (fun q hq => hatomic q (htr q hq).1 (htr q hq).2)
      exact hb.trans (Nat.mul_le_mul_left C (actual_uniform_step_getter_count H start hstart _ k (by omega))))
  have hfloor := (actual_uniform_step_resource_parameters H start hstart (contractionIterations c sigma0 D) 0 (by omega)).1
  rw [primitiveLower_execution]
  exact ⟨hcontract.1, hfloor, hcost, hcontract.2⟩

end OriginalRobustTrajectory

namespace FangqingGetterComposition
open OriginalBetaATSTrial

theorem baseCost_unit_eq_getter_count {Q A R : Type*} (getter : Q → A) (p : GetterProgram Q A R) :
    baseCost getter (fun _ => 1) p = (execute getter p).2 := by
  induction p with
  | pure r => rfl
  | ask q next ih => simp only [baseCost, execute, ih, Nat.add_comm]

end FangqingGetterComposition

namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings)
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_contraction_primitive_getter_count
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    (execute getter (loopProgram c sigma0 n ⟨0, start, start⟩)).2 ≤ getterCountCeiling c D n * n := by
  have h := loop_actual_weighted_cost_bound getter (fun _ => 1) c sigma0 n (getterCountCeiling c D n)
    ⟨0, start, start⟩ (fun k hk => by
      rw [baseCost_unit_eq_getter_count]
      exact actual_uniform_step_getter_count H start hstart n k (by omega))
  simpa only [baseCost_unit_eq_getter_count] using h

theorem actual_contraction_trace_at_start
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    ∀ q ∈ trace getter (loopProgram c sigma0 n ⟨0, start, start⟩),
      uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧
        ‖q.1 - start‖ ≤ uniformQueryRadius c D + D := by
  intro q hq
  have h := actual_contraction_getter_trace H start hstart n q hq
  refine ⟨h.1, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub q.1 (RobustAHPE.globalMinimizer g) start).trans
    (add_le_add h.2 (by simpa only [norm_sub_rev] using hstart))

noncomputable def contractionProgram (c : Settings) (sigma0 D : ℝ) (start : E) :
    GetterProgram (E × ℝ) (Answer E) E :=
  FangqingGetterComposition.map resultPoint (loopProgram c sigma0 (contractionIterations c sigma0 D) ⟨0, start, start⟩)

theorem actual_positive_contraction_program
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let n := contractionIterations c sigma0 D
    ‖(execute getter (contractionProgram c sigma0 D start)).1 - RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      0 < uniformPrecisionFloor c sigma0 D n ∧
      (execute getter (contractionProgram c sigma0 D start)).2 ≤ getterCountCeiling c D n * n ∧
      (∀ q ∈ trace getter (contractionProgram c sigma0 D start),
        uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧ ‖q.1 - start‖ ≤ uniformQueryRadius c D + D) ∧
      (n : ℝ) ≤ 1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
        (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  have h := actual_finite_second_order_contraction g c H.common sigma0 D H.D_pos H.margin H.sigma_lt_one H.rho_eq
    H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct start hstart
  simp only [contractionProgram, execute_map, OriginalCoupledQueryGeometry.trace_map_actual]
  exact ⟨h.1, (actual_uniform_step_resource_parameters H start hstart _ 0 (by omega)).1,
    actual_contraction_primitive_getter_count H start hstart _, actual_contraction_trace_at_start H start hstart _, h.2⟩

end OriginalRobustTrajectory


namespace OriginalActualDualPositiveContraction
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalDualCurvature OriginalDualMinimizer
open OriginalBetaATSTrial OriginalCoupledBetaSearch OriginalFirstCoupledStep
open OriginalDualGetterImplementation OriginalDualGetterResourceComposition
open OriginalRobustTrajectory FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def parameters (mu L rho D : ℝ) : Settings where
  mu := mu
  Lg := 2 * L
  M := (4 * Real.sqrt 2) * rho
  A := 0
  sigma := 1 / 8
  sigmaLow := 1 / 8
  sigmaUp := 1 / 4
  rho := mu * D / 2

theorem parameters_common (mu L rho D : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (hD : 0 < D) :
    CommonLegal (parameters mu L rho D) := by
  refine ⟨hmu, by dsimp [parameters]; positivity, ?_, by norm_num [parameters],
    by norm_num [parameters], by norm_num [parameters], by norm_num [parameters],
    by norm_num [parameters], by dsimp [parameters]; positivity⟩
  dsimp [parameters]
  positivity

noncomputable def originalProgram (mu L rho D : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F :=
  primitiveLower (oracleProgram L rho x uInit)
    (contractionProgram (parameters mu L rho D) (1 / 2) D yin)

noncomputable def originalQueryBudget (J : Joint E F → ℝ) (mu L rho D : ℝ) (x uInit : E) (yin : F) : ℕ :=
  let c := parameters mu L rho D
  let n := contractionIterations c (1 / 2) D
  queryBallBudget J L rho x uInit yin (uniformQueryRadius c D + D) (uniformPrecisionFloor c (1 / 2) D n) *
    (getterCountCeiling c D n * n)

theorem actual_dual_positive_contraction
    (J : Joint E F → ℝ) (mu L rho D : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (hD : 0 < D)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (originalProgram mu L rho D x uInit yin)
    ‖run.1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ D / 2 ∧
      run.2 ≤ originalQueryBudget J mu L rho D x uInit yin ∧
      (contractionIterations (parameters mu L rho D) (1 / 2) D : ℝ) ≤
        1 + (8 * LargeStepAHPE.rateConstant (1 / 2) (1 / 8)) ^ (2 / 7 : ℝ) *
          (((4 * Real.sqrt 2) * rho) * D / mu) ^ (2 / 7 : ℝ) := by
  let g := psi J L x
  let c := parameters mu L rho D
  let getter := actualGetter J L rho x uInit
  let n := contractionIterations c (1 / 2) D
  let p := contractionProgram c (1 / 2) D yin
  have hgC2 := psi_contDiff2 J L hL hC2 hLip x
  have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
  have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
  have hgHess := psi_hessian_lipschitz J L rho hL hrho.le hC2 hLip hHess x
  have hgetter := actual_getter_accuracy J L rho hL hrho.le hC2 hLip hHess x uInit
  have H : Hypotheses g c (1 / 2) D getter :=
    ⟨parameters_common mu L rho D hmu hL hrho hD, hD, by norm_num [c, parameters],
      by norm_num, rfl, hgC2, hgsc, hglip, hgHess, hgetter⟩
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
  have hvs : vStar (JointSliceRegularity.curry J) L x = RobustAHPE.globalMinimizer g :=
    RobustAHPE.globalMinimizer_unique g mu hmu (hgC2.differentiable (by norm_num)) hgsc _ hmin
  have hstart : ‖yin - RobustAHPE.globalMinimizer g‖ ≤ D := by rwa [← hvs]
  have h := actual_positive_contraction_program H yin hstart
  have hresource := actual_original_queries_from_checked_getter_budget J L rho hL hrho.le hLip x uInit yin
    (uniformQueryRadius c D + D) (uniformPrecisionFloor c (1 / 2) D n) h.2.1 p
    (getterCountCeiling c D n * n)
    (fun q hq => (h.2.2.2.1 q hq).2) (fun q hq => (h.2.2.2.1 q hq).1) h.2.2.1
  have hresult := actual_original_program_result J L rho x uInit p
  refine ⟨?_, hresource, h.2.2.2.2⟩
  change ‖(execute (OriginalDualOracleProgram.actualOracle J)
    (primitiveLower (oracleProgram L rho x uInit) p)).1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ _
  rw [hresult, hvs]
  exact h.1

end OriginalActualDualPositiveContraction


namespace OriginalDualPrimalRecovery
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalPrimalElimination OriginalDualCurvature OriginalDualMinimizer
open OriginalDualGetterImplementation OriginalDualResidualQueryBound
open OriginalBetaATSTrial FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def program (L tau : ℝ) (x uInit : E)
    (dualProgram : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  FangqingGetterComposition.bind dualProgram (fun v => FangqingGetterComposition.map
    (fun s : OriginalDualOracleProgram.QueryState E F => JointSliceRegularity.point s.u v)
    (liftQuery (OriginalDualOracleProgram.simulator L x v uInit (tau / 4))))

noncomputable def queryBudget (J : Joint E F → ℝ) (L D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x uInit yin + (D + tau / 4)) / (tau / 4)))

theorem actual_joint_recovery_from_actual_dual_program
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 < tau) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D)
    (dualProgram : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F)
    (hdual : ‖(execute (OriginalDualOracleProgram.actualOracle J) dualProgram).1 -
      vStar (JointSliceRegularity.curry J) L x‖ ≤ tau / 4) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program L tau x uInit dualProgram)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ (execute (OriginalDualOracleProgram.actualOracle J) dualProgram).2 + queryBudget J L D tau x uInit yin := by
  let first := execute (OriginalDualOracleProgram.actualOracle J) dualProgram
  let v := first.1
  let last := OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
    (OriginalDualOracleProgram.simulator L x v uInit (tau / 4))
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpu := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hlast := OriginalDualOracleProgram.reduced_dual_oracle_simulation J L rho hL hrho
    hC2 hLip hHess x uInit v (tau / 4) (by positivity)
  have hprimal := primal_lipschitz J L hL hJ hLip x v (vStar (JointSliceRegularity.curry J) L x)
  rw [hpu] at hprimal
  have hu : ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ≤ tau / 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub last.1.u (primal J L x v) (uStar (JointSliceRegularity.curry J) L x)
    have hd : ‖last.1.u - primal J L x v‖ ≤ tau / 4 := hlast.2.1
    linarith only [ht, hd, hprimal, hdual]
  have hball : ‖v - yin‖ ≤ D + tau / 4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub v (vStar (JointSliceRegularity.curry J) L x) yin
    rw [norm_sub_rev (vStar (JointSliceRegularity.curry J) L x) yin] at ht
    linarith only [ht, hwarm, hdual]
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x uInit v yin (D + tau / 4)
    (tau / 4) (by positivity) hball
  have hlastCost : last.2 ≤ queryBudget J L D tau x uInit yin := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact hc.trans (Nat.le_ceil _)
  have hexec : execute (OriginalDualOracleProgram.actualOracle J) (program L tau x uInit dualProgram) =
      (JointSliceRegularity.point last.1.u v, first.2 + last.2) := by
    simp only [program, execute_bind, execute_map, execute_liftQuery]
    rfl
  rw [hexec]
  constructor
  · have hn := WithLp.prod_norm_sq_eq_of_L2
      (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)
    have heq : ‖JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x‖ ^ 2 =
        ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ^ 2 +
          ‖v - vStar (JointSliceRegularity.curry J) L x‖ ^ 2 := by
      rw [JointSliceRegularity.point_eq_toLp] at hn ⊢
      exact hn
    have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 2)).mpr hu
    have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 4)).mpr hdual
    nlinarith only [heq, hu2, hv2, htau,
      norm_nonneg (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)]
  · exact add_le_add le_rfl hlastCost

end OriginalDualPrimalRecovery


namespace FangqingGetterComposition
open OriginalBetaATSTrial

theorem baseCost_map_eq {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ) (f : R → S)
    (p : GetterProgram Q A R) : baseCost getter cost (map f p) = baseCost getter cost p := by
  simp only [map, baseCost_bind, baseCost, Nat.add_zero]

end FangqingGetterComposition

namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings)
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def atRadius (c : Settings) (R : ℝ) : Settings := {c with rho := c.mu * R / 2}

noncomputable def oneRadiusProgram (c : Settings) (sigma0 R : ℝ) (start : E) : GetterProgram (E × ℝ) (Answer E) E :=
  contractionProgram (atRadius c R) sigma0 R start

noncomputable def radiusGetterFactor (c : Settings) (sigma0 R : ℝ) : ℕ :=
  getterCountCeiling (atRadius c R) R (contractionIterations c sigma0 R)

noncomputable def radiusBaseFactor (c : Settings) (K sigma0 R : ℝ) : ℕ :=
  stepCostCeiling (atRadius c R) K sigma0 R (contractionIterations c sigma0 R)

theorem contractionIterations_atRadius (c : Settings) (sigma0 R S : ℝ) :
    contractionIterations (atRadius c R) sigma0 S = contractionIterations c sigma0 S := rfl

theorem Hypotheses.atRadius {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R) : Hypotheses g (atRadius c R) sigma0 R getter := by
  refine ⟨⟨H.common.mu_pos, H.common.Lg_nonneg, H.common.M_pos, H.common.sigma_pos, H.common.sigma_lt_one,
      H.common.low_pos, H.common.low_lt_up, H.common.gap, ?_⟩,
    hR, H.margin, H.sigma_lt_one, rfl, H.C2, H.strongly_convex, H.gradient_lipschitz, H.hessian_lipschitz, H.getter_correct⟩
  change 0 < c.mu * R / 2
  exact div_pos (mul_pos H.common.mu_pos hR) (by norm_num)

theorem one_radius_program_spec
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2) :
    ‖(execute getter (oneRadiusProgram c sigma0 R start)).1 - RobustAHPE.globalMinimizer g‖ ≤ R / 2 ∧
      (execute getter (oneRadiusProgram c sigma0 R start)).2 ≤
        radiusGetterFactor c sigma0 R * contractionIterations c sigma0 R ∧
      baseCost getter cost (oneRadiusProgram c sigma0 R start) ≤
        radiusBaseFactor c K sigma0 R * contractionIterations c sigma0 R := by
  have HR := H.atRadius R hR
  have h := actual_positive_contraction_program HR start hstart
  dsimp only at h
  have hb := loop_actual_weighted_cost_bound getter cost (atRadius c R) sigma0 (contractionIterations c sigma0 R)
    (radiusBaseFactor c K sigma0 R) ⟨0, start, start⟩ (fun k hk =>
      actual_uniform_step_base_cost HR start hstart cost K hK hatomic _ k (by omega))
  exact ⟨h.1, h.2.2.1, by simpa only [oneRadiusProgram, contractionProgram, baseCost_map_eq, contractionIterations_atRadius] using hb⟩

noncomputable def restartProgram (c : Settings) (sigma0 : ℝ) : ℕ → ℝ → E → GetterProgram (E × ℝ) (Answer E) E
  | 0, _, start => .pure start
  | r + 1, R, start => bind (oneRadiusProgram c sigma0 R start)
      (fun point => restartProgram c sigma0 r (R / 2) point)

noncomputable def coefficientSum (coefficient : ℝ → ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | r + 1, R => coefficient R + coefficientSum coefficient r (R / 2)

noncomputable def coefficientMaximum (coefficient : ℝ → ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | r + 1, R => max (coefficient R) (coefficientMaximum coefficient r (R / 2))

theorem coefficient_sum_le_maximum (coefficient : ℝ → ℕ) (r : ℕ) (R : ℝ) :
    coefficientSum coefficient r R ≤ coefficientMaximum coefficient r R * r := by
  induction r generalizing R with
  | zero => simp only [coefficientSum, coefficientMaximum, Nat.mul_zero, le_refl]
  | succ r ih =>
    have htail := ih (R / 2)
    have hhead : coefficient R ≤ max (coefficient R) (coefficientMaximum coefficient r (R / 2)) := le_max_left _ _
    have hmax : coefficientMaximum coefficient r (R / 2) ≤ max (coefficient R) (coefficientMaximum coefficient r (R / 2)) := le_max_right _ _
    have hmul := Nat.mul_le_mul_right r hmax
    simp only [coefficientSum, coefficientMaximum]
    nlinarith only [htail, hhead, hmul]

theorem actual_positive_restarts
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (r : ℕ) (R : ℝ) (hR : 0 < R) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R) :
    ‖(execute getter (restartProgram c sigma0 r R start)).1 - RobustAHPE.globalMinimizer g‖ ≤ R / (2 : ℝ) ^ r ∧
      (execute getter (restartProgram c sigma0 r R start)).2 ≤
        coefficientSum (fun R => radiusGetterFactor c sigma0 R * contractionIterations c sigma0 R) r R ∧
      baseCost getter cost (restartProgram c sigma0 r R start) ≤
        coefficientSum (fun R => radiusBaseFactor c K sigma0 R * contractionIterations c sigma0 R) r R := by
  induction r generalizing R start with
  | zero => simpa only [restartProgram, execute, baseCost, coefficientSum, pow_zero, div_one, le_refl, and_self, and_true] using hstart
  | succ r ih =>
    let first := execute getter (oneRadiusProgram c sigma0 R start)
    have hfirst := one_radius_program_spec H R hR start hstart cost K hK hatomic
    have hsecond := ih (R / 2) (by positivity) first.1 hfirst.1
    simp only [restartProgram, execute_bind, baseCost_bind, coefficientSum]
    refine ⟨?_, Nat.add_le_add hfirst.2.1 hsecond.2.1, Nat.add_le_add hfirst.2.2 hsecond.2.2⟩
    convert! hsecond.1 using 1
    rw [pow_succ]
    ring

theorem contraction_iterations_monotone
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) :
    contractionIterations c sigma0 R ≤ contractionIterations c sigma0 S := by
  have hC := LargeStepAHPE.rateConstant_positive sigma0 c.sigmaLow H.sigma_positive H.sigma_lt_one H.common.low_pos
  have hscale : 8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * R / c.mu ≤
      8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * S / c.mu :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRS
      (mul_nonneg (mul_nonneg (by norm_num) hC.le) H.common.M_pos.le)) H.common.mu_pos.le
  have hbase : 0 ≤ 8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * R / c.mu := by
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) H.common.M_pos.le) hR) H.common.mu_pos.le
  unfold contractionIterations OriginalSecondOrderCount.iterations
  exact max_le_max le_rfl (Nat.ceil_mono (Real.rpow_le_rpow hbase hscale (by norm_num : (0 : ℝ) ≤ 2 / 7)))

theorem coefficient_sum_remove_iteration_factor
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (coefficient : ℝ → ℕ) (r : ℕ)
    (R : ℝ) (hR : 0 ≤ R) (hRD : R ≤ D) :
    coefficientSum (fun R => coefficient R * contractionIterations c sigma0 R) r R ≤
      contractionIterations c sigma0 D * coefficientSum coefficient r R := by
  induction r generalizing R with
  | zero => simp only [coefficientSum, Nat.mul_zero, le_refl]
  | succ r ih =>
    have hn := contraction_iterations_monotone H R D hR hRD
    have hhead := Nat.mul_le_mul_left (coefficient R) hn
    have hhalf : 0 ≤ R / 2 := by positivity
    have hhalfD : R / 2 ≤ D := by linarith only [hR, hRD]
    have htail := ih (R / 2) hhalf hhalfD
    simp only [coefficientSum]
    calc
      _ ≤ coefficient R * contractionIterations c sigma0 D +
          contractionIterations c sigma0 D * coefficientSum coefficient r (R / 2) := Nat.add_le_add hhead htail
      _ = _ := by ring

theorem actual_positive_restart_base_program
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (sigma0 D tau : ℝ)
    (H : Hypotheses g c sigma0 D (implementedGetter baseAnswer oracle))
    (htau : 0 < tau) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → (execute baseAnswer (oracle q)).2 ≤ logarithmicAtomicBound K q.2)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let r := FangqingHysteresis.halvingCount D tau
    let p := primitiveLower oracle (restartProgram c sigma0 r D start)
    ‖(execute baseAnswer p).1 - RobustAHPE.globalMinimizer g‖ ≤ tau ∧
      (execute baseAnswer p).2 ≤ contractionIterations c sigma0 D * r *
        coefficientMaximum (radiusBaseFactor c K sigma0) r D ∧
      (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) ∧
      (contractionIterations c sigma0 D : ℝ) ≤
        1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) * (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  let getter := implementedGetter baseAnswer oracle
  let r := FangqingHysteresis.halvingCount D tau
  have hs := actual_positive_restarts H (implementedCost baseAnswer oracle) K hK hatomic r D H.D_pos start hstart
  have hsum := coefficient_sum_remove_iteration_factor H (radiusBaseFactor c K sigma0) r D H.D_pos.le le_rfl
  have hmax := coefficient_sum_le_maximum (radiusBaseFactor c K sigma0) r D
  have hcost : baseCost getter (implementedCost baseAnswer oracle) (restartProgram c sigma0 r D start) ≤
      contractionIterations c sigma0 D * r * coefficientMaximum (radiusBaseFactor c K sigma0) r D := by
    calc
      _ ≤ contractionIterations c sigma0 D * coefficientSum (radiusBaseFactor c K sigma0) r D := hs.2.2.trans hsum
      _ ≤ contractionIterations c sigma0 D * (coefficientMaximum (radiusBaseFactor c K sigma0) r D * r) :=
        Nat.mul_le_mul_left _ hmax
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.logb 2 (max 1 (D / tau)) := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hr : (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) := by
    have h := (Nat.ceil_lt_add_one hlog0).le
    change (r : ℝ) ≤ _ at h
    linarith only [h]
  have hn := (OriginalSecondOrderCount.rounded_iteration_properties (LargeStepAHPE.rateConstant sigma0 c.sigmaLow)
    c.M D c.mu (LargeStepAHPE.rateConstant_positive sigma0 c.sigmaLow H.sigma_positive H.sigma_lt_one H.common.low_pos).le
    H.common.M_pos.le H.D_pos.le H.common.mu_pos).2.1
  rw [primitiveLower_execution]
  exact ⟨hs.1.trans (FangqingHysteresis.halving_precision D tau htau), hcost, hr, hn⟩

end OriginalRobustTrajectory


namespace OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings)
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def radiusPrecision (c : Settings) (sigma0 R : ℝ) : ℝ :=
  uniformPrecisionFloor (atRadius c R) sigma0 R (contractionIterations c sigma0 R)

noncomputable def precisionMinimum (c : Settings) (sigma0 : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | r + 1, R => min (radiusPrecision c sigma0 R) (precisionMinimum c sigma0 r (R / 2))

theorem firstWeightFloor_antitone (c : Settings) (hc : OriginalFirstCoupledStep.CommonLegal c)
    (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : firstWeightFloor c S ≤ firstWeightFloor c R := by
  have hnum : 0 ≤ c.sigmaLow * c.mu * (1 - c.sigma) :=
    mul_nonneg (mul_nonneg hc.low_pos.le hc.mu_pos.le) (sub_nonneg.mpr hc.sigma_lt_one.le)
  have hMR : 0 < c.M * (1 + c.Lg * R) :=
    mul_pos hc.M_pos (by nlinarith only [mul_nonneg hc.Lg_nonneg hR])
  have hden : c.M * (1 + c.Lg * R) ≤ c.M * (1 + c.Lg * S) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hRS hc.Lg_nonneg)) hc.M_pos.le
  exact div_le_div_of_nonneg_left hnum hMR hden

theorem stateRadius_monotone (c : Settings) (hc : OriginalFirstCoupledStep.CommonLegal c)
    (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : stateRadius c R ≤ stateRadius c S := by
  have hS : 0 ≤ S := hR.trans hRS
  have hfloorR := firstWeightFloor_positive c hc R hR
  have hfloorS := firstWeightFloor_positive c hc S hS
  have hfloor := firstWeightFloor_antitone c hc R S hR hRS
  have hinv : (c.mu * firstWeightFloor c R)⁻¹ ≤ (c.mu * firstWeightFloor c S)⁻¹ :=
    inv_anti₀ (mul_pos hc.mu_pos hfloorS) (mul_le_mul_of_nonneg_left hfloor hc.mu_pos.le)
  unfold stateRadius geometryRadius
  exact mul_le_mul hRS (add_le_add le_rfl hinv)
    (by have h := inv_nonneg.mpr (mul_nonneg hc.mu_pos.le hfloorR.le); linarith only [h]) hS

theorem uniformQueryRadius_monotone (c : Settings) (hc : OriginalFirstCoupledStep.CommonLegal c)
    (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : uniformQueryRadius c R ≤ uniformQueryRadius c S := by
  have hradius := stateRadius_monotone c hc R S hR hRS
  have hobs : observedCeiling c R ≤ observedCeiling c S := by
    unfold observedCeiling
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith only [hRS, hradius]) hc.Lg_nonneg)
  have hfrac := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hobs (le_refl (c.mu / 4))) (by norm_num : (0 : ℝ) ≤ 2)) hc.mu_pos.le
  unfold uniformQueryRadius
  linarith only [hRS, hradius, hfrac]

theorem radiusPrecision_positive
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R) : 0 < radiusPrecision c sigma0 R := by
  have HR := H.atRadius R hR
  have ht := (actual_uniform_step_resource_parameters HR (RobustAHPE.globalMinimizer g)
    (by simpa only [sub_self, norm_zero] using hR.le) (contractionIterations c sigma0 R) 0 (by omega)).1
  exact ht

theorem precisionMinimum_positive
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (r : ℕ) (R : ℝ) (hR : 0 < R) : 0 < precisionMinimum c sigma0 r R := by
  induction r generalizing R with
  | zero => norm_num [precisionMinimum]
  | succ r ih => exact lt_min (radiusPrecision_positive H R hR) (ih (R / 2) (by positivity))

theorem uniformQueryRadius_atRadius (c : Settings) (R S : ℝ) :
    uniformQueryRadius (atRadius c R) S = uniformQueryRadius c S := rfl

theorem one_radius_actual_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R) :
    ∀ q ∈ trace getter (oneRadiusProgram c sigma0 R start),
      radiusPrecision c sigma0 R ≤ q.2 ∧ ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c R := by
  have ht := actual_contraction_getter_trace (H.atRadius R hR) start hstart (contractionIterations c sigma0 R)
  simpa only [oneRadiusProgram, contractionProgram, OriginalCoupledQueryGeometry.trace_map_actual,
    contractionIterations_atRadius, radiusPrecision, uniformQueryRadius_atRadius] using ht

theorem actual_positive_restart_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (r : ℕ) (R : ℝ) (hR : 0 < R)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R) :
    ∀ q ∈ trace getter (restartProgram c sigma0 r R start),
      precisionMinimum c sigma0 r R ≤ q.2 ∧ ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c R := by
  induction r generalizing R start with
  | zero => simp only [restartProgram, trace, List.not_mem_nil, false_implies, implies_true]
  | succ r ih =>
    have hfirst := actual_positive_contraction_program (H.atRadius R hR) start hstart
    have hfirstdist : ‖(execute getter (oneRadiusProgram c sigma0 R start)).1 - RobustAHPE.globalMinimizer g‖ ≤ R / 2 := hfirst.1
    have hRhalf : 0 < R / 2 := by positivity
    have hsecond := ih (R / 2) hRhalf (execute getter (oneRadiusProgram c sigma0 R start)).1 hfirstdist
    intro q hq
    rw [restartProgram, OriginalCoupledQueryGeometry.trace_bind_actual, List.mem_append] at hq
    rcases hq with hq | hq
    · have h := one_radius_actual_trace H R hR start hstart q hq
      exact ⟨(min_le_left _ _).trans h.1, h.2⟩
    · have h := hsecond q hq
      exact ⟨(min_le_right _ _).trans h.1, h.2.trans
        (uniformQueryRadius_monotone c H.common (R / 2) R hRhalf.le (by linarith only [hR]))⟩

theorem actual_positive_restart_getter_count
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (r : ℕ) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    (execute getter (restartProgram c sigma0 r D start)).2 ≤
      contractionIterations c sigma0 D * r * coefficientMaximum (radiusGetterFactor c sigma0) r D := by
  have hs := (actual_positive_restarts H (fun _ => 0) 0 (by norm_num) (fun _ _ => Nat.zero_le _)
    r D H.D_pos start hstart).2.1
  have hsum := coefficient_sum_remove_iteration_factor H (radiusGetterFactor c sigma0) r D H.D_pos.le le_rfl
  have hmax := coefficient_sum_le_maximum (radiusGetterFactor c sigma0) r D
  calc
    _ ≤ contractionIterations c sigma0 D * coefficientSum (radiusGetterFactor c sigma0) r D := hs.trans hsum
    _ ≤ contractionIterations c sigma0 D * (coefficientMaximum (radiusGetterFactor c sigma0) r D * r) := Nat.mul_le_mul_left _ hmax
    _ = _ := by ring

theorem actual_positive_restarts_to_accuracy
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (tau : ℝ) (htau : 0 < tau) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let r := FangqingHysteresis.halvingCount D tau
    let p := restartProgram c sigma0 r D start
    ‖(execute getter p).1 - RobustAHPE.globalMinimizer g‖ ≤ tau ∧
      0 < precisionMinimum c sigma0 r D ∧
      (execute getter p).2 ≤ contractionIterations c sigma0 D * r * coefficientMaximum (radiusGetterFactor c sigma0) r D ∧
      (∀ q ∈ trace getter p, precisionMinimum c sigma0 r D ≤ q.2 ∧ ‖q.1 - start‖ ≤ uniformQueryRadius c D + D) ∧
      (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) := by
  dsimp only
  let r := FangqingHysteresis.halvingCount D tau
  have hs := actual_positive_restarts H (fun _ => 0) 0 (by norm_num) (fun _ _ => Nat.zero_le _) r D H.D_pos start hstart
  have hlog0 : 0 ≤ Real.logb 2 (max 1 (D / tau)) := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hr : (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) := by
    have h := (Nat.ceil_lt_add_one hlog0).le
    change (r : ℝ) ≤ _ at h
    linarith only [h]
  refine ⟨hs.1.trans (FangqingHysteresis.halving_precision D tau htau), precisionMinimum_positive H r D H.D_pos,
    actual_positive_restart_getter_count H r start hstart, ?_, hr⟩
  intro q hq
  have h := actual_positive_restart_trace H r D H.D_pos start hstart q hq
  exact ⟨h.1, (norm_sub_le_norm_sub_add_norm_sub q.1 (RobustAHPE.globalMinimizer g) start).trans
    (add_le_add h.2 (by simpa only [norm_sub_rev] using hstart))⟩

end OriginalRobustTrajectory


namespace OriginalActualDualSecondOrderWarm
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalDualCurvature OriginalDualMinimizer
open OriginalBetaATSTrial OriginalRobustTrajectory
open OriginalDualGetterImplementation OriginalDualGetterResourceComposition
open OriginalActualDualPositiveContraction FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def dualProgram (mu L rho D tol : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F :=
  if 0 < D then primitiveLower (oracleProgram L rho x uInit)
    (restartProgram (parameters mu L rho D) (1 / 2) (FangqingHysteresis.halvingCount D tol) D yin)
  else .pure yin

noncomputable def dualQueryBudget (J : Joint E F → ℝ) (mu L rho D tol : ℝ) (x uInit : E) (yin : F) : ℕ :=
  if 0 < D then
    let c := parameters mu L rho D
    let r := FangqingHysteresis.halvingCount D tol
    queryBallBudget J L rho x uInit yin (uniformQueryRadius c D + D) (precisionMinimum c (1 / 2) r D) *
      (contractionIterations c (1 / 2) D * r * coefficientMaximum (radiusGetterFactor c (1 / 2)) r D)
  else 0

theorem actual_positive_dual_restarts
    (J : Joint E F → ℝ) (mu L rho D tol : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htol : 0 < tol)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (dualProgram mu L rho D tol x uInit yin)
    ‖run.1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ tol ∧
      run.2 ≤ dualQueryBudget J mu L rho D tol x uInit yin := by
  classical
  by_cases hD : 0 < D
  · let g := psi J L x
    let c := parameters mu L rho D
    let getter := actualGetter J L rho x uInit
    let r := FangqingHysteresis.halvingCount D tol
    let p := restartProgram c (1 / 2) r D yin
    have hgC2 := psi_contDiff2 J L hL hC2 hLip x
    have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
    have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
    have hgHess := psi_hessian_lipschitz J L rho hL hrho.le hC2 hLip hHess x
    have hgetter := actual_getter_accuracy J L rho hL hrho.le hC2 hLip hHess x uInit
    have H : Hypotheses g c (1 / 2) D getter :=
      ⟨parameters_common mu L rho D hmu hL hrho hD, hD, by norm_num [c, parameters],
        by norm_num, rfl, hgC2, hgsc, hglip, hgHess, hgetter⟩
    have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
    have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
    have hvs : vStar (JointSliceRegularity.curry J) L x = RobustAHPE.globalMinimizer g :=
      RobustAHPE.globalMinimizer_unique g mu hmu (hgC2.differentiable (by norm_num)) hgsc _ hmin
    have hstart : ‖yin - RobustAHPE.globalMinimizer g‖ ≤ D := by rwa [← hvs]
    have h := actual_positive_restarts_to_accuracy H tol htol yin hstart
    have hresource := actual_original_queries_from_checked_getter_budget J L rho hL hrho.le hLip x uInit yin
      (uniformQueryRadius c D + D) (precisionMinimum c (1 / 2) r D) h.2.1 p
      (contractionIterations c (1 / 2) D * r * coefficientMaximum (radiusGetterFactor c (1 / 2)) r D)
      (fun q hq => (h.2.2.2.1 q hq).2) (fun q hq => (h.2.2.2.1 q hq).1) h.2.2.1
    have hresult := actual_original_program_result J L rho x uInit p
    constructor
    · simp only [dualProgram, if_pos hD]
      change ‖(execute (OriginalDualOracleProgram.actualOracle J)
        (primitiveLower (oracleProgram L rho x uInit) p)).1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ _
      rw [hresult, hvs]
      exact h.1
    · simpa only [dualProgram, dualQueryBudget, if_pos hD] using hresource
  · have hD0 : D = 0 := le_antisymm (le_of_not_gt hD) ((norm_nonneg _).trans hwarm)
    simp only [dualProgram, dualQueryBudget, if_neg hD, execute, Nat.le_refl, and_true]
    rw [hD0] at hwarm
    exact hwarm.trans htol.le

noncomputable def warmProgram (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  OriginalDualPrimalRecovery.program L tau x uInit (dualProgram mu L rho D (tau / 4) x uInit yin)

noncomputable def warmQueryBudget (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  dualQueryBudget J mu L rho D (tau / 4) x uInit yin + OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin

theorem actual_positive_second_order_joint_warm_solve
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (warmProgram mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ warmQueryBudget J mu L rho D tau x uInit yin := by
  have hdual := actual_positive_dual_restarts J mu L rho D (tau / 4) hmu hL hrho (by positivity)
    hC2 hLip hHess hsc x uInit yin hwarm
  have hrecover := OriginalDualPrimalRecovery.actual_joint_recovery_from_actual_dual_program
    J mu L rho D tau hmu hL hrho.le htau hC2 hLip hHess hsc x uInit yin hwarm
    (dualProgram mu L rho D (tau / 4) x uInit yin) hdual.1
  exact ⟨hrecover.1, hrecover.2.trans (add_le_add hdual.2 le_rfl)⟩

end OriginalActualDualSecondOrderWarm


namespace OriginalZeroCurvatureDualWarm
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalPrimalElimination OriginalDualCurvature OriginalDualMinimizer
open OriginalDualGetterImplementation OriginalDualResidualQueryBound
open OriginalDualGetterResourceComposition
open OriginalBetaATSTrial OriginalZeroCurvatureSearch OriginalZeroQueryGeometry
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def dualProgram (mu L tol : ℝ) (yin : F) : GetterProgram (F × ℝ) (Answer F) (TrialResult F) :=
  zeroProgram mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8) yin yin
noncomputable def dualFloor (getter : F × ℝ → Answer F) (mu L tol : ℝ) (yin : F) : ℝ :=
  zeroPrecisionFloor getter mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8) yin yin
noncomputable def dualBall (getter : F × ℝ → Answer F) (mu L : ℝ) (yin : F) : ℝ :=
  ‖yin - yin‖ + 2 * (observedBound getter (2 * L) yin yin + mu / 4) / mu
noncomputable def dualOriginalProgram (mu L tol : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (TrialResult F) :=
  primitiveLower (oracleProgram L 0 x uInit) (dualProgram mu L tol yin)
noncomputable def dualQueryBudget (J : Joint E F → ℝ) (mu L tol : ℝ) (x uInit : E) (yin : F) : ℕ :=
  let getter := actualGetter J L 0 x uInit
  queryBallBudget J L 0 x uInit yin (dualBall getter mu L yin) (dualFloor getter mu L tol yin)

theorem actual_zero_dual_accuracy
    (J : Joint E F → ℝ) (mu L tol : ℝ) (hmu : 0 < mu) (hL : 0 < L) (htol : 0 < tol)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hH0 : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) :
    ∃ v : F,
      (execute (OriginalDualOracleProgram.actualOracle J) (dualOriginalProgram mu L tol x uInit yin)).1 = .stop v ∧
      ‖v - vStar (JointSliceRegularity.curry J) L x‖ ≤ tol ∧
      (execute (OriginalDualOracleProgram.actualOracle J) (dualOriginalProgram mu L tol x uInit yin)).2 ≤
        3 * dualQueryBudget J mu L tol x uInit yin := by
  let getter := actualGetter J L 0 x uInit
  let g := psi J L x
  have hgC2 := psi_contDiff2 J L hL hC2 hLip x
  have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
  have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
  have hgH0 : ∀ z w : F, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
    simpa only [mul_zero, zero_mul] using psi_hessian_lipschitz J L 0 hL (by norm_num) hC2 hLip hH0 x
  have hgetter := actual_getter_accuracy J L 0 hL (by norm_num) hC2 hLip hH0 x uInit
  obtain ⟨v, hrun, hgrad, hcount, hfloor, _⟩ := zeroProgram_small_gradient_and_logarithmic_cost g mu (2 * L) 1
    (1 / 4) (mu * tol) (mu * tol / 8) hmu (by positivity) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by positivity) le_rfl hgC2 hgsc hglip hgH0 getter hgetter
    (fun _ => 0) 0 (by norm_num) (fun _ _ => Nat.zero_le _) yin yin
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
  have hdist := PacketCore.strongConvex_gradient_distance g mu hmu hgsc
    (hgC2.differentiable (by norm_num)) _ hmin v
  have hv : ‖v - vStar (JointSliceRegularity.curry J) L x‖ ≤ tol := by
    apply (mul_le_mul_iff_right₀ hmu).mp
    nlinarith only [hdist, hgrad]
  have hpoints := zeroProgram_actual_query_ball g mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8)
    hmu (by positivity) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    hgC2 hgsc hglip getter hgetter yin yin
  have hprecisions := zeroProgram_trace_floor getter mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8) yin yin
  have hcost := actual_original_queries_from_checked_getter_budget J L 0 hL (by norm_num) hLip x uInit yin
    (dualBall getter mu L yin) (dualFloor getter mu L tol yin) hfloor (dualProgram mu L tol yin) 3
    hpoints hprecisions hcount
  have hbase := primitiveLower_execution (OriginalDualOracleProgram.actualOracle J) (oracleProgram L 0 x uInit)
    (dualProgram mu L tol yin)
  refine ⟨v, ?_, hv, ?_⟩
  · change (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L 0 x uInit) (dualProgram mu L tol yin))).1 = _
    rw [hbase]
    exact hrun
  · simpa only [dualOriginalProgram, dualQueryBudget, Nat.mul_comm] using hcost

noncomputable def recoverProgram (L tau : ℝ) (x uInit : E) (yin : F) : TrialResult F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F)
  | .stop v => FangqingGetterComposition.map (fun s : OriginalDualOracleProgram.QueryState E F =>
      JointSliceRegularity.point s.u v) (liftQuery (OriginalDualOracleProgram.simulator L x v uInit (tau / 4)))
  | .step _ _ => .pure (JointSliceRegularity.point uInit yin)
noncomputable def warmProgram (mu L tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  FangqingGetterComposition.bind (dualOriginalProgram mu L (tau / 4) x uInit yin) (recoverProgram L tau x uInit yin)
noncomputable def recoveryQueryBudget (J : Joint E F → ℝ) (L D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x uInit yin + (D + tau / 4)) / (tau / 4)))
noncomputable def warmQueryBudget (J : Joint E F → ℝ) (mu L D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  3 * dualQueryBudget J mu L (tau / 4) x uInit yin + recoveryQueryBudget J L D tau x uInit yin

theorem actual_zero_curvature_joint_warm_solve
    (J : Joint E F → ℝ) (mu L D tau : ℝ) (hmu : 0 < mu) (hL : 0 < L) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hH0 : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (warmProgram mu L tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ warmQueryBudget J mu L D tau x uInit yin := by
  let first := execute (OriginalDualOracleProgram.actualOracle J) (dualOriginalProgram mu L (tau / 4) x uInit yin)
  obtain ⟨v, hfirst, hv, hfirstCost⟩ := actual_zero_dual_accuracy J mu L (tau / 4) hmu hL (by positivity)
    hC2 hLip hH0 hsc x uInit yin
  let last := OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
    (OriginalDualOracleProgram.simulator L x v uInit (tau / 4))
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpu := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hlast := OriginalDualOracleProgram.reduced_dual_oracle_simulation J L 0 hL (by norm_num)
    hC2 hLip hH0 x uInit v (tau / 4) (by positivity)
  have hprimal := primal_lipschitz J L hL hJ hLip x v (vStar (JointSliceRegularity.curry J) L x)
  rw [hpu] at hprimal
  have hu : ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ≤ tau / 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub last.1.u (primal J L x v) (uStar (JointSliceRegularity.curry J) L x)
    have hd : ‖last.1.u - primal J L x v‖ ≤ tau / 4 := hlast.2.1
    linarith only [ht, hd, hprimal, hv]
  have hball : ‖v - yin‖ ≤ D + tau / 4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub v (vStar (JointSliceRegularity.curry J) L x) yin
    rw [norm_sub_rev (vStar (JointSliceRegularity.curry J) L x) yin] at ht
    linarith only [ht, hwarm, hv]
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x uInit v yin (D + tau / 4)
    (tau / 4) (by positivity) hball
  have hlastCost : last.2 ≤ recoveryQueryBudget J L D tau x uInit yin := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact hc.trans (Nat.le_ceil _)
  have hexec : execute (OriginalDualOracleProgram.actualOracle J) (warmProgram mu L tau x uInit yin) =
      (JointSliceRegularity.point last.1.u v, first.2 + last.2) := by
    simp only [warmProgram, execute_bind, hfirst, recoverProgram, execute_map, execute_liftQuery]
    rfl
  rw [hexec]
  constructor
  · have hn := WithLp.prod_norm_sq_eq_of_L2
      (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)
    have heq : ‖JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x‖ ^ 2 =
        ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ^ 2 +
          ‖v - vStar (JointSliceRegularity.curry J) L x‖ ^ 2 := by
      rw [JointSliceRegularity.point_eq_toLp] at hn ⊢
      exact hn
    have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 2)).mpr hu
    have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 4)).mpr hv
    nlinarith only [heq, hu2, hv2, htau,
      norm_nonneg (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)]
  · exact add_le_add hfirstCost hlastCost

end OriginalZeroCurvatureDualWarm


namespace OriginalSecondOrderWarmAll
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def program (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  if 0 < rho then OriginalActualDualSecondOrderWarm.warmProgram mu L rho D tau x uInit yin
  else OriginalZeroCurvatureDualWarm.warmProgram mu L tau x uInit yin

noncomputable def queryBudget (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  if 0 < rho then OriginalActualDualSecondOrderWarm.warmQueryBudget J mu L rho D tau x uInit yin
  else OriginalZeroCurvatureDualWarm.warmQueryBudget J mu L D tau x uInit yin

theorem actual_second_order_joint_warm_solve
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ queryBudget J mu L rho D tau x uInit yin := by
  classical
  by_cases hpos : 0 < rho
  · simpa only [program, queryBudget, if_pos hpos] using
      OriginalActualDualSecondOrderWarm.actual_positive_second_order_joint_warm_solve J mu L rho D tau
        hmu hL hpos htau hC2 hLip hHess hsc x uInit yin hwarm
  · have hrho0 : rho = 0 := le_antisymm (le_of_not_gt hpos) hrho
    have hH0 : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
      simpa only [hrho0] using hHess
    simpa only [program, queryBudget, if_neg hpos] using
      OriginalZeroCurvatureDualWarm.actual_zero_curvature_joint_warm_solve J mu L D tau
        hmu hL htau hC2 hLip hH0 hsc x uInit yin hwarm

end OriginalSecondOrderWarmAll


namespace OriginalZeroUniformResources

open OriginalBetaSearchEndpoints OriginalCoupledBetaAlgebra OriginalZeroCurvatureSearch

noncomputable section

theorem high_endpoint_lambda_upper (A H : ℝ) (hA : 0 < A) (hH : 0 ≤ H) :
    lambda A (betaHigh A H) ≤ 4 * A + 8 * (1 + H) := by
  have hp := betaHigh_properties A H hA hH
  have hmargin := hp.1
  have hbeta0 : 0 ≤ betaHigh A H := by linarith only [hp.2.2.1]
  have hbeta1 : betaHigh A H ≤ 1 := hp.2.2.2.1.le
  have hsquare : betaHigh A H ^ 2 ≤ 1 := by nlinarith only [hbeta0, hbeta1]
  have heq : 1 - betaHigh A H = highMargin A H := by unfold betaHigh; ring
  have hfirst : lambda A (betaHigh A H) ≤ A / highMargin A H := by
    unfold lambda
    rw [heq]
    apply div_le_div_of_nonneg_right _ hmargin.le
    nlinarith only [mul_le_mul_of_nonneg_left hsquare hA.le]
  refine hfirst.trans ?_
  unfold highMargin
  rcases le_total (1 / 4 : ℝ) (A / (8 * (1 + H))) with hl | hr
  · rw [min_eq_left hl]
    norm_num
    nlinarith only [hH]
  · rw [min_eq_right hr]
    have hid : A / (A / (8 * (1 + H))) = 8 * (1 + H) := by field_simp [ne_of_gt hA]
    rw [hid]
    linarith only [hA]

theorem large_lambda_mono (mu sigma rho G Gmax : ℝ)
    (hmu : 0 < mu) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hG : G ≤ Gmax) : largeLambda mu sigma rho G ≤ largeLambda mu sigma rho Gmax := by
  unfold largeLambda
  gcongr

def lambdaCeiling (mu sigma rho Gmax : ℝ) : ℝ :=
  4 + 8 * (1 + largeLambda mu sigma rho Gmax)

theorem initial_lambda_uniform_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (mu Lg sigma rho Gmax : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (x y : E) (a : OriginalBetaATSTrial.Answer E)
    (hGmax : ‖a.grad‖ + 1 + Lg * ‖x - y‖ ≤ Gmax) :
    1 ≤ initialLambda mu Lg 1 sigma rho x y a ∧
      initialLambda mu Lg 1 sigma rho x y a ≤ lambdaCeiling mu sigma rho Gmax := by
  let G := ‖a.grad‖ + 1 + Lg * ‖x - y‖
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hlarge : 1 ≤ largeLambda mu sigma rho G := by
    unfold largeLambda
    have hh : 0 ≤ 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho) := by positivity
    linarith only [hh]
  have hp := betaHigh_properties 1 (largeLambda mu sigma rho G) (by norm_num)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlarge)
  have hmono := large_lambda_mono mu sigma rho G Gmax hmu hsigma0 hsigma1 hrho hGmax
  have hu := high_endpoint_lambda_upper 1 (largeLambda mu sigma rho G) (by norm_num)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlarge)
  change 1 ≤ lambda 1 (betaHigh 1 (largeLambda mu sigma rho G)) ∧
    lambda 1 (betaHigh 1 (largeLambda mu sigma rho G)) ≤ 4 + 8 * (1 + largeLambda mu sigma rho Gmax)
  refine ⟨hlarge.trans hp.2.2.2.2, ?_⟩
  nlinarith only [hu, hmono]

def toleranceFloor (mu Lg sigma rho Gmax : ℝ) : ℝ :=
  OriginalBetaATSUniform.uniformTolerance mu Lg 0 1 (lambdaCeiling mu sigma rho Gmax) sigma rho

def precisionFloor (mu Lg sigma rho Gmax : ℝ) : ℝ :=
  min 1 (min (toleranceFloor mu Lg sigma rho Gmax) (rho / 8))

theorem initial_tolerance_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (mu Lg sigma rho Gmax : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (x y : E) (a : OriginalBetaATSTrial.Answer E)
    (hGmax : ‖a.grad‖ + 1 + Lg * ‖x - y‖ ≤ Gmax) :
    0 < toleranceFloor mu Lg sigma rho Gmax ∧
      toleranceFloor mu Lg sigma rho Gmax ≤ initialTolerance mu Lg 1 sigma rho x y a := by
  have hlambda := initial_lambda_uniform_bounds mu Lg sigma rho Gmax hmu hLg hsigma0.le hsigma1 hrho x y a hGmax
  have hlam : 0 < initialLambda mu Lg 1 sigma rho x y a := lt_of_lt_of_le zero_lt_one hlambda.1
  have hup : 0 < lambdaCeiling mu sigma rho Gmax := hlam.trans_le hlambda.2
  refine ⟨OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 1 _ sigma rho
    hmu hLg le_rfl zero_lt_one hup hsigma0 hrho, ?_⟩
  exact OriginalUniformBetaResources.uniform_tolerance_mono mu Lg 0 1 _ _ _ sigma rho
    hmu hLg le_rfl zero_lt_one hlambda.1 hlam hlambda.2 hsigma0 hrho

theorem zero_precision_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (getter : E × ℝ → OriginalBetaATSTrial.Answer E)
    (mu Lg sigma rho Gmax : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (x y : E)
    (hGmax : ‖(getter (y, 1)).grad‖ + 1 + Lg * ‖x - y‖ ≤ Gmax) :
    0 < precisionFloor mu Lg sigma rho Gmax ∧ precisionFloor mu Lg sigma rho Gmax ≤
      zeroPrecisionFloor getter mu Lg 1 sigma rho (rho / 8) x y := by
  have ht := initial_tolerance_uniform_bound mu Lg sigma rho Gmax hmu hLg hsigma0 hsigma1 hrho
    x y (getter (y, 1)) hGmax
  exact ⟨lt_min zero_lt_one (lt_min ht.1 (by positivity)), min_le_min le_rfl (min_le_min ht.2 le_rfl)⟩

end
end OriginalZeroUniformResources


namespace OriginalOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def model (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) : ℝ :=
  inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3

theorem model_hasGradientAt (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    HasGradientAt (model v H M) (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s) s := by
  have heq : CertifiedATS.model v H M 0 = model v H M := by
    funext d
    simp only [CertifiedATS.model, model, mul_zero, div_zero, zero_mul, add_zero]
  have hh := CertifiedATS.model_hasGradientAt v H M 0 s
  rw [heq] at hh
  simpa only [inv_zero, zero_smul, add_zero] using hh

theorem model_lower_bound (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    -‖v‖ * ‖s‖ - ‖H‖ / 2 * ‖s‖ ^ 2 + M / 6 * ‖s‖ ^ 3 ≤ model v H M s := by
  have hv := real_inner_le_norm (-v) s
  rw [inner_neg_left, norm_neg] at hv
  have hH := real_inner_le_norm (-(H s)) s
  rw [inner_neg_left, norm_neg] at hH
  have hn := mul_le_mul_of_nonneg_right (H.le_opNorm s) (norm_nonneg s)
  unfold model
  nlinarith only [hv, hH, hn]

def modelRadius (v : E) (H : E →L[ℝ] E) (M : ℝ) : ℝ :=
  1 + 12 * (‖v‖ + ‖H‖) / M

theorem model_nonnegative_outside (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M)
    (s : E) (hout : modelRadius v H M ≤ ‖s‖) : 0 ≤ model v H M s := by
  have hR : 1 ≤ modelRadius v H M := by
    have hh : 0 ≤ 12 * (‖v‖ + ‖H‖) / M := by positivity
    unfold modelRadius
    linarith only [hh]
  have hr : 1 ≤ ‖s‖ := hR.trans hout
  have hMr : 12 * (‖v‖ + ‖H‖) ≤ M * ‖s‖ := by
    have hh := mul_le_mul_of_nonneg_left hout hM.le
    dsimp only [modelRadius] at hh
    have hid : M * (1 + 12 * (‖v‖ + ‖H‖) / M) = M + 12 * (‖v‖ + ‖H‖) := by
      field_simp <;> ring
    rw [hid] at hh
    linarith only [hh, hM]
  have hmul := mul_le_mul_of_nonneg_right hMr (sq_nonneg ‖s‖)
  have hvr : ‖v‖ * ‖s‖ ≤ ‖v‖ * ‖s‖ ^ 2 := by
    have hh : ‖s‖ ≤ ‖s‖ ^ 2 := by nlinarith only [hr]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg v)
  have hH0 := mul_nonneg (norm_nonneg H) (sq_nonneg ‖s‖)
  have hv0 := mul_nonneg (norm_nonneg v) (sq_nonneg ‖s‖)
  have hlower := model_lower_bound v H M s
  nlinarith only [hmul, hvr, hH0, hv0, hlower]

theorem exists_model_minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∃ s : E, ∀ t : E, model v H M s ≤ model v H M t := by
  let R := modelRadius v H M
  have hR : 0 < R := by dsimp only [R, modelRadius]; positivity
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR.le
  have hcont : Continuous (model v H M) :=
    (show Differentiable ℝ (model v H M) from fun s => (model_hasGradientAt v H M s).differentiableAt).continuous
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨s, ?_⟩
  intro t
  by_cases ht : t ∈ Metric.closedBall 0 R
  · exact hmin ht
  · have hout : modelRadius v H M ≤ ‖t‖ := by
      have hh : R < ‖t‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using ht
      exact hh.le
    have hs0 : model v H M s ≤ model v H M 0 := hmin hzero
    have h0 : model v H M 0 = 0 := by simp only [model, inner_zero_right, norm_zero]; ring
    rw [h0] at hs0
    exact hs0.trans (model_nonnegative_outside v H M hM t hout)

def minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) : E :=
  Classical.epsilon (fun s : E => ∀ t : E, model v H M s ≤ model v H M t)

theorem minimizer_is_actual (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∀ t : E, model v H M (minimizer v H M) ≤ model v H M t :=
  Classical.epsilon_spec (exists_model_minimizer v H M hM)

theorem minimizer_equation_and_decrease (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    let s := minimizer v H M
    v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 ∧
      model v H M s ≤ -(M / 12) * ‖s‖ ^ 3 := by
  dsimp only
  let s := minimizer v H M
  have hmin := minimizer_is_actual v H M hM
  have hloc : IsLocalMin (model v H M) s := Filter.Eventually.of_forall hmin
  have hg := hloc.hasFDerivAt_eq_zero (model_hasGradientAt v H M s).hasFDerivAt
  have heq : v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 := by
    have hh := congrArg (fun D : E →L[ℝ] ℝ => D (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s)) hg
    simpa only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.zero_apply,
      real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hh
  have hinner := congrArg (fun w : E => inner ℝ w s) heq
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at hinner
  have hsym : inner ℝ (CertifiedATS.sympart H s) s = inner ℝ (H s) s := by
    simp only [CertifiedATS.sympart, smul_apply, add_apply, real_inner_smul_left,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left, real_inner_comm s (H s)]
    ring
  rw [hsym] at hinner
  have hmirror := hmin (-s)
  have hneg : model v H M (-s) = -inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 := by
    simp only [model, inner_neg_right, map_neg, inner_neg_left, neg_neg, norm_neg]
  rw [hneg] at hmirror
  dsimp only [model] at hmirror ⊢
  refine ⟨heq, ?_⟩
  nlinarith only [hinner, hmirror]

end
end OriginalOuterCubic


namespace OriginalCubicTerminalCounterexample
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalSaddleTangent

abbrev Plane := WithLp 2 (ℝ × ℝ)
noncomputable def point (x y : ℝ) : Plane := WithLp.toLp 2 (x, y)
noncomputable def hessian (H : ℝ) : Plane →L[ℝ] Plane :=
  H • (primalProjection (E := ℝ) (F := ℝ))
noncomputable def energy (H : ℝ) (z : Plane) : ℝ := H / 2 * z.fst ^ 2
noncomputable def start (H : ℝ) : Plane := point (2 / H) 0
noncomputable def observedGradient (c : ℝ) : Plane := point 2 c
noncomputable def step (H c : ℝ) : Plane :=
  OriginalOuterCubic.minimizer (observedGradient c) (hessian H) 1

theorem hessian_fst (H : ℝ) (z : Plane) : (hessian H z).fst = H * z.fst := rfl

theorem hessian_snd (H : ℝ) (z : Plane) : (hessian H z).snd = 0 := by
  change H * 0 = 0
  ring

theorem norm_sq_components (z : Plane) : ‖z‖ ^ 2 = z.fst ^ 2 + z.snd ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using WithLp.prod_norm_sq_eq_of_L2 z

theorem energy_contDiff (H : ℝ) : ContDiff ℝ 2 (energy H) :=
  contDiff_const.mul ((WithLp.fstL 2 ℝ ℝ ℝ).contDiff.pow 2)

theorem energy_hasGradientAt (H : ℝ) (z : Plane) : HasGradientAt (energy H) (hessian H z) z := by
  have hf := ((WithLp.fstL 2 ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2
  have hd : HasFDerivAt (energy H) ((H * z.fst) • WithLp.fstL 2 ℝ ℝ ℝ) z := by
    convert! hf.const_mul (H / 2) using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
    change (H * z.fst) * v.fst = (H / 2) * ((2 : ℝ) * z.fst ^ (2 - 1) * v.fst)
    ring
  rw [hasGradientAt_iff_hasFDerivAt]
  have heq : InnerProductSpace.toDual ℝ Plane (hessian H z) = (H * z.fst) • WithLp.fstL 2 ℝ ℝ ℝ := by
    ext v
    rw [InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply]
    change inner ℝ (hessian H z).fst v.fst + inner ℝ (hessian H z).snd v.snd = _
    rw [hessian_fst, hessian_snd]
    simp only [Real.inner_apply, zero_mul, add_zero, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [heq]
  exact hd

theorem actual_hessian (H : ℝ) (z : Plane) : fderiv ℝ (gradient (energy H)) z = hessian H := by
  have heq : gradient (energy H) = hessian H := by funext w; exact (energy_hasGradientAt H w).gradient
  rw [heq]
  exact (hessian H).fderiv

theorem norm_gradient (H : ℝ) (z : Plane) : ‖gradient (energy H) z‖ = |H * z.fst| := by
  rw [(energy_hasGradientAt H z).gradient]
  have heq : hessian H z = JointSliceRegularity.axisX (F := ℝ) (H * z.fst) := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · exact hessian_fst H z
    · exact hessian_snd H z
  rw [heq, JointSliceRegularity.norm_axisX, Real.norm_eq_abs]

theorem initial_gap_and_bounded_below (H : ℝ) (hH : 0 < H) :
    (∀ z : Plane, 0 ≤ energy H z) ∧ energy H 0 = 0 ∧ energy H (start H) = 2 / H := by
  refine ⟨fun z => by dsimp [energy]; positivity, by simp [energy], ?_⟩
  change H / 2 * (2 / H) ^ 2 = 2 / H
  field_simp <;> ring

theorem hessian_lipschitz_zero (H : ℝ) :
    ∀ z w : Plane, ‖fderiv ℝ (gradient (energy H)) z - fderiv ℝ (gradient (energy H)) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
  intro z w
  simp only [actual_hessian, sub_self, norm_zero, zero_mul, le_refl]

theorem sympart_hessian (H : ℝ) : CertifiedATS.sympart (hessian H) = hessian H := by
  have hadj : (hessian H).adjoint = hessian H := by simp only [hessian, map_smul, primalProjection_selfadjoint]
  simp only [CertifiedATS.sympart, hadj]
  module

theorem actual_model_equations (H c : ℝ) :
    (∀ t : Plane, OriginalOuterCubic.model (observedGradient c) (hessian H) 1 (step H c) ≤
      OriginalOuterCubic.model (observedGradient c) (hessian H) 1 t) ∧
    (2 + H * (step H c).fst + (‖step H c‖ / 2) * (step H c).fst = 0) ∧
    (c + (‖step H c‖ / 2) * (step H c).snd = 0) := by
  have heq := (OriginalOuterCubic.minimizer_equation_and_decrease (observedGradient c) (hessian H) 1 (by norm_num)).1
  rw [sympart_hessian] at heq
  have hx := congrArg (fun z : Plane => z.fst) heq
  have hy := congrArg (fun z : Plane => z.snd) heq
  change 2 + H * (step H c).fst + (1 / 2 * ‖step H c‖) * (step H c).fst = 0 at hx
  simp only [WithLp.add_snd, WithLp.smul_snd, WithLp.zero_snd, hessian_snd, smul_eq_mul] at hy
  change c + 0 + (1 / 2 * ‖step H c‖) * (step H c).snd = 0 at hy
  exact ⟨OriginalOuterCubic.minimizer_is_actual _ _ 1 (by norm_num), by nlinarith only [hx], by nlinarith only [hy]⟩


theorem actual_step_geometry (H c : ℝ) (hH : 16 ≤ H) (hc : 0 < c) (hc1 : c ≤ 1) :
    2 * c ≤ ‖step H c‖ ^ 2 ∧ ‖step H c‖ ≤ 3 ∧ c ^ 2 ≤ ‖step H c‖ ^ 3 ∧
      ‖gradient (energy H) (start H + step H c)‖ ≤ 1 / 2 := by
  let d := step H c
  let r := ‖d‖
  have heq := actual_model_equations H c
  have hx : 2 + H * d.fst + (r / 2) * d.fst = 0 := heq.2.1
  have hy : c + (r / 2) * d.snd = 0 := heq.2.2
  have hr0 : 0 ≤ r := norm_nonneg d
  have hr : 0 < r := by
    by_contra hn
    have hz : r = 0 := le_antisymm (le_of_not_gt hn) hr0
    rw [hz] at hy
    simp only [zero_div, zero_mul, add_zero] at hy
    exact (ne_of_gt hc) hy
  have hsnd : |d.snd| ≤ r := WithLp.norm_snd_le ℝ d
  have hneg : -d.snd ≤ r := by have hh := (abs_le.mp hsnd).1; linarith only [hh]
  have hnegmul := mul_le_mul_of_nonneg_left hneg (show 0 ≤ r / 2 by positivity)
  have hlower : 2 * c ≤ r ^ 2 := by nlinarith only [hy, hnegmul]
  have hgtSq := norm_sq_components (observedGradient c)
  change ‖observedGradient c‖ ^ 2 = 2 ^ 2 + c ^ 2 at hgtSq
  have hcSq : c ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ hc.le (by norm_num : (0 : ℝ) ≤ 1)).mpr hc1
  have hgt : ‖observedGradient c‖ ≤ 3 := by nlinarith only [hgtSq, hcSq, norm_nonneg (observedGradient c)]
  have hnorm : r ^ 2 = d.fst ^ 2 + d.snd ^ 2 := norm_sq_components d
  have hnormmul := congrArg (fun t : ℝ => (r / 2) * t) hnorm
  have hxmul := congrArg (fun t : ℝ => t * d.fst) hx
  have hymul := congrArg (fun t : ℝ => t * d.snd) hy
  have hi := real_inner_le_norm (-(observedGradient c)) d
  rw [inner_neg_left, norm_neg, WithLp.prod_inner_apply] at hi
  simp only [Real.inner_apply] at hi
  change -(2 * d.fst + c * d.snd) ≤ ‖observedGradient c‖ * r at hi
  have hHsq : 0 ≤ H * d.fst ^ 2 := mul_nonneg (by linarith : 0 ≤ H) (sq_nonneg _)
  have hupper : (r ^ 2 / 2) * r ≤ ‖observedGradient c‖ * r := by
    nlinarith only [hxmul, hymul, hnormmul, hi, hHsq]
  have hhalf : r ^ 2 / 2 ≤ ‖observedGradient c‖ := (mul_le_mul_iff_left₀ hr).mp hupper
  have hrSq : r ^ 2 ≤ 6 := by linarith only [hhalf, hgt]
  have hr3 : r ≤ 3 := by nlinarith only [hrSq, hr0]
  have hc4 : (2 * c) ^ 2 ≤ (r ^ 2) ^ 2 := (sq_le_sq₀ (by positivity) (sq_nonneg _)).mpr hlower
  have hr4 := mul_le_mul_of_nonneg_right hr3 (pow_nonneg hr0 3)
  have hcube : c ^ 2 ≤ r ^ 3 := by nlinarith only [hc4, hr4, sq_nonneg c]
  have hHpos : 0 < H := by linarith only [hH]
  have hcoef : 0 < H + r / 2 := by positivity
  have hdneg : d.fst < 0 := by
    by_contra hn
    have hp := mul_nonneg hcoef.le (le_of_not_gt hn)
    nlinarith only [hp, hx]
  have hdu : |d.fst| ≤ 2 / H := by
    rw [abs_of_neg hdneg]
    apply (le_div_iff₀ hHpos).mpr
    have hp := mul_nonpos_of_nonneg_of_nonpos hr0 hdneg.le
    nlinarith only [hx, hp]
  have hpost : H * (2 / H + d.fst) = -(r / 2 * d.fst) := by
    have hcancel : H * (2 / H) = 2 := by field_simp
    nlinarith only [hx, hcancel]
  have hnew : ‖gradient (energy H) (start H + d)‖ ≤ 1 / 2 := by
    rw [norm_gradient]
    change |H * (2 / H + d.fst)| ≤ 1 / 2
    rw [hpost, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < r / 2)]
    calc
      (r / 2) * |d.fst| ≤ (r / 2) * (2 / H) := mul_le_mul_of_nonneg_left hdu (by positivity)
      _ = r / H := by ring
      _ ≤ 3 / H := div_le_div_of_nonneg_right hr3 hHpos.le
      _ ≤ 1 / 2 := (div_le_iff₀ hHpos).mpr (by linarith only [hH])
  exact ⟨hlower, hr3, hcube, hnew⟩


theorem energy_infimum (H : ℝ) (hH : 0 < H) : sInf (Set.range (energy H)) = 0 := by
  have hb := initial_gap_and_bounded_below H hH
  have hbounded : BddBelow (Set.range (energy H)) := ⟨0, by rintro _ ⟨z, rfl⟩; exact hb.1 z⟩
  have hmem : (0 : ℝ) ∈ Set.range (energy H) := ⟨0, hb.2.1⟩
  exact le_antisymm (csInf_le hbounded hmem) (le_csInf (Set.range_nonempty _) (by rintro _ ⟨z, rfl⟩; exact hb.1 z))

theorem gradient_at_start (H : ℝ) (hH : 0 < H) : gradient (energy H) (start H) = point 2 0 := by
  rw [(energy_hasGradientAt H (start H)).gradient]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change H * (2 / H) = 2
    field_simp
  · exact hessian_snd H (start H)

theorem terminal_point_differs (H c : ℝ) (hc : 0 < c) : start H + step H c ≠ start H := by
  intro heq
  have hs := congrArg (fun z : Plane => z.snd) heq
  change 0 + (step H c).snd = 0 at hs
  have hy := (actual_model_equations H c).2.2
  rw [zero_add] at hs
  rw [hs, mul_zero, add_zero] at hy
  exact (ne_of_gt hc) hy

noncomputable def getter (H c : ℝ) : Plane × ℝ → Answer Plane := by
  classical
  exact fun q => ⟨gradient (energy H) q.1 +
    (if q.1 = start H then JointSliceRegularity.axisY (E := ℝ) (min c q.2) else 0), hessian H⟩

theorem getter_correct (H c : ℝ) (hc : 0 < c) (z : Plane) (eta : ℝ) (heta : 0 < eta) :
    ‖(getter H c (z, eta)).grad - gradient (energy H) z‖ ≤ eta ∧
      ‖(getter H c (z, eta)).hess - fderiv ℝ (gradient (energy H)) z‖ ≤ eta := by
  classical
  constructor
  · unfold getter
    dsimp only
    split_ifs
    · have heq : gradient (energy H) z + JointSliceRegularity.axisY (E := ℝ) (min c eta) -
          gradient (energy H) z = JointSliceRegularity.axisY (E := ℝ) (min c eta) := by abel
      rw [heq, JointSliceRegularity.norm_axisY, Real.norm_eq_abs, abs_of_nonneg (le_min hc.le heta.le)]
      exact min_le_right _ _
    · simpa only [add_zero, sub_self, norm_zero] using heta.le
  · simpa only [getter, actual_hessian, sub_self, norm_zero] using heta.le

theorem getter_at_start (H c eta : ℝ) (hH : 0 < H) (hc : c ≤ eta) :
    getter H c (start H, eta) = ⟨observedGradient c, hessian H⟩ := by
  classical
  simp only [getter, if_pos rfl, min_eq_left hc]
  rw [gradient_at_start H hH]
  apply congrArg (fun v : Plane => Answer.mk v (hessian H))
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change 2 + 0 = 2
    ring
  · change 0 + c = c
    ring

theorem getter_at_terminal (H c eta : ℝ) (hc : 0 < c) :
    getter H c (start H + step H c, eta) =
      ⟨gradient (energy H) (start H + step H c), hessian H⟩ := by
  simp only [getter, if_neg (terminal_point_differs H c hc), add_zero]

structure StandardOutput where
  point : Plane
  success : Bool
  moves : ℕ
  cubicSteps : ℝ

noncomputable def standardIteration (H : ℝ) : GetterProgram (Plane × ℝ) (Answer Plane) StandardOutput := by
  classical
  exact .ask (start H, 1 / 1024) (fun initial =>
    if ‖initial.grad‖ ≤ 1 / 2 then .pure ⟨start H, true, 0, 0⟩ else
      let d := OriginalOuterCubic.minimizer initial.grad initial.hess 1
      .ask (start H + d, 1 / 1024) (fun final =>
        .pure ⟨start H + d, if ‖final.grad‖ ≤ 1 / 2 then true else false, 1, ‖d‖ ^ 3⟩))

theorem actual_standard_iteration (H c : ℝ) (hH : 16 ≤ H) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    execute (getter H c) (standardIteration H) =
      (⟨start H + step H c, true, 1, ‖step H c‖ ^ 3⟩, 2) := by
  have hHpos : 0 < H := by linarith only [hH]
  have hc1 : c ≤ 1 := by linarith only [hsmall]
  have hfirst := getter_at_start H c (1 / 1024) hHpos (by linarith only [hsmall])
  have hnext := getter_at_terminal H c (1 / 1024) hc
  have hstop := (actual_step_geometry H c hH hc hc1).2.2.2
  have hnonstop : ¬ ‖observedGradient c‖ ≤ (1 / 2 : ℝ) := by
    have hh := WithLp.norm_fst_le ℝ (observedGradient c)
    change |(2 : ℝ)| ≤ ‖observedGradient c‖ at hh
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith only [hh]
  dsimp only [step] at hnext hstop
  simp only [standardIteration, execute, hfirst, if_neg hnonstop, hnext, if_pos hstop]
  rfl

theorem no_uniform_terminal_included_cubic_sum_bound
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    ∃ H : ℝ, 16 ≤ H ∧ ContDiff ℝ 2 (energy H) ∧
      (∀ z : Plane, 0 ≤ energy H z) ∧ sInf (Set.range (energy H)) = 0 ∧
      energy H (start H) - sInf (Set.range (energy H)) = 2 / H ∧
      (∀ z w : Plane, ‖fderiv ℝ (gradient (energy H)) z - fderiv ℝ (gradient (energy H)) w‖ ≤ (0 : ℝ) * ‖z - w‖) ∧
      (∀ z : Plane, ∀ eta : ℝ, 0 < eta →
        ‖(getter H c (z, eta)).grad - gradient (energy H) z‖ ≤ eta ∧
        ‖(getter H c (z, eta)).hess - fderiv ℝ (gradient (energy H)) z‖ ≤ eta) ∧
      (∀ t : Plane, OriginalOuterCubic.model (observedGradient c) (hessian H) 1 (step H c) ≤
        OriginalOuterCubic.model (observedGradient c) (hessian H) 1 t) ∧
      2 * c ≤ ‖step H c‖ ^ 2 ∧
      (execute (getter H c) (standardIteration H)).1.success = true ∧
      (execute (getter H c) (standardIteration H)).1.moves = 1 ∧
      ‖gradient (energy H) (execute (getter H c) (standardIteration H)).1.point‖ ≤ 1 / 2 ∧
      C * (energy H (start H) - sInf (Set.range (energy H))) <
        (execute (getter H c) (standardIteration H)).1.cubicSteps := by
  let H := 16 + 4 * (C + 1) / c ^ 2
  have hH : 16 ≤ H := by
    have hp : 0 ≤ 4 * (C + 1) / c ^ 2 := by positivity
    dsimp [H]
    linarith only [hp]
  have hHpos : 0 < H := by linarith only [hH]
  have hgap := initial_gap_and_bounded_below H hHpos
  have hinf := energy_infimum H hHpos
  have hr := actual_step_geometry H c hH hc (by linarith only [hsmall])
  have hexec := actual_standard_iteration H c hH hc hsmall
  have hcSq : 0 < c ^ 2 := sq_pos_of_pos hc
  have hHc : 2 * C < H * c ^ 2 := by
    have heq : H * c ^ 2 = 16 * c ^ 2 + 4 * (C + 1) := by dsimp [H]; field_simp <;> ring
    rw [heq]
    nlinarith only [hC, hcSq]
  have hviolate : C * (2 / H) < ‖step H c‖ ^ 3 := by
    have hh : C * (2 / H) < c ^ 2 := by
      have heq : C * (2 / H) = 2 * C / H := by ring
      rw [heq]
      exact (div_lt_iff₀ hHpos).mpr (by nlinarith only [hHc])
    exact hh.trans_le hr.2.2.1
  refine ⟨H, hH, energy_contDiff H, hgap.1, hinf, ?_, hessian_lipschitz_zero H,
    getter_correct H c hc, (actual_model_equations H c).1, hr.1, ?_, ?_, ?_, ?_⟩
  · rw [hinf, sub_zero]
    exact hgap.2.2
  · rw [hexec]
  · rw [hexec]
  · rw [hexec]
    exact hr.2.2.2
  · rw [hexec, hinf, sub_zero, hgap.2.2]
    exact hviolate

end OriginalCubicTerminalCounterexample


namespace OriginalOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem cubic_taylor_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z s : E) :
    f (z + s) ≤ f z + inner ℝ (gradient f z) s +
      (1 / 2 : ℝ) * inner ℝ (fderiv ℝ (gradient f) z s) s + M / 6 * ‖s‖ ^ 3 := by
  let H := fderiv ℝ (gradient f) z
  let phi : ℝ → ℝ := fun t => f (z + t • s) - f z - t * inner ℝ (gradient f z) s -
    t ^ 2 / 2 * inner ℝ (H s) s - (M / 6 * ‖s‖ ^ 3) * t ^ 3
  let phi' : ℝ → ℝ := fun t => inner ℝ (gradient f (z + t • s)) s -
    inner ℝ (gradient f z) s - t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2
  have hdiff : Differentiable ℝ f := hC2.differentiable (by norm_num)
  have hderiv : ∀ t : ℝ, HasDerivAt phi (phi' t) t := by
    intro t
    have hcurve : HasDerivAt (fun t : ℝ => z + t • s) s t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const s).const_add z
    have hgcurve : HasDerivAt (fun t : ℝ => f (z + t • s))
        (inner ℝ (gradient f (z + t • s)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (z + t • s)).hasFDerivAt.comp_hasDerivAt t hcurve)
    have hlin := (hasDerivAt_id t).mul_const (inner ℝ (gradient f z) s)
    have hquad := (((hasDerivAt_id t).pow 2).div_const 2).mul_const (inner ℝ (H s) s)
    have hcubic := ((hasDerivAt_id t).pow 3).const_mul (M / 6 * ‖s‖ ^ 3)
    simp only [id_eq, Pi.pow_apply] at hlin hquad hcubic
    have hh := (((hgcurve.sub_const (f z)).sub hlin).sub hquad).sub hcubic
    convert! hh using 1 <;> dsimp only [phi, phi'] <;> ring
  have hnonpos : phi' ≤ 0 := by
    intro t
    let R := gradient f (z + t • s) - gradient f z - H (t • s)
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z (t • s)
    change ‖R‖ ≤ M / 2 * ‖t • s‖ ^ 2 at hR
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hR
    have hinner := real_inner_le_norm R s
    have hm := mul_le_mul_of_nonneg_right hR (norm_nonneg s)
    have he : inner ℝ R s = inner ℝ (gradient f (z + t • s)) s -
        inner ℝ (gradient f z) s - t * inner ℝ (H s) s := by
      simp only [R, inner_sub_left, map_smul, real_inner_smul_left]
    rw [he] at hinner
    change inner ℝ (gradient f (z + t • s)) s - inner ℝ (gradient f z) s -
      t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2 ≤ 0
    nlinarith only [hinner, hm]
  have hanti := antitone_of_hasDerivAt_nonpos hderiv hnonpos
  have hh := hanti (by norm_num : (0 : ℝ) ≤ 1)
  dsimp only [phi] at hh
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), one_pow, sub_self, sub_zero, zero_div] at hh
  change f (z + s) ≤ _
  nlinarith only [hh]

end OriginalOuterCubic


namespace OriginalOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem inexact_step_bounds
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z v : E) (Ht : E →L[ℝ] E) (deltaG deltaH : ℝ)
    (hG : ‖v - gradient f z‖ ≤ deltaG)
    (hHt : ‖Ht - fderiv ℝ (gradient f) z‖ ≤ deltaH) :
    let s := minimizer v Ht (2 * M)
    f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2 ∧
      ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG := by
  dsimp only
  let s := minimizer v Ht (2 * M)
  let H := fderiv ℝ (gradient f) z
  have hm := minimizer_equation_and_decrease v Ht (2 * M) (by positivity)
  change v + CertifiedATS.sympart Ht s + (2 * M / 2 * ‖s‖) • s = 0 ∧
    model v Ht (2 * M) s ≤ -(2 * M / 12) * ‖s‖ ^ 3 at hm
  have htaylor := cubic_taylor_upper f hC2 M hM hH z s
  have hg : ‖gradient f z - v‖ ≤ deltaG := by simpa only [norm_sub_rev] using hG
  have hgnorm := real_inner_le_norm (gradient f z - v) s
  have hgmul := mul_le_mul_of_nonneg_right hg (norm_nonneg s)
  simp only [inner_sub_left] at hgnorm
  have hdiff : ‖H - Ht‖ ≤ deltaH := by simpa only [norm_sub_rev] using hHt
  have hnorm := ((H - Ht).le_opNorm s).trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg s))
  have hinner := real_inner_le_norm ((H - Ht) s) s
  have hhmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg s)
  simp only [sub_apply, inner_sub_left] at hinner
  have hmodel := hm.2
  dsimp only [model] at hmodel
  simp only [sub_apply] at hhmul
  change f (z + s) ≤ f z + inner ℝ (gradient f z) s +
    (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 at htaylor
  refine ⟨?_, ?_⟩
  · change f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2
    nlinarith only [htaylor, hmodel, hgnorm, hgmul, hinner, hhmul]
  · change ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG
    have hself := CertifiedATS.gradient_derivative_selfadjoint f hC2 z
    have hsym : ‖H - CertifiedATS.sympart Ht‖ ≤ deltaH := by
      rw [norm_sub_rev]
      exact (CertifiedATS.sympart_error_bound Ht H hself).trans hHt
    have hsymnorm := ((H - CertifiedATS.sympart Ht).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hsym (norm_nonneg s))
    let R := gradient f (z + s) - gradient f z - H s
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z s
    change ‖R‖ ≤ M / 2 * ‖s‖ ^ 2 at hR
    have hzero : v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s = 0 := by
      convert! hm.1 using 1 <;> ring
    have he : gradient f (z + s) = R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s - (M * ‖s‖) • s := by
      calc
        _ = gradient f (z + s) - (v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s) := by rw [hzero, sub_zero]
        _ = _ := by simp only [R, sub_apply]; module
    have hn1 := norm_sub_le (R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s) ((M * ‖s‖) • s)
    have hn2 := norm_add_le (R + (gradient f z - v)) ((H - CertifiedATS.sympart Ht) s)
    have hn3 := norm_add_le R (gradient f z - v)
    have hsmul : ‖(M * ‖s‖) • s‖ = M * ‖s‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM.le (norm_nonneg _))]
      ring
    rw [← he, hsmul] at hn1
    nlinarith only [hn1, hn2, hn3, hR, hg, hsymnorm]

theorem nonterminal_scalar_decrease (M eps r q Gnew Fchange : ℝ)
    (hM : 0 < M) (heps : 0 < eps) (hr : 0 ≤ r) (hq : 0 ≤ q) (hqsq : q ^ 2 = M * eps)
    (hnew : eps / 3 < Gnew)
    (hgrad : Gnew ≤ (3 * M / 2) * r ^ 2 + (q / 1024) * r + eps / 1024)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    eps / 16 ≤ M * r ^ 2 ∧ Fchange ≤ -(M / 4) * r ^ 3 := by
  have hyoung : 2 * r * q ≤ M * r ^ 2 + eps := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [sq_nonneg (M * r - q), hqsq]
  have hradius : eps / 16 ≤ M * r ^ 2 := by
    nlinarith only [hgrad, hyoung, hnew, heps]
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, hq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  refine ⟨hradius, ?_⟩
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

end OriginalOuterCubic


open OriginalOuterCubic



namespace OriginalOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def tolerance (M eps : ℝ) : ℝ := min (eps / 1024) (Real.sqrt (M * eps) / 1024)
def stepRadius (M eps : ℝ) : ℝ := Real.sqrt (eps / (16 * M))
def stepCharge (M eps : ℝ) : ℝ := M / 4 * stepRadius M eps ^ 3

structure CubicOutput (E : Type*) where
  point : E
  success : Bool
  moves : ℕ
  charged : ℕ
  cubicSteps : ℝ

def appendCharged (s : E) (out : CubicOutput E) : CubicOutput E :=
  ⟨out.point, out.success, out.moves + 1, out.charged + 1, ‖s‖ ^ 3 + out.cubicSteps⟩

def loop (M eps : ℝ) : ℕ → E → Answer E → GetterProgram (E × ℝ) (Answer E) (CubicOutput E)
  | 0, x, _ => .pure ⟨x, false, 0, 0, 0⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, true, 0, 0, 0⟩
      else
        let s := minimizer a.grad a.hess (2 * M)
        let y := x + s
        .ask (y, tolerance M eps) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
          else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))

def program (M eps : ℝ) (n : ℕ) (start : E) : GetterProgram (E × ℝ) (Answer E) (CubicOutput E) :=
  .ask (start, tolerance M eps) (fun a => loop M eps n start a)

theorem radius_properties (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    0 < tolerance M eps ∧ 0 < stepRadius M eps ∧
      M * stepRadius M eps ^ 2 = eps / 16 ∧ 0 < stepCharge M eps := by
  have ht : 0 < tolerance M eps := by unfold tolerance; positivity
  have hr : 0 < stepRadius M eps := by unfold stepRadius; positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ eps / (16 * M))
  have hid : M * stepRadius M eps ^ 2 = eps / 16 := by
    unfold stepRadius
    rw [hs]
    field_simp
  exact ⟨ht, hr, hid, by unfold stepCharge; positivity⟩

def Accurate (f : E → ℝ) (M eps : ℝ) (x : E) (a : Answer E) : Prop :=
  ‖a.grad - gradient f x‖ ≤ eps / 1024 ∧
    ‖a.hess - fderiv ℝ (gradient f) x‖ ≤ Real.sqrt (M * eps) / 1024

theorem accurate_stop (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ‖a.grad‖ ≤ eps / 2) : ‖gradient f x‖ ≤ eps := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_sub_le a.grad (a.grad - gradient f x)
  have hid : a.grad - (a.grad - gradient f x) = gradient f x := by abel
  rw [hid] at ht
  linarith only [ht, he, hstop, heps]

theorem accurate_nonterminal (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ¬ ‖a.grad‖ ≤ eps / 2) : eps / 3 < ‖gradient f x‖ := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_add_le (a.grad - gradient f x) (gradient f x)
  have hid : (a.grad - gradient f x) + gradient f x = a.grad := by abel
  rw [hid] at ht
  linarith only [ht, he, lt_of_not_ge hstop, heps]

theorem large_radius_scalar_decrease (M eps r q Fchange : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hqsq : q ^ 2 = M * eps)
    (hradius : eps / 16 ≤ M * r ^ 2)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    Fchange ≤ -(M / 4) * r ^ 3 := by
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

theorem actual_step_radius_and_descent
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    let s := minimizer a.grad a.hess (2 * M)
    (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) ∧
    (∀ ay : Answer E, Accurate f M eps (x + s) ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
      stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) := by
  dsimp only
  let s := minimizer a.grad a.hess (2 * M)
  have hp := radius_properties M eps hM heps
  have hs := inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024) (Real.sqrt (M * eps) / 1024)
    (ha.1) ha.2
  have hqsq := Real.sq_sqrt (by positivity : 0 ≤ M * eps)
  have hq : 0 ≤ Real.sqrt (M * eps) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · intro hr
    have hsq := (sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mpr hr
    have hm := mul_le_mul_of_nonneg_left hsq hM.le
    have hradius : eps / 16 ≤ M * ‖s‖ ^ 2 := by linarith only [hm, hp.2.2.1]
    have hd := large_radius_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps)) (f (x + s) - f x)
      hM (norm_nonneg _) hqsq hradius hs.1
    linarith only [hd]
  · intro ay hay haway
    have hlarge := accurate_nonterminal f M eps heps (x + s) ay hay haway
    have hscalar := nonterminal_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps))
      ‖gradient f (x + s)‖ (f (x + s) - f x) hM heps (norm_nonneg _) hq hqsq hlarge hs.2 hs.1
    have hsq : stepRadius M eps ^ 2 ≤ ‖s‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ hM).mp
      linarith only [hp.2.2.1, hscalar.1]
    exact ⟨(sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mp hsq, by linarith only [hscalar.2]⟩

end
end OriginalOuterCubicSeparateErrors




namespace OriginalOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def LoopSpec (f : E → ℝ) (M eps lower : ℝ) (n : ℕ) (x : E) (run : CubicOutput E × ℕ) : Prop :=
  stepCharge M eps * (run.1.charged : ℝ) ≤ f x - lower ∧
  M / 4 * run.1.cubicSteps ≤ f x - lower + stepCharge M eps ∧
  run.1.moves ≤ run.1.charged + 1 ∧
  (run.1.success = true → ‖gradient f run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.charged = n) ∧ run.2 = run.1.moves

theorem actual_cubic_loop_spec
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (n : ℕ) (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    LoopSpec f M eps lower n x (execute getter (loop M eps n x a)) := by
  have hp := radius_properties M eps hM heps
  have hradius0 := hp.2.1.le
  induction n generalizing x a with
  | zero =>
      simp only [loop, execute, LoopSpec]
      refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
        by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
        by omega, ?_, fun _ => by trivial, by trivial⟩
      intro hf
      cases hf
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute, LoopSpec]
        refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
          by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
          by omega, fun _ => accurate_stop f M eps heps x a ha hstop, ?_, by trivial⟩
        intro hf
        cases hf
      · let s := minimizer a.grad a.hess (2 * M)
        let y := x + s
        let ay := getter (y, tolerance M eps)
        have hay : Accurate f M eps y ay := hvalid y
        have hstep := actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f y) ∧
          (∀ ay : Answer E, Accurate f M eps y ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f y) at hstep
        rw [loop, if_neg hstop]
        change LoopSpec f M eps lower (n + 1) x
          (execute getter (.ask (y, tolerance M eps) (fun ay =>
            if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))))
        simp only [execute]
        change LoopSpec f M eps lower (n + 1) x
          ((execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).1,
           (execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).2 + 1)
        by_cases hnextstop : ‖ay.grad‖ ≤ eps / 2
        · have hbudget : M / 4 * ‖s‖ ^ 3 ≤ f x - lower + stepCharge M eps := by
            by_cases hr : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hr
              linarith only [hd, hbelow y, hp.2.2.2]
            · have hrle : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hr).le
              have hcube : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ M / 4)
              change M / 4 * ‖s‖ ^ 3 ≤ f x - lower + M / 4 * stepRadius M eps ^ 3
              linarith only [hh, hbelow x]
          simp only [if_pos hnextstop, execute, LoopSpec]
          refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
            hbudget, by omega, fun _ => accurate_stop f M eps heps y ay hay hnextstop, ?_, by trivial⟩
          intro hf
          cases hf
        · have hd := hstep.2 ay hay hnextstop
          have hradius := hd.1
          have hcube : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by gcongr
          have hcharge : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
          have hi := ih y ay hay
          simp only [LoopSpec] at hi
          simp only [if_neg hnextstop, FangqingGetterComposition.execute_map,
            LoopSpec, appendCharged, Nat.cast_add, Nat.cast_one]
          refine ⟨by nlinarith only [hi.1, hd.2, hcharge],
            by nlinarith only [hi.2.1, hd.2], ?_, hi.2.2.2.1, ?_, ?_⟩
          · have hh := hi.2.2.1
            omega
          · intro hf
            have hh := hi.2.2.2.2.1 hf
            omega
          · have hh := hi.2.2.2.2.2
            omega

noncomputable def fuel (Delta M eps : ℝ) : ℕ := Nat.ceil (Delta / stepCharge M eps) + 1

theorem actual_finite_cubic_termination
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    run.1.success = true ∧ ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
      run.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
      (run.2 : ℝ) ≤ 2 + Delta / stepCharge M eps := by
  dsimp only
  let a := getter (start, tolerance M eps)
  let rest := execute getter (loop M eps (fuel Delta M eps) start a)
  have hp := radius_properties M eps hM heps
  have hs := actual_cubic_loop_spec f hC2 M eps lower hM heps hH hbelow getter hvalid
    (fuel Delta M eps) start a (hvalid start)
  change LoopSpec f M eps lower (fuel Delta M eps) start rest at hs
  dsimp only [LoopSpec] at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps :=
    (le_div_iff₀ hp.2.2.2).mpr (by nlinarith only [hs.1, hgap])
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hn := hs.2.2.2.2.1 hb
        rw [hn] at hc
        have hceil : Delta / stepCharge M eps ≤ (Nat.ceil (Delta / stepCharge M eps) : ℝ) := Nat.le_ceil _
        unfold fuel at hc
        push_cast at hc
        linarith only [hc, hceil]
  have hmoves : (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.2.2.1
    linarith only [hh, hc]
  have hcubic : rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < M / 4)).mp
    have hid : M / 4 * (4 * Delta / M + stepRadius M eps ^ 3) = Delta + stepCharge M eps := by
      unfold stepCharge
      field_simp <;> ring
    rw [hid]
    nlinarith only [hs.2.1, hgap]
  change rest.1.success = true ∧ ‖gradient f rest.1.point‖ ≤ eps ∧
    (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧ ((rest.2 + 1 : ℕ) : ℝ) ≤ _
  refine ⟨hsuccess, hs.2.2.2.1 hsuccess, hmoves, hcubic, ?_⟩
  rw [hs.2.2.2.2.2]
  push_cast
  linarith only [hmoves]

end OriginalOuterCubicSeparateErrors




namespace OriginalOuterCubicSeparateErrors

theorem radius_and_charge_identities (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) ∧
      stepCharge M eps = eps ^ (3 / 2 : ℝ) / (256 * Real.sqrt M) := by
  have hr : stepRadius M eps = Real.sqrt eps / (4 * Real.sqrt M) := by
    unfold stepRadius
    rw [Real.sqrt_div heps.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have he3 : Real.sqrt eps ^ 3 = eps * Real.sqrt eps := by rw [pow_succ, Real.sq_sqrt heps.le]
  have hM3 : Real.sqrt M ^ 3 = M * Real.sqrt M := by rw [pow_succ, Real.sq_sqrt hM.le]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hcube : stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) := by
    rw [hr, div_pow, mul_pow, he3, hM3, hepow]
    norm_num
    ring
  refine ⟨hcube, ?_⟩
  unfold stepCharge
  rw [hcube]
  field_simp [ne_of_gt hM, ne_of_gt (Real.sqrt_pos.mpr hM)]
  <;> ring

theorem reciprocal_charge_identity (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    Delta / stepCharge M eps = 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  rw [(radius_and_charge_identities M eps hM heps).2, div_div_eq_mul_div]
  ring

noncomputable def epsilonThreshold (Delta M : ℝ) : ℝ := (Delta * Real.sqrt M) ^ (2 / 3 : ℝ)

theorem epsilon_threshold_properties (Delta M eps : ℝ) (hDelta : 0 < Delta) (hM : 0 < M)
    (heps : 0 < eps) (hsmall : eps ≤ epsilonThreshold Delta M) :
    0 < epsilonThreshold Delta M ∧ eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M := by
  have hx : 0 < Delta * Real.sqrt M := by positivity
  have hpos : 0 < epsilonThreshold Delta M := by unfold epsilonThreshold; positivity
  have hp := Real.rpow_le_rpow heps.le hsmall (by norm_num : (0 : ℝ) ≤ 3 / 2)
  change eps ^ (3 / 2 : ℝ) ≤ ((Delta * Real.sqrt M) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) at hp
  rw [← Real.rpow_mul hx.le] at hp
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hp
  exact ⟨hpos, hp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

open OriginalBetaATSTrial (Answer execute)

theorem cubic_asymptotic_rate_and_full_step_budget
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta)
    (hsmall : eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) ∧
      run.1.cubicSteps ≤ 5 * Delta / M ∧
      (run.2 : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  dsimp only
  have hDelta : 0 ≤ Delta := by linarith only [hgap, hbelow start]
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hs := actual_finite_cubic_termination f hC2 M eps lower Delta hM heps hH hbelow getter hvalid start hgap
  have hrate : 1 ≤ Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) :=
    (le_div_iff₀ hpow).mpr (by simpa only [one_mul] using hsmall)
  let t := Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ)
  change 1 ≤ t at hrate
  rw [reciprocal_charge_identity Delta M eps hM heps] at hs
  have hcube : stepRadius M eps ^ 3 ≤ Delta / (64 * M) := by
    rw [(radius_and_charge_identities M eps hM heps).1]
    calc
      _ ≤ (Delta * Real.sqrt M) / (64 * M * Real.sqrt M) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by field_simp [ne_of_gt (Real.sqrt_pos.mpr hM)]
  refine ⟨hs.2.1, ?_, ?_, ?_⟩
  · have hh := hs.2.2.1
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]
  · have hh := hs.2.2.2.1
    have hn : 0 ≤ Delta / M := by positivity
    rw [show 4 * Delta / M = 4 * (Delta / M) by ring] at hh
    rw [show Delta / (64 * M) = (Delta / M) / 64 by ring] at hcube
    rw [show 5 * Delta / M = 5 * (Delta / M) by ring]
    nlinarith only [hh, hcube, hn]
  · have hh := hs.2.2.2.2
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]

end OriginalOuterCubicSeparateErrors


namespace OriginalCubicFullProgramCounterexample

open OriginalCubicTerminalCounterexample OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 2000000

def internalCurvature : ℝ := 1 / 2
def paperCurvature : ℝ := 1

def originalGap (H : ℝ) : ℝ := 8 / (3 * H)

def fullProgram (H : ℝ) : GetterProgram (Plane × ℝ) (Answer Plane)
    (OriginalOuterCubicSeparateErrors.CubicOutput Plane) :=
  OriginalOuterCubicSeparateErrors.program internalCurvature 1
    (OriginalOuterCubicSeparateErrors.fuel (originalGap H) internalCurvature 1) (start H)

theorem actual_tolerance_positive_and_lower_bound :
    0 < OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1 ∧
      1 / 4096 ≤ OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1 / 2) * 1)
  have hn := Real.sqrt_nonneg ((1 / 2 : ℝ) * 1)
  have hlo : (1 / 4 : ℝ) ≤ Real.sqrt ((1 / 2 : ℝ) * 1) := by nlinarith only [hs, hn]
  dsimp [OriginalOuterCubicSeparateErrors.tolerance, internalCurvature]
  constructor
  · positivity
  · exact le_min (by norm_num) (by nlinarith only [hlo])

theorem actual_getter_separate_errors
    (H c : ℝ) (hc : 0 < c) (x : Plane) :
    OriginalOuterCubicSeparateErrors.Accurate (energy H) internalCurvature 1 x
      (getter H c (x, OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1)) := by
  have hh := getter_correct H c hc x _ actual_tolerance_positive_and_lower_bound.1
  refine ⟨hh.1.trans (min_le_left _ _), hh.2.trans (min_le_right _ _)⟩

theorem actual_complete_program_execution
    (H c : ℝ) (hH : 16 ≤ H) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    execute (getter H c) (fullProgram H) =
      (⟨start H + step H c, true, 1, 0, ‖step H c‖ ^ 3⟩, 2) := by
  have hHpos : 0 < H := by linarith only [hH]
  have hfirst := getter_at_start H c (OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1)
    hHpos (hsmall.trans actual_tolerance_positive_and_lower_bound.2)
  have hnext := getter_at_terminal H c (OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1) hc
  have hstop := (actual_step_geometry H c hH hc (by linarith only [hsmall])).2.2.2
  have hnonstop : ¬ ‖observedGradient c‖ ≤ (1 / 2 : ℝ) := by
    have hh := WithLp.norm_fst_le ℝ (observedGradient c)
    change |(2 : ℝ)| ≤ ‖observedGradient c‖ at hh
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith only [hh]
  have hregularizer : 2 * internalCurvature = 1 := by norm_num [internalCurvature]
  dsimp only [step] at hnext hstop
  simp only [fullProgram, OriginalOuterCubicSeparateErrors.program, OriginalOuterCubicSeparateErrors.fuel,
    execute, OriginalOuterCubicSeparateErrors.loop, hregularizer, hfirst, if_neg hnonstop,
    hnext, if_pos hstop]
  rfl

theorem actual_complete_program_query_trace
    (H c : ℝ) (hH : 16 ≤ H) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    FangqingGetterComposition.trace (getter H c) (fullProgram H) =
      [(start H, OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1),
       (start H + step H c, OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1)] := by
  have hHpos : 0 < H := by linarith only [hH]
  have hfirst := getter_at_start H c (OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1)
    hHpos (hsmall.trans actual_tolerance_positive_and_lower_bound.2)
  have hnext := getter_at_terminal H c (OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1) hc
  have hstop := (actual_step_geometry H c hH hc (by linarith only [hsmall])).2.2.2
  have hnonstop : ¬ ‖observedGradient c‖ ≤ (1 / 2 : ℝ) := by
    have hh := WithLp.norm_fst_le ℝ (observedGradient c)
    change |(2 : ℝ)| ≤ ‖observedGradient c‖ at hh
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith only [hh]
  have hregularizer : 2 * internalCurvature = 1 := by norm_num [internalCurvature]
  dsimp only [step] at hnext hstop
  simp only [fullProgram, OriginalOuterCubicSeparateErrors.program, OriginalOuterCubicSeparateErrors.fuel,
    FangqingGetterComposition.trace, OriginalOuterCubicSeparateErrors.loop, hregularizer,
    hfirst, if_neg hnonstop, hnext, if_pos hstop]
  rfl

def movementCubes : List (Plane × ℝ) → ℝ
  | [] => 0
  | [_] => 0
  | p :: q :: rest => ‖q.1 - p.1‖ ^ 3 + movementCubes (q :: rest)

theorem instrumented_cubicSteps_is_sum_of_all_actual_moves
    (H c : ℝ) (hH : 16 ≤ H) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    (execute (getter H c) (fullProgram H)).1.cubicSteps =
      movementCubes (FangqingGetterComposition.trace (getter H c) (fullProgram H)) ∧
    (FangqingGetterComposition.trace (getter H c) (fullProgram H)).length =
      (execute (getter H c) (fullProgram H)).1.moves + 1 := by
  rw [actual_complete_program_execution H c hH hc hsmall, actual_complete_program_query_trace H c hH hc hsmall]
  simp only [movementCubes, add_sub_cancel_left, add_zero, List.length_cons, List.length_nil]
  constructor <;> trivial

theorem full_program_has_no_uniform_all_move_cubic_budget
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    ∃ H : ℝ, 16 ≤ H ∧
      (∀ x, 0 ≤ energy H x) ∧ sInf (Set.range (energy H)) = 0 ∧
      energy H (start H) - sInf (Set.range (energy H)) ≤ originalGap H ∧
      (∀ x, OriginalOuterCubicSeparateErrors.Accurate (energy H) internalCurvature 1 x
        (getter H c (x, OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1))) ∧
      (execute (getter H c) (fullProgram H)).1.success = true ∧
      (execute (getter H c) (fullProgram H)).1.moves = 1 ∧
      (execute (getter H c) (fullProgram H)).2 = 2 ∧
      ‖gradient (energy H) (execute (getter H c) (fullProgram H)).1.point‖ ≤ 1 / 2 ∧
      (execute (getter H c) (fullProgram H)).1.cubicSteps =
        movementCubes (FangqingGetterComposition.trace (getter H c) (fullProgram H)) ∧
      C * originalGap H / internalCurvature < (execute (getter H c) (fullProgram H)).1.cubicSteps ∧
      C * originalGap H / paperCurvature < (execute (getter H c) (fullProgram H)).1.cubicSteps := by
  let H := 16 + 8 * (C + 1) / c ^ 2
  have hH : 16 ≤ H := by
    have hp : 0 ≤ 8 * (C + 1) / c ^ 2 := by positivity
    dsimp [H]
    linarith only [hp]
  have hHp : 0 < H := by linarith only [hH]
  have hgap := initial_gap_and_bounded_below H hHp
  have hinf := energy_infimum H hHp
  have hrun := actual_complete_program_execution H c hH hc hsmall
  have hr := actual_step_geometry H c hH hc (by linarith only [hsmall])
  have hHc : 16 * C < 3 * H * c ^ 2 := by
    have hi : H * c ^ 2 = 16 * c ^ 2 + 8 * (C + 1) := by dsimp [H]; field_simp <;> ring
    nlinarith only [hi, hC, sq_pos_of_pos hc]
  have hv : C * originalGap H / internalCurvature < c ^ 2 := by
    change C * (8 / (3 * H)) / (1 / 2) < c ^ 2
    rw [show C * (8 / (3 * H)) / (1 / 2) = 16 * C / (3 * H) by ring]
    exact (div_lt_iff₀ (by positivity : 0 < 3 * H)).mpr (by nlinarith only [hHc])
  refine ⟨H, hH, hgap.1, hinf, ?_, actual_getter_separate_errors H c hc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinf, sub_zero, hgap.2.2]
    dsimp [originalGap]
    apply (div_le_div_iff₀ hHp (by positivity : 0 < 3 * H)).mpr
    nlinarith only [hHp]
  · rw [hrun]
  · rw [hrun]
  · rw [hrun]
  · rw [hrun]
    exact hr.2.2.2
  · exact (instrumented_cubicSteps_is_sum_of_all_actual_moves H c hH hc hsmall).1
  · rw [hrun]
    exact hv.trans_le hr.2.2.1
  · rw [hrun]
    have hgap0 : 0 ≤ C * originalGap H := by dsimp [originalGap]; positivity
    have hh : C * originalGap H / paperCurvature ≤ C * originalGap H / internalCurvature := by
      dsimp [paperCurvature, internalCurvature]
      nlinarith only [hgap0]
    exact hh.trans_lt (hv.trans_le hr.2.2.1)

end
end OriginalCubicFullProgramCounterexample


namespace OriginalSchurInverse

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev Joint (E F : Type*) := WithLp 2 (E × F)

noncomputable def blockXX (H : Joint E F →L[ℝ] Joint E F) : E →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp (H.comp JointSliceRegularity.axisX.toContinuousLinearMap)

noncomputable def blockXY (H : Joint E F →L[ℝ] Joint E F) : F →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp (H.comp JointSliceRegularity.axisY.toContinuousLinearMap)

noncomputable def blockYX (H : Joint E F →L[ℝ] Joint E F) : E →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp (H.comp JointSliceRegularity.axisX.toContinuousLinearMap)

noncomputable def blockYY (H : Joint E F →L[ℝ] Joint E F) : F →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp (H.comp JointSliceRegularity.axisY.toContinuousLinearMap)

noncomputable def schur (H : Joint E F →L[ℝ] Joint E F) : E →L[ℝ] E :=
  blockXX H - (blockXY H).comp ((blockYY H).inverse.comp (blockYX H))


end OriginalSchurInverse

namespace OriginalEnvelopeOracle

open OriginalSaddleImplicit OriginalSaddleTangent

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def plugInGradient (L : ℝ) (x : E) (w : Joint E F) : E :=
  (2 * L) • (x - w.fst)

noncomputable def plugInHessian (J : Joint E F → ℝ) (L : ℝ) (w : Joint E F) : E →L[ℝ] E :=
  (2 * L) • ContinuousLinearMap.id ℝ E -
    (4 * L ^ 2) • (OriginalSchurInverse.schur (saddleHessian J L w)).inverse


end OriginalEnvelopeOracle

namespace OriginalEnvelopeOracleProgram
open OriginalSaddleImplicit OriginalSaddleTangent OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

structure Estimate (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  saddle : Joint E F
  grad : E
  hess : E →L[ℝ] E

noncomputable def hessianFromAnswer (L : ℝ) (H : Joint E F →L[ℝ] Joint E F) : E →L[ℝ] E :=
  (2 * L) • ContinuousLinearMap.id ℝ E - (4 * L ^ 2) •
    (OriginalSchurInverse.schur (H + (2 * L) • primalProjection)).inverse

noncomputable def fromAnswer (L : ℝ) (x : E) (w : Joint E F)
    (a : OriginalDualOracleProgram.OracleAnswer (Joint E F)) : Estimate E F :=
  ⟨w, OriginalEnvelopeOracle.plugInGradient L x w, hessianFromAnswer L a.hess⟩

noncomputable def program (L : ℝ) (x : E)
    (warm : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F)) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  FangqingGetterComposition.bind warm (fun w => .ask w (fun a => .pure (fromAnswer L x w a)))

theorem actual_execution (J : Joint E F → ℝ) (L : ℝ) (x : E)
    (warm : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F)) :
    let first := execute (OriginalDualOracleProgram.actualOracle J) warm
    execute (OriginalDualOracleProgram.actualOracle J) (program L x warm) =
      (⟨first.1, OriginalEnvelopeOracle.plugInGradient L x first.1,
        OriginalEnvelopeOracle.plugInHessian J L first.1⟩, first.2 + 1) := by
  simp only [program, execute_bind, execute, fromAnswer, hessianFromAnswer,
    OriginalEnvelopeOracle.plugInHessian, saddleHessian, OriginalDualOracleProgram.actualOracle]


end OriginalEnvelopeOracleProgram


namespace OriginalCubicSaddleEmbedding

open OriginalCubicTerminalCounterexample OriginalSaddleTangent

abbrev SaddleSpace := WithLp 2 (Plane × ℝ)
noncomputable def saddlePoint (u : Plane) (y : ℝ) : SaddleSpace := WithLp.toLp 2 (u, y)
noncomputable def saddle (H : ℝ) (z : SaddleSpace) : ℝ := energy (4 * H / 3) z.fst - z.snd ^ 2 / 2
noncomputable def saddleHessian (H : ℝ) : SaddleSpace →L[ℝ] SaddleSpace :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).symm.toContinuousLinearMap.comp
    (((hessian (4 * H / 3)).comp (WithLp.fstL 2 ℝ Plane ℝ)).prod
      (-(WithLp.sndL 2 ℝ Plane ℝ)))
noncomputable def proxPoint (x : Plane) : Plane := point ((3 / 4 : ℝ) * x.fst) x.snd
noncomputable def trueSaddlePoint (x : Plane) : SaddleSpace := saddlePoint (proxPoint x) 0

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

local instance : NormedSpace ℝ Plane := inferInstance
local instance : NormedSpace ℝ SaddleSpace := inferInstance
local instance : ContinuousSMul ℝ SaddleSpace := inferInstance

theorem curry_eq_saddlePoint (H : ℝ) (u : Plane) (y : ℝ) :
    JointSliceRegularity.curry (saddle H) u y = saddle H (saddlePoint u y) := by
  unfold JointSliceRegularity.curry
  rw [JointSliceRegularity.point_eq_toLp]
  rfl

theorem joint_norm_sq (z : SaddleSpace) : ‖z‖ ^ 2 = z.fst.fst ^ 2 + z.fst.snd ^ 2 + z.snd ^ 2 := by
  have h1 := WithLp.prod_norm_sq_eq_of_L2 z
  rw [norm_sq_components] at h1
  simpa only [Real.norm_eq_abs, sq_abs] using h1

theorem saddleHessian_coordinates (H : ℝ) (z : SaddleSpace) :
    (saddleHessian H z).fst = hessian (4 * H / 3) z.fst ∧ (saddleHessian H z).snd = -z.snd := ⟨rfl, rfl⟩

theorem saddleHessian_symmetric (H : ℝ) : (saddleHessian H).toLinearMap.IsSymmetric := by
  intro z w
  change inner ℝ (hessian (4 * H / 3) z.fst) w.fst + inner ℝ (-z.snd) w.snd =
    inner ℝ z.fst (hessian (4 * H / 3) w.fst) + inner ℝ z.snd (-w.snd)
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [Real.inner_apply]
  change (hessian (4 * H / 3) z.fst).fst * w.fst.fst +
      (hessian (4 * H / 3) z.fst).snd * w.fst.snd + (-z.snd) * w.snd =
    z.fst.fst * (hessian (4 * H / 3) w.fst).fst +
      z.fst.snd * (hessian (4 * H / 3) w.fst).snd + z.snd * (-w.snd)
  simp only [hessian_fst, hessian_snd, Real.inner_apply, zero_mul, mul_zero, add_zero]
  ring

theorem saddle_eq_half_inner (H : ℝ) (z : SaddleSpace) :
    saddle H z = (1 / 2 : ℝ) * (saddleHessian H).reApplyInnerSelf z := by
  change energy (4 * H / 3) z.fst - z.snd ^ 2 / 2 =
    (1 / 2 : ℝ) * (inner ℝ (hessian (4 * H / 3) z.fst) z.fst + inner ℝ (-z.snd) z.snd)
  rw [WithLp.prod_inner_apply]
  simp only [Real.inner_apply]
  change energy (4 * H / 3) z.fst - z.snd ^ 2 / 2 = (1 / 2 : ℝ) *
    ((hessian (4 * H / 3) z.fst).fst * z.fst.fst + (hessian (4 * H / 3) z.fst).snd * z.fst.snd + (-z.snd) * z.snd)
  simp only [hessian_fst, hessian_snd, Real.inner_apply, zero_mul, add_zero, energy]
  ring

theorem actual_saddle_gradient (H : ℝ) (z : SaddleSpace) : HasGradientAt (saddle H) (saddleHessian H z) z := by
  have heq : saddle H = fun z => (1 / 2 : ℝ) * (saddleHessian H).reApplyInnerSelf z := funext (saddle_eq_half_inner H)
  have hd : HasFDerivAt (saddle H) (innerSL ℝ (saddleHessian H z)) z := by
    rw [heq]
    have hh := ((saddleHessian_symmetric H).hasStrictFDerivAt_reApplyInnerSelf z).hasFDerivAt.const_mul (1 / 2 : ℝ)
    convert! hh using 1
    ext v
    simp only [two_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    ring
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hd

theorem actual_saddle_hessian (H : ℝ) (z : SaddleSpace) :
    fderiv ℝ (gradient (saddle H)) z = saddleHessian H := by
  have heq : gradient (saddle H) = saddleHessian H := funext (fun z => (actual_saddle_gradient H z).gradient)
  rw [heq]
  exact (saddleHessian H).hasFDerivAt.fderiv

theorem actual_saddle_contDiff (H : ℝ) : ContDiff ℝ 2 (saddle H) :=
  ((energy_contDiff (4 * H / 3)).comp (WithLp.fstL 2 ℝ Plane ℝ).contDiff).sub
    (((WithLp.sndL 2 ℝ Plane ℝ).contDiff.pow 2).div_const 2)

theorem actual_saddle_hessian_norm_bound (H : ℝ) (hH : 16 ≤ H) (z : SaddleSpace) :
    ‖saddleHessian H z‖ ≤ (2 * H) * ‖z‖ := by
  have hn := joint_norm_sq (saddleHessian H z)
  rw [(saddleHessian_coordinates H z).1, (saddleHessian_coordinates H z).2, hessian_fst, hessian_snd] at hn
  have hz := joint_norm_sq z
  have hHpos : 0 < H := by linarith only [hH]
  have hcoef : (4 * H / 3) ^ 2 ≤ (2 * H) ^ 2 := by nlinarith only [sq_nonneg H]
  have hone : 1 ≤ (2 * H) ^ 2 := by nlinarith only [hH]
  have h1 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg z.fst.fst)
  have h2 := mul_le_mul_of_nonneg_right hone (sq_nonneg z.snd)
  have h3 := mul_nonneg (sq_nonneg (2 * H)) (sq_nonneg z.fst.snd)
  have hs : ‖saddleHessian H z‖ ^ 2 ≤ ((2 * H) * ‖z‖) ^ 2 := by
    rw [mul_pow, hz]
    nlinarith only [hn, h1, h2, h3]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

theorem actual_joint_smooth_and_hessian_lipschitz
    (H rho : ℝ) (hH : 16 ≤ H) (hrho : 0 ≤ rho) :
    (∀ z w : SaddleSpace, ‖gradient (saddle H) z - gradient (saddle H) w‖ ≤ (2 * H) * ‖z - w‖) ∧
    (∀ z w : SaddleSpace, ‖fderiv ℝ (gradient (saddle H)) z - fderiv ℝ (gradient (saddle H)) w‖ ≤ rho * ‖z - w‖) := by
  constructor
  · intro z w
    rw [(actual_saddle_gradient H z).gradient, (actual_saddle_gradient H w).gradient, ← map_sub]
    exact actual_saddle_hessian_norm_bound H hH _
  · intro z w
    simp only [actual_saddle_hessian, sub_self, norm_zero]
    positivity

theorem actual_dual_strong_concavity (H : ℝ) (u : Plane) :
    StrongConvexOn (Set.univ : Set ℝ) 1 (fun y => -saddle H (saddlePoint u y)) := by
  apply strongConvexOn_iff_convex.mpr
  have heq : (fun y : ℝ => -saddle H (saddlePoint u y) - (1 : ℝ) / 2 * ‖y‖ ^ 2) =
      (fun _ => -energy (4 * H / 3) u) := by
    funext y
    change -(energy (4 * H / 3) u - y ^ 2 / 2) - 1 / 2 * |y| ^ 2 = _
    rw [sq_abs]
    ring
  rw [heq]
  exact convexOn_const _ convex_univ

theorem actual_inner_maximum_zero (H : ℝ) (u : Plane) :
    (∀ y : ℝ, saddle H (saddlePoint u y) ≤ saddle H (saddlePoint u 0)) ∧
      saddle H (saddlePoint u 0) = energy (4 * H / 3) u := by
  constructor
  · intro y
    change energy (4 * H / 3) u - y ^ 2 / 2 ≤ energy (4 * H / 3) u - 0 ^ 2 / 2
    nlinarith only [sq_nonneg y]
  · change energy (4 * H / 3) u - 0 ^ 2 / 2 = _
    ring

theorem actual_phi (H : ℝ) (u : Plane) :
    OriginalSaddleTransfer.phi (JointSliceRegularity.curry (saddle H)) u = energy (4 * H / 3) u := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rw [curry_eq_saddlePoint]
    exact (actual_inner_maximum_zero H u).2
  rintro _ ⟨y, rfl⟩
  rw [curry_eq_saddlePoint]
  exact ((actual_inner_maximum_zero H u).1 y).trans_eq (actual_inner_maximum_zero H u).2

theorem exact_quadratic_moreau_identity (H : ℝ) (x u : Plane) :
    energy (4 * H / 3) u + (2 * H) * ‖u - x‖ ^ 2 = energy H x +
      (8 * H / 3) * (u.fst - (3 / 4 : ℝ) * x.fst) ^ 2 +
      (2 * H) * (u.snd - x.snd) ^ 2 := by
  rw [norm_sq_components]
  change (4 * H / 3) / 2 * u.fst ^ 2 + (2 * H) * ((u.fst - x.fst) ^ 2 + (u.snd - x.snd) ^ 2) = _
  dsimp only [energy]
  ring

theorem actual_envelope (H : ℝ) (hH : 0 < H) (x : Plane) :
    OriginalSaddleTransfer.saddleEnvelope (JointSliceRegularity.curry (saddle H)) (2 * H) x = energy H x := by
  unfold OriginalSaddleTransfer.saddleEnvelope
  have hi (u : Plane) :
      sSup (Set.range (OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x u)) =
        energy (4 * H / 3) u + (2 * H) * ‖u - x‖ ^ 2 := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨0, ?_⟩, ?_⟩
    · unfold OriginalSaddleTransfer.saddleObjective
      rw [curry_eq_saddlePoint]
      change energy (4 * H / 3) u - 0 ^ 2 / 2 + _ = _
      ring
    · rintro _ ⟨y, rfl⟩
      unfold OriginalSaddleTransfer.saddleObjective
      rw [curry_eq_saddlePoint]
      change energy (4 * H / 3) u - y ^ 2 / 2 + _ ≤ _
      nlinarith only [sq_nonneg y]
  simp_rw [hi]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨proxPoint x, ?_⟩
    dsimp only
    rw [exact_quadratic_moreau_identity]
    change energy H x + (8 * H / 3) * ((3 / 4 : ℝ) * x.fst - (3 / 4 : ℝ) * x.fst) ^ 2 +
      (2 * H) * (x.snd - x.snd) ^ 2 = energy H x
    ring
  · rintro _ ⟨u, rfl⟩
    dsimp only
    rw [exact_quadratic_moreau_identity]
    have h1 : 0 ≤ (8 * H / 3) * (u.fst - (3 / 4 : ℝ) * x.fst) ^ 2 := by positivity
    have h2 : 0 ≤ (2 * H) * (u.snd - x.snd) ^ 2 := by positivity
    linarith only [h1, h2]

theorem original_primal_gap_and_exact_dual_initialization (H : ℝ) (hH : 16 ≤ H) :
    let phi := OriginalSaddleTransfer.phi (JointSliceRegularity.curry (saddle H))
    sInf (Set.range phi) = 0 ∧ phi (start H) - sInf (Set.range phi) = 8 / (3 * H) ∧
      (∀ y : ℝ, saddle H (saddlePoint (start H) y) ≤ saddle H (saddlePoint (start H) 0)) ∧
      (8 / (3 * H)) * (2 * H) / 1 ^ 2 = 16 / 3 := by
  dsimp only
  have hp : 0 < H := by linarith only [hH]
  have heq : OriginalSaddleTransfer.phi (JointSliceRegularity.curry (saddle H)) = energy (4 * H / 3) :=
    funext (actual_phi H)
  rw [heq]
  have hinf := energy_infimum (4 * H / 3) (by positivity)
  rw [hinf, sub_zero]
  refine ⟨rfl, ?_, (actual_inner_maximum_zero H (start H)).1, ?_⟩
  · change (4 * H / 3) / 2 * (2 / H) ^ 2 = 8 / (3 * H)
    field_simp <;> ring
  · field_simp <;> ring

end
end OriginalCubicSaddleEmbedding


namespace OriginalCubicSaddleEmbedding

open OriginalCubicTerminalCounterexample OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 5000

def primalSchur (H : ℝ) : Plane →L[ℝ] Plane :=
  hessian (4 * H / 3) + (4 * H) • ContinuousLinearMap.id ℝ Plane

def primalSchurInverse (H : ℝ) : Plane →L[ℝ] Plane :=
  (3 / (16 * H)) • OriginalSaddleTangent.primalProjection +
    (1 / (4 * H)) • (ContinuousLinearMap.id ℝ Plane - OriginalSaddleTangent.primalProjection)

theorem primalSchur_fst (H : ℝ) (z : Plane) : (primalSchur H z).fst = (16 * H / 3) * z.fst := by
  change (hessian (4 * H / 3) z).fst + (4 * H) * z.fst = _
  rw [hessian_fst]
  ring

theorem primalSchur_snd (H : ℝ) (z : Plane) : (primalSchur H z).snd = (4 * H) * z.snd := by
  change (hessian (4 * H / 3) z).snd + (4 * H) * z.snd = _
  rw [hessian_snd]
  ring

theorem primalSchurInverse_fst (H : ℝ) (z : Plane) : (primalSchurInverse H z).fst = (3 / (16 * H)) * z.fst := by
  change (3 / (16 * H)) * z.fst + (1 / (4 * H)) * (z.fst - z.fst) = _
  ring

theorem primalSchurInverse_snd (H : ℝ) (z : Plane) : (primalSchurInverse H z).snd = (1 / (4 * H)) * z.snd := by
  change (3 / (16 * H)) * 0 + (1 / (4 * H)) * (z.snd - 0) = _
  ring

theorem actual_primal_schur_inverse (H : ℝ) (hH : H ≠ 0) :
    (primalSchur H).inverse = primalSchurInverse H := by
  apply ContinuousLinearMap.inverse_eq
  · apply ContinuousLinearMap.ext
    intro z
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change (primalSchur H (primalSchurInverse H z)).fst = z.fst
      rw [primalSchur_fst, primalSchurInverse_fst]
      field_simp [hH]
      <;> ring
    · change (primalSchur H (primalSchurInverse H z)).snd = z.snd
      rw [primalSchur_snd, primalSchurInverse_snd]
      field_simp [hH]
      <;> ring
  · apply ContinuousLinearMap.ext
    intro z
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change (primalSchurInverse H (primalSchur H z)).fst = z.fst
      rw [primalSchurInverse_fst, primalSchur_fst]
      field_simp [hH]
      <;> ring
    · change (primalSchurInverse H (primalSchur H z)).snd = z.snd
      rw [primalSchurInverse_snd, primalSchur_snd]
      field_simp [hH]
      <;> ring

theorem actual_saddle_schur (H : ℝ) (w : SaddleSpace) :
    OriginalSchurInverse.schur (OriginalSaddleTangent.saddleHessian (saddle H) (2 * H) w) = primalSchur H := by
  rw [OriginalSaddleTangent.saddleHessian, actual_saddle_hessian]
  rw [show 2 * (2 * H) = 4 * H by ring]
  have hXY : OriginalSchurInverse.blockXY
      (saddleHessian H + (4 * H) • OriginalSaddleTangent.primalProjection) = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    change hessian (4 * H / 3) 0 + (4 * H) • (0 : Plane) = 0
    simp
  have hXX : OriginalSchurInverse.blockXX
      (saddleHessian H + (4 * H) • OriginalSaddleTangent.primalProjection) = primalSchur H := by
    apply ContinuousLinearMap.ext
    intro x
    change hessian (4 * H / 3) x + (4 * H) • x = primalSchur H x
    rfl
  unfold OriginalSchurInverse.schur
  rw [hXY, hXX]
  simp

theorem actual_plugin_hessian (H : ℝ) (hH : H ≠ 0) (w : SaddleSpace) :
    OriginalEnvelopeOracle.plugInHessian (saddle H) (2 * H) w = hessian H := by
  unfold OriginalEnvelopeOracle.plugInHessian
  rw [actual_saddle_schur, actual_primal_schur_inverse H hH]
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change (2 * (2 * H)) * z.fst - (4 * (2 * H) ^ 2) * (primalSchurInverse H z).fst = (hessian H z).fst
    rw [primalSchurInverse_fst, hessian_fst]
    field_simp [hH]
    <;> ring
  · change (2 * (2 * H)) * z.snd - (4 * (2 * H) ^ 2) * (primalSchurInverse H z).snd = (hessian H z).snd
    rw [primalSchurInverse_snd, hessian_snd]
    field_simp [hH]
    <;> ring

def noise (H c : ℝ) (q : Plane × ℝ) : ℝ := if q.1 = start H then min c q.2 else 0

def approximateSaddle (H c : ℝ) (q : Plane × ℝ) : SaddleSpace :=
  saddlePoint (proxPoint q.1 - JointSliceRegularity.axisY (E := ℝ) (noise H c q / (4 * H))) 0

theorem actual_plugin_gradient_is_getter (H c : ℝ) (hH : H ≠ 0) (q : Plane × ℝ) :
    OriginalEnvelopeOracle.plugInGradient (2 * H) q.1 (approximateSaddle H c q) = (getter H c q).grad := by
  classical
  rw [show (getter H c q).grad = gradient (energy H) q.1 + JointSliceRegularity.axisY (E := ℝ) (noise H c q) by
    unfold getter noise
    split_ifs <;> simp]
  rw [(energy_hasGradientAt H q.1).gradient]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · change (2 * (2 * H)) * (q.1.fst - ((3 / 4 : ℝ) * q.1.fst - 0)) = H * q.1.fst + 0
    ring
  · change (2 * (2 * H)) * (q.1.snd - (q.1.snd - noise H c q / (4 * H))) = (hessian H q.1).snd + noise H c q
    rw [hessian_snd]
    field_simp [hH]
    <;> ring

def exactBundleGetterProgram (H c : ℝ) (q : Plane × ℝ) :
    GetterProgram SaddleSpace (OriginalDualOracleProgram.OracleAnswer SaddleSpace) (Answer Plane) :=
  FangqingGetterComposition.map (fun out => Answer.mk out.grad out.hess)
    (OriginalEnvelopeOracleProgram.program (2 * H) q.1 (.pure (approximateSaddle H c q)))

theorem actual_bundled_oracle_execution_is_getter (H c : ℝ) (hH : H ≠ 0) (q : Plane × ℝ) :
    execute (OriginalDualOracleProgram.actualOracle (saddle H)) (exactBundleGetterProgram H c q) =
      (getter H c q, 1) := by
  rw [exactBundleGetterProgram, FangqingGetterComposition.execute_map,
    OriginalEnvelopeOracleProgram.actual_execution]
  simp only [execute]
  rw [actual_plugin_gradient_is_getter H c hH q, actual_plugin_hessian H hH]
  rfl

theorem approximate_saddle_distance_certificate
    (H c : ℝ) (hH : 0 < H) (hc : 0 < c) (q : Plane × ℝ) (hq : 0 < q.2) :
    ‖approximateSaddle H c q - trueSaddlePoint q.1‖ ≤ q.2 / (4 * H) := by
  have hn : 0 ≤ noise H c q ∧ noise H c q ≤ q.2 := by
    unfold noise
    split_ifs
    · exact ⟨le_min hc.le hq.le, min_le_right _ _⟩
    · exact ⟨le_rfl, hq.le⟩
  have heq : approximateSaddle H c q - trueSaddlePoint q.1 =
      JointSliceRegularity.axisX (F := ℝ) (-JointSliceRegularity.axisY (E := ℝ) (noise H c q / (4 * H))) := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change proxPoint q.1 - JointSliceRegularity.axisY (E := ℝ) (noise H c q / (4 * H)) - proxPoint q.1 = _
      change proxPoint q.1 - JointSliceRegularity.axisY (E := ℝ) (noise H c q / (4 * H)) - proxPoint q.1 =
        -JointSliceRegularity.axisY (E := ℝ) (noise H c q / (4 * H))
      abel
    · change (0 : ℝ) - 0 = 0
      ring
  rw [heq, JointSliceRegularity.norm_axisX, norm_neg, JointSliceRegularity.norm_axisY,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn.1 (by positivity))]
  exact div_le_div_of_nonneg_right hn.2 (by positivity)

theorem true_point_is_actual_saddle (H : ℝ) (hH : 0 < H) (x u : Plane) (y : ℝ) :
    OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x (proxPoint x) y ≤
      OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x (proxPoint x) 0 ∧
    OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x (proxPoint x) 0 ≤
      OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x u 0 := by
  constructor
  · unfold OriginalSaddleTransfer.saddleObjective
    simp only [curry_eq_saddlePoint]
    exact add_le_add ((actual_inner_maximum_zero H (proxPoint x)).1 y) le_rfl
  · unfold OriginalSaddleTransfer.saddleObjective
    simp only [curry_eq_saddlePoint]
    change energy (4 * H / 3) (proxPoint x) - 0 ^ 2 / 2 + (2 * H) * ‖proxPoint x - x‖ ^ 2 ≤
      energy (4 * H / 3) u - 0 ^ 2 / 2 + (2 * H) * ‖u - x‖ ^ 2
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero]
    rw [exact_quadratic_moreau_identity, exact_quadratic_moreau_identity]
    change energy H x + (8 * H / 3) * ((3 / 4 : ℝ) * x.fst - (3 / 4 : ℝ) * x.fst) ^ 2 +
      (2 * H) * (x.snd - x.snd) ^ 2 ≤ _
    have h1 : 0 ≤ (8 * H / 3) * (u.fst - (3 / 4 : ℝ) * x.fst) ^ 2 := by positivity
    have h2 : 0 ≤ (2 * H) * (u.snd - x.snd) ^ 2 := by positivity
    nlinarith only [h1, h2]

theorem actual_yStar_is_zero (H : ℝ) (u : Plane) :
    OriginalSaddleTransfer.yStar (JointSliceRegularity.curry (saddle H)) u = 0 := by
  let Y := OriginalSaddleTransfer.yStar (JointSliceRegularity.curry (saddle H)) u
  have hex : ∃ Y : ℝ, ∀ y, JointSliceRegularity.curry (saddle H) u y ≤ JointSliceRegularity.curry (saddle H) u Y :=
    ⟨0, by intro y; simpa only [curry_eq_saddlePoint] using (actual_inner_maximum_zero H u).1 y⟩
  have hm := Classical.epsilon_spec hex
  change ∀ y : ℝ, JointSliceRegularity.curry (saddle H) u y ≤ JointSliceRegularity.curry (saddle H) u Y at hm
  have hh := hm 0
  simp only [curry_eq_saddlePoint] at hh
  change energy (4 * H / 3) u - 0 ^ 2 / 2 ≤ energy (4 * H / 3) u - Y ^ 2 / 2 at hh
  have hsq : Y ^ 2 = 0 := le_antisymm (by nlinarith only [hh]) (sq_nonneg Y)
  exact sq_eq_zero_iff.mp hsq

theorem actual_uStar_is_proxPoint (H : ℝ) (hH : 0 < H) (x : Plane) :
    OriginalSaddleTransfer.uStar (JointSliceRegularity.curry (saddle H)) (2 * H) x = proxPoint x := by
  let P := OriginalSaddleTransfer.phi (JointSliceRegularity.curry (saddle H))
  have heq (u : Plane) : MoreauTransfer.objective P (2 * H) x u = energy H x +
      (8 * H / 3) * (u.fst - (3 / 4 : ℝ) * x.fst) ^ 2 + (2 * H) * (u.snd - x.snd) ^ 2 := by
    unfold MoreauTransfer.objective
    dsimp only [P]
    rw [actual_phi, exact_quadratic_moreau_identity]
  have hprox : MoreauTransfer.objective P (2 * H) x (proxPoint x) = energy H x := by
    rw [heq]
    change energy H x + (8 * H / 3) * ((3 / 4 : ℝ) * x.fst - (3 / 4 : ℝ) * x.fst) ^ 2 + (2 * H) * (x.snd - x.snd) ^ 2 = _
    ring
  have hmin : ∀ u, MoreauTransfer.objective P (2 * H) x (proxPoint x) ≤ MoreauTransfer.objective P (2 * H) x u := by
    intro u
    rw [hprox, heq]
    have h1 : 0 ≤ (8 * H / 3) * (u.fst - (3 / 4 : ℝ) * x.fst) ^ 2 := by positivity
    have h2 : 0 ≤ (2 * H) * (u.snd - x.snd) ^ 2 := by positivity
    linarith only [h1, h2]
  let U := OriginalSaddleTransfer.uStar (JointSliceRegularity.curry (saddle H)) (2 * H) x
  have hex : ∃ U : Plane, ∀ v, MoreauTransfer.objective P (2 * H) x U ≤ MoreauTransfer.objective P (2 * H) x v :=
    ⟨proxPoint x, hmin⟩
  have hselected := Classical.epsilon_spec hex
  change ∀ v, MoreauTransfer.objective P (2 * H) x U ≤ MoreauTransfer.objective P (2 * H) x v at hselected
  have hh := hselected (proxPoint x)
  rw [hprox, heq] at hh
  have h1 : 0 ≤ (8 * H / 3) * (U.fst - (3 / 4 : ℝ) * x.fst) ^ 2 := by positivity
  have h2 : 0 ≤ (2 * H) * (U.snd - x.snd) ^ 2 := by positivity
  have ha : U.fst - (3 / 4 : ℝ) * x.fst = 0 := by
    by_contra hn
    have hp := mul_pos (by positivity : 0 < 8 * H / 3) (sq_pos_of_ne_zero hn)
    linarith only [hh, h2, hp]
  have hb : U.snd - x.snd = 0 := by
    by_contra hn
    have hp := mul_pos (by positivity : 0 < 2 * H) (sq_pos_of_ne_zero hn)
    linarith only [hh, h1, hp]
  apply (WithLp.ext_iff 2).mpr
  exact Prod.ext (by change U.fst = (3 / 4 : ℝ) * x.fst; linarith only [ha])
    (by change U.snd = x.snd; linarith only [hb])

theorem actual_zStar_is_trueSaddlePoint (H : ℝ) (hH : 0 < H) (x : Plane) :
    OriginalSaddleStability.zStar (JointSliceRegularity.curry (saddle H)) (2 * H) x = trueSaddlePoint x := by
  unfold OriginalSaddleStability.zStar OriginalSaddleTransfer.vStar
  rw [actual_uStar_is_proxPoint H hH, actual_yStar_is_zero]
  rfl

theorem approximate_saddle_distance_to_original_zStar
    (H c : ℝ) (hH : 0 < H) (hc : 0 < c) (q : Plane × ℝ) (hq : 0 < q.2) :
    ‖approximateSaddle H c q - OriginalSaddleStability.zStar (JointSliceRegularity.curry (saddle H)) (2 * H) q.1‖ ≤ q.2 / (4 * H) := by
  rw [actual_zStar_is_trueSaddlePoint H hH]
  exact approximate_saddle_distance_certificate H c hH hc q hq

end
end OriginalCubicSaddleEmbedding


namespace OriginalCubicSaddleEmbedding

open OriginalCubicTerminalCounterexample OriginalCubicFullProgramCounterexample
  OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

noncomputable def realizeRequests {Q A R B C : Type*}
    (request : Q → GetterProgram B C A) : GetterProgram Q A R → GetterProgram B C R
  | .pure r => .pure r
  | .ask q next => FangqingGetterComposition.bind (request q) (fun a => realizeRequests request (next a))

theorem actual_request_realization_preserves_execution
    {Q A R B C : Type*} (base : B → C) (request : Q → GetterProgram B C A) (getter : Q → A)
    (hrequest : ∀ q, execute base (request q) = (getter q, 1)) (P : GetterProgram Q A R) :
    execute base (realizeRequests request P) = execute getter P := by
  induction P with
  | pure r => rfl
  | ask q next ih =>
      simp only [realizeRequests, execute_bind, hrequest q, ih, execute]
      exact Prod.ext rfl (by omega)

def bundledFullProgram (H c : ℝ) :
    GetterProgram SaddleSpace (OriginalDualOracleProgram.OracleAnswer SaddleSpace)
      (OriginalOuterCubicSeparateErrors.CubicOutput Plane) :=
  realizeRequests (exactBundleGetterProgram H c) (fullProgram H)

theorem actual_complete_bundled_program_execution
    (H c : ℝ) (hH : 16 ≤ H) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c) =
      (⟨start H + step H c, true, 1, 0, ‖step H c‖ ^ 3⟩, 2) := by
  rw [bundledFullProgram, actual_request_realization_preserves_execution
    (OriginalDualOracleProgram.actualOracle (saddle H)) (exactBundleGetterProgram H c) (getter H c)
      (actual_bundled_oracle_execution_is_getter H c (by linarith only [hH] : H ≠ 0))]
  exact actual_complete_program_execution H c hH hc hsmall

def standingRho (H : ℝ) : ℝ := 1 / (8 * (1 + 2 * H) ^ (3 / 2 : ℝ))

theorem standing_curvature_calibration (H : ℝ) (hH : 16 ≤ H) :
    0 < standingRho H ∧ 1 ≤ (2 * H) / 1 ∧
      8 * standingRho H * (1 + (2 * H) / 1) ^ (3 / 2 : ℝ) = paperCurvature := by
  have hb : 0 < 1 + 2 * H := by linarith only [hH]
  have hp : 0 < (1 + 2 * H) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hb _
  refine ⟨by unfold standingRho; positivity, by simpa using (show (1 : ℝ) ≤ 2 * H by linarith only [hH]), ?_⟩
  dsimp [standingRho, paperCurvature]
  field_simp [hp.ne']
  <;> ring

/- This is an explicitly negative theorem. It concerns the stated universal
all-move cubic sum, not the main minimax theorem. The complete general outer
program is the checked finite-fuel program. The final move is identified by
its actual consecutive-query trace and by the full exact-bundle execution. -/
theorem original_outer_cubic_sum_full_saddle_counterexample
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hsmall : c ≤ 1 / 4096) :
    ∃ H : ℝ, 16 ≤ H ∧
      0 < standingRho H ∧
      ContDiff ℝ 2 (saddle H) ∧
      (∀ z w : SaddleSpace, ‖gradient (saddle H) z - gradient (saddle H) w‖ ≤ (2 * H) * ‖z - w‖) ∧
      (∀ z w : SaddleSpace, ‖fderiv ℝ (gradient (saddle H)) z - fderiv ℝ (gradient (saddle H)) w‖ ≤ standingRho H * ‖z - w‖) ∧
      (∀ u : Plane, StrongConvexOn (Set.univ : Set ℝ) 1 (fun y => -JointSliceRegularity.curry (saddle H) u y)) ∧
      (∀ x : Plane, OriginalSaddleTransfer.saddleEnvelope (JointSliceRegularity.curry (saddle H)) (2 * H) x = energy H x) ∧
      (let Phi := OriginalSaddleTransfer.phi (JointSliceRegularity.curry (saddle H));
        sInf (Set.range Phi) = 0 ∧ Phi (start H) - sInf (Set.range Phi) = originalGap H) ∧
      (∀ y : ℝ, JointSliceRegularity.curry (saddle H) (start H) y ≤ JointSliceRegularity.curry (saddle H) (start H) 0) ∧
      originalGap H * (2 * H) / 1 ^ 2 = 16 / 3 ∧
      8 * standingRho H * (1 + (2 * H) / 1) ^ (3 / 2 : ℝ) = paperCurvature ∧
      ContDiff ℝ 2 (energy H) ∧ (∀ x : Plane, 0 ≤ energy H x) ∧
      sInf (Set.range (energy H)) = 0 ∧
      energy H (start H) - sInf (Set.range (energy H)) ≤ originalGap H ∧
      (∀ t : Plane, OriginalOuterCubic.model (observedGradient c) (hessian H) paperCurvature (step H c) ≤
        OriginalOuterCubic.model (observedGradient c) (hessian H) paperCurvature t) ∧
      2 * c ≤ ‖step H c‖ ^ 2 ∧
      (∀ x y : Plane, ‖fderiv ℝ (gradient (energy H)) x - fderiv ℝ (gradient (energy H)) y‖ ≤ paperCurvature * ‖x - y‖) ∧
      (∀ x : Plane, OriginalOuterCubicSeparateErrors.Accurate (energy H) internalCurvature 1 x
        (getter H c (x, OriginalOuterCubicSeparateErrors.tolerance internalCurvature 1))) ∧
      (∀ request : Plane × ℝ,
        execute (OriginalDualOracleProgram.actualOracle (saddle H)) (exactBundleGetterProgram H c request) =
          (getter H c request, 1)) ∧
      (∀ request : Plane × ℝ, 0 < request.2 →
        ‖approximateSaddle H c request - OriginalSaddleStability.zStar (JointSliceRegularity.curry (saddle H)) (2 * H) request.1‖ ≤ request.2 / (4 * H)) ∧
      (∀ x u : Plane, ∀ y : ℝ,
        OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x (proxPoint x) y ≤
          OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x (proxPoint x) 0 ∧
        OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x (proxPoint x) 0 ≤
          OriginalSaddleTransfer.saddleObjective (JointSliceRegularity.curry (saddle H)) (2 * H) x u 0) ∧
      (execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c)).1.success = true ∧
      (execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c)).1.moves = 1 ∧
      (execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c)).2 = 2 ∧
      ‖gradient (energy H) (execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c)).1.point‖ ≤ 1 / 2 ∧
      (execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c)).1.cubicSteps =
        movementCubes (FangqingGetterComposition.trace (getter H c) (fullProgram H)) ∧
      C * originalGap H / paperCurvature <
        (execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c)).1.cubicSteps := by
  obtain ⟨H, hH, hbelow, hEinf, hEgap, hAcc, hsuccess, hmoves, hcalls, hstop, htrace, hbadInternal, hbadPaper⟩ :=
    full_program_has_no_uniform_all_move_cubic_budget C c hC hc hsmall
  have hHp : 0 < H := by linarith only [hH]
  have hcal := standing_curvature_calibration H hH
  have hClass := actual_joint_smooth_and_hessian_lipschitz H (standingRho H) hH hcal.1.le
  have hOriginal := original_primal_gap_and_exact_dual_initialization H hH
  have hfull := actual_complete_bundled_program_execution H c hH hc hsmall
  have hsame := actual_request_realization_preserves_execution
    (OriginalDualOracleProgram.actualOracle (saddle H)) (exactBundleGetterProgram H c) (getter H c)
    (actual_bundled_oracle_execution_is_getter H c hHp.ne') (fullProgram H)
  change execute (OriginalDualOracleProgram.actualOracle (saddle H)) (bundledFullProgram H c) =
    execute (getter H c) (fullProgram H) at hsame
  refine ⟨H, hH, hcal.1, actual_saddle_contDiff H, hClass.1, hClass.2, ?_, actual_envelope H hHp,
    ?_, ?_, hOriginal.2.2.2, hcal.2.2, energy_contDiff H, hbelow, hEinf, hEgap,
    (actual_model_equations H c).1, (actual_step_geometry H c hH hc (by linarith only [hsmall])).1,
    ?_, hAcc, actual_bundled_oracle_execution_is_getter H c hHp.ne',
    ?_, true_point_is_actual_saddle H hHp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simpa only [curry_eq_saddlePoint] using actual_dual_strong_concavity H u
  · exact ⟨hOriginal.1, hOriginal.2.1⟩
  · intro y
    simpa only [curry_eq_saddlePoint] using hOriginal.2.2.1 y
  · intro x y
    simp only [actual_hessian, sub_self, norm_zero]
    exact mul_nonneg (by norm_num [paperCurvature]) (norm_nonneg _)
  · intro request hrequest
    exact approximate_saddle_distance_to_original_zStar H c hHp hc request hrequest
  · rw [hsame]; exact hsuccess
  · rw [hsame]; exact hmoves
  · rw [hsame]; exact hcalls
  · rw [hsame]; exact hstop
  · rw [hsame]; exact htrace
  · rw [hsame]; exact hbadPaper

end
end OriginalCubicSaddleEmbedding
end PaperAudit.OuterCounterexample
