import MinimaxAudit.CriterionFull

/-!
Strong monotonicity of the actual scalar/saddle gradient implies genuine
strong convexity/concavity support inequalities. The support conclusion is
proved by the one-dimensional mean value theorem, never supplied as a field.
-/
namespace MinimaxAudit

section ScalarStrong
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Global strong monotonicity of a true gradient gives the exact
mu/2 quadratic support inequality. Differentiability is enough. -/
theorem strong_gradient_support (f : E → ℝ) (g : E → E) (mu : ℝ)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hstrong : ∀ x y, mu * ‖x - y‖ ^ 2 ≤ inner ℝ (g x - g y) (x - y))
    (x y : E) :
    f x + inner ℝ (g x) (y - x) + mu / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  let d : E := y - x
  let line : ℝ → E := fun t => x + t • d
  let err : ℝ → ℝ := fun t =>
    f (line t) - f x - t * inner ℝ (g x) d - mu / 2 * t ^ 2 * ‖d‖ ^ 2
  have hline (t : ℝ) : HasDerivAt line d t := by
    simpa [line] using ((hasDerivAt_id t).smul_const d).const_add x
  have hfline (t : ℝ) : HasDerivAt (fun u => f (line u)) (inner ℝ (g (line t)) d) t := by
    convert! (hg (line t)).hasFDerivAt.comp_hasDerivAt t (hline t) using 1
  have herr (t : ℝ) : HasDerivAt err
      (inner ℝ (g (line t)) d - inner ℝ (g x) d - mu * t * ‖d‖ ^ 2) t := by
    have h := ((hfline t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (g x) d))
    have h2 := (((hasDerivAt_id t).pow 2).const_mul (mu / 2)).mul_const (‖d‖ ^ 2)
    convert! h.sub h2 using 1 <;> simp [err] <;> (try ring_nf) <;> simp_all
  have hmono : MonotoneOn err (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun t _ => (herr t).continuousAt.continuousWithinAt)
      (fun t _ => (herr t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht0 : 0 < t := (show t ∈ Set.Ioo (0 : ℝ) 1 by simpa using ht).1
    have hs := hstrong (line t) x
    have hdisp : line t - x = t • d := by simp [line]
    rw [hdisp, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, inner_smul_right,
      inner_sub_left] at hs
    have hpair : mu * t * ‖d‖ ^ 2 ≤ inner ℝ (g (line t)) d - inner ℝ (g x) d := by
      apply (mul_le_mul_iff_right₀ ht0).1
      nlinarith [hs]
    rw [(herr t).deriv]
    linarith
  have h01 := hmono (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  have hlin0 : line 0 = x := by simp [line]
  have hlin1 : line 1 = y := by dsimp [line, d]; simp
  dsimp [err] at h01
  rw [hlin0, hlin1] at h01
  simp only [zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), one_mul, one_pow,
    sub_self] at h01
  dsimp [d] at h01
  linarith

/-- Genuine supporting linear forms imply convexity, proved by combining
the supports at a convex combination. -/
theorem convex_univ_of_linear_support (f : E → ℝ) (g : E → E)
    (hsupport : ∀ x y, f x + inner ℝ (g x) (y - x) ≤ f y) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : E := a • x + b • y
  have h1 := mul_le_mul_of_nonneg_left (hsupport z x) ha
  have h2 := mul_le_mul_of_nonneg_left (hsupport z y) hb
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = a • x + b • y - (a + b) • z := by module
      _ = 0 := by rw [hab, one_smul]; dsimp [z]; abel
  have hlin : a * inner ℝ (g z) (x - z) + b * inner ℝ (g z) (y - z) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hvec]
    simp
  change f z ≤ a * f x + b * f y
  have hz : a * f z + b * f z = f z := by nlinarith [congrArg (fun t : ℝ => t * f z) hab]
  linarith

/-- The actual gradient monotonicity hypothesis yields mathlib's genuine
StrongConvexOn predicate, rather than a custom assumed support predicate. -/
theorem strong_convex_univ_of_strong_gradient (f : E → ℝ) (g : E → E) (mu : ℝ)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hstrong : ∀ x y, mu * ‖x - y‖ ^ 2 ≤ inner ℝ (g x - g y) (x - y)) :
    StrongConvexOn Set.univ mu f := by
  rw [strongConvexOn_iff_convex]
  apply convex_univ_of_linear_support _ (fun x => g x - mu • x)
  intro x y
  have hs := strong_gradient_support f g mu hg hstrong x y
  simp only [inner_sub_right] at hs
  have hn := congrArg (fun r : ℝ => mu / 2 * r) (norm_sub_sq_real y x)
  rw [real_inner_comm] at hn
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  nlinarith [hs, hn]

end ScalarStrong

section SaddleStrong

/-- Exact ambient monotonicity pairing in primal/dual coordinates. -/
theorem scalar_saddle_pairing_blocks {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (z w : SaddleSpace dx dy) :
    inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w) =
      inner ℝ (primalBlock (gradient phi z) - primalBlock (gradient phi w))
        (primalBlock z - primalBlock w) +
      inner ℝ ((-dualBlock (gradient phi z)) - (-dualBlock (gradient phi w)))
        (dualBlock z - dualBlock w) := by
  have hdisp : z - w = joinBlocks (primalBlock z - primalBlock w) (dualBlock z - dualBlock w) := by
    rw [join_blocks_sub, join_blocks, join_blocks]
  change inner ℝ
    (euclideanSaddleSign dx dy (gradient phi z) - euclideanSaddleSign dx dy (gradient phi w)) (z - w) = _
  rw [saddle_sign_blocks, saddle_sign_blocks, ← join_blocks_sub, hdisp, join_blocks_inner]

theorem scalar_saddle_primal_strong_gradient {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    (y : Dual dy) (x u : Primal dx) :
    mu * ‖x - u‖ ^ 2 ≤
      inner ℝ (primalBlock (gradient phi (joinBlocks x y)) -
        primalBlock (gradient phi (joinBlocks u y))) (x - u) := by
  have h := hs (joinBlocks x y) (joinBlocks u y)
  have hn : ‖joinBlocks x y - joinBlocks u y‖ = ‖x - u‖ := by
    rw [← join_blocks_sub, sub_self, ← primal_embedding_apply]
    exact (primalEmbedding dx dy).norm_map _
  rw [hn, scalar_saddle_pairing_blocks] at h
  simpa using h

theorem scalar_saddle_dual_strong_gradient {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    (x : Primal dx) (y v : Dual dy) :
    mu * ‖y - v‖ ^ 2 ≤
      inner ℝ ((-dualBlock (gradient phi (joinBlocks x y))) -
        (-dualBlock (gradient phi (joinBlocks x v)))) (y - v) := by
  have h := hs (joinBlocks x y) (joinBlocks x v)
  have hn : ‖joinBlocks x y - joinBlocks x v‖ = ‖y - v‖ := by
    rw [← join_blocks_sub, sub_self, ← dual_embedding_apply]
    exact (dualEmbedding dx dy).norm_map _
  rw [hn, scalar_saddle_pairing_blocks] at h
  simpa using h

/-- Actual primal fiber support, derived from the true signed saddle
operator's strong monotonicity. -/
theorem saddle_strong_primal_support {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    (x u : Primal dx) (y : Dual dy) :
    phi (joinBlocks x y) + inner ℝ (primalBlock (gradient phi (joinBlocks x y))) (u - x) +
      mu / 2 * ‖u - x‖ ^ 2 ≤ phi (joinBlocks u y) := by
  exact strong_gradient_support (fun t => phi (joinBlocks t y))
    (fun t => primalBlock (gradient phi (joinBlocks t y))) mu
    (fun t => has_gradient_primal_slice (hphi (joinBlocks t y)).hasGradientAt)
    (scalar_saddle_primal_strong_gradient phi mu hs y) x u

/-- Actual dual fiber support for the negative potential. -/
theorem saddle_strong_dual_support {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    (x : Primal dx) (y v : Dual dy) :
    phi (joinBlocks x v) ≤ phi (joinBlocks x y) +
      inner ℝ (dualBlock (gradient phi (joinBlocks x y))) (v - y) - mu / 2 * ‖v - y‖ ^ 2 := by
  have hg (t : Dual dy) : HasGradientAt (fun u => -phi (joinBlocks x u))
      (-dualBlock (gradient phi (joinBlocks x t))) t := by
    apply hasGradientAt_iff_hasFDerivAt.2
    simpa only [map_neg] using!
      (has_gradient_dual_slice (hphi (joinBlocks x t)).hasGradientAt).hasFDerivAt.neg
  have h := strong_gradient_support (fun t => -phi (joinBlocks x t))
    (fun t => -dualBlock (gradient phi (joinBlocks x t))) mu hg
    (scalar_saddle_dual_strong_gradient phi mu hs x) y v
  rw [inner_neg_left] at h
  linarith

/-- Source strong convexity/concavity is a genuine mathlib predicate,
proved here from actual signed-gradient strong monotonicity. -/
theorem saddle_strong_convex_concave {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w)) :
    (∀ y : Dual dy, StrongConvexOn Set.univ mu (fun x => phi (joinBlocks x y))) ∧
    (∀ x : Primal dx, StrongConcaveOn Set.univ mu (fun y => phi (joinBlocks x y))) := by
  constructor
  · intro y
    exact strong_convex_univ_of_strong_gradient (fun t => phi (joinBlocks t y))
      (fun t => primalBlock (gradient phi (joinBlocks t y))) mu
      (fun t => has_gradient_primal_slice (hphi (joinBlocks t y)).hasGradientAt)
      (scalar_saddle_primal_strong_gradient phi mu hs y)
  · intro x
    have hg (t : Dual dy) : HasGradientAt (fun u => -phi (joinBlocks x u))
        (-dualBlock (gradient phi (joinBlocks x t))) t := by
      apply hasGradientAt_iff_hasFDerivAt.2
      simpa only [map_neg] using!
        (has_gradient_dual_slice (hphi (joinBlocks x t)).hasGradientAt).hasFDerivAt.neg
    have h := strong_convex_univ_of_strong_gradient (fun t => -phi (joinBlocks x t))
      (fun t => -dualBlock (gradient phi (joinBlocks x t))) mu hg
      (scalar_saddle_dual_strong_gradient phi mu hs x)
    have h0 : StrongConvexOn Set.univ mu (-(fun t : Dual dy => phi (joinBlocks x t))) := h
    have hh : StrongConcaveOn Set.univ mu (-(-(fun t : Dual dy => phi (joinBlocks x t)))) := h0.neg
    simpa only [neg_neg] using hh

/-- A genuine ambient saddle zero supplies the source's quadratic
primal/dual comparison witness, derived from strong monotonicity. -/
theorem saddle_strong_zero_comparison_lower {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    (xstar : Primal dx) (ystar : Dual dy)
    (hzero : scalarSaddleOperator phi (joinBlocks xstar ystar) = 0)
    (x : Primal dx) (y : Dual dy) :
    mu / 2 * (‖x - xstar‖ ^ 2 + ‖y - ystar‖ ^ 2) ≤
      phi (joinBlocks x ystar) - phi (joinBlocks xstar y) := by
  have hgzero : gradient phi (joinBlocks xstar ystar) = 0 := by
    apply (euclideanSaddleSign dx dy).injective
    simpa [scalarSaddleOperator] using hzero
  have hpzero : primalBlock (gradient phi (joinBlocks xstar ystar)) = 0 := by
    rw [hgzero]
    ext i
    rfl
  have hdzero : dualBlock (gradient phi (joinBlocks xstar ystar)) = 0 := by
    rw [hgzero]
    ext i
    rfl
  have hP := saddle_strong_primal_support phi hphi mu hs xstar x ystar
  have hD := saddle_strong_dual_support phi hphi mu hs xstar ystar y
  rw [hpzero, inner_zero_left, add_zero] at hP
  rw [hdzero, inner_zero_left, add_zero] at hD
  nlinarith

/-- Compact continuous primal/dual slices bound the actual comparison set. -/
theorem saddle_differences_bddAbove_of_compact {P Q : Type*}
    [TopologicalSpace P] [TopologicalSpace Q]
    {X : Set P} {Y : Set Q} (phi : P → Q → ℝ)
    (hcX : IsCompact X) (hcY : IsCompact Y) (hneX : X.Nonempty) (hneY : Y.Nonempty)
    (x : P) (y : Q) (hcontX : ContinuousOn (fun u => phi u y) X)
    (hcontY : ContinuousOn (fun v => phi x v) Y) :
    BddAbove (saddleDifferences X Y phi x y) := by
  obtain ⟨xmin, hxmin, hmin⟩ := hcX.exists_isMinOn hneX hcontX
  obtain ⟨ymax, hymax, hmax⟩ := hcY.exists_isMaxOn hneY hcontY
  refine ⟨phi x ymax - phi xmin y, ?_⟩
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact sub_le_sub (hmax hv) (hmin hu)

/-- Source's actual saddle-gap strong-convexity separation, with
boundedness proved from the real compact domains and differentiability. -/
theorem saddle_strong_zero_gap_lower {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (hcX : IsCompact X) (hcY : IsCompact Y)
    (xstar : Primal dx) (ystar : Dual dy) (hxstar : xstar ∈ X) (hystar : ystar ∈ Y)
    (hzero : scalarSaddleOperator phi (joinBlocks xstar ystar) = 0)
    (x : Primal dx) (y : Dual dy) :
    mu / 2 * (‖x - xstar‖ ^ 2 + ‖y - ystar‖ ^ 2) ≤
      auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) x y := by
  have hb := saddle_differences_bddAbove_of_compact (fun u v => phi (joinBlocks u v))
    hcX hcY ⟨xstar, hxstar⟩ ⟨ystar, hystar⟩ x y
    (hphi.continuous.comp (continuous_join_primal y)).continuousOn
    (hphi.continuous.comp (continuous_join_dual x)).continuousOn
  exact (saddle_strong_zero_comparison_lower phi hphi mu hs xstar ystar hzero x y).trans
    (comparison_le_saddleGap hb hxstar hystar)

/-- The source's outer-primal-shell gap bound follows from the actual
strong saddle operator, without an assumed gap/support inequality. -/
theorem saddle_strong_primal_shell_gap_lower {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ) (hmu : 0 ≤ mu)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (hcX : IsCompact X) (hcY : IsCompact Y)
    (xstar : Primal dx) (ystar : Dual dy) (hxstar : xstar ∈ X) (hystar : ystar ∈ Y)
    (hzero : scalarSaddleOperator phi (joinBlocks xstar ystar) = 0)
    (x : Primal dx) (y : Dual dy) (R : ℝ) (hR : 0 ≤ R)
    (hshell : R / 2 ≤ ‖x - xstar‖) :
    mu * R ^ 2 / 8 ≤ auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) x y := by
  have hg := saddle_strong_zero_gap_lower phi hphi mu hs hcX hcY xstar ystar hxstar hystar hzero x y
  have hdual : 0 ≤ mu / 2 * ‖y - ystar‖ ^ 2 := by positivity
  apply shell_gap_lower hmu hR hshell
  nlinarith

/-- The dual outer-shell case is obtained by the same actual gap witness. -/
theorem saddle_strong_dual_shell_gap_lower {dx dy : ℕ}
    (phi : SaddleSpace dx dy → ℝ) (hphi : Differentiable ℝ phi) (mu : ℝ) (hmu : 0 ≤ mu)
    (hs : ∀ z w, mu * ‖z - w‖ ^ 2 ≤
      inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w))
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (hcX : IsCompact X) (hcY : IsCompact Y)
    (xstar : Primal dx) (ystar : Dual dy) (hxstar : xstar ∈ X) (hystar : ystar ∈ Y)
    (hzero : scalarSaddleOperator phi (joinBlocks xstar ystar) = 0)
    (x : Primal dx) (y : Dual dy) (R : ℝ) (hR : 0 ≤ R)
    (hshell : R / 2 ≤ ‖y - ystar‖) :
    mu * R ^ 2 / 8 ≤ auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) x y := by
  have hg := saddle_strong_zero_gap_lower phi hphi mu hs hcX hcY xstar ystar hxstar hystar hzero x y
  have hprimal : 0 ≤ mu / 2 * ‖x - xstar‖ ^ 2 := by positivity
  apply shell_gap_lower hmu hR hshell
  nlinarith

end SaddleStrong
end MinimaxAudit
