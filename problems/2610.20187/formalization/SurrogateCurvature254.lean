import SurrogateDomination254

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Paper254

def scalarSurrogate (γ s : ℝ) : ℝ := s + γ/2*s^2
def scalarTilt (γ s : ℝ) : ℝ := Real.exp (-(γ/2)*scalarSurrogate γ s)
def scalarTiltDeriv (γ s : ℝ) : ℝ := -(γ/2)*(1+γ*s)*scalarTilt γ s
def scalarTiltSecond (γ s : ℝ) : ℝ :=
  ((γ/2)^2*(1+γ*s)^2-γ^2/2)*scalarTilt γ s

theorem scalarSurrogate_derivative (γ s : ℝ) :
    HasDerivAt (scalarSurrogate γ) (1+γ*s) s := by
  convert (hasDerivAt_id s).add (((hasDerivAt_id s).pow 2).const_mul (γ/2)) using 1
  dsimp
  ring

theorem scalarTilt_derivative (γ s : ℝ) :
    HasDerivAt (scalarTilt γ) (scalarTiltDeriv γ s) s := by
  convert ((scalarSurrogate_derivative γ s).const_mul (-(γ/2))).exp using 1
  dsimp [scalarTiltDeriv, scalarTilt]
  ring

theorem scalarTilt_second (γ s : ℝ) :
    HasDerivAt (scalarTiltDeriv γ) (scalarTiltSecond γ s) s := by
  have hl := (((hasDerivAt_id s).const_mul γ).const_add 1).const_mul (-(γ/2))
  convert hl.mul (scalarTilt_derivative γ s) using 1
  dsimp [scalarTiltDeriv, scalarTiltSecond]
  ring

theorem scalarTilt_concave (γ : ℝ) (hγ : 0 < γ) :
    ConcaveOn ℝ (Icc (-1/(4*γ)) (1/(4*γ))) (scalarTilt γ) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun s _ => (scalarTilt_derivative γ s).continuousAt.continuousWithinAt)
    (fun s _ => (scalarTilt_derivative γ s).hasDerivWithinAt)
    (fun s _ => (scalarTilt_second γ s).hasDerivWithinAt)
  intro s hs
  have hb : s ∈ Icc (-1/(4*γ)) (1/(4*γ)) := interior_subset hs
  have hp : 0 < 4*γ := by positivity
  have hl := (div_le_iff₀ hp).mp hb.1
  have hu := (le_div_iff₀ hp).mp hb.2
  have hq := Audit254.surrogate_curvature (γ*s) (by nlinarith) (by nlinarith)
  have hc : (γ/2)^2*(1+γ*s)^2-γ^2/2 ≤ 0 := by
    have hm := mul_nonneg (sq_nonneg γ) (show 0 ≤ 2-(1+γ*s)^2 by linarith)
    nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg hc (Real.exp_pos _).le

/-- Lemma B.1's exp-concavity assertion for the common rank-one surrogate,
proved from the actual gradient and domain bounds. -/
theorem surrogate_expConcave {d : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) {g w : Space d}
    (hg : ‖g‖ ≤ G) (hw : w ∈ W.carrier) :
    ExpConcaveOn (curvature D G η / 2) W.carrier
      (rankOneSurrogate (curvature D G η) g w) := by
  let γ := curvature D G η
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hgd : G*D ≤ 1/(4*γ) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*γ)).mpr
    have hh := curvature_times_radius D G η hD hG
    change γ*(G*D) ≤ 1/4 at hh
    nlinarith
  have hmem : ∀ v ∈ W.carrier, ⟪g,v-w⟫ ∈ Icc (-1/(4*γ)) (1/(4*γ)) := by
    intro v hv
    have hh := le_trans (gradient_inner_bound W hG.le hg hw hv) hgd
    have hh' := abs_le.mp hh
    exact ⟨by simpa only [neg_div] using hh'.1, hh'.2⟩
  refine ⟨W.convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := (scalarTilt_concave γ hγ).2 (hmem x hx) (hmem y hy) ha hb hab
  have he : ⟪g, (a • x + b • y)-w⟫ =
      a*⟪g,x-w⟫ + b*⟪g,y-w⟫ := by
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
    have hm := congrArg (fun z : ℝ => z * ⟪g,w⟫) hab
    nlinarith [hm]
  change a • scalarTilt γ ⟪g,x-w⟫ + b • scalarTilt γ ⟪g,y-w⟫ ≤
    scalarTilt γ ⟪g,(a • x+b • y)-w⟫
  rw [he]
  exact hc

theorem surrogate_properties {d : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) {f : Loss d}
    (hf : ExpConcaveOn η W.carrier f) {g w : Space d}
    (hd : HasGradientWithinAt f g W.carrier w) (hg : ‖g‖ ≤ G)
    (hw : w ∈ W.carrier) :
    (∀ v ∈ W.carrier, f w-f v ≤
      rankOneSurrogate (curvature D G η) g w w-rankOneSurrogate (curvature D G η) g w v) ∧
    ExpConcaveOn (curvature D G η/2) W.carrier
      (rankOneSurrogate (curvature D G η) g w) := by
  constructor
  · intro v hv
    have hz : rankOneSurrogate (curvature D G η) g w w = 0 := by
      simp [rankOneSurrogate]
    rw [hz, zero_sub]
    exact surrogate_domination W hD hG hη hf hd hg hw hv
  · exact surrogate_expConcave W hD hG hη hg hw

end Paper254
#print axioms Paper254.surrogate_expConcave
#print axioms Paper254.surrogate_properties
