import GradientHessian.LeafOracle
import GradientHessian.JetLocality
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The complete physical ordinary jet factors through a single numerical
matrix product. The decoder is jointly continuous in the query point and
the returned product, with all marked coefficients fixed and known. -/

noncomputable section
namespace GradientHessian.Leaf
open InnerCoordinates JetLocality Filter
open scoped Topology InnerProductSpace

def capSlope (L r : ℝ) : ℝ := deriv (LeafCutoff.radial L) r/(2*r)

theorem capSlope_zero {L r : ℝ} (hL : 0 < L) (hr : r ≤ L) : capSlope L r = 0 := by
  have ha : r/L-1 ≤ 0 := by have h := (div_le_one hL).mpr hr; linarith
  rw [capSlope, (LeafCutoff.radial_derivative L r).deriv]
  simp [Profiles.step₁, ha]

theorem capSlope_continuous {L : ℝ} (hL : 0 < L) : Continuous (capSlope L) := by
  have hd : Continuous (deriv (LeafCutoff.radial L)) := by
    have he : deriv (LeafCutoff.radial L) = fun r => -Profiles.step₁ (r/L-1)/L :=
      funext (fun r => (LeafCutoff.radial_derivative L r).deriv)
    rw [he]
    have hs : Continuous Profiles.step₁ := continuous_iff_continuousAt.mpr
      (fun r => (Profiles.step₁_derivative r).continuousAt)
    exact (hs.comp ((continuous_id.div_const L).sub continuous_const)).neg.div_const L
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    have he : capSlope L =ᶠ[𝓝 (0:ℝ)] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hL] with t ht
      exact capSlope_zero hL ht.le
    exact continuousAt_const.congr_of_eventuallyEq he
  · exact hd.continuousAt.div (continuousAt_const.mul continuousAt_id) (mul_ne_zero (by norm_num) hr)

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem valueFromProduct_continuous (M : ℝ) {L : ℝ} (hL : 0 < L) :
    Continuous (fun p : Y × Y => valueFromProduct M L p.1 p.2) := by
  unfold valueFromProduct
  exact (continuous_const.mul (continuous_fst.norm.pow 2)).add
    ((continuous_const.mul ((LeafCutoff.cutoff_contDiff hL).continuous.comp continuous_fst)).mul
      (continuous_fst.inner (continuous_snd.sub (continuous_const.smul continuous_fst))))

theorem gradientFromProduct_continuous (M : ℝ) {L : ℝ} (hL : 0 < L) :
    Continuous (fun p : Y × Y => gradientFromProduct M L p.1 p.2) := by
  have hs := (capSlope_continuous hL).comp
    (continuous_fst : Continuous (Prod.fst : Y×Y → Y)).norm
  have hc := (LeafCutoff.cutoff_contDiff hL).continuous.comp (continuous_fst : Continuous (Prod.fst : Y×Y → Y))
  have ht := continuous_snd.sub ((continuous_const : Continuous (fun _ : Y×Y => 2*M)).smul continuous_fst)
  exact ((continuous_const.smul continuous_fst).add (hc.smul ht)).add
    ((hs.mul (continuous_fst.inner ht)).smul continuous_fst)

/-- This term contains no matrix parameter. -/
def knownTerm (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (Z : Space Y E m) : ℝ := Inner.publicQuadratic m Inner.absoluteDepth Z + Inner.residual b a v Z

theorem knownTerm_contDiff (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E) :
    ContDiff ℝ 3 (knownTerm b a v) :=
  (Inner.publicQuadratic_contDiff m Inner.absoluteDepth).add (Inner.residual_contDiff b a v)

/-- A total decoder: the second argument is just the returned vector Ay.
No matrix or derivative of a matrix-dependent function is stored here. -/
def ordinaryDecoder (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E)
    (p : Space Y E m × Y) : ℝ × (Space Y E m →L[ℝ] ℝ) :=
  (valueFromProduct m (capRadius m) (numerical Y E m (Inner.absoluteDepth+2) p.1) p.2 + knownTerm b a v p.1,
    (innerSL ℝ (gradientFromProduct m (capRadius m)
      (numerical Y E m (Inner.absoluteDepth+2) p.1) p.2)).comp (numerical Y E m (Inner.absoluteDepth+2)) +
      fderiv ℝ (knownTerm b a v) p.1)

theorem ordinaryDecoder_continuous (hm : 1 ≤ m) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) : Continuous (ordinaryDecoder b a v) := by
  have hp : Continuous (fun p : Space Y E m × Y => (numerical Y E m (Inner.absoluteDepth+2) p.1,p.2)) :=
    ((numerical Y E m (Inner.absoluteDepth+2)).continuous.comp continuous_fst).prodMk continuous_snd
  have hvalue := ((valueFromProduct_continuous (m:ℝ) (capRadius_pos hm)).comp hp).add
    ((knownTerm_contDiff b a v).continuous.comp continuous_fst)
  have hgrad := (gradientFromProduct_continuous (m:ℝ) (capRadius_pos hm)).comp hp
  have hcov := ((innerSL ℝ : Y →L[ℝ] Y →L[ℝ] ℝ).continuous.comp hgrad).clm_comp
    (continuous_const : Continuous (fun _ : Space Y E m × Y => numerical Y E m (Inner.absoluteDepth+2)))
  exact hvalue.prodMk (hcov.add (((knownTerm_contDiff b a v).continuous_fderiv
    (by decide : (1:WithTop ℕ∞) ≤ 3)).comp continuous_fst))

theorem ordinaryDecoder_borel (hm : 1 ≤ m) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) :
    @Measurable (Space Y E m × Y) (ℝ × (Space Y E m →L[ℝ] ℝ))
      (borel _) (borel _) (ordinaryDecoder b a v) :=
  (ordinaryDecoder_continuous hm b a v).borel_measurable

theorem ordinaryDecoder_measurable [MeasurableSpace (Space Y E m)] [BorelSpace (Space Y E m)]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology (Space Y E m)] [SecondCountableTopology Y]
    (hm : 1 ≤ m) (b a : Fin m → Y) (v : Fin m → Fin (Inner.absoluteDepth+2) → E) :
    @Measurable (Space Y E m × Y) (ℝ × (Space Y E m →L[ℝ] ℝ))
      inferInstance (borel _) (ordinaryDecoder b a v) :=
  (ordinaryDecoder_borel hm b a v).mono OpensMeasurableSpace.borel_le le_rfl

variable [CompleteSpace Y]

theorem ordinaryJet_one_product (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    ordinaryJet (objective A b a v) Z =
      ordinaryDecoder b a v (Z,A (numerical Y E m (Inner.absoluteDepth+2) Z)) := by
  have he : objective A b a v = fun W =>
      LeafNumerical.base m (capRadius m) A (numerical Y E m (Inner.absoluteDepth+2) W) + knownTerm b a v W := by
    funext W
    rw [objective_decomposition]
    unfold knownTerm
    ring
  have hn := (LeafNumerical.base_hasGradientAt (M := m) (capRadius_pos hm) A hsym
    (numerical Y E m (Inner.absoluteDepth+2) Z)).hasFDerivAt
  have hD : HasFDerivAt (LeafNumerical.base m (capRadius m) A)
      (innerSL ℝ (gradientFromProduct m (capRadius m)
        (numerical Y E m (Inner.absoluteDepth+2) Z) (A (numerical Y E m (Inner.absoluteDepth+2) Z))))
      (numerical Y E m (Inner.absoluteDepth+2) Z) := by
    convert hn using 1
  have h := (hD.comp Z (numerical Y E m (Inner.absoluteDepth+2)).hasFDerivAt).add
    (((knownTerm_contDiff b a v).differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) Z).hasFDerivAt)
  apply Prod.ext
  · change objective A b a v Z = _
    rw [he]
    rfl
  · change fderiv ℝ (objective A b a v) Z = _
    rw [he]
    exact h.fderiv

/-- When the full matrix is already known, differentiating the displayed
physical covector gives its full Hessian, including mixed memory entries. -/
def knownMatrixDecoder (A : Y →L[ℝ] Y) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    ℝ × (Space Y E m →L[ℝ] ℝ) × (Space Y E m →L[ℝ] (Space Y E m →L[ℝ] ℝ)) :=
  ((ordinaryDecoder b a v (Z,A (numerical Y E m (Inner.absoluteDepth+2) Z))).1,
    (ordinaryDecoder b a v (Z,A (numerical Y E m (Inner.absoluteDepth+2) Z))).2,
    fderiv ℝ (fun W => (ordinaryDecoder b a v (W,A (numerical Y E m (Inner.absoluteDepth+2) W))).2) Z)

theorem richJet_known_matrix (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) (Z : Space Y E m) :
    richJet (objective A b a v) Z = knownMatrixDecoder A b a v Z := by
  have h := ordinaryJet_one_product hm A hsym b a v Z
  have hd : fderiv ℝ (objective A b a v) = fun W =>
      (ordinaryDecoder b a v (W,A (numerical Y E m (Inner.absoluteDepth+2) W))).2 :=
    funext (fun W => congrArg Prod.snd (ordinaryJet_one_product hm A hsym b a v W))
  have hval : objective A b a v Z =
      (ordinaryDecoder b a v (Z,A (numerical Y E m (Inner.absoluteDepth+2) Z))).1 := congrArg Prod.fst h
  have hder : fderiv ℝ (objective A b a v) Z =
      (ordinaryDecoder b a v (Z,A (numerical Y E m (Inner.absoluteDepth+2) Z))).2 := congrArg Prod.snd h
  exact Prod.ext hval (Prod.ext hder (congrArg (fun f => fderiv ℝ f Z) hd))

theorem knownMatrixDecoder_continuous (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) : Continuous (knownMatrixDecoder A b a v) := by
  rw [← funext (richJet_known_matrix hm A hsym b a v)]
  have hc := objective_contDiff hm A b a v
  exact hc.continuous.prodMk ((hc.continuous_fderiv (by decide : (1:WithTop ℕ∞) ≤ 3)).prodMk
    ((hc.fderiv_right (by decide : (2:WithTop ℕ∞)+1 ≤ 3)).continuous_fderiv
      (by decide : (1:WithTop ℕ∞) ≤ 2)))

theorem knownMatrixDecoder_borel (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (b a : Fin m → Y)
    (v : Fin m → Fin (Inner.absoluteDepth+2) → E) :
    @Measurable (Space Y E m)
      (ℝ × (Space Y E m →L[ℝ] ℝ) × (Space Y E m →L[ℝ] (Space Y E m →L[ℝ] ℝ)))
      (borel _) (borel _) (knownMatrixDecoder A b a v) :=
  (knownMatrixDecoder_continuous hm A hsym b a v).borel_measurable

end GradientHessian.Leaf
