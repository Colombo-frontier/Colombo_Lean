import Bilevel.PartialLegendreEnvelope

/-! Full informative-gradient envelope for two actual partial conjugates.
The common gradient may be unbounded: only its Lipschitz constant and the
uniform difference of the two full gradients enter the proof. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G G₀ : Joint X Y → Joint X Y}
  (hG : LipschitzWith δ G) (hG₀ : LipschitzWith δ G₀) (hδ : δ<1)

omit [CompleteSpace X] in
theorem jointSolution_difference_bound {η : ℝ}
    (hdiff : ∀ v,‖G v-G₀ v‖≤η) (x : X) (y : Y) :
    ‖jointSolution hG hδ x y-jointSolution hG₀ hδ x y‖≤η/(1-(δ:ℝ)) := by
  let z := jointSolution hG hδ x y
  let w := jointSolution hG₀ hδ x y
  have hz : z+(G (pack x z)).snd=y := jointSolution_equation hG hδ x y
  have hw : w+(G₀ (pack x w)).snd=y := jointSolution_equation hG₀ hδ x y
  have hid : z-w=(G₀ (pack x w)).snd-(G (pack x z)).snd := by
    calc
      z-w = (z+(G (pack x z)).snd)-(w+(G₀ (pack x w)).snd)+
        ((G₀ (pack x w)).snd-(G (pack x z)).snd) := by abel
      _ = _ := by rw [hz,hw,sub_self,zero_add]
  have ht := norm_sub_le_norm_sub_add_norm_sub (G₀ (pack x w)).snd
    (G₀ (pack x z)).snd (G (pack x z)).snd
  rw [← hid] at ht
  have hlocal := (jointSlice_lipschitz hG₀ x).dist_le_mul w z
  rw [dist_eq_norm,dist_eq_norm,norm_sub_rev w z] at hlocal
  have hdiff' : ‖G₀ (pack x z)-G (pack x z)‖≤η := by
    rw [norm_sub_rev]
    exact hdiff _
  have hpart := (WithLp.norm_snd_le X (G₀ (pack x z)-G (pack x z))).trans hdiff'
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  change ‖z-w‖≤η/(1-(δ:ℝ))
  apply (le_div_iff₀ hd).mpr
  change ‖(G₀ (pack x z)).snd-(G (pack x z)).snd‖≤η at hpart
  nlinarith

omit [CompleteSpace X] in
theorem jointGradient_difference_bound {η : ℝ}
    (hdiff : ∀ v,‖G v-G₀ v‖≤η) (q : Joint X Y) :
    ‖jointGradient hG hδ q-jointGradient hG₀ hδ q‖≤Real.sqrt 2*(η/(1-(δ:ℝ))) := by
  let z := jointSolution hG hδ q.fst q.snd
  let w := jointSolution hG₀ hδ q.fst q.snd
  let R := η/(1-(δ:ℝ))
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hη : 0≤η := (norm_nonneg (G 0-G₀ 0)).trans (hdiff 0)
  have hR : 0≤R := div_nonneg hη hd.le
  have hsol : ‖z-w‖≤R := jointSolution_difference_bound hG hG₀ hδ hdiff q.fst q.snd
  have ha : ‖(G (pack q.fst z)).fst-(G₀ (pack q.fst z)).fst‖≤η :=
    (WithLp.norm_fst_le X (G (pack q.fst z)-G₀ (pack q.fst z))).trans (hdiff _)
  have hl := hG₀.dist_le_mul (pack q.fst z) (pack q.fst w)
  rw [dist_eq_norm,dist_eq_norm] at hl
  have he : ‖pack q.fst z-pack q.fst w‖=‖z-w‖ := by
    change ‖pack (q.fst-q.fst) (z-w)‖=‖z-w‖
    rw [sub_self,norm_pack_zero_left]
  rw [he] at hl
  have hb := (WithLp.norm_fst_le X (G₀ (pack q.fst z)-G₀ (pack q.fst w))).trans hl
  have htri := norm_sub_le_norm_sub_add_norm_sub (G (pack q.fst z)).fst
    (G₀ (pack q.fst z)).fst (G₀ (pack q.fst w)).fst
  have heq : η+(δ:ℝ)*R=R := by dsimp [R]; field_simp; ring
  have hmacro : ‖(G (pack q.fst z)).fst-(G₀ (pack q.fst w)).fst‖≤R := by
    have hm := mul_le_mul_of_nonneg_left hsol δ.coe_nonneg
    change ‖(G₀ (pack q.fst z)).fst-(G₀ (pack q.fst w)).fst‖≤(δ:ℝ)*‖z-w‖ at hb
    linarith
  have hx : ‖(jointGradient hG hδ q-jointGradient hG₀ hδ q).fst‖≤R := by
    change ‖-(G (pack q.fst z)).fst-(-(G₀ (pack q.fst w)).fst)‖≤R
    rw [show -(G (pack q.fst z)).fst-(-(G₀ (pack q.fst w)).fst)=
      -((G (pack q.fst z)).fst-(G₀ (pack q.fst w)).fst) by abel,norm_neg]
    exact hmacro
  have hy : ‖(jointGradient hG hδ q-jointGradient hG₀ hδ q).snd‖≤R := hsol
  have hxs := (sq_le_sq₀ (norm_nonneg _) hR).mpr hx
  have hys := (sq_le_sq₀ (norm_nonneg _) hR).mpr hy
  change ‖jointGradient hG hδ q-jointGradient hG₀ hδ q‖≤Real.sqrt 2*R
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hR)).mp
  rw [norm_sq,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  linarith

variable (P P₀ : Joint X Y → ℝ)
  (hP : ∀ q,HasGradientAt P (G q) q) (hP₀ : ∀ q,HasGradientAt P₀ (G₀ q) q)
include hP hP₀

theorem informative_hasGradientAt (m : ℝ) (q : Joint X Y) :
    HasGradientAt (fun v => m*(jointConjugate hG hδ P v-jointConjugate hG₀ hδ P₀ v))
      (m • (jointGradient hG hδ q-jointGradient hG₀ hδ q)) q := by
  have hh := ((jointConjugate_hasGradientAt hG hδ P hP q).hasFDerivAt.sub
    (jointConjugate_hasGradientAt hG₀ hδ P₀ hP₀ q).hasFDerivAt).const_smul m
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1
  ext v
  simp [InnerProductSpace.toDual_apply,real_inner_smul_left,inner_sub_left]

/-- Source `rec:lem:conjugate-envelope`, for actual full gradients of the
actual scalar conjugate difference. No bounded common-gradient premise. -/
theorem informative_gradient_bound {m η : ℝ} (hm : 0≤m)
    (hdiff : ∀ v,‖G v-G₀ v‖≤η) (q : Joint X Y) :
    ‖gradient (fun v => m*(jointConjugate hG hδ P v-jointConjugate hG₀ hδ P₀ v)) q‖ ≤
      (Real.sqrt 2*m/(1-(δ:ℝ)))*η := by
  rw [(informative_hasGradientAt hG hG₀ hδ P P₀ hP hP₀ m q).gradient,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg hm]
  have hh := mul_le_mul_of_nonneg_left (jointGradient_difference_bound hG hG₀ hδ hdiff q) hm
  convert hh using 1
  ring

end Bilevel.PartialLegendre
