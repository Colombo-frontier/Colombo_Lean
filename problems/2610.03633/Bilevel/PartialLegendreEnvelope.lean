import Bilevel.PartialLegendreJoint

/-! The joint envelope derivative of the actual partial conjugate is derived
from its value function, stationarity, and a quadratic Taylor remainder. -/
noncomputable section
open scoped RealInnerProductSpace Topology
open Filter Asymptotics
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {δ : NNReal} {G : Joint X Y → Joint X Y} (hG : LipschitzWith δ G) (hδ : δ<1)

def jointGradient (q : Joint X Y) : Joint X Y :=
  let z := jointSolution hG hδ q.fst q.snd
  pack (-(G (pack q.fst z)).fst) z

def jointRemainderConstant (δ : ℝ) : ℝ :=
  let C := (1+δ)/(1-δ)
  C+(1+δ)/2*C^2+δ/2

omit [CompleteSpace X] in
theorem jointConjugate_remainder_identity (P : Joint X Y → ℝ) (q d : Joint X Y) :
    let z := jointSolution hG hδ q.fst q.snd
    let e := jointSolution hG hδ (q+d).fst (q+d).snd-z
    jointConjugate hG hδ P (q+d)-jointConjugate hG hδ P q-⟪jointGradient hG hδ q,d⟫ =
      ⟪d.snd,e⟫-‖e‖^2/2-
        (P (pack q.fst z+pack d.fst e)-P (pack q.fst z)-⟪G (pack q.fst z),pack d.fst e⟫) := by
  let z := jointSolution hG hδ q.fst q.snd
  let w := jointSolution hG hδ (q+d).fst (q+d).snd
  let e := w-z
  have hw : w=z+e := by dsimp [e]; abel
  have hz : z+(G (pack q.fst z)).snd=q.snd := jointSolution_equation hG hδ q.fst q.snd
  have hnorm : ‖w‖^2=‖z‖^2+2*⟪z,e⟫+‖e‖^2 := by rw [hw,norm_add_sq_real]
  have hpoint : pack (q.fst+d.fst) w=pack q.fst z+pack d.fst e := by rw [hw]; rfl
  have hinner : ⟪q.snd+d.snd,w⟫ =
      ⟪q.snd,z⟫+⟪q.snd,e⟫+⟪d.snd,z⟫+⟪d.snd,e⟫ := by
    rw [hw]
    simp only [inner_add_left,inner_add_right]
    ring
  dsimp only
  rw [jointConjugate_value,jointConjugate_value]
  change (⟪q.snd+d.snd,w⟫-(‖w‖^2/2+P (pack (q.fst+d.fst) w)))-
    (⟪q.snd,z⟫-(‖z‖^2/2+P (pack q.fst z)))-⟪pack (-(G (pack q.fst z)).fst) z,d⟫ =
    ⟪d.snd,e⟫-‖e‖^2/2-(P (pack q.fst z+pack d.fst e)-P (pack q.fst z)-
      ⟪G (pack q.fst z),pack d.fst e⟫)
  rw [hnorm,hpoint,hinner]
  simp only [WithLp.prod_inner_apply]
  change _-(⟪-(G (pack q.fst z)).fst,d.fst⟫+⟪z,d.snd⟫) =
    _-(P (pack q.fst z+pack d.fst e)-P (pack q.fst z)-
      (⟪(G (pack q.fst z)).fst,d.fst⟫+⟪(G (pack q.fst z)).snd,e⟫))
  rw [inner_neg_left,real_inner_comm d.snd z,← hz]
  simp only [inner_add_left]
  ring

variable (P : Joint X Y → ℝ) (hP : ∀ q,HasGradientAt P (G q) q)
include hP

theorem jointConjugate_remainder (q d : Joint X Y) :
    ‖jointConjugate hG hδ P (q+d)-jointConjugate hG hδ P q-⟪jointGradient hG hδ q,d⟫‖ ≤
      jointRemainderConstant (δ:ℝ)*‖d‖^2 := by
  let z := jointSolution hG hδ q.fst q.snd
  let e := jointSolution hG hδ (q+d).fst (q+d).snd-z
  let v := pack q.fst z
  let step := pack d.fst e
  let R := P (v+step)-P v-⟪G v,step⟫
  let C := (1+(δ:ℝ))/(1-(δ:ℝ))
  have hδ0 : 0≤(δ:ℝ) := δ.coe_nonneg
  have hC : 0≤C := div_nonneg (by positivity) (sub_nonneg.mpr (show (δ:ℝ)≤1 from hδ.le))
  have he : ‖e‖≤C*‖d‖ := by
    have hh := jointSolution_lipschitz_bound hG hδ (q+d) q
    simpa only [add_sub_cancel_left] using hh
  have hx : ‖d.fst‖≤‖d‖ := WithLp.norm_fst_le X d
  have hy : ‖d.snd‖≤‖d‖ := WithLp.norm_snd_le X d
  have ht : ‖R‖≤(δ:ℝ)/2*‖step‖^2 :=
    JointDerivative.gradient_taylor P G (δ:ℝ) hP
      (fun u v => by simpa only [dist_eq_norm] using hG.dist_le_mul u v) v step
  have hs : ‖step‖^2=‖d.fst‖^2+‖e‖^2 := norm_sq step
  have hbound : ‖⟪d.snd,e⟫-‖e‖^2/2-R‖ ≤
      ‖d.snd‖*‖e‖+‖e‖^2/2+(δ:ℝ)/2*(‖d.fst‖^2+‖e‖^2) := by
    have hn := (norm_sub_le (⟪d.snd,e⟫-‖e‖^2/2) R).trans
      (add_le_add_right (norm_sub_le ⟪d.snd,e⟫ (‖e‖^2/2)) ‖R‖)
    have hi : ‖⟪d.snd,e⟫‖≤‖d.snd‖*‖e‖ := norm_inner_le_norm d.snd e
    rw [Real.norm_of_nonneg (by positivity : 0≤‖e‖^2/2)] at hn
    rw [hs] at ht
    linarith
  rw [jointConjugate_remainder_identity hG hδ P q d]
  change ‖⟪d.snd,e⟫-‖e‖^2/2-R‖≤jointRemainderConstant (δ:ℝ)*‖d‖^2
  apply hbound.trans
  calc
    _ ≤ ‖d‖*(C*‖d‖)+(C*‖d‖)^2/2+(δ:ℝ)/2*(‖d‖^2+(C*‖d‖)^2) := by gcongr
    _ = _ := by dsimp [jointRemainderConstant,C]; ring

theorem jointConjugate_hasGradientAt (q : Joint X Y) :
    HasGradientAt (jointConjugate hG hδ P) (jointGradient hG hδ q) q := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply IsBigO.trans_isLittleO _ (isLittleO_norm_pow_id (E' := Joint X Y) one_lt_two)
  apply IsBigO.of_bound (jointRemainderConstant (δ:ℝ))
  apply Filter.Eventually.of_forall
  intro d
  change ‖jointConjugate hG hδ P (q+d)-jointConjugate hG hδ P q-⟪jointGradient hG hδ q,d⟫‖ ≤
    jointRemainderConstant (δ:ℝ)*‖‖d‖^2‖
  rw [Real.norm_of_nonneg (sq_nonneg ‖d‖)]
  exact jointConjugate_remainder hG hδ P hP q d

theorem jointConjugate_gradient (q : Joint X Y) :
    gradient (jointConjugate hG hδ P) q=jointGradient hG hδ q :=
  (jointConjugate_hasGradientAt hG hδ P hP q).gradient

theorem jointConjugate_partial_x (x : X) (y : Y) :
    HasGradientAt (fun u => jointConjugate hG hδ P (pack u y))
      (-(G (pack x (jointSolution hG hδ x y))).fst) x :=
  PrimitiveGeometry.partial_x (jointConjugate_hasGradientAt hG hδ P hP (pack x y))

theorem jointConjugate_partial_y (x : X) (y : Y) :
    HasGradientAt (fun v => jointConjugate hG hδ P (pack x v)) (jointSolution hG hδ x y) y :=
  PrimitiveGeometry.partial_y (jointConjugate_hasGradientAt hG hδ P hP (pack x y))

end Bilevel.PartialLegendre
