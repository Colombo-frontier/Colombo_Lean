import Bilevel.ChiExtensionReadoutGradient
import Bilevel.ChiPrimitiveAssembly

/-! Regularity of the actual upper readout, retaining the spectator outer
variables and the Euclidean normalization of the normal coordinates. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiUpper
open PrimitiveGeometry PartialLegendre ChiPrimitive
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def baseProjection : FullNormalVariables X U V →L[ℝ] Joint X U :=
  packLinear.comp ((jointFstLinear.comp jointFstLinear).prod (jointFstLinear.comp jointSndLinear))

omit [CompleteSpace X] [CompleteSpace U] [CompleteSpace V] in
theorem baseProjection_norm : ‖(baseProjection : FullNormalVariables X U V →L[ℝ] Joint X U)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖pack q.fst.fst q.snd.fst‖ ≤ 1*‖q‖
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq]
  change ‖q.fst.fst‖^2+‖q.snd.fst‖^2 ≤ (‖q.fst.fst‖^2+‖q.fst.snd‖^2)+(‖q.snd.fst‖^2+‖q.snd.snd‖^2)
  nlinarith only [sq_nonneg ‖q.fst.snd‖,sq_nonneg ‖q.snd.snd‖]

def fullUpper (f : Joint X U → ℝ) (b : V) (q : FullNormalVariables X U V) : ℝ :=
  f (pack q.fst.fst q.snd.fst)+⟪b,q.snd.snd⟫

def fullUpperGradient (f : Joint X U → ℝ) (b : V) (q : FullNormalVariables X U V) :
    FullNormalVariables X U V :=
  let g := gradient f (pack q.fst.fst q.snd.fst)
  pack (pack g.fst 0) (pack g.snd b)

theorem fullUpper_hasGradientAt (f : Joint X U → ℝ) (hf : Differentiable ℝ f)
    (b : V) (q : FullNormalVariables X U V) :
    HasGradientAt (fullUpper f b) (fullUpperGradient f b q) q := by
  have ha := (hf (baseProjection q)).hasFDerivAt.comp q
    ((baseProjection : FullNormalVariables X U V →L[ℝ] Joint X U).hasFDerivAt (x:=q))
  let R : FullNormalVariables X U V →L[ℝ] V := jointSndLinear.comp jointSndLinear
  have hb := ((InnerProductSpace.toDual ℝ V b).comp R).hasFDerivAt (x:=q)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert ha.add hb using 1
  ext v
  rw [(hf (baseProjection q)).hasGradientAt.hasFDerivAt.fderiv]
  simp [fullUpperGradient,baseProjection,R,packLinear,pack, jointFstLinear,jointSndLinear,
    ContinuousLinearMap.comp_apply,WithLp.prod_inner_apply,add_assoc]

theorem fullUpper_differentiable (f : Joint X U → ℝ) (hf : Differentiable ℝ f) (b : V) :
    Differentiable ℝ (fullUpper f b) := fun q => (fullUpper_hasGradientAt f hf b q).differentiableAt

theorem fullUpper_lower_gradient (f : Joint X U → ℝ) (hf : Differentiable ℝ f)
    (b : V) (x : Joint X U) (y : Joint U V) :
    gradient (fun v => fullUpper f b (pack x v)) y=
      pack (gradient (fun u => f (pack x.fst u)) y.fst) b := by
  rw [(partial_y (fullUpper_hasGradientAt f hf b (pack x y))).gradient]
  rw [(partial_y (hf (pack x.fst y.fst)).hasGradientAt).gradient]
  rfl

theorem fullUpper_lower_bound (f : Joint X U → ℝ) (hf : Differentiable ℝ f)
    (b : V) {C : ℝ} (hb : ∀ x u,‖gradient (fun v => f (pack x v)) u‖ ≤ C)
    (x : Joint X U) (y : Joint U V) :
    ‖gradient (fun v => fullUpper f b (pack x v)) y‖ ≤ C+‖b‖ := by
  rw [fullUpper_lower_gradient f hf b]
  exact (norm_pack_le_add _ _).trans (add_le_add_right (hb _ _) _)

theorem fullUpper_gradient_lipschitz (f : Joint X U → ℝ) (hf : Differentiable ℝ f)
    (b : V) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z w,‖gradient f z-gradient f w‖ ≤ L*‖z-w‖)
    (q r : FullNormalVariables X U V) :
    ‖gradient (fullUpper f b) q-gradient (fullUpper f b) r‖ ≤ L*‖q-r‖ := by
  rw [(fullUpper_hasGradientAt f hf b q).gradient,(fullUpper_hasGradientAt f hf b r).gradient]
  have hid : ‖fullUpperGradient f b q-fullUpperGradient f b r‖=
      ‖gradient f (baseProjection q)-gradient f (baseProjection r)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_sq]
    change (‖(gradient f (baseProjection q)).fst-(gradient f (baseProjection r)).fst‖^2+‖(0:U)-0‖^2)+
      (‖(gradient f (baseProjection q)).snd-(gradient f (baseProjection r)).snd‖^2+‖b-b‖^2)=_
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
    rfl
  rw [hid]
  apply (hlip _ _).trans
  apply mul_le_mul_of_nonneg_left _ hL
  rw [← map_sub]
  exact (baseProjection.le_opNorm (q-r)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right baseProjection_norm (norm_nonneg (q-r)))

end Bilevel.ChiUpper
