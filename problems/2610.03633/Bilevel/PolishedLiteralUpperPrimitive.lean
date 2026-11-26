import Bilevel.PolishedLiteralUpperCertificate
import Bilevel.PartialLegendreJoint

/-! The actual source upper primitive on outer (x,v) and lower (u,s).
The unused v is retained. Its full gradient uses the joint Euclidean norm. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

abbrev PrimitiveSpace (X U : Type*) := Joint (Joint X U) (Joint U ℝ)

def upperProjection : PrimitiveSpace X U →L[ℝ] Joint X U :=
  (packLinear (X:=X) (Y:=U)).comp
    (((fstMap (X:=X) (U:=U)).comp (fstMap (X:=Joint X U) (U:=Joint U ℝ))).prod
      ((fstMap (X:=U) (U:=ℝ)).comp (sndMap (X:=Joint X U) (U:=Joint U ℝ))))

omit [CompleteSpace X] [CompleteSpace U] in
theorem upperProjection_apply (z : PrimitiveSpace X U) :
    upperProjection z=pack z.fst.fst z.snd.fst := rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem upperProjection_norm_le : ‖upperProjection (X:=X) (U:=U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul,upperProjection_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq,norm_sq,norm_sq,norm_sq]
  change ‖z.fst.fst‖^2+‖z.snd.fst‖^2≤
    ‖z.fst.fst‖^2+‖z.fst.snd‖^2+(‖z.snd.fst‖^2+‖z.snd.snd‖^2)
  nlinarith [sq_nonneg ‖z.fst.snd‖,sq_nonneg ‖z.snd.snd‖]

def upperNormalLinear (L : ℝ) : PrimitiveSpace X U →L[ℝ] ℝ :=
  L • (sndMap (X:=U) (U:=ℝ)).comp (sndMap (X:=Joint X U) (U:=Joint U ℝ))

theorem linear_second_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E →L[ℝ] ℝ) (z : E) : ‖iteratedFDeriv ℝ 2 p z‖=0 := by
  rw [← norm_iteratedFDeriv_fderiv (n:=1),← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
  have he : fderiv ℝ (p : E → ℝ)=fun _ => p := funext (fun y => p.fderiv)
  rw [he,fderiv_const]
  simp only [Pi.zero_apply,norm_zero]

theorem contraction_add_linear_second {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 3 f) (p : E →L[ℝ] F) (hp : ‖p‖≤1)
    (l : E →L[ℝ] ℝ) (C : ℝ) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤C) (z : E) :
    ‖iteratedFDeriv ℝ 2 (fun w => f (p w)+l w) z‖≤C := by
  have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
  change ‖iteratedFDeriv ℝ 2 (fun w => (f ∘ p) w+l w) z‖≤C
  rw [iteratedFDeriv_add_apply' (((hf.comp p.contDiff).of_le h23).contDiffAt)
    ((l.contDiff.of_le h23).contDiffAt)]
  have hc := (ChiOuter.contraction_jet_bound p hp hf z 2 (by norm_num)).trans (hb _)
  have hl : ‖iteratedFDeriv ℝ 2 l z‖≤0 := (linear_second_zero l z).le
  exact (norm_add_le _ _).trans ((add_le_add hc hl).trans_eq (add_zero _))

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

def upperJoint (z : PrimitiveSpace X U) : ℝ :=
  PolishedLiteralJointMean.upper P.data z.fst.fst z.fst.snd z.snd

theorem upperJoint_eq : P.upperJoint=fun z =>
    (P.upperBase ∘ upperProjection) z+upperNormalLinear P.L z := rfl

theorem upperJoint_contDiff : ContDiff ℝ 3 P.upperJoint :=
  (P.upperBase_contDiff.comp (upperProjection (X:=X) (U:=U)).contDiff).add
    (upperNormalLinear (X:=X) (U:=U) P.L).contDiff

theorem upperJoint_second_bound (C : ℝ) (hb : ∀ z,‖iteratedFDeriv ℝ 2 P.upperBase z‖≤C) :
    ∀ z,‖iteratedFDeriv ℝ 2 P.upperJoint z‖≤C := by
  intro z
  exact contraction_add_linear_second P.upperBase P.upperBase_contDiff
    (upperProjection (X:=X) (U:=U)) upperProjection_norm_le
    (upperNormalLinear (X:=X) (U:=U) P.L) C hb z

theorem upper_lower_hasGradientAt (x : X) (v : U) (y : Joint U ℝ) :
    HasGradientAt (PolishedLiteralJointMean.upper P.data x v)
      (pack (gradient (fun u => P.upperBase (pack x u)) y.fst) P.L) y := by
  have hdiff : Differentiable ℝ (fun u => P.upperBase (pack x u)) :=
    ((P.upperBase_contDiff.comp ((packLinear (X:=X) (Y:=U)).contDiff.comp
      (contDiff_const.prodMk contDiff_id))).differentiable (by norm_num))
  have hu := (hdiff y.fst).hasGradientAt.hasFDerivAt.comp y
    (fstMap (X:=U) (U:=ℝ)).hasFDerivAt
  have hs := ((sndMap (X:=U) (U:=ℝ)).hasFDerivAt (x:=y)).const_mul P.L
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hu.add hs using 1
  ext w
  simp [InnerProductSpace.toDual_apply,WithLp.prod_inner_apply,ContinuousLinearMap.comp_apply,
    fstMap,sndMap,pack,mul_comm]

theorem upper_lower_gradient_bound (C : ℝ) (hL : 0≤P.L)
    (hb : ∀ x u,‖gradient (fun v => P.upperBase (pack x v)) u‖≤C)
    (x : X) (v : U) (y : Joint U ℝ) :
    ‖gradient (PolishedLiteralJointMean.upper P.data x v) y‖≤C+P.L := by
  rw [(P.upper_lower_hasGradientAt x v y).gradient]
  have ht := PartialLegendre.norm_pack_le_add
    (gradient (fun u => P.upperBase (pack x u)) y.fst) P.L
  rw [Real.norm_eq_abs,abs_of_nonneg hL] at ht
  exact ht.trans (add_le_add_right (hb x y.fst) P.L)

end Parameters

theorem source_upper_primitive_budgets :
    ∀ (Km A Cu ζ : ℝ),1≤Km → 0≤A → 1≤Cu → 0<ζ → ζ≤1 →
    ∃ C : ℝ,0<C ∧
    ∀ (κ : ℝ),4≤κ → 2/ζ^3≤κ →
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)),P.SourceCalibration Km A Cu ζ κ →
      0<P.L → 0<P.macroNode.width → P.macroNode.width≤1 →
      (∀ x v y,‖gradient (PolishedLiteralJointMean.upper P.data x v) y‖≤C*P.L) ∧
      (∀ z,‖iteratedFDeriv ℝ 2 P.upperJoint z‖≤C*P.L) ∧
      (∀ z z',‖gradient P.upperJoint z-gradient P.upperJoint z'‖≤C*P.L*‖z-z'‖) := by
  intro Km A Cu ζ hKm hA hCu hζ hζ1
  obtain ⟨C,hC,hb⟩ := source_base_budgets Km A Cu ζ hKm hA hCu hζ hζ1
  refine ⟨C+1,by linarith,?_⟩
  intro κ hκ hκscale X U _ _ _ _ _ _ P hcal hL hw hw1
  obtain ⟨_,hsecond,hlower⟩ := hb κ hκ hκscale X U P hcal hL hw
  have hC1 : C*P.L≤(C+1)*P.L := by nlinarith
  have h2 := P.upperJoint_second_bound (C*P.L) hsecond
  have h2' (z : PrimitiveSpace X U) : ‖iteratedFDeriv ℝ 2 P.upperJoint z‖≤(C+1)*P.L :=
    (h2 z).trans hC1
  refine ⟨?_,h2',?_⟩
  · intro x v y
    have hg (x : X) (u : U) : ‖gradient (fun v => P.upperBase (pack x v)) u‖≤C*P.L :=
      (hlower x u).trans (by nlinarith only [mul_le_mul_of_nonneg_left hw1 (mul_nonneg hC hL.le)])
    exact (P.upper_lower_gradient_bound (C*P.L) hL.le hg x v y).trans_eq (by ring)
  · exact GradientJetBounds.gradient_lipschitz P.upperJoint_contDiff ((C+1)*P.L) h2'

end Bilevel.PolishedLiteral
