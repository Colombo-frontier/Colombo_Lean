import Bilevel.EndpointTransportNormalSpace
import Bilevel.ChiUpperRegularity

/-! Actual upper readout in the heterogeneous physical variables. Its
normal linear term has zero Hessian; only the base contributes curvature. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiExtension
variable {E U T V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def upperCore (base : Joint E T → ℝ) (b : V) (z : Joint (Joint E T) V) : ℝ :=
  base z.fst+⟪b,z.snd⟫

theorem upperCore_contDiff (base : Joint E T → ℝ) (hbase : ContDiff ℝ 3 base) (b : V) :
    ContDiff ℝ 3 (upperCore base b) := by
  let A : Joint (Joint E T) V →L[ℝ] Joint E T := jointFstLinear
  let R : Joint (Joint E T) V →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ V b).comp jointSndLinear
  change ContDiff ℝ 3 (fun z => (base ∘ A) z+R z)
  exact (hbase.comp A.contDiff).add R.contDiff

theorem upperCore_second_bound (base : Joint E T → ℝ) (hbase : ContDiff ℝ 3 base) (b : V)
    (z : Joint (Joint E T) V) :
    ‖iteratedFDeriv ℝ 2 (upperCore base b) z‖≤‖iteratedFDeriv ℝ 2 base z.fst‖ := by
  let A : Joint (Joint E T) V →L[ℝ] Joint E T := jointFstLinear
  let R : Joint (Joint E T) V →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ V b).comp jointSndLinear
  have hA : ‖A‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.fst‖≤1*‖q‖
    rw [one_mul]
    exact WithLp.norm_fst_le (Joint E T) q
  have hz : ‖iteratedFDeriv ℝ 2 R z‖=0 := by
    rw [← norm_iteratedFDeriv_fderiv (n:=1)]
    have he : fderiv ℝ R=fun _ => R := funext (fun x => R.fderiv)
    rw [he,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]
  have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
  have hR : ContDiff ℝ 3 R := R.contDiff
  change ‖iteratedFDeriv ℝ 2 (fun q => (base ∘ A) q+R q) z‖≤_
  rw [iteratedFDeriv_add_apply' (((hbase.comp A.contDiff).of_le h23).contDiffAt)
    ((hR.of_le h23).contDiffAt)]
  apply (norm_add_le _ _).trans
  rw [hz,add_zero]
  exact ChiExtension.contraction_jet hbase A hA z 2 (by norm_num)

def physicalUpper {D : ℕ} (base : Joint E T → ℝ) (b : V) :
    Joint (HybridOuter E U D) (Joint T V) → ℝ := physicalExtension (upperCore base b)

omit [CompleteSpace V] in
theorem physicalUpper_apply {D : ℕ} (base : Joint E T → ℝ) (b : V)
    (z : Joint (HybridOuter E U D) (Joint T V)) :
    physicalUpper base b z=base (pack z.fst.fst.fst z.snd.fst)+⟪b,z.snd.snd⟫ := rfl

theorem physicalUpper_contDiff {D : ℕ} (base : Joint E T → ℝ) (hbase : ContDiff ℝ 3 base) (b : V) :
    ContDiff ℝ 3 (physicalUpper (U:=U) (D:=D) base b) :=
  physicalExtension_contDiff (upperCore_contDiff base hbase b)

theorem physicalUpper_second_bound {D : ℕ} (base : Joint E T → ℝ) (hbase : ContDiff ℝ 3 base) (b : V)
    (z : Joint (HybridOuter E U D) (Joint T V)) :
    ‖iteratedFDeriv ℝ 2 (physicalUpper base b) z‖≤‖iteratedFDeriv ℝ 2 base (pack z.fst.fst.fst z.snd.fst)‖ :=
  (physicalExtension_jet_bound (upperCore_contDiff base hbase b) z 2 (by norm_num)).trans
    (upperCore_second_bound base hbase b (normalCoordinates z))

variable [CompleteSpace E] [CompleteSpace T]

theorem physicalUpper_lower_gradient_bound {D : ℕ} (base : Joint E T → ℝ)
    (hbase : ContDiff ℝ 3 base) (b : V) {C : ℝ}
    (hb : ∀ x t,‖gradient (fun v => base (pack x v)) t‖≤C)
    (x : HybridOuter E U D) (y : Joint T V) :
    ‖gradient (fun w => physicalUpper base b (pack x w)) y‖≤C+‖b‖ := by
  exact ChiUpper.fullUpper_lower_bound base (hbase.differentiable (by norm_num)) b hb (pack x.fst.fst (0:T)) y

end Bilevel.EndpointTransportResponse
