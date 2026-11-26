import Bilevel.EndpointTransportHybridOperators
import Bilevel.ChiExtensionReadoutGradient
import Bilevel.ChiExtensionReassociate

/-! The actual physical extension ignores the spectator outer coordinates.
Its pullback is a contraction and retains the complete normal derivative. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiExtension
variable {E U T V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def normalCoordinatesLinear {D : ℕ} : Joint (HybridOuter E U D) (Joint T V) →ₗ[ℝ] Joint (Joint E T) V where
  toFun z := pack (pack z.fst.fst.fst z.snd.fst) z.snd.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem normalCoordinatesLinear_norm_le {D : ℕ} (z : Joint (HybridOuter E U D) (Joint T V)) :
    ‖normalCoordinatesLinear z‖≤‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖pack (pack z.fst.fst.fst z.snd.fst) z.snd.snd‖^2≤‖z‖^2
  simp only [norm_sq]
  change (‖z.fst.fst.fst‖^2+‖z.snd.fst‖^2)+‖z.snd.snd‖^2≤
    ((‖z.fst.fst.fst‖^2+‖z.fst.fst.snd‖^2)+‖z.fst.snd‖^2)+(‖z.snd.fst‖^2+‖z.snd.snd‖^2)
  nlinarith only [sq_nonneg ‖z.fst.fst.snd‖,sq_nonneg ‖z.fst.snd‖]

def normalCoordinates {D : ℕ} : Joint (HybridOuter E U D) (Joint T V) →L[ℝ] Joint (Joint E T) V :=
  normalCoordinatesLinear.mkContinuous 1 (fun z => by simpa only [one_mul] using normalCoordinatesLinear_norm_le z)

theorem normalCoordinates_apply {D : ℕ} (z : Joint (HybridOuter E U D) (Joint T V)) :
    normalCoordinates z=pack (pack z.fst.fst.fst z.snd.fst) z.snd.snd := rfl

theorem normalCoordinates_norm_le {D : ℕ} :
    ‖(normalCoordinates (E:=E) (U:=U) (T:=T) (V:=V) (D:=D))‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using normalCoordinatesLinear_norm_le z

def physicalExtension {D : ℕ} (f : Joint (Joint E T) V → ℝ) :
    Joint (HybridOuter E U D) (Joint T V) → ℝ := f ∘ normalCoordinates

theorem physicalExtension_contDiff {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) : ContDiff ℝ 3 (physicalExtension (U:=U) (D:=D) f) := by
  change ContDiff ℝ 3 (f ∘ (normalCoordinates (E:=E) (U:=U) (T:=T) (V:=V) (D:=D)))
  exact hf.comp (normalCoordinates (E:=E) (U:=U) (T:=T) (V:=V) (D:=D)).contDiff

theorem physicalExtension_jet_bound {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (z : Joint (HybridOuter E U D) (Joint T V)) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (physicalExtension f) z‖≤‖iteratedFDeriv ℝ k f (normalCoordinates z)‖ := by
  exact ChiExtension.contraction_jet hf
    (normalCoordinates (E:=E) (U:=U) (T:=T) (V:=V) (D:=D))
    (normalCoordinates_norm_le (E:=E) (U:=U) (T:=T) (V:=V) (D:=D)) z k hk

theorem physicalExtension_zero_trace {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hzero : ∀ p,f (pack p (0:V))=0) (x : HybridOuter E U D) (t : T) :
    physicalExtension f (pack x (pack t (0:V)))=0 := hzero (pack x.fst.fst t)

variable [CompleteSpace E] [CompleteSpace U] [CompleteSpace T] [CompleteSpace V]

theorem physicalExtension_normal_gradient {D : ℕ} {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 f) (x : HybridOuter E U D) (t : T) (v : V) :
    (gradient (physicalExtension f) (pack x (pack t v))).snd.snd=
      gradient (fun q : V => f (pack (pack x.fst.fst t) q)) v := by
  have h := (((physicalExtension_contDiff (U:=U) (D:=D) hf).differentiable (by norm_num))
    (pack x (pack t v))).hasGradientAt
  exact (PrimitiveGeometry.partial_y (PrimitiveGeometry.partial_y h)).gradient.symm

theorem physicalExtension_readout_trace {D s : ℕ} {f : Full (Joint E T) s → ℝ}
    (hf : ContDiff ℝ 3 f) (base value : Joint E T → ℝ) (d : ℝ)
    (htrace : ∀ p,base p+d*normalReadout s (gradient (fun q : Normals s => f (pack p q)) 0)=value p)
    (x : HybridOuter E U D) (t : T) :
    base (pack x.fst.fst t)+⟪d • normalOnes s,
      (gradient (physicalExtension f) (pack x (pack t (0:Normals s)))).snd.snd⟫=
      value (pack x.fst.fst t) := by
  rw [physicalExtension_normal_gradient hf,real_inner_smul_left,
    ← InnerProductSpace.toDual_apply,normalOnes_toDual]
  exact htrace _

end Bilevel.EndpointTransportResponse
