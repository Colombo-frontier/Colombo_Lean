import Bilevel.EndpointTransportProductSupport
import Bilevel.ChiCarrierNormalSpace
import Bilevel.ChiHybridCorrection

/-! Actual heterogeneous product known spaces. Both physical endpoints retain
their separate layer spaces; public normals can be kept by taking the right
factor to be top. Gradient membership is derived from the actual partials. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiCarrier PartialLegendre
variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

def jointKnown (V : Submodule ℝ A) (W : Submodule ℝ B) : Submodule ℝ (Joint A B) where
  carrier := {z | z.fst∈V ∧ z.snd∈W}
  zero_mem' := ⟨V.zero_mem,W.zero_mem⟩
  add_mem' := fun hx hy => ⟨V.add_mem hx.1 hy.1,W.add_mem hx.2 hy.2⟩
  smul_mem' := fun c _ hx => ⟨V.smul_mem c hx.1,W.smul_mem c hx.2⟩

omit [CompleteSpace A] [CompleteSpace B] in
theorem mem_jointKnown (V : Submodule ℝ A) (W : Submodule ℝ B) (z : Joint A B) :
    z∈jointKnown V W ↔ z.fst∈V ∧ z.snd∈W := Iff.rfl

theorem gradient_jointKnown_iff (V : Submodule ℝ A) (W : Submodule ℝ B)
    {f : Joint A B → ℝ} (z : Joint A B) (hf : DifferentiableAt ℝ f z) :
    gradient f z∈jointKnown V W ↔
      gradient (fun a => f (pack a z.snd)) z.fst∈V ∧
      gradient (fun b => f (pack z.fst b)) z.snd∈W := by
  have hg := hf.hasGradientAt
  change HasGradientAt f (pack ((gradient f z).fst) ((gradient f z).snd))
    (pack z.fst z.snd) at hg
  rw [mem_jointKnown,(partial_x hg).gradient,(partial_y hg).gradient]

theorem fst_composition_gradient_mem (V : Submodule ℝ A) (W : Submodule ℝ B)
    {f : A → ℝ} (hf : ContDiff ℝ 3 f) (z : Joint A B) (hm : gradient f z.fst∈V) :
    gradient (f ∘ jointFstLinear) z∈jointKnown V W := by
  apply (gradient_jointKnown_iff V W z
    ((hf.comp (jointFstLinear (A:=A) (B:=B)).contDiff).differentiable (by norm_num) z)).mpr
  exact ⟨hm,gradient_const_mem W (f z.fst) z.snd⟩

theorem snd_composition_gradient_mem (V : Submodule ℝ A) (W : Submodule ℝ B)
    {f : B → ℝ} (hf : ContDiff ℝ 3 f) (z : Joint A B) (hm : gradient f z.snd∈W) :
    gradient (f ∘ jointSndLinear) z∈jointKnown V W := by
  apply (gradient_jointKnown_iff V W z
    ((hf.comp (jointSndLinear (A:=A) (B:=B)).contDiff).differentiable (by norm_num) z)).mpr
  exact ⟨gradient_const_mem V (f z.snd) z.fst,hm⟩

omit [CompleteSpace A] [CompleteSpace B] in
theorem jointKnown_isClosed (V : Submodule ℝ A) (W : Submodule ℝ B)
    (hV : IsClosed (V : Set A)) (hW : IsClosed (W : Set B)) :
    IsClosed (jointKnown V W : Set (Joint A B)) :=
  (hV.preimage (jointFstLinear (A:=A) (B:=B)).continuous).inter
    (hW.preimage (jointSndLinear (A:=A) (B:=B)).continuous)

end Bilevel.EndpointTransportResponse
