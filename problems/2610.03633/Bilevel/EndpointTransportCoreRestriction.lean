import Bilevel.EndpointTransportNormalSpace
import Bilevel.ChiVirtualInclusion
import Bilevel.ChiFineCouplingCore

/-! Recover the actual core derivative bounds from the full hybrid extension
using an isometric section. The four numeric fine parameters identify the
same source fine function across all completed dimensions and frames. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiPrefixEvaluation
variable {E U T V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def normalCoordinatesSection (D : ℕ) :
    Joint (Joint E T) V →ₗᵢ[ℝ] Joint (HybridOuter E U D) (Joint T V) where
  toLinearMap :=
    { toFun := fun z => pack (pack (pack z.fst.fst (0:U)) (0:Block D)) (pack z.fst.snd z.snd)
      map_add' := by
        intro x y
        change pack (pack (pack (x.fst.fst+y.fst.fst) (0:U)) (0:Block D))
            (pack (x.fst.snd+y.fst.snd) (x.snd+y.snd))=
          pack (pack (pack (x.fst.fst+y.fst.fst) (0+0:U)) (0+0:Block D))
            (pack (x.fst.snd+y.fst.snd) (x.snd+y.snd))
        rw [zero_add,zero_add]
      map_smul' := by
        intro c x
        change pack (pack (pack (c • x.fst.fst) (0:U)) (0:Block D))
            (pack (c • x.fst.snd) (c • x.snd))=
          pack (pack (pack (c • x.fst.fst) (c • (0:U))) (c • (0:Block D)))
            (pack (c • x.fst.snd) (c • x.snd))
        rw [smul_zero,smul_zero] }
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_sq]
    change (‖z.fst.fst‖^2+‖(0:U)‖^2+‖(0:Block D)‖^2)+
      (‖z.fst.snd‖^2+‖z.snd‖^2)=(‖z.fst.fst‖^2+‖z.fst.snd‖^2)+‖z.snd‖^2
    simp only [norm_zero,zero_pow (by norm_num : 2≠0),add_zero]
    ring

theorem normalCoordinates_section (D : ℕ) (z : Joint (Joint E T) V) :
    normalCoordinates (normalCoordinatesSection (U:=U) D z)=z := rfl

theorem physicalExtension_section (D : ℕ) (f : Joint (Joint E T) V → ℝ) :
    physicalExtension (U:=U) (D:=D) f ∘ normalCoordinatesSection D=f := rfl

theorem core_contDiff_of_physicalExtension (D : ℕ) {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 (physicalExtension (U:=U) (D:=D) f)) : ContDiff ℝ 3 f := by
  rw [← physicalExtension_section (U:=U) D f]
  exact hf.comp (normalCoordinatesSection (E:=E) (U:=U) (T:=T) (V:=V) D).toContinuousLinearMap.contDiff

theorem core_jet_bound_of_physicalExtension (D : ℕ) {f : Joint (Joint E T) V → ℝ}
    (hf : ContDiff ℝ 3 (physicalExtension (U:=U) (D:=D) f))
    (k : ℕ) (hk : k≤3) (C : ℝ)
    (hbound : ∀ z,‖iteratedFDeriv ℝ k (physicalExtension (U:=U) (D:=D) f) z‖≤C)
    (z : Joint (Joint E T) V) : ‖iteratedFDeriv ℝ k f z‖≤C := by
  have h := isometric_jet_restriction (normalCoordinatesSection (U:=U) D) _ hf z k hk
  rw [physicalExtension_section] at h
  exact h.trans (hbound _)

theorem fine_parameters_eq (P Q : ChiFine.Parameters)
    (hℓ : P.ℓ=Q.ℓ) (hβ : P.β=Q.β) (hθ : P.θ=Q.θ) (hc : P.c=Q.c) : P=Q := by
  cases P
  cases Q
  cases hℓ
  cases hβ
  cases hθ
  cases hc
  rfl

theorem source_fine_parameters_eq (P Q : ChiFine.Parameters) (c ℓ β : ℝ) (θ : ℝ → ℝ)
    (hPc : P.c=c) (hPℓ : P.ℓ=ℓ) (hPβ : P.β=β) (hPθ : P.θ=θ P.ℓ)
    (hQc : Q.c=c) (hQℓ : Q.ℓ=ℓ) (hQβ : Q.β=β) (hQθ : Q.θ=θ Q.ℓ) : P=Q := by
  apply fine_parameters_eq P Q (hPℓ.trans hQℓ.symm) (hPβ.trans hQβ.symm) _ (hPc.trans hQc.symm)
  rw [hPθ,hQθ,hPℓ,hQℓ]

end Bilevel.EndpointTransportResponse
