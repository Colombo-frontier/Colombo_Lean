import Bilevel.EndpointTransportHybridGradient

/-! Isometric identification of one endpoint outer block with the
one-block source objective. No gradient factor is lost in this regrouping. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiCarrier
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def oneBlockCoordinates : Joint E F →ₗᵢ[ℝ] Joint E (Blocks 1 F) where
  toFun z := pack z.fst (insertion 1 0 z.snd)
  map_add' z w := by
    change pack (z.fst+w.fst) (insertion 1 0 (z.snd+w.snd))=_
    rw [map_add]
    rfl
  map_smul' a z := by
    change pack (a • z.fst) (insertion 1 0 (a • z.snd))=_
    rw [map_smul]
    rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq]
    change ‖z.fst‖^2+‖insertion 1 0 z.snd‖^2=‖z‖^2
    rw [(insertion 1 0).norm_map,norm_sq]

theorem oneBlockCoordinates_fst (z : Joint E F) : (oneBlockCoordinates z).fst=z.fst := rfl

theorem oneBlockCoordinates_zero_block (z : Joint E F) : (oneBlockCoordinates z).snd 0=z.snd := by
  change insertion 1 0 z.snd 0=z.snd
  simp only [insertion_apply,if_pos rfl,if_true]

theorem oneBlockCoordinates_surjective : Function.Surjective (oneBlockCoordinates (E:=E) (F:=F)) := by
  intro y
  refine ⟨pack y.fst (y.snd 0),?_⟩
  apply (WithLp.equiv 2 (E×Blocks 1 F)).injective
  change (y.fst,insertion 1 0 (y.snd 0))=(y.fst,y.snd)
  apply congrArg (fun v : Blocks 1 F => (y.fst,v))
  ext i
  have hi : i=(0:Fin 1) := Subsingleton.elim _ _
  subst i
  exact oneBlockCoordinates_zero_block (E:=E) (F:=F) (pack y.fst (y.snd 0))

def oneBlockCoordinatesEquiv : Joint E F ≃ₗᵢ[ℝ] Joint E (Blocks 1 F) :=
  LinearIsometryEquiv.ofSurjective oneBlockCoordinates oneBlockCoordinates_surjective

variable [CompleteSpace E] [CompleteSpace F]

theorem oneBlock_gradient_norm (f : Joint E (Blocks 1 F) → ℝ) (x : Joint E F)
    (hf : DifferentiableAt ℝ f (oneBlockCoordinates x)) :
    ‖gradient (fun z => f (oneBlockCoordinates z)) x‖=‖gradient f (oneBlockCoordinates x)‖ := by
  have h := gradient_norm_comp_isometryEquiv oneBlockCoordinatesEquiv f x hf
  simpa only [oneBlockCoordinatesEquiv,LinearIsometryEquiv.coe_ofSurjective] using h

end Bilevel.EndpointTransportResponse
