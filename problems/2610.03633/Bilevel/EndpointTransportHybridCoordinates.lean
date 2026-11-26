import Bilevel.EndpointTransportHybridObjective

/-! The finite source variables and the heterogeneous hybrid variables differ
only by an isometric regrouping of the final endpoint block. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiCarrier ChiOuter

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]

def appendBlocks (J : ℕ) : Joint (Blocks J B) B →ₗᵢ[ℝ] Blocks (J+1) B where
  toFun z := (WithLp.equiv 2 _).symm (Fin.snoc (fun i => z.fst i) z.snd)
  map_add' z w := by
    ext i
    change Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => (z+w).fst j) (z+w).snd i=
      Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => z.fst j) z.snd i+
        Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => w.fst j) w.snd i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [PiLp.add_apply,Fin.snoc_last]
      rfl
    · simp only [PiLp.add_apply,Fin.snoc_castSucc]
      rfl
  map_smul' a z := by
    ext i
    change Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => (a • z).fst j) (a • z).snd i=
      a • Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => z.fst j) z.snd i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [PiLp.smul_apply,Fin.snoc_last]
      rfl
    · simp only [PiLp.smul_apply,Fin.snoc_castSucc]
      rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,norm_sq,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_castSucc]
    change (∑ i : Fin J,‖Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => z.fst j) z.snd i.castSucc‖^2)+
      ‖Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => z.fst j) z.snd (Fin.last J)‖^2=_
    simp only [Fin.snoc_castSucc,Fin.snoc_last]

theorem appendBlocks_castSucc (J : ℕ) (z : Joint (Blocks J B) B) (i : Fin J) :
    appendBlocks J z i.castSucc=z.fst i := by
  change Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => z.fst j) z.snd i.castSucc=z.fst i
  exact Fin.snoc_castSucc _ _ _

theorem appendBlocks_last (J : ℕ) (z : Joint (Blocks J B) B) :
    appendBlocks J z (Fin.last J)=z.snd := by
  change Fin.snoc (α:=fun _ : Fin (J+1) => B) (fun j => z.fst j) z.snd (Fin.last J)=z.snd
  exact Fin.snoc_last _ _

theorem appendBlocks_surjective (J : ℕ) : Function.Surjective (appendBlocks (B:=B) J) := by
  intro y
  refine ⟨pack ((WithLp.equiv 2 _).symm (fun i : Fin J => y i.castSucc)) (y (Fin.last J)),?_⟩
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact appendBlocks_last J _
  · exact appendBlocks_castSucc J _ j

def appendBlocksEquiv (J : ℕ) : Joint (Blocks J B) B ≃ₗᵢ[ℝ] Blocks (J+1) B :=
  LinearIsometryEquiv.ofSurjective (appendBlocks J) (appendBlocks_surjective J)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceCoordinates (J D : ℕ) : HybridOuter E (Blocks J (Block D)) D →ₗᵢ[ℝ] Joint E (Blocks (J+1) (Block D)) where
  toFun z := pack z.fst.fst (appendBlocks J (pack z.fst.snd z.snd))
  map_add' z w := by
    change pack (z.fst.fst+w.fst.fst) (appendBlocks J (pack z.fst.snd z.snd+pack w.fst.snd w.snd))=_
    rw [map_add]
    rfl
  map_smul' a z := by
    change pack (a • z.fst.fst) (appendBlocks J (a • pack z.fst.snd z.snd))=_
    rw [map_smul]
    rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq]
    change ‖z.fst.fst‖^2+‖appendBlocks J (pack z.fst.snd z.snd)‖^2=‖z‖^2
    rw [(appendBlocks J).norm_map,norm_sq,norm_sq,norm_sq]
    change ‖z.fst.fst‖^2+(‖z.fst.snd‖^2+‖z.snd‖^2)=(‖z.fst.fst‖^2+‖z.fst.snd‖^2)+‖z.snd‖^2
    ring

theorem sourceCoordinates_surjective (J D : ℕ) : Function.Surjective (sourceCoordinates (E:=E) J D) := by
  intro y
  obtain ⟨z,hz⟩ := appendBlocks_surjective J y.snd
  refine ⟨pack (pack y.fst z.fst) z.snd,?_⟩
  change pack y.fst (appendBlocks J z)=y
  rw [hz]
  rfl

def sourceCoordinatesEquiv (J D : ℕ) : HybridOuter E (Blocks J (Block D)) D ≃ₗᵢ[ℝ] Joint E (Blocks (J+1) (Block D)) :=
  LinearIsometryEquiv.ofSurjective (sourceCoordinates J D) (sourceCoordinates_surjective J D)

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem sourceCoordinates_padded {D J : ℕ} (κ : ℝ) (x : HybridOuter E (Blocks J (Block D)) D) :
    padded (EndpointTransportNormalization.gain κ • (sourceCoordinates J D x).snd)=sourceOuterCoordinates κ x := by
  funext k
  by_cases hk : k<J
  · have he : (⟨k,by omega⟩ : Fin (J+1))=(⟨k,hk⟩ : Fin J).castSucc := rfl
    simp only [padded,block,dif_pos (show k<J+1 by omega),PiLp.proj_apply,PiLp.smul_apply]
    change EndpointTransportNormalization.gain κ • appendBlocks J (pack x.fst.snd x.snd) ⟨k,by omega⟩=_
    rw [he,appendBlocks_castSucc]
    simp only [sourceOuterCoordinates,Function.update_of_ne (by omega : k≠J),padded,block,dif_pos hk,
      PiLp.proj_apply,PiLp.smul_apply]
    rfl
  · by_cases he : k=J
    · subst k
      simp only [padded,block,dif_pos (show J<J+1 by omega),PiLp.proj_apply,PiLp.smul_apply]
      change EndpointTransportNormalization.gain κ • appendBlocks J (pack x.fst.snd x.snd) (Fin.last J)=_
      rw [appendBlocks_last]
      simp only [sourceOuterCoordinates,Function.update_self]
      rfl
    · simp only [padded,block,dif_neg (show ¬k<J+1 by omega),ContinuousLinearMap.zero_apply]
      simp only [sourceOuterCoordinates,Function.update_of_ne he,padded,block,dif_neg hk,ContinuousLinearMap.zero_apply]

theorem source_outer_eq_jointOuter {D J : ℕ} (κ : ℝ) (M : ChiRecursive.Node E) (ν : ℝ)
    (G : ChiRecursive.Geometry (Block D)) (ρ R : ℕ → ℝ)
    (x : HybridOuter E (Blocks J (Block D)) D) :
    ChiOuter.outerObjective M ν G ρ R J x.fst.fst (sourceOuterCoordinates κ x)=
      jointOuter (J+1) M ν G ρ R J (EndpointTransportNormalization.gain κ) (sourceCoordinates J D x) := by
  unfold jointOuter
  rw [sourceCoordinates_padded]
  rfl

end Bilevel.EndpointTransportResponse
