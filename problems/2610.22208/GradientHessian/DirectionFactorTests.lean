import GradientHessian.DirectionFactorActions

/-! Literal geometric tests at a canonical factor action read exactly the
isolated sphere coordinate. Address casts do not change the physical block. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical RawDirection RawHierarchy HigherHierarchy HierarchyAddresses FrontierState

def centerPath (h depth : ℕ) (w : Word depth) : Word (h+1+depth-(h+1)) :=
  fun a => w ⟨a.val,by have := a.isLt; omega⟩

def oldPath (depth : ℕ) (w : Word depth) : Word (0+depth) :=
  fun a => w ⟨a.val,by have := a.isLt; omega⟩

theorem centerFactorNode (h depth : ℕ) (w : Word depth) :
    localNode (⟨h,by omega⟩ : Fin (h+1+depth)) (centerPath h depth w)=
      CensoredDirection.addressedNode (h+1) depth w := by
  exact address_depth_cast (L := h+1+depth+1) (a := h+1+depth-(h+1)) (b := depth)
    (by omega) (by omega) (by omega) w

theorem oldFactorNode (depth : ℕ) (w : Word depth) :
    oldNode (oldPath depth w)=CensoredDirection.addressedNode 0 depth w :=
  address_depth_cast (by omega) _ _ w

theorem prepend_last : ∀ depth (w : Word depth) (i : Fin 8),
    leafWord (0+depth) (prependSlot 0 depth w i) ⟨depth,by omega⟩=i
  | 0,_,_ => rfl
  | depth+1,w,i => by
    simpa only [prependSlot,leafWord,Fin.cons_succ] using prepend_last depth (Fin.tail w) i

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem center_factor_test (K : ℝ) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x : Raw d n r J E H (h+1+depth)) :
    localCenter K (assemble P B fallback (h+1+depth) x) ⟨h,by omega⟩ (centerPath h depth w) i=
      radius (4096*J^2) K h • (RawCenterFactor.factor h depth w i x).1 := by
  have hc := centerSlot_lookup (h+1+depth) ⟨h,by omega⟩ (centerPath h depth w) i x
  have he : centerSlot (J := J) (⟨h,by omega⟩ : Fin (h+1+depth)) (centerPath h depth w) i=
      embed (h+1) depth w (.inr i) := Option.some.inj (centerFactorAction_slot h depth w i)
  rw [he] at hc
  have hd := eq_of_heq (hc.symm.trans (lookup_embed (h+1) depth w (.inr i) x))
  simp only [localCenter,dataAtHeight_assemble,RawCenterFactor.factor_direction]
  exact congrArg (fun v => radius (4096*J^2) K h • v) hd

theorem old_factor_direction (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x : Raw d n r J E H (0+depth)) :
    oldDirection (assemble P B fallback (0+depth) x) (oldPath depth w) i j=
      (RawMemoryHierarchyFactor.oldFactor depth w i j x).1 := by
  have hc := oldSlot_lookup (0+depth) (oldPath depth w) i j x
  have he : oldSlot (0+depth) (oldPath depth w) i j=embed 0 depth w (.inl (i,j)) :=
    Option.some.inj (oldFactorAction_slot depth w i j)
  rw [he] at hc
  have hd := eq_of_heq (hc.symm.trans (lookup_embed 0 depth w (.inl (i,j)) x))
  simpa only [oldDirection,oldData,dataAtHeight_assemble,RawMemoryHierarchyFactor.oldFactor_direction] using hd

theorem old_factor_test (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x : Raw d n r J E H (0+depth))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (0+depth)) :
    oldReadout (assemble P B fallback (0+depth) x) (oldPath depth w) i j Z=
      LatchChain.u (Inner.radius (FirstHeight.depth (4096*J^2+1)) j)
        (RawMemoryHierarchyFactor.oldFactor depth w i j x).1 (oldRegisterProjection (0+depth) i j Z) := by
  simp only [oldReadout,old_factor_direction P B fallback]

theorem inner_factor_direction (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x : Raw d n r J E H (0+depth)) :
    (leafCoefficients (assemble P B fallback (0+depth) x) (leafEquiv (0+depth) (prependSlot 0 depth w i))).v j k=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k x).1 := by
  have hc := innerSlot_lookup (0+depth) (prependSlot 0 depth w i) j k x
  rw [innerSlot_prepend] at hc
  have hd := eq_of_heq (hc.symm.trans (lookup_embed 0 depth w (.inr (i,j,k)) x))
  simpa only [leafCoefficients,Equiv.symm_apply_apply,RawLeafLocality.leaf_v_assemble,
    RawMemoryHierarchyFactor.innerFactor_direction] using hd

theorem inner_factor_test (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x : Raw d n r J E H (0+depth))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (0+depth)) :
    innerReadout (assemble P B fallback (0+depth) x) (leafEquiv (0+depth) (prependSlot 0 depth w i)) j k Z=
      LatchChain.u (Inner.radius Inner.absoluteDepth k) (RawMemoryHierarchyFactor.innerFactor depth w i j k x).1
        (innerRegisterProjection (0+depth) j k Z) := by
  simp only [innerReadout,inner_factor_direction P B fallback]

end GradientHessian.GeometricRepair
