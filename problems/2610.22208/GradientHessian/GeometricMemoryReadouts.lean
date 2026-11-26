import GradientHessian.GeometricRepairRules
import GradientHessian.RawLeafLocality

/-! Literal geometric readouts depend only on the corresponding raw memory
tree. Numerical matrices and marks do not enter center or memory tests. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical HigherHierarchy HierarchyAddresses RawHierarchy RawLeafLocality

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

theorem memory_cast_eq {a b : ℕ} (hab : a=b) (x y : Raw d n r J E H a)
    (he : memory a x=memory a y) : memory b (castRaw hab x)=memory b (castRaw hab y) := by
  subst b
  exact he

theorem rawAt_memory_eq (h : ℕ) : ∀ (depth : ℕ) (w : Word depth)
    (x y : Raw d n r J E H (h+depth)), memory (h+depth) x=memory (h+depth) y →
      memory h (rawAt h depth w x)=memory h (rawAt h depth w y)
  | 0,w,x,y,he => he
  | depth+1,w,x,y,he => rawAt_memory_eq h depth (Fin.tail w) (x.1 (w 0)) (y.1 (w 0))
      (congrArg (fun v : MemoryTree J E H (h+depth+1) => v.1 (w 0)) he)

theorem rawAtHeight_memory_eq (t h : ℕ) (hh : h≤t) (w : Word (t-h))
    (x y : Raw d n r J E H t) (he : memory t x=memory t y) :
    memory h (rawAtHeight t h hh w x)=memory h (rawAtHeight t h hh w y) :=
  rawAt_memory_eq h (t-h) w _ _ (memory_cast_eq _ x y he)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem localCenter_eq_of_memory (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t)
    (he : memory t x=memory t y) (h : Fin t) (w : Word (t-(h.val+1))) (i : Fin 8) :
    localCenter K (assemble P B fallback t x) h w i=localCenter K (assemble P B fallback t y) h w i := by
  have hm := rawAtHeight_memory_eq t (h.val+1) (Nat.succ_le_of_lt h.isLt) w x y he
  have hd := congrArg (fun v : MemoryTree J E H (h.val+1) => v.2 i) hm
  simp only [localCenter,dataAtHeight_assemble]
  exact congrArg (fun v => radius (4096*J^2) K h.val • v) hd

theorem oldDirection_eq_of_memory (t : ℕ) (x y : Raw d n r J E H t)
    (he : memory t x=memory t y) (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) :
    oldDirection (assemble P B fallback t x) w i j=oldDirection (assemble P B fallback t y) w i j := by
  have hm := rawAtHeight_memory_eq t 0 (Nat.zero_le t) w x y he
  have hd := congrArg (fun v : MemoryTree J E H 0 => v.2 i j) hm
  simpa only [oldDirection,oldData,dataAtHeight_assemble] using hd

theorem leaf_v_eq_of_memory (t : ℕ) (x y : Raw d n r J E H t)
    (he : memory t x=memory t y) (leaf : FrontierState.Leaf (t+1)) :
    (leafCoefficients (assemble P B fallback t x) leaf).v=
      (leafCoefficients (assemble P B fallback t y) leaf).v := by
  simp only [leafCoefficients,leaf_v_assemble,he]

theorem oldReadout_eq_of_memory (t : ℕ) (x y : Raw d n r J E H t)
    (he : memory t x=memory t y) (w : Word t) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    oldReadout (assemble P B fallback t x) w i j Z=oldReadout (assemble P B fallback t y) w i j Z := by
  rw [oldReadout,oldReadout,oldDirection_eq_of_memory P B fallback t x y he]

theorem innerReadout_eq_of_memory (t : ℕ) (x y : Raw d n r J E H t)
    (he : memory t x=memory t y) (leaf : FrontierState.Leaf (t+1))
    (task : Fin (4096*J^2+1)) (j : Fin (Inner.absoluteDepth+2))
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :
    innerReadout (assemble P B fallback t x) leaf task j Z=
      innerReadout (assemble P B fallback t y) leaf task j Z := by
  rw [innerReadout,innerReadout,leaf_v_eq_of_memory P B fallback t x y he]

end GradientHessian.GeometricRepair
