import GradientHessian.RawLeafLocality

/-! The complete memory tree determines every localized, old and inner
direction at every coefficient address. -/

noncomputable section
namespace GradientHessian.RawMemoryTree
open RawHierarchy RawSubtreeFactor RawLeafLocality

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

def select (h : ℕ) : (depth : ℕ) → Word depth → MemoryTree J E H (h+depth) → MemoryTree J E H h
  | 0,_,v => v
  | depth+1,w,v => select h depth (Fin.tail w) (v.1 (w 0))

theorem select_memory (h : ℕ) : ∀ depth (w : Word depth) (x : Raw d n r J E H (h+depth)),
    select h depth w (memory (h+depth) x)=memory h (selectedRaw h depth w x)
  | 0,_w,_x => rfl
  | depth+1,w,x => select_memory h depth (Fin.tail w) (x.1 (w 0))

theorem selected_memory_eq (h depth : ℕ) (w : Word depth)
    (x y : Raw d n r J E H (h+depth)) (he : memory (h+depth) x=memory (h+depth) y) :
    memory h (selectedRaw h depth w x)=memory h (selectedRaw h depth w y) := by
  rw [← select_memory,← select_memory,he]

theorem localized_eq (h depth : ℕ) (w : Word depth)
    (x y : Raw d n r J E H (h+1+depth)) (he : memory (h+1+depth) x=memory (h+1+depth) y) :
    (selectedRaw (h+1) depth w x).2=(selectedRaw (h+1) depth w y).2 :=
  congrArg (fun z : MemoryTree J E H (h+1) => z.2) (selected_memory_eq (h+1) depth w x y he)

theorem old_eq (depth : ℕ) (w : Word depth)
    (x y : Raw d n r J E H (0+depth)) (he : memory (0+depth) x=memory (0+depth) y) :
    (selectedRaw 0 depth w x).2.2.2=(selectedRaw 0 depth w y).2.2.2 :=
  congrArg Prod.snd (selected_memory_eq 0 depth w x y he)

theorem inner_eq (depth : ℕ) (w : Word depth)
    (x y : Raw d n r J E H (0+depth)) (he : memory (0+depth) x=memory (0+depth) y) :
    (selectedRaw 0 depth w x).2.2.1=(selectedRaw 0 depth w y).2.2.1 :=
  congrArg Prod.fst (selected_memory_eq 0 depth w x y he)

end GradientHessian.RawMemoryTree
