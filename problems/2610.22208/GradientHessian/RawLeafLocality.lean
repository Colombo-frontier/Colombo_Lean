import GradientHessian.RawFactorCoefficients
import GradientHessian.RawSubtreeFactor

/-! Equality of the external factor preserves every other numerical leaf
and the entire hierarchy of memory directions. These are identities of the
raw coefficient maps, before any algorithm or probability argument. -/

noncomputable section
namespace GradientHessian.RawLeafLocality
open RawHierarchy HigherHierarchy RawLeafFactor

variable (J : ℕ) (E : Type) (H : ℕ → Type)

def MemoryTree : ℕ → Type
  | 0 => RawFirstFactor.InnerDirections J E × RawFirstFactor.OuterDirections J E
  | t+1 => (Fin 8 → MemoryTree t) × (Fin 8 → H t)

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}

def memory : (t : ℕ) → Raw d n r J E H t → MemoryTree J E H t
  | 0,x => x.2.2
  | t+1,x => (fun i => memory t (x.1 i),x.2)

def leafMemory : (t : ℕ) → MemoryTree J E H t → LeafSlot t →
    Fin (4096*J^2+1) → Fin (Inner.absoluteDepth+2) → E
  | 0,v,i => v.1 i
  | t+1,v,i => leafMemory t (v.1 i.1) i.2

variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

theorem rest_eq_child (t : ℕ) (i : LeafSlot (t+1)) (x y : Raw d n r J E H (t+1))
    (he : (factor (t+1) i x).2=(factor (t+1) i y).2) :
    (factor t i.2 (x.1 i.1)).2=(factor t i.2 (y.1 i.1)).2 :=
  congrArg Prod.fst he

theorem rest_eq_sibling (t : ℕ) (i : LeafSlot (t+1)) (x y : Raw d n r J E H (t+1))
    (he : (factor (t+1) i x).2=(factor (t+1) i y).2) (j : Fin 8) (hj : j≠i.1) :
    x.1 j=y.1 j := by
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
  exact congrArg (fun z : Rest d n r J E H (t+1) => z.2.1 k) he

theorem rest_eq_memory : ∀ t (i : LeafSlot t) (x y : Raw d n r J E H t),
    (factor t i x).2=(factor t i y).2 → memory t x=memory t y
  | 0,_i,_x,_y,he => congrArg (fun z : Rest d n r J E H 0 => z.2.2) he
  | t+1,i,x,y,he => by
    apply Prod.ext
    · funext j
      by_cases hj : j=i.1
      · subst j
        exact rest_eq_memory t i.2 _ _ (rest_eq_child t i x y he)
      · change memory t (x.1 j)=memory t (y.1 j)
        rw [rest_eq_sibling t i x y he j hj]
    · exact congrArg (fun z : Rest d n r J E H (t+1) => z.2.2) he

theorem rest_eq_other_numerical : ∀ t (i : LeafSlot t) (x y : Raw d n r J E H t),
    (factor t i x).2=(factor t i y).2 → ∀ q : LeafSlot t, q≠i →
      leafNumerical t x q=leafNumerical t y q
  | 0,i,x,y,he,q,hq => by
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hq
    exact Prod.ext
      (congrArg (fun z : Rest d n r J E H 0 => z.1 k) he)
      (congrArg (fun z : Rest d n r J E H 0 => z.2.1 k) he)
  | t+1,i,x,y,he,q,hq => by
    by_cases hj : q.1=i.1
    · have htail : q.2≠i.2 := fun h => hq (Prod.ext hj h)
      change leafNumerical t (x.1 q.1) q.2=leafNumerical t (y.1 q.1) q.2
      rw [hj]
      exact rest_eq_other_numerical t i.2 _ _ (rest_eq_child t i x y he) q.2 htail
    · change leafNumerical t (x.1 q.1) q.2=leafNumerical t (y.1 q.1) q.2
      rw [rest_eq_sibling t i x y he q.1 hj]

theorem replace_memory (t : ℕ) (i : LeafSlot t) (z : RawFirstFactor.Target d n r J)
    (x : Raw d n r J E H t) : memory t (replace t i z x)=memory t x :=
  rest_eq_memory t i _ _ (by simpa only using congrArg Prod.snd (factor_replace t i z x))

theorem replace_other_numerical (t : ℕ) (i : LeafSlot t) (z : RawFirstFactor.Target d n r J)
    (x : Raw d n r J E H t) (q : LeafSlot t) (hq : q≠i) :
    leafNumerical t (replace t i z x) q=leafNumerical t x q :=
  rest_eq_other_numerical t i _ _ (by simpa only using congrArg Prod.snd (factor_replace t i z x)) q hq

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [MeasurableSpace E] [∀ t, MeasurableSpace (H t)] in
theorem leaf_v_assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (x : Raw d n r J E H t) (q : LeafSlot t),
    (leafData t (assemble P B fallback t x) q).v=leafMemory t (memory t x) q
  | 0,_x,_q => rfl
  | t+1,x,q => leaf_v_assemble P B fallback t (x.1 q.1) q.2

theorem rest_eq_leaf_v (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (x y : Raw d n r J E H t)
    (he : (factor t i x).2=(factor t i y).2) (q : LeafSlot t) :
    (leafData t (assemble P B fallback t x) q).v=(leafData t (assemble P B fallback t y) q).v := by
  rw [leaf_v_assemble,leaf_v_assemble,rest_eq_memory t i x y he]

theorem rest_eq_other_leaf (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (x y : Raw d n r J E H t)
    (he : (factor t i x).2=(factor t i y).2) (q : LeafSlot t) (hq : q≠i) :
    leafData t (assemble P B fallback t x) q=leafData t (assemble P B fallback t y) q := by
  have hn := rest_eq_other_numerical t i x y he q hq
  have hA : (leafData t (assemble P B fallback t x) q).A=
      (leafData t (assemble P B fallback t y) q).A := by rw [leaf_A_assemble,leaf_A_assemble,hn]
  have hb : (leafData t (assemble P B fallback t x) q).b=
      (leafData t (assemble P B fallback t y) q).b := by funext j; rw [leaf_b_assemble,leaf_b_assemble,hn]
  have ha : (leafData t (assemble P B fallback t x) q).a=
      (leafData t (assemble P B fallback t y) q).a := by funext j; rw [leaf_a_assemble,leaf_a_assemble,hn]
  have hv := rest_eq_leaf_v P B fallback t i x y he q
  cases hx : leafData t (assemble P B fallback t x) q
  cases hy : leafData t (assemble P B fallback t y) q
  simp only [hx,hy] at hA hb ha hv
  simp only [LeafCoefficients.mk.injEq]
  exact ⟨hA,hb,ha,hv⟩

end GradientHessian.RawLeafLocality
