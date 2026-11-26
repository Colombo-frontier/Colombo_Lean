import GradientHessian.CensoredJointOracle
import GradientHessian.RawLeafLocality
import GradientHessian.RawHierarchyMeasurability

/-! A literal coefficient table for a numerical oracle simulation. Replacing
one leaf's matrix and numerical marks preserves every memory direction and
every other leaf. The replacement table can be assembled from the external
raw factor and a finite cache of supplied coefficients. -/

noncomputable section
namespace GradientHessian.NumericalCoefficientPatch
open Classical HigherHierarchy HierarchyParameters CensoredHierarchy CensoredOracle RawHierarchy

variable {Y E : Type} {H : ℕ → Type} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

abbrev numerical (_t : ℕ) := (Y →L[ℝ] Y) × (Fin (m+1) → Y) × (Fin (m+1) → Y)

def patch : (t : ℕ) → LeafSlot t → numerical (Y := Y) (m := m) t →
    Parameters Y E H m t → Parameters Y E H m t
  | 0,i,z,θ => (fun q => if q=i then (z.1,z.2.1,z.2.2,(θ.1 q).2.2.2) else θ.1 q,θ.2)
  | t+1,i,z,θ => (fun q => if q=i.1 then patch t i.2 z (θ.1 q) else θ.1 q,θ.2)

def atLeaf : (t : ℕ) → LeafSlot t → Parameters Y E H m t → Leaf.MatrixMarks Y E (m+1)
  | 0,i,θ => θ.1 i
  | t+1,i,θ => atLeaf t i.2 (θ.1 i.1)

theorem patch_at : ∀ t (i : LeafSlot t) (z : numerical (Y := Y) (m := m) t)
    (θ : Parameters Y E H m t),
    atLeaf t i (patch t i z θ)=(z.1,z.2.1,z.2.2,(atLeaf t i θ).2.2.2)
  | 0,_,_,_ => by simp [patch,atLeaf]
  | t+1,i,z,θ => by simpa only [patch,atLeaf,if_true] using patch_at t i.2 z (θ.1 i.1)

theorem patch_other : ∀ t (i q : LeafSlot t) (z : numerical (Y := Y) (m := m) t)
    (θ : Parameters Y E H m t), q≠i → atLeaf t q (patch t i z θ)=atLeaf t q θ
  | 0,i,q,z,θ,hq => by simp only [atLeaf,patch,if_neg hq]
  | t+1,i,q,z,θ,hq => by
    by_cases hh : q.1=i.1
    · simpa only [atLeaf,patch,if_pos hh] using patch_other t i.2 q.2 z (θ.1 q.1)
        (fun he => hq (Prod.ext hh he))
    · simp only [atLeaf,patch,if_neg hh]

theorem patch_continuous : ∀ t (i : LeafSlot t),
    Continuous (fun p : numerical (Y := Y) (m := m) t × Parameters Y E H m t => patch t i p.1 p.2)
  | 0,i => by
    apply Continuous.prodMk
    · apply continuous_pi
      intro q
      change Continuous (fun p : numerical (Y := Y) (m := m) 0 × Parameters Y E H m 0 =>
        if q=i then (p.1.1,p.1.2.1,p.1.2.2,(p.2.1 q).2.2.2) else p.2.1 q)
      split_ifs <;> fun_prop
    · exact continuous_snd.snd
  | t+1,i => by
    apply Continuous.prodMk
    · apply continuous_pi
      intro q
      change Continuous (fun p : numerical (Y := Y) (m := m) (t+1) × Parameters Y E H m (t+1) =>
        if q=i.1 then patch t i.2 p.1 (p.2.1 q) else p.2.1 q)
      split_ifs
      · exact (patch_continuous t i.2).comp (continuous_fst.prodMk (by fun_prop))
      · fun_prop
    · exact continuous_snd.snd

def leafMask : (t : ℕ) → Plan m t → CensoredLeaf.Mask (m+1)
  | 0,p => p.2.2
  | t+1,p => leafMask t p.2.2

/-- Supplying a cached coefficient table on precisely the entries used by
the current mask preserves the complete known part of the recursive jet. -/
theorem selected_sameKnown : ∀ t (p : Plan m t) (θ : Parameters Y E H m t)
    (z : numerical (Y := Y) (m := m) t),
    (∀ j,j≤(leafMask t p).current → z.2.1 j=(atLeaf t (selectedLeaf m t p) θ).2.1 j) →
    (∀ j,j<(leafMask t p).current ∨ (j=(leafMask t p).current ∧ (leafMask t p).readout=true) →
      z.2.2 j=(atLeaf t (selectedLeaf m t p) θ).2.2.1 j) →
    SameKnown t p θ (patch t (selectedLeaf m t p) z θ)
  | 0,p,θ,z,hb,ha => by
    refine ⟨?_,?_,?_⟩
    · intro q hq
      simp only [patch,selectedLeaf,if_neg (ne_of_lt hq)]
    · intro q _; rfl
    · simp only [patch,selectedLeaf,if_true]
      apply CensoredLeaf.view_congr
      · intro j hj; exact (hb j hj).symm
      · intro j hj; exact (ha j hj).symm
      · intro _ _; rfl
  | t+1,p,θ,z,hb,ha => by
    refine ⟨?_,?_,?_⟩
    · intro q hq
      simp only [patch,selectedLeaf,if_neg (ne_of_lt hq)]
    · intro q _; rfl
    · simpa only [patch,selectedLeaf,if_true] using selected_sameKnown t p.2.2 (θ.1 p.1) z hb ha

theorem ordinary_selected_patch {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ : Parameters Y E H m t) (z : numerical (Y := Y) (m := m) t)
    (hb : ∀ j,j≤(leafMask t p).current → z.2.1 j=(atLeaf t (selectedLeaf m t p) θ).2.1 j)
    (ha : ∀ j,j<(leafMask t p).current ∨ (j=(leafMask t p).current ∧ (leafMask t p).readout=true) →
      z.2.2 j=(atLeaf t (selectedLeaf m t p) θ).2.2.1 j)
    (Z : Space Y E H m t) (Ay : Y) :
    ordinaryDecoder K t p ((θ,Z),Ay)=ordinaryDecoder K t p ((patch t (selectedLeaf m t p) z θ,Z),Ay) :=
  ordinaryDecoder_erasure hK t p θ _ (selected_sameKnown t p θ z hb ha) Z Ay

def FutureLeaf : (t : ℕ) → Plan m t → LeafSlot t → Prop
  | 0,p,i => p.1 < i
  | t+1,p,i => p.1 < i.1 ∨ p.1=i.1 ∧ FutureLeaf t p.2.2 i.2

theorem sameKnown_self : ∀ t (p : Plan m t) (θ : Parameters Y E H m t), SameKnown t p θ θ
  | 0,_,_ => ⟨fun _ _ => rfl,fun _ _ => rfl,rfl⟩
  | t+1,p,θ => ⟨fun _ _ => rfl,fun _ _ => rfl,sameKnown_self t p.2.2 (θ.1 p.1)⟩

theorem future_sameKnown : ∀ t (p : Plan m t) (i : LeafSlot t)
    (θ : Parameters Y E H m t) (z : numerical (Y := Y) (m := m) t),
    FutureLeaf t p i → SameKnown t p θ (patch t i z θ)
  | 0,p,i,θ,z,hf => by
    change p.1 < i at hf
    refine ⟨?_,?_,?_⟩
    · intro q hq
      simp only [patch,if_neg (ne_of_lt (hq.trans hf))]
    · intro q _; rfl
    · simp only [patch,if_neg (ne_of_lt hf)]
  | t+1,p,i,θ,z,hf => by
    refine ⟨?_,?_,?_⟩
    · intro q hq
      have hqi : q≠i.1 := by rcases hf with hh | ⟨hh,_⟩ <;> omega
      simp only [patch,if_neg hqi]
    · intro q _; rfl
    · rcases hf with hh | ⟨hh,ht⟩
      · simpa only [patch,if_neg (ne_of_lt hh)] using sameKnown_self t p.2.2 (θ.1 p.1)
      · simpa only [patch,if_pos hh] using future_sameKnown t p.2.2 i.2 (θ.1 p.1) z ht

theorem future_ne_selected : ∀ t (p : Plan m t) (i : LeafSlot t),
    FutureLeaf t p i → selectedLeaf m t p≠i
  | 0,p,i,h => by
    change p.1 < i at h
    change p.1≠i
    exact ne_of_lt h
  | t+1,p,i,h => by
    intro he
    have hh : p.1=i.1 := congrArg Prod.fst he
    rcases h with h | ⟨_,h⟩
    · exact (ne_of_lt h) hh
    · exact future_ne_selected t p.2.2 i.2 h (congrArg Prod.snd he)

theorem selectedMatrix_atLeaf : ∀ t (p : Plan m t) (θ : Parameters Y E H m t),
    selectedMatrix t p (decode t θ)=(atLeaf t (selectedLeaf m t p) θ).1
  | 0,_,_ => rfl
  | t+1,p,θ => selectedMatrix_atLeaf t p.2.2 (θ.1 p.1)

theorem future_selectedMatrix (t : ℕ) (p : Plan m t) (i : LeafSlot t)
    (θ : Parameters Y E H m t) (z : numerical (Y := Y) (m := m) t) (hf : FutureLeaf t p i) :
    selectedMatrix t p (decode t (patch t i z θ))=selectedMatrix t p (decode t θ) := by
  rw [selectedMatrix_atLeaf,selectedMatrix_atLeaf,
    patch_other t i (selectedLeaf m t p) z θ (future_ne_selected t p i hf)]

theorem rich_future_patch {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) (i : LeafSlot t)
    (θ : Parameters Y E H m t) (z : numerical (Y := Y) (m := m) t) (hf : FutureLeaf t p i)
    (Z : Space Y E H m t) :
    richDecoder K t p (θ,Z)=richDecoder K t p (patch t i z θ,Z) :=
  richDecoder_erasure hK t p θ _ (future_sameKnown t p i θ z hf)
    (future_selectedMatrix t p i θ z hf).symm Z

variable {d n r J : ℕ} [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]

/-- Once numerical entries are replaced, the entire actual coefficient tree
depends on the external leaf factor alone, for arbitrary raw realizations. -/
theorem patch_coefficients_rest (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) :
    ∀ t (i : LeafSlot t) (x y : Raw d n r J E H t)
    (z : numerical (Y := EuclideanSpace ℝ (Fin d)) (m := 4096*J^2) t),
    (RawLeafFactor.factor t i x).2=(RawLeafFactor.factor t i y).2 →
    patch t i z (coefficients P B fallback t x)=patch t i z (coefficients P B fallback t y)
  | 0,i,x,y,z,he => by
    have hm := RawLeafLocality.rest_eq_memory 0 i x y he
    apply Prod.ext
    · funext q
      by_cases hq : q=i
      · subst q
        simp only [patch,if_true]
        exact congrArg (fun v => (z.1,z.2.1,z.2.2,v))
          (RawLeafLocality.rest_eq_leaf_v P B fallback 0 i x y he i)
      · simp only [patch,if_neg hq]
        exact congrArg (fun a => (a.A,a.b,a.a,a.v))
          (RawLeafLocality.rest_eq_other_leaf P B fallback 0 i x y he q hq)
    · change x.2.2.2=y.2.2.2
      exact congrArg (fun v : RawLeafLocality.MemoryTree J E H 0 => v.2) hm
  | t+1,i,x,y,z,he => by
    apply Prod.ext
    · funext q
      by_cases hq : q=i.1
      · subst q
        simpa only [patch,if_true,coefficients] using patch_coefficients_rest P B fallback t i.2
          (x.1 i.1) (y.1 i.1) z (RawLeafLocality.rest_eq_child t i x y he)
      · simp only [patch,if_neg hq,coefficients]
        rw [RawLeafLocality.rest_eq_sibling t i x y he q hq]
    · exact congrArg (fun v : RawLeafFactor.Rest d n r J E H (t+1) => v.2.2) he

end GradientHessian.NumericalCoefficientPatch
