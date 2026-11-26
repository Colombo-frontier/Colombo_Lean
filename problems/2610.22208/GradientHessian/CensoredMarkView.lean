import GradientHessian.CensoredOracleView
import GradientHessian.RawHierarchyMeasurability
import GradientHessian.RawMarkLocality

/-! Erasure of a genuinely future mark from the literal finite oracle view.
The comparison is made in the original raw factor, before any conditioning. -/

noncomputable section
namespace GradientHessian.CensoredMark
open Classical HigherHierarchy RawHierarchy CensoredHierarchy CensoredOracle

def Future {m : ℕ} : (t : ℕ) → Plan m t → LeafSlot t → Fin (m+1) → Prop
  | 0,p,i,j => p.1 < i ∨ p.1 = i ∧ p.2.2.current < j
  | t+1,p,i,j => p.1 < i.1 ∨ p.1 = i.1 ∧ Future t p.2.2 i.2 j

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]

theorem rest_eq_child (t : ℕ) (i : LeafSlot (t+1)) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H (t+1))
    (he : (RawMarkFactor.factor (t+1) i j x).2=(RawMarkFactor.factor (t+1) i j y).2) :
    (RawMarkFactor.factor t i.2 j (x.1 i.1)).2=(RawMarkFactor.factor t i.2 j (y.1 i.1)).2 := by
  apply Prod.ext
  · simpa only [RawMarkFactor.factor_matrix,RawLeafFactor.leafNumerical] using
      congrArg (fun z : RawMarkFactor.Rest d n r J E H (t+1) => z.1) he
  · apply Prod.ext
    · exact congrArg (fun z : RawMarkFactor.Rest d n r J E H (t+1) => z.2.1) he
    · exact RawLeafLocality.rest_eq_child t i x y (RawMarkLocality.rest_eq_leaf_rest (t+1) i j x y he)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

theorem sameKnown_refl : ∀ t (p : Plan (4096*J^2) t)
    (θ : HierarchyParameters.Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t),
    SameKnown t p θ θ
  | 0,_,_ => ⟨fun _ _ => rfl,fun _ _ => rfl,rfl⟩
  | t+1,p,θ => ⟨fun _ _ => rfl,fun _ _ => rfl,sameKnown_refl t p.2.2 (θ.1 p.1)⟩

theorem base_other_coefficients (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (i : LeafSlot 0) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H 0)
    (he : (RawMarkFactor.factor 0 i j x).2=(RawMarkFactor.factor 0 i j y).2)
    (q : Fin 8) (hq : q≠i) :
    (coefficients P B fallback 0 x).1 q=(coefficients P B fallback 0 y).1 q := by
  exact congrArg (fun a => (a.A,a.b,a.a,a.v))
    (RawMarkLocality.rest_eq_other_leaf P B fallback 0 i j x y he q hq)

theorem sameKnown_of_future (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (p : Plan (4096*J^2) t) (i : LeafSlot t)
    (j : Fin (4096*J^2+1)) (x y : Raw d n r J E H t),
    (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2 → Future t p i j →
    SameKnown t p (coefficients P B fallback t x) (coefficients P B fallback t y) := by
  intro t
  induction t with
  | zero =>
    intro p i j x y he hf
    have hm := RawMarkLocality.rest_eq_memory 0 i j x y he
    have hv : x.2.2.1=y.2.2.1 := congrArg Prod.fst hm
    have ho : x.2.2.2=y.2.2.2 := congrArg Prod.snd hm
    refine ⟨?_,?_,?_⟩
    · intro q hq
      apply base_other_coefficients P B fallback i j x y he q
      rcases hf with hl | ⟨hl,_⟩ <;> omega
    · intro q _
      exact congrFun ho q
    · rcases hf with hl | ⟨hl,hj⟩
      · rw [congrArg Prod.snd (base_other_coefficients P B fallback i j x y he p.1 (ne_of_lt hl))]
      · apply CensoredLeaf.view_congr
        · intro k hk
          have hk' : k≠j := ne_of_lt (hk.trans_lt hj)
          have h := RawMarkLocality.rest_eq_other_b P B fallback 0 i j x y he k hk'
          simpa only [← hl] using h
        · intro k hk
          have hk' : k≠j := by rcases hk with hk | ⟨hk,_⟩ <;> omega
          have h := RawMarkLocality.rest_eq_other_a P B fallback 0 i j x y he k hk'
          simpa only [← hl] using h
        · intro k _
          exact congrArg (fun v => v p.1 k) hv
  | succ t ih =>
    intro p i j x y he hf
    have hl := RawMarkLocality.rest_eq_leaf_rest (t+1) i j x y he
    have hm := RawMarkLocality.rest_eq_memory (t+1) i j x y he
    have ho : x.2=y.2 := congrArg (fun z : RawLeafLocality.MemoryTree J E H (t+1) => z.2) hm
    refine ⟨?_,?_,?_⟩
    · intro q hq
      have hqi : q≠i.1 := by rcases hf with hi | ⟨hi,_⟩ <;> omega
      change coefficients P B fallback t (x.1 q)=coefficients P B fallback t (y.1 q)
      rw [RawLeafLocality.rest_eq_sibling t i x y hl q hqi]
    · intro q _
      exact congrFun ho q
    · change SameKnown t p.2.2 (coefficients P B fallback t (x.1 p.1))
        (coefficients P B fallback t (y.1 p.1))
      rcases hf with hi | ⟨hi,hf⟩
      · rw [RawLeafLocality.rest_eq_sibling t i x y hl p.1 (ne_of_lt hi)]
        exact sameKnown_refl _ _ _
      · rw [hi]
        exact ih p.2.2 i.2 j _ _ (rest_eq_child t i j x y he) hf

theorem known_eq (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (K : ℝ) (t : ℕ) (p : Plan (4096*J^2) t) (i : LeafSlot t)
    (j : Fin (4096*J^2+1)) (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2)
    (hf : Future t p i j) :
    known K t p (assemble P B fallback t x)=known K t p (assemble P B fallback t y) := by
  simpa only [decode_coefficients] using known_eq_of_sameKnown K t p _ _
    (sameKnown_of_future P B fallback t p i j x y he hf)

theorem weight_eq (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (K : ℝ) (t : ℕ) (p : Plan (4096*J^2) t) (i : LeafSlot t)
    (j : Fin (4096*J^2+1)) (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2)
    (hf : Future t p i j) :
    weight K t p (assemble P B fallback t x)=weight K t p (assemble P B fallback t y) := by
  simpa only [decode_coefficients] using weight_eq_of_sameKnown K t p _ _
    (sameKnown_of_future P B fallback t p i j x y he hf)

end GradientHessian.CensoredMark
