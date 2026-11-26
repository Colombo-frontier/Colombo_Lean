import GradientHessian.CensoredMarkView
import GradientHessian.RawCenterLocality
import GradientHessian.RawMemoryGlobalLocality

/-! Literal hidden-direction erasure propagated along the raw coefficient
path. Endpoint predicates mention only finite plan indices and disclosure
flags. The external coordinate is the original presampling factor. -/

noncomputable section
namespace GradientHessian.CensoredDirection
open Classical HigherHierarchy RawHierarchy CensoredHierarchy CensoredOracle
  RawSubtreeLocality RawSubtreeFactor

def HiddenAt {m : ℕ} (h : ℕ) (endpoint : Plan m h → Prop) :
    (depth : ℕ) → Word depth → Plan m (h+depth) → Prop
  | 0,_,p => endpoint p
  | depth+1,w,p => p.1 < w 0 ∨ p.1 = w 0 ∧ HiddenAt h endpoint depth (Fin.tail w) p.2.2

def HiddenBlock {m : ℕ} (i : Fin 8) : {t : ℕ} → Plan m t → Prop
  | 0,p => ¬(i < p.1 ∨ p.2.1 i=true)
  | _+1,p => ¬(i < p.1 ∨ p.2.1 i=true)

def HiddenInner {m : ℕ} (i : Fin 8) (j : Fin (m+1)) (p : Plan m 0) : Prop :=
  p.1 < i ∨ p.1 = i ∧ p.2.2.memory j=false

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem lift_sameKnown (h : ℕ) (rel : Raw d n r J E H h → Raw d n r J E H h → Prop)
    (endpoint : Plan (4096*J^2) h → Prop)
    (hend : ∀ p x y,rel x y → endpoint p →
      SameKnown h p (coefficients P B fallback h x) (coefficients P B fallback h y)) :
    ∀ depth (w : Word depth) (p : Plan (4096*J^2) (h+depth))
      (x y : Raw d n r J E H (h+depth)),
    PathChange h rel depth w x y → HiddenAt h endpoint depth w p →
      SameKnown (h+depth) p (coefficients P B fallback (h+depth) x) (coefficients P B fallback (h+depth) y) := by
  intro depth
  induction depth with
  | zero => intro w p x y hc hp; exact hend p x y hc hp
  | succ depth ih =>
    intro w p x y hc hp
    refine ⟨?_,?_,?_⟩
    · intro i hi
      have hiw : i≠w 0 := by rcases hp with hh | ⟨hh,_⟩ <;> omega
      change coefficients P B fallback (h+depth) (x.1 i)=coefficients P B fallback (h+depth) (y.1 i)
      rw [hc.2.1 i hiw]
    · intro i _
      exact congrFun hc.1 i
    · change SameKnown (h+depth) p.2.2 (coefficients P B fallback (h+depth) (x.1 p.1))
        (coefficients P B fallback (h+depth) (y.1 p.1))
      rcases hp with hh | ⟨hh,hp⟩
      · rw [hc.2.1 p.1 (ne_of_lt hh)]
        exact CensoredMark.sameKnown_refl _ _ _
      · rw [hh]
        exact ih (Fin.tail w) p.2.2 _ _ hc.2.2 hp

theorem center_endpoint (h : ℕ) (i : Fin 8) (p : Plan (4096*J^2) (h+1))
    (x y : Raw d n r J E H (h+1)) (hc : RawCenterLocality.LocalChange h i x y)
    (hp : HiddenBlock i p) :
    SameKnown (h+1) p (coefficients P B fallback (h+1) x) (coefficients P B fallback (h+1) y) := by
  refine ⟨?_,?_,?_⟩
  · intro a _
    change coefficients P B fallback h (x.1 a)=coefficients P B fallback h (y.1 a)
    rw [hc.1]
  · intro a ha
    exact hc.2 a (fun he => hp (by simpa only [he] using ha))
  · change SameKnown h p.2.2 (coefficients P B fallback h (x.1 p.1)) (coefficients P B fallback h (y.1 p.1))
    rw [hc.1]
    exact CensoredMark.sameKnown_refl _ _ _

theorem old_endpoint (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (p : Plan (4096*J^2) 0) (x y : Raw d n r J E H 0)
    (hc : RawMemoryLocality.OldChange i j x y) (hp : HiddenBlock i p) :
    SameKnown 0 p (coefficients P B fallback 0 x) (coefficients P B fallback 0 y) := by
  have hX : x.1=y.1 := congrArg (fun a : RawMemoryFactor.Header d n r J => a.1) hc.1
  have hM : x.2.1=y.2.1 := congrArg Prod.snd hc.1
  have hV : x.2.2.1=y.2.2.1 := hc.2.1
  have hchild : (coefficients P B fallback 0 x).1=(coefficients P B fallback 0 y).1 := by
    simp only [coefficients,hX,hM,hV]
  refine ⟨fun a _ => congrFun hchild a,?_,?_⟩
  · intro a ha
    funext k
    exact hc.2.2 a k (Or.inl (fun he => hp (by simpa only [he] using ha)))
  · rw [congrArg Prod.snd (congrFun hchild p.1)]

theorem inner_endpoint (i : Fin 8) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (p : Plan (4096*J^2) 0) (x y : Raw d n r J E H 0)
    (hc : RawMemoryLocality.InnerChange i j k x y) (hp : HiddenInner i j p) :
    SameKnown 0 p (coefficients P B fallback 0 x) (coefficients P B fallback 0 y) := by
  have hX : x.1=y.1 := congrArg (fun a : RawMemoryFactor.Header d n r J => a.1) hc.1
  have hM : x.2.1=y.2.1 := congrArg Prod.snd hc.1
  have hV : x.2.2.2=y.2.2.2 := hc.2.1
  have hchild (a : Fin 8) (ha : a≠i) :
      (coefficients P B fallback 0 x).1 a=(coefficients P B fallback 0 y).1 a := by
    have hv : x.2.2.1 a=y.2.2.1 a := funext (fun b => funext (fun c => hc.2.2 a b c (Or.inl ha)))
    simp only [coefficients,hX,hM,hv]
  refine ⟨?_,?_,?_⟩
  · intro a ha
    apply hchild
    rcases hp with hh | ⟨hh,_⟩ <;> omega
  · intro a _
    exact congrFun hV a
  · apply CensoredLeaf.view_congr
    · intro a _
      simp only [coefficients,hM]
    · intro a _
      simp only [coefficients,hX,hM]
    · intro a ha
      funext b
      apply hc.2.2
      rcases hp with hh | ⟨hh,hp⟩
      · exact Or.inl (ne_of_lt hh)
      · right; left
        intro he
        subst a
        simp [hp] at ha

theorem center_sameKnown (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (p : Plan (4096*J^2) (h+1+depth)) (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (hp : HiddenAt (h+1) (HiddenBlock i) depth w p) :
    SameKnown (h+1+depth) p (coefficients P B fallback (h+1+depth) x)
      (coefficients P B fallback (h+1+depth) y) :=
  lift_sameKnown P B fallback (h+1) (RawCenterLocality.LocalChange h i) (HiddenBlock i)
    (center_endpoint P B fallback h i) depth w p x y
    (RawCenterLocality.pathChange_of_rest_eq h depth w i x y he) hp

theorem old_sameKnown (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (p : Plan (4096*J^2) (0+depth))
    (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (hp : HiddenAt 0 (HiddenBlock i) depth w p) :
    SameKnown (0+depth) p (coefficients P B fallback (0+depth) x) (coefficients P B fallback (0+depth) y) :=
  lift_sameKnown P B fallback 0 (RawMemoryLocality.OldChange i j) (HiddenBlock i)
    (old_endpoint P B fallback i j) depth w p x y
    (RawMemoryGlobalLocality.old_pathChange depth w i j x y he) hp

theorem inner_sameKnown (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (p : Plan (4096*J^2) (0+depth))
    (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (hp : HiddenAt 0 (HiddenInner i j) depth w p) :
    SameKnown (0+depth) p (coefficients P B fallback (0+depth) x) (coefficients P B fallback (0+depth) y) :=
  lift_sameKnown P B fallback 0 (RawMemoryLocality.InnerChange i j k) (HiddenInner i j)
    (inner_endpoint P B fallback i j k) depth w p x y
    (RawMemoryGlobalLocality.inner_pathChange depth w i j k x y he) hp

end GradientHessian.CensoredDirection
