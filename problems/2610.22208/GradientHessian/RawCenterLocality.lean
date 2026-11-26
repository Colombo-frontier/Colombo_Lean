import GradientHessian.RawCenterFactor
import GradientHessian.RawSubtreeLocality
import GradientHessian.RawLeafLocality

/-! An isolated center changes exactly one direction at its addressed
node. Every child subtree, other center and ancestor field is preserved,
and therefore all numerical leaf coefficients remain identical. -/

noncomputable section
namespace GradientHessian.RawCenterLocality
open RawHierarchy RawSubtreeFactor HigherHierarchy

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def LocalChange (h : ℕ) (i : Fin 8) (x y : Raw d n r J E H (h+1)) : Prop :=
  x.1=y.1 ∧ ∀ j,j≠i → x.2 j=y.2 j

theorem localChange_of_rest_eq (h : ℕ) (i : Fin 8) (x y : Raw d n r J E H (h+1))
    (he : (RawCenterFactor.localFactor h i x).2=(RawCenterFactor.localFactor h i y).2) :
    LocalChange h i x y := by
  refine ⟨congrArg (fun z : RawCenterFactor.LocalRest d n r J E H h => z.1) he,?_⟩
  intro j hj
  obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hj
  exact congrArg (fun z : RawCenterFactor.LocalRest d n r J E H h => z.2 q) he

theorem rest_eq_subtree_rest (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    (factor (h+1) depth w x).2=(factor (h+1) depth w y).2 :=
  congrArg (fun z : RawCenterFactor.Rest d n r J E H h depth => z.2) he

theorem rest_eq_local_rest (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    (RawCenterFactor.localFactor h i (selectedRaw (h+1) depth w x)).2=
      (RawCenterFactor.localFactor h i (selectedRaw (h+1) depth w y)).2 := by
  have ht := congrArg Prod.fst he
  change (RawCenterFactor.localFactor h i (factor (h+1) depth w x).1).2=
    (RawCenterFactor.localFactor h i (factor (h+1) depth w y).1).2 at ht
  simpa only [factor_target] using ht

theorem pathChange_of_rest_eq (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    RawSubtreeLocality.PathChange (h+1) (LocalChange h i) depth w x y :=
  RawSubtreeLocality.pathChange_of_rest_eq (h+1) (LocalChange h i) depth w x y
    (rest_eq_subtree_rest h depth w i x y he)
    (localChange_of_rest_eq h i _ _ (rest_eq_local_rest h depth w i x y he))

def replace (h depth : ℕ) (w : Word depth) (i : Fin 8) (z : H h)
    (x : Raw d n r J E H (h+1+depth)) : Raw d n r J E H (h+1+depth) :=
  (RawCenterFactor.factor h depth w i).symm (z,(RawCenterFactor.factor h depth w i x).2)

theorem factor_replace (h depth : ℕ) (w : Word depth) (i : Fin 8) (z : H h)
    (x : Raw d n r J E H (h+1+depth)) :
    RawCenterFactor.factor h depth w i (replace h depth w i z x)=
      (z,(RawCenterFactor.factor h depth w i x).2) :=
  (RawCenterFactor.factor h depth w i).apply_symm_apply _

theorem replace_direction (h depth : ℕ) (w : Word depth) (i : Fin 8) (z : H h)
    (x : Raw d n r J E H (h+1+depth)) :
    (selectedRaw (h+1) depth w (replace h depth w i z x)).2 i=z := by
  rw [← RawCenterFactor.factor_direction h depth w i,factor_replace]

theorem replace_pathChange (h depth : ℕ) (w : Word depth) (i : Fin 8) (z : H h)
    (x : Raw d n r J E H (h+1+depth)) :
    RawSubtreeLocality.PathChange (h+1) (LocalChange h i) depth w (replace h depth w i z x) x :=
  pathChange_of_rest_eq h depth w i _ _
    (by simpa only using congrArg Prod.snd (factor_replace h depth w i z x))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rest_eq_all_leafData (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    ∀ q, leafData (h+1+depth) (assemble P B fallback (h+1+depth) x) q=
      leafData (h+1+depth) (assemble P B fallback (h+1+depth) y) q := by
  let rel := fun t (a b : Raw d n r J E H t) =>
    ∀ q, leafData t (assemble P B fallback t a) q=leafData t (assemble P B fallback t b) q
  have hs : ∀ t (a b : Raw d n r J E H (t+1)),
      (∀ j,rel t (a.1 j) (b.1 j)) → a.2=b.2 → rel (t+1) a b := by
    intro t a b hc _ q
    exact hc q.1 q.2
  apply RawSubtreeLocality.lift_relation rel (fun _ _ _ => rfl) hs (h+1) depth w x y
    (rest_eq_subtree_rest h depth w i x y he)
  intro q
  have hc := (localChange_of_rest_eq h i _ _ (rest_eq_local_rest h depth w i x y he)).1
  change leafData h (assemble P B fallback h ((selectedRaw (h+1) depth w x).1 q.1)) q.2=
    leafData h (assemble P B fallback h ((selectedRaw (h+1) depth w y).1 q.1)) q.2
  rw [hc]

end GradientHessian.RawCenterLocality
