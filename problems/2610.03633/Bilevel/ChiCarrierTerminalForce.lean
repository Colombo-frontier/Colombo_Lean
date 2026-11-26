import Bilevel.ChiCarrierFineSelection
import Bilevel.ChiCarrierBlockGradient

/-! Actual deepest-block differentiation through the finite ancestor
selection. Earlier selectors have zero derivative in the terminal block;
their nonnegative weights form a subprobability and do not amplify force. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def selectVectors (m : ℕ) (D : Geometry E) (leaf : ℕ → List ℕ → Blocks m E → E) :
    ℕ → ℕ → List ℕ → Blocks m E → E
  | 0,j,I,x => leaf j I x
  | d+1,j,I,x => ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x •
      selectVectors m D leaf d (j+1) (child I i.val) x

theorem selectVectors_norm_le (m : ℕ) (D : Geometry E) (leaf : ℕ → List ℕ → Blocks m E → E)
    (d j : ℕ) (I : List ℕ) (x : Blocks m E) (B : ℝ) (hB : 0≤B)
    (hbase : ∀ P,‖leaf (j+d) P x‖≤B) : ‖selectVectors m D leaf d j I x‖≤B := by
  induction d generalizing j I with
  | zero => exact hbase I
  | succ d ih =>
    change ‖∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x •
      selectVectors m D leaf d (j+1) (child I i.val) x‖≤B
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x*B := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_eq_abs]
        have hw : 0≤jointSelector m j (D j I) i x := ((D j I).selector_range i (block m j x)).1
        rw [abs_of_nonneg hw]
        apply mul_le_mul_of_nonneg_left _ ((D j I).selector_range i (block m j x)).1
        exact ih (j+1) (child I i.val) (fun P => by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbase P)
      _ = (∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x)*B := (Finset.sum_mul _ _ _).symm
      _ ≤ 1*B := mul_le_mul_of_nonneg_right ((D j I).selector_sum_le_one (block m j x)) hB
      _ = B := one_mul B

theorem gradient_mul_C3 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f g : F → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x : F) :
    gradient (fun y => f y*g y) x=f x • gradient g x+g x • gradient f x := by
  have hd := ((hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt).mul
    ((hg.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have hh : HasGradientAt (fun y => f y*g y) (f x • gradient g x+g x • gradient f x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_add,map_smul] using hd
  exact hh.gradient

theorem selected_gradient_terminal_block {m : ℕ} (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
    (d j : ℕ) (I : List ℕ) (t : Fin m) (ht : t.val=j+d) (x : Blocks m E) :
    (gradient (selectFamily m D leaf d j I) x) t=
      selectVectors m D (fun k P y => (gradient (leaf k P) y) t) d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    change (gradient (fun y => ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x) t=_
    rw [gradient_finset_sum Finset.univ (fun i : Fin ((D j I).n+1) => fun y : Blocks m E =>
      jointSelector m j (D j I) i y*selectFamily m D leaf d (j+1) (child I i.val) y)
      (fun i => (jointSelector_contDiff m j (D j I) i 3).mul
        (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)))]
    let ev : Blocks m E →L[ℝ] E := PiLp.proj 2 (fun _ : Fin m => E) t
    change ev (∑ i : Fin ((D j I).n+1),gradient (fun y => jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x)=_
    rw [map_sum]
    change (∑ i : Fin ((D j I).n+1),ev (gradient (fun y => jointSelector m j (D j I) i y*
      selectFamily m D leaf d (j+1) (child I i.val) y) x))=
      ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x •
        selectVectors m D (fun k P y => (gradient (leaf k P) y) t) d (j+1) (child I i.val) x
    apply Finset.sum_congr rfl
    intro i _
    rw [gradient_mul_C3 (jointSelector_contDiff m j (D j I) i 3)
      (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)),map_add,map_smul,map_smul]
    have hjm : j < m := by have := t.isLt;omega
    have hst : ev (gradient (jointSelector m j (D j I) i) x)=0 := by
      change (gradient ((D j I).selector i ∘ block m j) x) t=0
      rw [gradient_block_composition x ⟨j,hjm⟩ ((D j I).selector_contDiff i 3),insertion_apply,
        if_neg (by intro he;have hv := congrArg Fin.val he;change t.val=j at hv;omega)]
    rw [hst,smul_zero,add_zero]
    congr 1
    exact ih (j+1) (child I i.val) (by omega)

end Bilevel.ChiCarrier
