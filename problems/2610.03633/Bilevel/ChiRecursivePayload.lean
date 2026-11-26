import Bilevel.ChiBoundedChainUniformLocal
import Bilevel.ChiBoundedChainSelectors

/-! The actual bounded-chain recursive payload. Each node is the explicit
radially composed chain with its two receivers. Public radial penalties are
kept outside this recursion. Prefixes identify independently framed nodes. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiRecursive
open ChiBoundedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Node (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  n : ℕ
  ell : ℝ
  width : ℝ
  receiver : ℝ
  nu : ℝ
  force : ℝ
  parentWidth : ℝ
  tailRadius : ℝ
  radius : ℝ
  frame : Space n →ₗᵢ[ℝ] E

namespace Node

def coordinates (D : Node E) (u : E) : Space D.n :=
  WrappedChain.coordinates D.n D.radius D.frame u

def H (D : Node E) (u : E) : ℝ :=
  payload D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius (D.coordinates u)

def selector (D : Node E) (i : Fin (D.n+1)) (u : E) : ℝ :=
  ChiBoundedChain.selector D.n i (D.width⁻¹ • D.coordinates u)

def residual (D : Node E) (i : Fin (D.n+1)) (u : E) : ℝ :=
  Rterm D.n D.ell D.width i (D.coordinates u)

def release (D : Node E) (u : E) : ℝ :=
  releaseGate (D.coordinates u (Fin.last D.n)/D.parentWidth)

theorem coordinates_zero (D : Node E) : D.coordinates 0=0 := by
  simp [coordinates,WrappedChain.coordinates,RadialWrapper.compress]

theorem release_zero (D : Node E) : D.release 0=0 := by
  simp only [release,coordinates_zero,PiLp.zero_apply,zero_div]
  exact releaseGate_zero (by norm_num)

theorem selector_range (D : Node E) (i : Fin (D.n+1)) (u : E) :
    0≤D.selector i u ∧ D.selector i u≤1 := ChiBoundedChain.selector_range _ _ _

theorem selector_sum_le_one (D : Node E) (u : E) :
    ∑ i : Fin (D.n+1),D.selector i u≤1 := ChiBoundedChain.selector_sum_le_one _ _

theorem selector_unique (D : Node E) (i j : Fin (D.n+1)) (u : E)
    (hi : D.selector i u≠0) (hj : D.selector j u≠0) : i=j :=
  ChiBoundedChain.selector_unique i j _ hi hj

theorem residual_nonpos (D : Node E) (hD : 0≤D.ell) (i : Fin (D.n+1)) (u : E) :
    D.residual i u≤0 := Rterm_nonpos _ _ _ hD _ _

theorem H_zero_eq_residual_sum (D : Node E) :
    D.H 0=∑ i : Fin (D.n+1),D.residual i 0 := by
  have hp : ChiBoundedChain.psi 0=0 := psi_zero (by norm_num)
  have he : evenGate 0=0 := evenGate_zero (by norm_num)
  have hm : tailMask (0:Fin (D.n+1)) (0:Space D.n)=1 :=
    tailMask_one_of_small _ _ (by intros; simp)
  unfold H residual
  rw [coordinates_zero,← R_eq_sum]
  simp only [payload,positiveReceiver,negativeReceiver,PiLp.zero_apply,primitive_zero,add_zero,
    chain,R,ZeroChainResidualScaled.scaled,smul_zero]
  congr 1
  rw [value,ChiBoundedChain.residual,Fin.sum_univ_succ]
  simp [edge,ChiBoundedChain.residualTerm,ChiBoundedChain.selector,hp,he,hm]

end Node

abbrev Geometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℕ → List ℕ → Node E

def child (I : List ℕ) (i : ℕ) : List ℕ := I++[i]

/-- Exactly the recursive source formula, with centered leaves. -/
def payloadValue (D : Geometry E) : ℕ → ℕ → List ℕ → (ℕ → E) → ℝ
  | 0,j,I,u => (D j I).H (u j)-(D j I).H 0
  | d+1,j,I,u =>
      (D j I).H (u j)-(∑ i : Fin ((D j I).n+1),(D j I).residual i (u j))+
      (∑ i : Fin ((D j I).n+1),(D j I).residual i (u j)*
        (D (j+1) (child I i.val)).release (u (j+1)))+
      ∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*
        payloadValue D d (j+1) (child I i.val) u

theorem payloadValue_zero (D : Geometry E) (d j : ℕ) (I : List ℕ) :
    payloadValue D d j I (fun _ => 0)=0 := by
  induction d generalizing j I with
  | zero => simp [payloadValue]
  | succ d ih =>
    simp only [payloadValue,Node.release_zero,mul_zero,Finset.sum_const_zero,
      ih,add_zero,Node.H_zero_eq_residual_sum,sub_self]

/-- A payload only reads its own block and later blocks. -/
theorem payloadValue_congr_tail (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (u v : ℕ → E) (huv : ∀ k,j≤k → u k=v k) :
    payloadValue D d j I u=payloadValue D d j I v := by
  induction d generalizing j I with
  | zero => simp only [payloadValue,huv j le_rfl]
  | succ d ih =>
    simp only [payloadValue,huv j le_rfl,huv (j+1) (by omega)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ih (j+1) (child I i.val) (fun k hk => huv k (by omega))]

theorem payloadValue_update_earlier (D : Geometry E) (d j k : ℕ) (I : List ℕ)
    (u : ℕ → E) (v : E) (hkj : k<j) :
    payloadValue D d j I (Function.update u k v)=payloadValue D d j I u := by
  apply payloadValue_congr_tail
  intro t ht
  rw [Function.update_of_ne (by omega : t≠k)]

/-- The exact single-block formula from which the local gradient and its
one-child perturbation will be differentiated. -/
theorem payloadValue_update_current (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (u : ℕ → E) (v : E) :
    payloadValue D (d+1) j I (Function.update u j v)=
      (D j I).H v-(∑ i : Fin ((D j I).n+1),(D j I).residual i v)+
      (∑ i : Fin ((D j I).n+1),(D j I).residual i v*
        (D (j+1) (child I i.val)).release (u (j+1)))+
      ∑ i : Fin ((D j I).n+1),(D j I).selector i v*
        payloadValue D d (j+1) (child I i.val) u := by
  simp only [payloadValue,Function.update_self,Function.update_of_ne (show j+1≠j by omega),
    payloadValue_update_earlier D d (j+1) j _ u v (by omega)]

/-- Selected carrier at a specified relative depth, obtained by multiplying
the actual ancestor selectors while descending the actual tree. -/
def selectedCarrier (D : Geometry E) : ℕ → ℕ → List ℕ → ℕ → (ℕ → E) → ℝ
  | 0,j,I,0,u => (D j I).H (u j)-(D j I).H 0
  | 0,_,_,_+1,_ => 0
  | _+1,j,I,0,u =>
      (D j I).H (u j)-(∑ i : Fin ((D j I).n+1),(D j I).residual i (u j))+
      ∑ i : Fin ((D j I).n+1),(D j I).residual i (u j)*
        (D (j+1) (child I i.val)).release (u (j+1))
  | d+1,j,I,k+1,u => ∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*
      selectedCarrier D d (j+1) (child I i.val) k u

/-- Exact depth expansion of the constructed source payload. -/
theorem payloadValue_trace (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    payloadValue D d j I u=∑ k : Fin (d+1),selectedCarrier D d j I k.val u := by
  induction d generalizing j I with
  | zero => simp [payloadValue,selectedCarrier]
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,selectedCarrier,payloadValue]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum,← ih]

end Bilevel.ChiRecursive
