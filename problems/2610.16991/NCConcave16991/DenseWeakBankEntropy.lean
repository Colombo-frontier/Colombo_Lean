import NCConcave16991.DenseWeakProductBank
import NCConcave16991.DenseWeakInformationChain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Entropy and information of the actual finite product bank -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype I] [Fintype J]

def map (P : FiniteLaw I) (f : I → J) : FiniteLaw J where
  mass := fun j ↦ ∑ i, if f i = j then P.mass i else 0
  nonneg := fun j ↦ Finset.sum_nonneg (fun i _ ↦ by split_ifs; exact P.nonneg i; rfl)
  sum_one := by
    rw [Finset.sum_comm]
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using P.sum_one

theorem map_eventMass (P : FiniteLaw I) (f : I → J) (E : Set J) :
    (P.map f).eventMass E = P.eventMass (f ⁻¹' E) := by
  classical
  unfold eventMass map
  have hj (j : J) :
      (if j ∈ E then ∑ i, if f i = j then P.mass i else 0 else 0) =
        ∑ i, if j ∈ E then if f i = j then P.mass i else 0 else 0 := by
    by_cases h : j ∈ E <;> simp [h]
  simp_rw [hj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have he (j : J) :
      (if j ∈ E then if f i = j then P.mass i else 0 else 0) =
        if f i = j then (if f i ∈ E then P.mass i else 0) else 0 := by
    by_cases h : f i = j
    · subst j; simp
    · simp [h]
  simp_rw [he]
  simp

theorem map_pi_mass {D : Type*} [Fintype D] [DecidableEq D]
    (P : D → FiniteLaw I) (f : D → I → J) (y : D → J) :
    ((pi P).map (fun x d ↦ f d (x d))).mass y =
      (pi (fun d ↦ (P d).map (f d))).mass y := by
  have hf : {x : D → I | (fun d ↦ f d (x d)) = y} =
      rectangle (fun d ↦ {i | f d i = y d}) := by
    ext x
    exact funext_iff
  change (pi P).eventMass {x | (fun d ↦ f d (x d)) = y} =
    ∏ d, (P d).eventMass {i | f d i = y d}
  rw [hf, pi_rectangle_eventMass]

def splitFirst (D : ℕ) (I : Type*) : (Fin (D + 1) → I) ≃ I × (Fin D → I) where
  toFun := fun x ↦ (x 0, Fin.tail x)
  invFun := fun x ↦ Fin.cons x.1 x.2
  left_inv := Fin.cons_self_tail
  right_inv := fun x ↦ by simp

theorem pi_succ_entropy (D : ℕ) (P : Fin (D + 1) → FiniteLaw I) :
    (pi P).entropy = (P 0).entropy + (pi (fun d : Fin D ↦ P d.succ)).entropy := by
  rw [← product_entropy]
  unfold entropy finiteEntropy
  apply Fintype.sum_equiv (splitFirst D I)
  intro x
  congr 1
  exact Fin.prod_univ_succ (fun d ↦ (P d).mass (x d))

theorem pi_entropy (D : ℕ) (P : Fin D → FiniteLaw I) :
    (pi P).entropy = ∑ d, (P d).entropy := by
  induction D with
  | zero => simp [entropy, finiteEntropy, pi]
  | succ D ih =>
      rw [pi_succ_entropy, ih, Fin.sum_univ_succ]

def unzip (D : ℕ) : (Fin D → I × J) ≃ (Fin D → I) × (Fin D → J) where
  toFun := fun x ↦ (fun d ↦ (x d).1, fun d ↦ (x d).2)
  invFun := fun x d ↦ (x.1 d, x.2 d)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

def jointPi (D : ℕ) (P : Fin D → FiniteLaw (I × J)) :
    FiniteLaw ((Fin D → I) × (Fin D → J)) where
  mass := fun x ↦ (pi P).mass ((unzip D).symm x)
  nonneg := fun x ↦ (pi P).nonneg _
  sum_one := by
    rw [← (pi P).sum_one]
    apply Fintype.sum_equiv (unzip D).symm
    intro x
    rfl

theorem jointPi_entropy (D : ℕ) (P : Fin D → FiniteLaw (I × J)) :
    (jointPi D P).entropy = ∑ d, (P d).entropy := by
  rw [← pi_entropy]
  unfold entropy finiteEntropy
  apply Fintype.sum_equiv (unzip D).symm
  intro x
  rfl

theorem jointPi_fst_mass (D : ℕ) (P : Fin D → FiniteLaw (I × J)) :
    (jointPi D P).fst.mass = (pi (fun d ↦ (P d).fst)).mass := by
  funext x
  unfold fst rowMass jointPi pi
  exact (Fintype.prod_sum (fun d j ↦ (P d).mass (x d,j))).symm

theorem jointPi_snd_mass (D : ℕ) (P : Fin D → FiniteLaw (I × J)) :
    (jointPi D P).snd.mass = (pi (fun d ↦ (P d).snd)).mass := by
  funext y
  unfold snd jointPi pi
  exact (Fintype.prod_sum (fun d i ↦ (P d).mass (i,y d))).symm

/-- The mutual information of independent actual label/response columns is
the sum of their individual actual mutual informations. -/
theorem jointPi_mutualInformation (D : ℕ) (P : Fin D → FiniteLaw (I × J)) :
    (jointPi D P).mutualInformation = ∑ d, (P d).mutualInformation := by
  unfold mutualInformation
  have hf : (jointPi D P).fst.entropy = ∑ d, (P d).fst.entropy := by
    change finiteEntropy _ = _
    rw [jointPi_fst_mass]
    exact pi_entropy D (fun d ↦ (P d).fst)
  have hs : (jointPi D P).snd.entropy = ∑ d, (P d).snd.entropy := by
    change finiteEntropy _ = _
    rw [jointPi_snd_mass]
    exact pi_entropy D (fun d ↦ (P d).snd)
  rw [hf, hs, jointPi_entropy]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

end NCConcave16991.DenseWeakHiding.FiniteLaw
