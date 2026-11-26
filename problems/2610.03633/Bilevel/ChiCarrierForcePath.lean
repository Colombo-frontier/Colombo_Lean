import Bilevel.ChiCarrierClosedForce
import Bilevel.ChiCarrierFineSupport

/-! Actual selector uniqueness leaves a single path for the pre-wrapper
force. This identifies the frame against which a new column is tested. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem jointSelector_ne_zero_activeChild (m j : ℕ) (D : Node E) (x : Blocks m E)
    (i : Fin (D.n+1)) (hi : jointSelector m j D i x≠0) : activeChild m j D x=i := by
  apply activeChild_eq m j D x i 0 (by norm_num)
  intro hz
  have hn := congrArg norm hz
  rw [norm_iteratedFDeriv_zero,norm_zero] at hn
  exact hi (norm_eq_zero.mp hn)

theorem selectVectors_eq_active_leaf (m : ℕ) (D : Geometry E)
    (leaf : ℕ → List ℕ → Blocks m E → E) (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    ∃ w : ℝ,0≤w ∧ w≤1 ∧ selectVectors m D leaf d j I x=
      w • leaf (j+d) (terminalPrefix m D d j I x) x := by
  classical
  induction d generalizing j I with
  | zero => exact ⟨1,by norm_num,le_rfl,by simp only [selectVectors,terminalPrefix,Nat.add_zero,one_smul]⟩
  | succ d ih =>
    let a := activeChild m j (D j I) x
    have hs : selectVectors m D leaf (d+1) j I x=jointSelector m j (D j I) a x •
        selectVectors m D leaf d (j+1) (child I a.val) x := by
      apply Finset.sum_eq_single a
      · intro i _ hia
        have hz : jointSelector m j (D j I) i x=0 := by
          by_contra hn
          exact hia (jointSelector_ne_zero_activeChild m j (D j I) x i hn).symm
        rw [hz,zero_smul]
      · simp
    obtain ⟨w,hw,hw1,he⟩ := ih (j+1) (child I a.val)
    have ha := (D j I).selector_range a (block m j x)
    refine ⟨jointSelector m j (D j I) a x*w,mul_nonneg ha.1 hw,?_,?_⟩
    · exact (mul_le_mul_of_nonneg_left hw1 ha.1).trans (by simpa only [mul_one] using ha.2)
    · rw [hs,he,smul_smul]
      simp only [terminalPrefix,a,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem selectedClosedForce_active_path (m : ℕ) (D : Geometry E) (t j : ℕ) (I : List ℕ) (x : Blocks m E) :
    ∃ w : ℝ,0≤w ∧ w≤1 ∧ selectedClosedForce m D t j I x=
      w • closedJointForce m D (j+t) (terminalPrefix m D t j I x) x :=
  selectVectors_eq_active_leaf m D (fun k P y => closedJointForce m D k P y) t j I x

theorem selectedClosedForce_new_column_zero {m : ℕ} (D : Geometry E) (t j : ℕ) (I : List ℕ)
    (x : Blocks m E) (r : ℕ)
    (hh : 0<(D (j+t) (terminalPrefix m D t j I x)).width)
    (hp : ∀ i : Fin ((D (j+t) (terminalPrefix m D t j I x)).n+1),
      0<(D (j+t+1) (child (terminalPrefix m D t j I x) i.val)).parentWidth)
    (hw : ∀ i : Fin ((D (j+t) (terminalPrefix m D t j I x)).n+1),
      (D (j+t+1) (child (terminalPrefix m D t j I x) i.val)).width≤
      (D (j+t+1) (child (terminalPrefix m D t j I x) i.val)).parentWidth)
    (hchild : ∀ i : Fin ((D (j+t) (terminalPrefix m D t j I x)).n+1),r ≤ i.val →
      |(D (j+t+1) (child (terminalPrefix m D t j I x) i.val)).coordinates (block m (j+t+1) x)
        (Fin.last (D (j+t+1) (child (terminalPrefix m D t j I x) i.val)).n)|≤
      (D (j+t+1) (child (terminalPrefix m D t j I x) i.val)).width/4)
    (hz : ∀ k : Fin ((D (j+t) (terminalPrefix m D t j I x)).n+1),r≤k.val →
      |(D (j+t) (terminalPrefix m D t j I x)).coordinates (block m (j+t) x) k|≤
      (D (j+t) (terminalPrefix m D t j I x)).width/4)
    (k : Fin ((D (j+t) (terminalPrefix m D t j I x)).n+1)) (hk : r≤k.val) :
    ⟪(D (j+t) (terminalPrefix m D t j I x)).frame (basis k),selectedClosedForce m D t j I x⟫=0 := by
  obtain ⟨w,_,_,he⟩ := selectedClosedForce_active_path m D t j I x
  rw [he,real_inner_smul_right,closedJointForce_new_column_zero D (j+t) (terminalPrefix m D t j I x)
    r hh x hp hw hchild hz k hk,mul_zero]

end Bilevel.ChiCarrier
