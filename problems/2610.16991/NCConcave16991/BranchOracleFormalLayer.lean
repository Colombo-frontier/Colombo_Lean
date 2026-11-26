import NCConcave16991.BranchOracleWords
import NCConcave16991.BranchGeometry

/-! # Literal formal word layers and coordinate branch actions -/

namespace NCConcave16991.BranchOracle
noncomputable section
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def wordHeadTail (t : ℕ) : Word ι (t + 1) ≃ ι × Word ι t where
  toFun w := (w 0, Fin.tail w)
  invFun p := Fin.cons (α := fun _ : Fin (t + 1) ↦ ι) p.1 p.2
  left_inv w := Fin.cons_self_tail w
  right_inv p := by rcases p with ⟨i,w⟩; simp

theorem sum_word_succ {R : Type*} [AddCommMonoid R] (t : ℕ) (f : Word ι (t + 1) → R) :
    ∑ w, f w = ∑ i : ι, ∑ w : Word ι t, f (Fin.cons i w) := by
  calc
    _ = ∑ p : ι × Word ι t, f ((wordHeadTail (ι := ι) t).symm p) :=
      Fintype.sum_equiv (wordHeadTail (ι := ι) t) _ _ (by intro w; simp)
    _ = _ := Fintype.sum_prod_type _

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev FormalLayer (t : ℕ) := PiLp 2 (fun _ : Word ι t ↦ E)

def prepend (t : ℕ) (i : ι) (x : FormalLayer (ι := ι) E t) : FormalLayer (ι := ι) E (t + 1) :=
  WithLp.toLp 2 (fun w ↦ if w 0 = i then x (Fin.tail w) else 0)

def slice (t : ℕ) (i : ι) (y : FormalLayer (ι := ι) E (t + 1)) : FormalLayer (ι := ι) E t :=
  WithLp.toLp 2 (fun w ↦ y (Fin.cons i w))

theorem prepend_norm_sq (t : ℕ) (i : ι) (x : FormalLayer (ι := ι) E t) :
    ‖prepend E t i x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, sum_word_succ]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro w _
    simp [prepend]
  · intro j _ hji
    simp [prepend, hji]
  · simp

def prependIsometry (t : ℕ) (i : ι) : FormalLayer (ι := ι) E t →ₗᵢ[ℝ] FormalLayer (ι := ι) E (t + 1) where
  toFun := prepend E t i
  map_add' := by
    intro x y
    apply PiLp.ext
    intro w
    by_cases h : w 0 = i <;> simp [prepend, h]
  map_smul' := by
    intro c x
    apply PiLp.ext
    intro w
    by_cases h : w 0 = i <;> simp [prepend, h]
  norm_map' x := by
    change ‖prepend E t i x‖ = ‖x‖
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (prepend_norm_sq E t i x)

def formalBranchFamily (t : ℕ) : BranchGeometry.BranchFamily (ι := ι)
    (FormalLayer (ι := ι) E t) (FormalLayer (ι := ι) E (t + 1)) where
  branch := prependIsometry E t
  orthogonal := by
    intro i j hij x y
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro w _
    by_cases hi : w 0 = i
    · have hj : w 0 ≠ j := by intro hj; exact hij (hi.symm.trans hj)
      simp [prependIsometry, prepend, hi, hj, hij]
    · simp [prependIsometry, prepend, hi]

theorem prepend_inner (t : ℕ) (i : ι) (x : FormalLayer (ι := ι) E t)
    (y : FormalLayer (ι := ι) E (t + 1)) :
    ⟪prepend E t i x, y⟫_ℝ = ⟪x, slice E t i y⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, sum_word_succ]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro w _
    simp [prepend, slice]
  · intro j _ hji
    simp [prepend, hji]
  · simp

theorem formalBranch_adjoint_apply (t : ℕ) (i : ι) (y : FormalLayer (ι := ι) E (t + 1)) :
    ((formalBranchFamily E t).branch i).toContinuousLinearMap.adjoint y = slice E t i y := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact prepend_inner E t i x y

def formalTarget (t : ℕ) (e : E) : FormalLayer (ι := ι) E t :=
  WithLp.toLp 2 (fun _ ↦ BranchGeometry.beta ι ^ t • e)

theorem formalTarget_forward (t : ℕ) (e : E) :
    (formalBranchFamily (ι := ι) E t).normalizedIsometry (formalTarget (ι := ι) E t e) = formalTarget (ι := ι) E (t + 1) e := by
  rw [BranchGeometry.BranchFamily.normalizedIsometry_apply]
  apply PiLp.ext
  intro w
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
  change BranchGeometry.beta ι •
    (∑ i : ι, if w 0 = i then BranchGeometry.beta ι ^ t • e else 0) = BranchGeometry.beta ι ^ (t + 1) • e
  simp [pow_succ, smul_smul, mul_comm]

theorem formalTarget_norm (t : ℕ) (e : E) : ‖formalTarget (ι := ι) E t e‖ = ‖e‖ := by
  induction t with
  | zero =>
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp [formalTarget, Word]
  | succ t ih =>
    rw [← formalTarget_forward, LinearIsometry.norm_map, ih]

end
end NCConcave16991.BranchOracle
