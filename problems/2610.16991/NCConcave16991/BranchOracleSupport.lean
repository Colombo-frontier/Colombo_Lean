import NCConcave16991.BranchOracleFormalLayer
import NCConcave16991.BranchOracleAccounting

/-! # Actual word support under matrix actions, inverse reveals and releases -/

namespace NCConcave16991.BranchOracle
noncomputable section
open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The larger support space leaves coordinates inside the reachable word
set unrestricted. This preserves the same uniform-target correlation bound. -/
def wordSupport (t : ℕ) (S : Finset (Word ι t)) (W : Submodule ℝ E) :
    Submodule ℝ (FormalLayer (ι := ι) E t) where
  carrier := {z | ∀ w, w ∉ S → z w ∈ W}
  zero_mem' := by intro w _; exact W.zero_mem
  add_mem' := by intro x y hx hy w hw; exact W.add_mem (hx w hw) (hy w hw)
  smul_mem' := by intro a x hx w hw; exact W.smul_mem a (hx w hw)

theorem wordSupport_mono {t : ℕ} {S T : Finset (Word ι t)} {W U : Submodule ℝ E}
    (hST : S ⊆ T) (hWU : W ≤ U) : wordSupport t S W ≤ wordSupport t T U := by
  intro z hz w hw
  exact hWU (hz w (fun h ↦ hw (hST h)))

theorem all_coordinates_mem_wordSupport {t : ℕ} (S : Finset (Word ι t)) (W : Submodule ℝ E)
    (z : FormalLayer (ι := ι) E t) (hz : ∀ w, z w ∈ W) : z ∈ wordSupport t S W := fun w _ ↦ hz w

theorem prepend_mem_wordSupport (p : WordProfile ι) (W : Submodule ℝ E) (t : ℕ) (i : ι)
    (x : FormalLayer (ι := ι) E t) (hx : x ∈ wordSupport t (p.words t) W) :
    prepend E t i x ∈ wordSupport (t + 1) ((p.matrixStep i).words (t + 1)) W := by
  intro w hw
  by_cases hi : w 0 = i
  · have ht : Fin.tail w ∉ p.words t := by
      intro ht
      apply hw
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨Fin.tail w, ht, ?_⟩
      rw [← hi]
      exact Fin.cons_self_tail w
    simpa [prepend, hi] using hx (Fin.tail w) ht
  · simpa [prepend, hi] using W.zero_mem

theorem slice_mem_wordSupport (p : WordProfile ι) (W : Submodule ℝ E) (t : ℕ) (i : ι)
    (y : FormalLayer (ι := ι) E (t + 1)) (hy : y ∈ wordSupport (t + 1) (p.words (t + 1)) W) :
    slice E t i y ∈ wordSupport t (p.words t) W := by
  intro w hw
  have hcons : Fin.cons i w ∉ p.words (t + 1) := by
    intro h
    exact hw (by simpa using p.deletion t (Fin.cons i w) h)
  exact hy (Fin.cons i w) hcons

theorem forward_mem_wordSupport (p : WordProfile ι) (W : Submodule ℝ E) (t : ℕ) (i : ι)
    (x : FormalLayer (ι := ι) E t) (hx : x ∈ wordSupport t (p.words t) W) :
    (formalBranchFamily E t).branch i x ∈ wordSupport (t + 1) ((p.matrixStep i).words (t + 1)) W :=
  prepend_mem_wordSupport p W t i x hx

theorem transpose_mem_wordSupport (p : WordProfile ι) (W : Submodule ℝ E) (t : ℕ) (i : ι)
    (y : FormalLayer (ι := ι) E (t + 1)) (hy : y ∈ wordSupport (t + 1) (p.words (t + 1)) W) :
    ((formalBranchFamily E t).branch i).toContinuousLinearMap.adjoint y ∈ wordSupport t (p.words t) W := by
  rw [formalBranch_adjoint_apply]
  exact slice_mem_wordSupport p W t i y hy

theorem source_mem_after_release (p : WordProfile ι) (W : Submodule ℝ E) (j t : ℕ)
    (ht : t ≤ j) (e : E) : formalTarget (ι := ι) E t e ∈ wordSupport t ((p.prefixReset j).words t) W := by
  intro w hw
  simp [WordProfile.prefixReset, ht] at hw

/-- The exact inverse-reveal span enlargement is absorbed by a reservoir
containing every slice of the newly assigned formal Gaussian. -/
theorem inverse_span_mem_wordSupport {t : ℕ} (S : Finset (Word ι t)) (W : Submodule ℝ E)
    (K : Submodule ℝ (FormalLayer (ι := ι) E t)) (hK : K ≤ wordSupport t S W)
    (g y : FormalLayer (ι := ι) E t) (hg : ∀ w, g w ∈ W)
    (hy : y ∈ K ⊔ Submodule.span ℝ ({g} : Set (FormalLayer (ι := ι) E t))) :
    y ∈ wordSupport t S W := by
  apply (sup_le hK ?_) hy
  apply Submodule.span_le.mpr
  intro x hx
  have he : x = g := by simpa only [Set.mem_singleton_iff] using hx
  subst x
  exact all_coordinates_mem_wordSupport S W g hg

end
end NCConcave16991.BranchOracle
