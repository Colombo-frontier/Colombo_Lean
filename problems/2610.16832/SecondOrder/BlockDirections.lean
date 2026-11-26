import SecondOrder.DirectionalCurvature

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev HomogeneousBlocks (J E : Type*) := PiLp 2 (fun _ : J => E)

def blockProj (j : J) : HomogeneousBlocks J E →L[ℝ] E :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : J => E) j

@[simp] theorem blockProj_apply (j : J) (x : HomogeneousBlocks J E) : blockProj j x = x j := rfl

def blockUnit (j : J) (v : E) : HomogeneousBlocks J E :=
  (WithLp.equiv 2 (J → E)).symm (Pi.single j v)

@[simp] theorem blockUnit_apply (j : J) (v : E) (i : J) : blockUnit j v i = if i=j then v else 0 := by
  by_cases h : i=j
  · subst i; simp [blockUnit]
  · simp [blockUnit, h]

@[simp] theorem blockUnit_norm (j : J) (v : E) : ‖blockUnit j v‖ = ‖v‖ :=
  PiLp.norm_equiv_symm_single 2 (fun _ : J => E) j v

theorem secondQuadratic_block {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (i j : J) (x : HomogeneousBlocks J E) (v : E) :
    secondQuadratic (fun y : HomogeneousBlocks J E => f (y i)) x (blockUnit j v) =
      if i=j then secondQuadratic f (x i) v else 0 := by
  change secondQuadratic (f ∘ blockProj i) x (blockUnit j v) = _
  rw [secondQuadratic_comp_linear hf, blockProj_apply, blockProj_apply, blockUnit_apply]
  split_ifs <;> simp

theorem fderiv_block {f : E → ℝ} (hf : Differentiable ℝ f)
    (i j : J) (x : HomogeneousBlocks J E) (v : E) :
    fderiv ℝ (fun y : HomogeneousBlocks J E => f (y i)) x (blockUnit j v) =
      if i=j then fderiv ℝ f (x i) v else 0 := by
  change fderiv ℝ (f ∘ blockProj i) x (blockUnit j v) = _
  rw [fderiv_comp x (hf _) (blockProj i).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv,
    blockProj_apply, blockUnit_apply]
  split_ifs <;> simp

/-- A direction in one block sees only the matching factor of a two-block product. -/
theorem secondQuadratic_two_blocks {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (i j k : J) (hij : i ≠ j) (x : HomogeneousBlocks J E) (v : E) :
    secondQuadratic (fun y : HomogeneousBlocks J E => f (y i)*g (y j)) x (blockUnit k v) =
      (if i=k then g (x j)*secondQuadratic f (x i) v else 0)+
      (if j=k then f (x i)*secondQuadratic g (x j) v else 0) := by
  have hf' : ContDiff ℝ 2 (fun y : HomogeneousBlocks J E => f (y i)) := hf.comp (blockProj (E := E) i).contDiff
  have hg' : ContDiff ℝ 2 (fun y : HomogeneousBlocks J E => g (y j)) := hg.comp (blockProj (E := E) j).contDiff
  rw [secondQuadratic_mul hf' hg', secondQuadratic_block hf, secondQuadratic_block hg,
    fderiv_block (hf.differentiable (by norm_num)), fderiv_block (hg.differentiable (by norm_num))]
  by_cases hi : i=k
  · subst k; simp [hij, hij.symm]
  · by_cases hj : j=k
    · subst k; simp [hi]
    · simp [hi, hj]

end
end SecondOrder
