import RandomizedFO2003.GradientCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RandomizedFO2003.Cascade

open Calculus
open scoped BigOperators

abbrev BlockProduct (N : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin N => E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def blockProjection (N : ℕ) (i : Fin N) : BlockProduct N E →L[ℝ] E :=
  PiLp.proj 2 (fun _ : Fin N => E) i

@[simp] theorem blockProjection_apply {N : ℕ} (i : Fin N) (z : BlockProduct N E) :
    blockProjection N i z = z i := rfl

noncomputable def blockEmbed {N : ℕ} (i : Fin N) (v : E) : BlockProduct N E :=
  (WithLp.equiv 2 (Fin N → E)).symm (Pi.single i v)

omit [InnerProductSpace ℝ E] in
@[simp] theorem blockEmbed_apply {N : ℕ} (i j : Fin N) (v : E) :
    blockEmbed i v j = if j = i then v else 0 := by simp [blockEmbed, Pi.single_apply]

omit [InnerProductSpace ℝ E] in
@[simp] theorem blockEmbed_norm {N : ℕ} (i : Fin N) (v : E) : ‖blockEmbed i v‖ = ‖v‖ :=
  PiLp.norm_equiv_symm_single 2 (fun _ : Fin N => E) i v

@[simp] theorem inner_blockEmbed_left {N : ℕ} (i : Fin N) (v : E) (z : BlockProduct N E) :
    inner (𝕜 := ℝ) (blockEmbed i v) z = inner (𝕜 := ℝ) v (z i) := by
  rw [PiLp.inner_apply]
  calc
    _ = inner (𝕜 := ℝ) (blockEmbed i v i) (z i) := by
      apply Finset.sum_eq_single i
      · intro j _hj hji
        rw [blockEmbed_apply, if_neg hji, inner_zero_left]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    _ = _ := by simp

omit [InnerProductSpace ℝ E] in
theorem block_norm_le {N : ℕ} (z : BlockProduct N E) (i : Fin N) : ‖z i‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z i

@[simp] theorem blockEmbed_smul {N : ℕ} (i : Fin N) (c : ℝ) (v : E) :
    blockEmbed i (c • v) = c • blockEmbed i v := by
  ext j
  simp only [blockEmbed_apply, PiLp.smul_apply]
  split_ifs <;> simp

omit [InnerProductSpace ℝ E] in
@[simp] theorem blockEmbed_zero {N : ℕ} (i : Fin N) : blockEmbed i (0 : E) = 0 := by
  ext j
  simp [blockEmbed_apply]

theorem block_sum_apply {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → BlockProduct N E) (i : Fin N) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i := map_sum (blockProjection N i) f s

theorem sum_blockEmbed_apply {N : ℕ} (f : Fin N → E) (i : Fin N) :
    (∑ j : Fin N, blockEmbed j (f j)) i = f i := by
  simp [block_sum_apply, blockEmbed_apply]

theorem sum_blockEmbed_succ_apply {N : ℕ} (f : Fin N → E) (i : Fin (N + 1)) :
    (∑ j : Fin N, blockEmbed j.succ (f j)) i = Fin.cases 0 f i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [block_sum_apply, blockEmbed_apply, eq_comm, Fin.succ_ne_zero]
  · simp [block_sum_apply, blockEmbed_apply]

theorem sum_blockEmbed_castSucc_apply {N : ℕ} (f : Fin N → E) (i : Fin (N + 1)) :
    (∑ j : Fin N, blockEmbed j.castSucc (f j)) i = Fin.lastCases 0 f i := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [block_sum_apply, blockEmbed_apply, eq_comm, Fin.castSucc_ne_last]
  · simp [block_sum_apply, blockEmbed_apply]

variable [CompleteSpace E]

instance blockProduct_complete (N : ℕ) : CompleteSpace (BlockProduct N E) :=
  inferInstanceAs (CompleteSpace (Fin N → E))

@[simp] theorem blockProjection_adjoint {N : ℕ} (i : Fin N) (v : E) :
    (blockProjection N i).adjoint v = blockEmbed i v := by
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left, inner_blockEmbed_left, blockProjection_apply]

theorem hasGradientAt_block {N : ℕ} (i : Fin N) {f : E → ℝ} {g : E} (z : BlockProduct N E)
    (hf : HasGradientAt f g (z i)) :
    HasGradientAt (fun y : BlockProduct N E => f (y i)) (blockEmbed i g) z := by
  simpa only [blockProjection_adjoint] using hasGradientAt_comp_linear (blockProjection N i) z hf

end RandomizedFO2003.Cascade
