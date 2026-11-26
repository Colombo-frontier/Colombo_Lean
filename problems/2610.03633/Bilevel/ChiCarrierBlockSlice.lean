import Bilevel.ChiCarrierJoint
import Bilevel.GradientJetBounds

/-! Isometric insertion into the actual finite Hilbert block product and
comparison of an actual source block derivative with the full gradient. -/
noncomputable section
namespace Bilevel.ChiCarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

instance blocks_complete (m : ℕ) : CompleteSpace (Blocks m E) :=
  (completeSpace_congr (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => E)).isUniformEmbedding).mpr inferInstance

def insertion (m : ℕ) (i : Fin m) : E →ₗᵢ[ℝ] Blocks m E where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin m → E)).symm.toLinearMap.comp (LinearMap.single ℝ (fun _ => E) i)
  norm_map' v := PiLp.norm_equiv_symm_single 2 (fun _ : Fin m => E) i v

omit [CompleteSpace E] in
theorem insertion_apply (m : ℕ) (i k : Fin m) (v : E) :
    insertion m i v k=if k=i then v else 0 := by
  simp [insertion,Pi.single_apply]

def replaceBlock {m : ℕ} (x : Blocks m E) (i : Fin m) (v : E) : Blocks m E :=
  x+insertion m i (v-x i)

omit [CompleteSpace E] in
theorem replaceBlock_self {m : ℕ} (x : Blocks m E) (i : Fin m) : replaceBlock x i (x i)=x := by
  simp [replaceBlock]

omit [CompleteSpace E] in
theorem padded_replaceBlock {m : ℕ} (x : Blocks m E) (i : Fin m) (v : E) :
    padded (replaceBlock x i v)=Function.update (padded x) i.val v := by
  funext j
  by_cases hj : j<m
  · by_cases hji : j=i.val
    · subst j
      simp [padded,block,replaceBlock,insertion_apply]
    · have hfin : (⟨j,hj⟩:Fin m)≠i := by intro he;exact hji (congrArg Fin.val he)
      simp [padded,block,hj,replaceBlock,PiLp.add_apply,insertion_apply,hfin,
        Function.update_of_ne hji]
  · have hji : j≠i.val := by intro he;subst j;exact hj i.isLt
    simp [padded,block,hj,Function.update_of_ne hji]

omit [CompleteSpace E] in
theorem replaceBlock_hasFDerivAt {m : ℕ} (x : Blocks m E) (i : Fin m) (v : E) :
    HasFDerivAt (replaceBlock x i) (insertion m i).toContinuousLinearMap v := by
  have hh := (((insertion (E:=E) m i).toContinuousLinearMap.hasFDerivAt).comp v
    ((hasFDerivAt_id v).sub_const (x i))).const_add x
  simpa only [replaceBlock,ContinuousLinearMap.comp_id] using hh

/-- This compares derivatives of the actual zero-padded source function;
there is no assumed equality between block and joint derivatives. -/
theorem source_block_derivative_le_gradient {m : ℕ} (F : (ℕ → E) → ℝ)
    (x : Blocks m E) (i : Fin m)
    (hF : DifferentiableAt ℝ (fun y : Blocks m E => F (padded y)) x) :
    ‖fderiv ℝ (fun v => F (Function.update (padded x) i.val v)) (x i)‖≤
      ‖gradient (fun y : Blocks m E => F (padded y)) x‖ := by
  have he : (fun v => F (Function.update (padded x) i.val v))=
      (fun y : Blocks m E => F (padded y)) ∘ replaceBlock x i := by
    funext v
    rw [Function.comp_apply,padded_replaceBlock]
  have hFc : HasFDerivAt (fun y : Blocks m E => F (padded y))
      (fderiv ℝ (fun y : Blocks m E => F (padded y)) x) (replaceBlock x i (x i)) := by
    simpa only [replaceBlock_self] using hF.hasFDerivAt
  have hcomp := hFc.comp (x i) (replaceBlock_hasFDerivAt x i (x i))
  rw [he]
  have hcomp' : HasFDerivAt ((fun y : Blocks m E => F (padded y)) ∘ replaceBlock x i)
      ((fderiv ℝ (fun y : Blocks m E => F (padded y)) x).comp (insertion m i).toContinuousLinearMap) (x i) := by
    exact hcomp
  rw [hcomp'.fderiv,GradientJetBounds.gradient_norm_eq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (insertion (E:=E) m i).norm_toContinuousLinearMap_le (norm_nonneg _)).trans_eq (mul_one _))

end Bilevel.ChiCarrier
