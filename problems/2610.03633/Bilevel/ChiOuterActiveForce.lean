import Bilevel.ChiCarrierActiveForce
import Bilevel.ChiOuterFineLocality

/-! The actual one-sided macro selector preserves the terminal pre-wrapper
fine-force bound. Neither outer stage count nor recursion depth appears. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule SmallGapLiftSupport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerFineLatentForce (m : ℕ) (M : Node E) (D : Geometry F) (P : ChiFine.Parameters)
    (lambdaExt s : ℝ) (d : ℕ) (a : E) (x : Blocks m F) : F :=
  ∑ i : Fin (M.n+1),wrappedSelector M i a • selectedFineLatentForce m D P lambdaExt s d 0 [i.val] x

theorem outerCoupling_terminal_force {m : ℕ} (M : Node E) (D : Geometry F) (P : ChiFine.Parameters)
    (d : ℕ) (t : Fin m) (ht : t.val=d) (lambdaExt s R : ℝ) (hR : 0<R)
    (hell : ∀ Q,(D d Q).ell=P.ℓ) (hwidth : ∀ Q,(D d Q).width=P.β)
    (hRnode : ∀ Q,(D d Q).radius=R) (a : E) (x : Blocks m F) :
    (gradient (fun y => lambdaExt*outerCoupling m M D d P.c P.θ
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) s 0)) x) t=
      RadialWrapper.compressDerivative R (x t) (outerFineLatentForce m M D P lambdaExt s d a x) := by
  let leaf := fun i : Fin (M.n+1) => fun y : Blocks m F =>
    lambdaExt*selectedCoupling m D d 0 [i.val] P.c P.θ (CompensatedMean.pack (Blocks m F) y s 0)
  have hleaf (i : Fin (M.n+1)) : ContDiff ℝ 3 (leaf i) :=
    contDiff_const.mul (selectedCoupling_slice_contDiff m D d 0 [i.val] P.c P.θ s)
  have he : (fun y => lambdaExt*outerCoupling m M D d P.c P.θ
      (CompensatedMean.pack (Joint E (Blocks m F)) (pack a y) s 0))=
      (fun y => ∑ i : Fin (M.n+1),leaf i y*wrappedSelector M i a) := by
    funext y
    rw [outerCoupling_inner_eq,outerSelected_inner_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [leaf]
    ring
  rw [he,ChiFine.finite_weighted_gradient Finset.univ leaf hleaf]
  let ev : Blocks m F →L[ℝ] F := PiLp.proj 2 (fun _ : Fin m => F) t
  change ev (∑ i : Fin (M.n+1),wrappedSelector M i a • gradient (leaf i) x)=_
  simp only [map_sum,map_smul]
  unfold outerFineLatentForce
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1
  exact selectedCoupling_terminal_force D P d 0 [i.val] t (by omega) lambdaExt s R hR
    (by simpa only [zero_add] using hell) (by simpa only [zero_add] using hwidth)
    (by simpa only [zero_add] using hRnode) x

theorem outerFineLatentForce_bound : ∃ B : ℝ,1≤B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (m : ℕ) (M : Node E) (D : Geometry F) (P : ChiFine.Parameters) (lambdaExt : ℝ),0≤lambdaExt →
      ∀ (s : ℝ) (d : ℕ) (a : E) (x : Blocks m F),
      ‖outerFineLatentForce m M D P lambdaExt s d a x‖≤
        2*C*B*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ := by
  obtain ⟨B,hB,hforce⟩ := selectedFineLatentForce_bound
  refine ⟨B,hB,fun E F _ _ _ _ _ _ m M D P lambdaExt hlambda s d a x => ?_⟩
  let H := 2*C*B*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ
  have hH : 0≤H := by
    have := C_pos
    have := P.c_pos
    have := P.ell_nonneg
    positivity
  unfold outerFineLatentForce
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin (M.n+1),wrappedSelector M i a*H := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (wrappedSelector_range M i a).1]
      exact mul_le_mul_of_nonneg_left (hforce F m D P lambdaExt hlambda s d 0 [i.val] x)
        (wrappedSelector_range M i a).1
    _ = (∑ i : Fin (M.n+1),wrappedSelector M i a)*H := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*H := mul_le_mul_of_nonneg_right (wrappedSelector_sum M a) hH
    _ = _ := one_mul H

end Bilevel.ChiOuter
