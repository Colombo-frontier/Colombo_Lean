import Bilevel.ChiOuterSourceBarrier
import Bilevel.ChiRecursiveJointObjective
import Bilevel.PrimitiveGeometry

/-! The actual outer-plus-recursive objective on a finite Euclidean product,
with dilation only in the inner variables. No block-to-full gradient
comparison is assumed. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerProjection (m : ℕ) : Joint E (Blocks m F) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E (Blocks m F)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E (Blocks m F)).toContinuousLinearMap

def innerProjection (m : ℕ) : Joint E (Blocks m F) →L[ℝ] Blocks m F :=
  (ContinuousLinearMap.snd ℝ E (Blocks m F)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E (Blocks m F)).toContinuousLinearMap

theorem macro_contDiff (M : Node E) (ν : ℝ) (k : ℕ) :
    ContDiff ℝ k (macroValue M.n M.ell M.width ν M.radius M.frame) :=
  ((chain_contDiff M.n M.ell M.width k).comp
    (M.frame.toContinuousLinearMap.adjoint.contDiff.comp (compress_contDiff M.radius k))).add
      (full_bowl_contDiff ν M.radius k)

def jointOuter (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) (d : ℕ)
    (K : ℝ) (z : Joint E (Blocks m F)) : ℝ := outerObjective M ν D ρ R d z.fst (padded (K • z.snd))

theorem jointOuter_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (K : ℝ) (k : ℕ) : ContDiff ℝ k (jointOuter m M ν D ρ R d K) := by
  let X := outerProjection (E:=E) (F:=F) m
  let V := K • innerProjection (E:=E) (F:=F) m
  have hs (i : Fin (M.n+1)) : ContDiff ℝ k (fun z : Joint E (Blocks m F) =>
      (jointRelease m 0 (D 0 [i.val]) (V z)-1)*wrappedResidual M i (X z)+
        jointPayload m D d 0 [i.val] (V z)*wrappedSelector M i (X z)) :=
    ((((jointRelease_contDiff m 0 (D 0 [i.val]) k).comp V.contDiff).sub contDiff_const).mul
      ((wrappedResidual_contDiff M i k).comp X.contDiff)).add
      (((jointPayload_contDiff m D d 0 [i.val] k).comp V.contDiff).mul
        ((wrappedSelector_contDiff M i k).comp X.contDiff))
  exact (((macro_contDiff M ν k).comp X.contDiff).add (ContDiff.sum (fun i _ => hs i))).add
    ((publicValue_joint_contDiff m ρ R d 0 k).comp V.contDiff)

theorem jointOuter_inner_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (x : E) (k : ℕ) :
    ContDiff ℝ k (fun v : Blocks m F => outerObjective M ν D ρ R d x (padded v)) := by
  have hs (i : Fin (M.n+1)) : ContDiff ℝ k (fun v : Blocks m F =>
      (jointRelease m 0 (D 0 [i.val]) v-1)*wrappedResidual M i x+
        jointPayload m D d 0 [i.val] v*wrappedSelector M i x) :=
    (((jointRelease_contDiff m 0 (D 0 [i.val]) k).sub contDiff_const).mul contDiff_const).add
      ((jointPayload_contDiff m D d 0 [i.val] k).mul contDiff_const)
  exact (contDiff_const.add (ContDiff.sum (fun i _ => hs i))).add
    (publicValue_joint_contDiff m ρ R d 0 k)

theorem jointOuter_gradient_of_blocks (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (K : ℝ) (hK : 0<K) (x : E) (v : Blocks (d+1) F) (target : ℝ)
    (hb : (target≤‖fderiv ℝ (fun y => outerObjective M ν D ρ R d y (padded (K • v))) x‖) ∨
      ∃ k : ℕ,k≤d ∧ target/K≤‖fderiv ℝ
        (fun y => outerObjective M ν D ρ R d x (Function.update (padded (K • v)) k y)) (padded (K • v) k)‖) :
    target≤‖gradient (jointOuter (d+1) M ν D ρ R d K) (pack x v)‖ := by
  let G := jointOuter (d+1) M ν D ρ R d K
  have hG := ((jointOuter_contDiff (d+1) M ν D ρ R d K 1).differentiable (by norm_num) (pack x v)).hasGradientAt
  rcases hb with ho|⟨k,hk,hi⟩
  · have hx := PrimitiveGeometry.partial_x hG
    have he : ‖fderiv ℝ (fun y => outerObjective M ν D ρ R d y (padded (K • v))) x‖=
        ‖(gradient G (pack x v)).fst‖ := by
      rw [norm_fderiv_eq_norm_gradient]
      exact congrArg norm hx.gradient
    rw [he] at ho
    exact ho.trans (WithLp.norm_fst_le E (gradient G (pack x v)))
  · let i : Fin (d+1) := ⟨k,by omega⟩
    have hp : padded (K • v) k=(K • v) i := by
      simp only [padded,block,dif_pos (show k<d+1 by omega),PiLp.proj_apply]
      rfl
    rw [hp] at hi
    have hdiff := (jointOuter_inner_contDiff (d+1) M ν D ρ R d x 1).differentiable (by norm_num)
    have hblock := source_block_derivative_le_gradient (outerObjective M ν D ρ R d x) (K • v) i (hdiff _)
    have hinner := hi.trans hblock
    have hy := PrimitiveGeometry.partial_y hG
    have hnorm : ‖gradient (fun w : Blocks (d+1) F => outerObjective M ν D ρ R d x (padded (K • w))) v‖=
        K*‖gradient (fun w : Blocks (d+1) F => outerObjective M ν D ρ R d x (padded w)) (K • v)‖ := by
      rw [gradient_norm_comp_smul _ hdiff,abs_of_pos hK]
    have htarget := (div_le_iff₀ hK).mp hinner
    have he : gradient (fun w : Blocks (d+1) F => outerObjective M ν D ρ R d x (padded (K • w))) v=
        (gradient G (pack x v)).snd := hy.gradient
    have hg : target≤‖(gradient G (pack x v)).snd‖ := by
      rw [← he,hnorm]
      nlinarith only [htarget]
    exact hg.trans (WithLp.norm_snd_le E (gradient G (pack x v)))

end Bilevel.ChiOuter
