import Bilevel.ChiRecursiveObjective
import Bilevel.ChiCarrierBlockSlice
import Bilevel.PublicRadialExtension

/-! The actual finite Hilbert-product objective and conversion of a proved
block barrier to its full gradient, including the source K amplification. -/
noncomputable section
namespace Bilevel.ChiRecursive
open ChiCarrier RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem full_bowl_contDiff (ρ R : ℝ) (k : ℕ) : ContDiff ℝ k (bowl (E:=E) ρ R) := by
  convert contDiff_const.mul (PublicRadialExtension.bowl_contDiff (E:=E) R k) using 1
  funext v
  simp only [bowl,one_mul]
  ring

def jointObjective (m : ℕ) (D : Geometry E) (ρ R : ℕ → ℝ) (d j : ℕ)
    (I : List ℕ) (w Rp : ℝ) (x : Blocks m E) : ℝ := objective D ρ R d j I w Rp (padded x)

omit [CompleteSpace E] in
theorem publicValue_joint_contDiff (m : ℕ) (ρ R : ℕ → ℝ) (d j k : ℕ) :
    ContDiff ℝ k (fun x : Blocks m E => publicValue ρ R d j (padded x)) := by
  induction d generalizing j with
  | zero => exact (full_bowl_contDiff (ρ j) (R j) k).comp (block (E:=E) m j).contDiff
  | succ d ih => exact ((full_bowl_contDiff (ρ j) (R j) k).comp (block (E:=E) m j).contDiff).add (ih (j+1))

theorem jointObjective_contDiff (m : ℕ) (D : Geometry E) (ρ R : ℕ → ℝ) (d j : ℕ)
    (I : List ℕ) (w Rp : ℝ) (k : ℕ) : ContDiff ℝ k (jointObjective m D ρ R d j I w Rp) :=
  ((publicValue_joint_contDiff m ρ R d j k).add
    (contDiff_const.mul (jointPayload_contDiff m D d j I k))).add
    (contDiff_const.mul (jointRelease_contDiff m j (D j I) k))

theorem jointObjective_gradient_of_block_barrier (D : Geometry E) (ρ R : ℕ → ℝ)
    (d : ℕ) (I : List ℕ) (w Rp : ℝ) (x : Blocks (d+1) E) {target : ℝ}
    (hb : ∃ k : ℕ,k≤d ∧ target≤
      ‖fderiv ℝ (fun v => objective D ρ R d 0 I w Rp (Function.update (padded x) k v)) (padded x k)‖) :
    target≤‖gradient (jointObjective (d+1) D ρ R d 0 I w Rp) x‖ := by
  obtain ⟨k,hk,hbound⟩ := hb
  let i : Fin (d+1) := ⟨k,by omega⟩
  have hp : padded x k=x i := by simp only [padded,block,dif_pos (show k<d+1 by omega),PiLp.proj_apply];rfl
  rw [hp] at hbound
  exact hbound.trans (source_block_derivative_le_gradient (objective D ρ R d 0 I w Rp) x i
    ((jointObjective_contDiff (d+1) D ρ R d 0 I w Rp 1).differentiable (by norm_num) x))

theorem gradient_norm_comp_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (f : F → ℝ) (hf : Differentiable ℝ f) (K : ℝ) (x : F) :
    ‖gradient (fun v => f (K • v)) x‖=|K| * ‖gradient f (K • x)‖ := by
  have hg := (hf (K • x)).hasGradientAt
  have hc := hg.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul K)
  have hh : HasGradientAt (fun v => f (K • v)) (K • gradient f (K • x)) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hc using 1
    ext v
    simp [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right]
  rw [hh.gradient,norm_smul,Real.norm_eq_abs]

theorem amplified_jointObjective_gradient (D : Geometry E) (ρ R : ℕ → ℝ)
    (d : ℕ) (I : List ℕ) (w Rp K : ℝ) (hK : 0≤K) (x : Blocks (d+1) E) {target : ℝ}
    (hb : ∃ k : ℕ,k≤d ∧ target≤
      ‖fderiv ℝ (fun v => objective D ρ R d 0 I w Rp (Function.update (padded (K • x)) k v))
        (padded (K • x) k)‖) :
    K*target≤‖gradient (fun v => jointObjective (d+1) D ρ R d 0 I w Rp (K • v)) x‖ := by
  rw [gradient_norm_comp_smul _ ((jointObjective_contDiff (d+1) D ρ R d 0 I w Rp 1).differentiable (by norm_num)),
    abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left (jointObjective_gradient_of_block_barrier D ρ R d I w Rp (K • x) hb) hK

end Bilevel.ChiRecursive
