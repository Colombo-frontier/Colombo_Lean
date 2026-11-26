import SampleReuse.CurvaturePotential
import SecondOrder.BlockDirections

open SecondOrder
open scoped BigOperators InnerProductSpace Classical

namespace SampleReuse
noncomputable section

/-- T+1 coordinates, matching q_(T+1) in the source. -/
def deterministicCurvatureChain (T : ℕ) (x : Point (T+1)) : ℝ :=
  curvatureGate 1*curvaturePotential (x 0) +
    ∑ i : Fin T, curvatureGate (x i.castSucc)*curvaturePotential (x i.succ)

theorem deterministicCurvatureChain_contDiff (T : ℕ) (n : ℕ∞) :
    ContDiff ℝ n (deterministicCurvatureChain T) := by
  apply ContDiff.add
  · exact contDiff_const.mul ((curvaturePotential_contDiff n).comp
      (blockProj (E := ℝ) (0 : Fin (T+1))).contDiff)
  · apply ContDiff.sum
    intro i _
    exact ((curvatureGate_contDiff n).comp (blockProj (E := ℝ) i.castSucc).contDiff).mul
      ((curvaturePotential_contDiff n).comp (blockProj (E := ℝ) i.succ).contDiff)

theorem scalar_secondQuadratic {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    secondQuadratic f x 1 = deriv (deriv f) x := by
  rw [secondQuadratic_eq_inner hf]
  have he : gradient f = deriv f := funext (fun y => gradient_eq_deriv' (g := f) (u := y))
  rw [he, fderiv_deriv]
  simp

theorem deterministicCurvatureChain_diagonal (T : ℕ) (x : Point (T+1)) (j : Fin (T+1)) :
    secondQuadratic (deterministicCurvatureChain T) x (blockUnit j (1:ℝ)) =
      curvatureGate 1 * (if (0 : Fin (T+1)) = j then deriv (deriv curvaturePotential) (x 0) else 0) +
      ∑ i : Fin T,
        ((if i.castSucc = j then curvaturePotential (x i.succ)*
          deriv (deriv curvatureGate) (x i.castSucc) else 0) +
         (if i.succ = j then curvatureGate (x i.castSucc)*
          deriv (deriv curvaturePotential) (x i.succ) else 0)) := by
  have hg : ContDiff ℝ 2 curvatureGate := curvatureGate_contDiff 2
  have hb : ContDiff ℝ 2 curvaturePotential := curvaturePotential_contDiff 2
  have hhead : ContDiff ℝ 2 (fun y : Point (T+1) => curvaturePotential (y 0)) :=
    hb.comp (blockProj (E := ℝ) (0 : Fin (T+1))).contDiff
  have hlink (i : Fin T) : ContDiff ℝ 2 (fun y : Point (T+1) =>
      curvatureGate (y i.castSucc)*curvaturePotential (y i.succ)) :=
    (hg.comp (blockProj (E := ℝ) i.castSucc).contDiff).mul
      (hb.comp (blockProj (E := ℝ) i.succ).contDiff)
  unfold deterministicCurvatureChain
  rw [secondQuadratic_add (contDiff_const.mul hhead) (ContDiff.sum (fun i _ => hlink i)),
    secondQuadratic_const_mul hhead, secondQuadratic_block hb,
    secondQuadratic_sum _ hlink]
  congr 1
  · split_ifs <;> simp only [scalar_secondQuadratic hb]
  · apply Finset.sum_congr rfl
    intro i _
    have hne : i.castSucc ≠ i.succ := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val+1 at hv
      omega
    rw [secondQuadratic_two_blocks hg hb i.castSucc i.succ j hne]
    split_ifs <;> simp only [scalar_secondQuadratic hg, scalar_secondQuadratic hb]

theorem deterministicCurvatureChain_zero (T : ℕ) : deterministicCurvatureChain T 0 = 0 := by
  simp [deterministicCurvatureChain, curvaturePotential_zero]

theorem deterministicCurvatureChain_range (T : ℕ) (x : Point (T+1)) :
    -4*(T+1:ℕ) ≤ deterministicCurvatureChain T x ∧ deterministicCurvatureChain T x ≤ 0 := by
  have hprod (u v : ℝ) : -4 ≤ curvatureGate u*curvaturePotential v ∧
      curvatureGate u*curvaturePotential v ≤ 0 := by
    have hg := curvatureGate_nonneg u
    have hg1 := curvatureGate_le_one u
    have hb := curvaturePotential_range v
    constructor
    · nlinarith [mul_nonneg hg (show 0 ≤ curvaturePotential v+4 by linarith)]
    · exact mul_nonpos_of_nonneg_of_nonpos hg hb.2
  have hhead := hprod 1 (x 0)
  have hlo := Finset.sum_le_sum (fun (i : Fin T) (_ : i ∈ Finset.univ) => (hprod (x i.castSucc) (x i.succ)).1)
  have hhi := Finset.sum_le_sum (fun (i : Fin T) (_ : i ∈ Finset.univ) => (hprod (x i.castSucc) (x i.succ)).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_const_zero] at hlo hhi
  unfold deterministicCurvatureChain
  push_cast
  constructor <;> linarith

end
end SampleReuse
