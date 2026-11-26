import SampleReuse.RandomFrameRadialJet
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
namespace SampleReuse.RandomFrame

open SecondOrder
open scoped InnerProductSpace

variable {P E Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem contDiff_parameter_fderiv {f : P → E → Y} {m n : WithTop ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) (hmn : m+1 ≤ n) :
    ContDiff ℝ m (fun p : P × E => fderiv ℝ (f p.1) p.2) := by
  have hh : ContDiff ℝ n (fun z : (P × E) × E => f z.1.1 z.2) :=
    hf.comp ((contDiff_fst.fst).prodMk contDiff_snd)
  exact hh.fderiv contDiff_snd hmn

section Inner
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem contDiff_parameter_gradient {f : P → H → ℝ} {m n : WithTop ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) (hmn : m+1 ≤ n) :
    ContDiff ℝ m (fun p : P × H => gradient (f p.1) p.2) :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    (contDiff_parameter_fderiv hf hmn)

theorem continuous_parameter_fullJet {f : P → H → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    Continuous (fun p : P × H => fullJet (f p.1) p.2) := by
  have hg : ContDiff ℝ 1 (fun p : P × H => gradient (f p.1) p.2) :=
    contDiff_parameter_gradient hf (by norm_num)
  have hH : ContDiff ℝ 0 (fun p : P × H => fderiv ℝ (gradient (f p.1)) p.2) :=
    contDiff_parameter_fderiv (f := fun a x => gradient (f a) x)
      (m := 0) (n := 1) hg (by norm_num)
  exact hf.continuous.prodMk (hg.continuous.prodMk hH.continuous)

end Inner

/-- A scalar prefix formula uses exactly the first `n+1` ambient vectors.
The sum is indexed by the original chain length so it matches truncation
without extending an incomplete frame or choosing a measurable completion. -/
def prefixCurvatureCore {d : ℕ} (T n : ℕ) (A β : ℝ)
    (z : Fin (n+1) → Point d) (x : Point d) : ℝ :=
  A * (curvatureGate 1 * curvaturePotential (β * ⟪z 0, x⟫_ℝ) +
    ∑ i : Fin T, if hi : i.val+1 < n+1 then
      curvatureGate (β * ⟪z ⟨i.val, by omega⟩, x⟫_ℝ) *
        curvaturePotential (β * ⟪z ⟨i.val+1, hi⟩, x⟫_ℝ) else 0)

theorem prefixCurvatureCore_contDiff {d : ℕ} (T n : ℕ) (A β : ℝ) (k : ℕ∞) :
    ContDiff ℝ k (Function.uncurry (prefixCurvatureCore (d := d) T n A β)) := by
  have hc (i : Fin (n+1)) :
      ContDiff ℝ k (fun p : (Fin (n+1) → Point d) × Point d => β * ⟪p.1 i, p.2⟫_ℝ) :=
    contDiff_const.mul (((contDiff_apply ℝ (Point d) i).comp contDiff_fst).inner ℝ contDiff_snd)
  apply ContDiff.mul contDiff_const
  apply ContDiff.add
  · exact contDiff_const.mul ((curvaturePotential_contDiff k).comp (hc 0))
  · apply ContDiff.sum
    intro i _
    by_cases hi : i.val+1 < n+1
    · simp only [dif_pos hi]
      exact ((curvatureGate_contDiff k).comp (hc ⟨i.val, by omega⟩)).mul
        ((curvaturePotential_contDiff k).comp (hc ⟨i.val+1, hi⟩))
    · simp only [dif_neg hi]
      exact contDiff_const

theorem curvatureFrameMap_coordinate {d T : ℕ}
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (β : ℝ) (x : Point d) (i : Fin (T+1)) :
    curvatureFrameMap U β x i = β * ⟪U (blockUnit i (1:ℝ)), x⟫_ℝ := by
  have hi := U.toContinuousLinearMap.adjoint_inner_right (blockUnit i (1:ℝ)) x
  have hs (v : Point (T+1)) : ⟪blockUnit i (1:ℝ), v⟫_ℝ = v i := by
    have he : blockUnit i (1:ℝ) = EuclideanSpace.single i (1:ℝ) := by
      ext j
      by_cases hij : j = i
      · simp only [blockUnit_apply, EuclideanSpace.single_apply, if_pos hij]
      · simp only [blockUnit_apply, EuclideanSpace.single_apply, if_neg hij]
    rw [he]
    simpa only [map_one, one_mul] using EuclideanSpace.inner_single_left i (1:ℝ) v
  rw [hs] at hi
  simpa only [curvatureFrameMap, curvatureFrameProjection, ContinuousLinearMap.smul_apply,
    PiLp.smul_apply, smul_eq_mul] using congrArg (fun a : ℝ => β*a) hi

theorem truncatedFrameCore_eq_prefix {d T n : ℕ}
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β : ℝ) (hn : n ≤ T) :
    truncatedFrameCore U A β (n+1) =
      prefixCurvatureCore T n A β (fun i => U (blockUnit (Fin.castLE (by omega) i) (1:ℝ))) := by
  funext x
  unfold truncatedFrameCore scalarLinearScaling truncatedCurvatureChain prefixCurvatureCore
  congr 2
  · rw [curvatureFrameMap_coordinate]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val+1 < n+1
    · simp only [if_pos hi, dif_pos hi, curvatureFrameMap_coordinate]
      rfl
    · simp only [if_neg hi, dif_neg hi]

def prefixRadialLoss {d : ℕ} (T n : ℕ) (A β b R : ℝ)
    (z : Fin (n+1) → Point d) : Point d → ℝ :=
  radialGlobalization (prefixCurvatureCore T n A β z) b R

theorem prefixRadialLoss_contDiff {d : ℕ} (T n : ℕ) (A β b : ℝ)
    {R : ℝ} (hR : 0 < R) (k : ℕ∞) :
    ContDiff ℝ k (Function.uncurry (prefixRadialLoss (d := d) T n A β b R)) :=
  (((radialCutoffLoss_contDiff hR k).comp contDiff_snd).mul
    (prefixCurvatureCore_contDiff T n A β k)).add
      ((radialWallLoss_contDiff b hR k).comp contDiff_snd)

def prefixRadialReply {d : ℕ} (T n : ℕ) (A β b R : ℝ)
    (z : Fin (n+1) → Point d) : Point d → ℝ × Point d × (Point d →L[ℝ] Point d) :=
  fullJet (prefixRadialLoss T n A β b R z)

theorem measurable_prefixRadialReply {d : ℕ} (T n : ℕ) (A β b : ℝ)
    {R : ℝ} (hR : 0 < R) :
    Measurable (Function.uncurry (prefixRadialReply (d := d) T n A β b R)) := by
  have hc := continuous_parameter_fullJet (prefixRadialLoss_contDiff (d := d) T n A β b hR 2)
  exact hc.fst.measurable.prodMk (hc.snd.fst.measurable.prodMk hc.snd.snd.measurable)

theorem truncatedRadialFrame_eq_prefix {d T n : ℕ}
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b R : ℝ) (hn : n ≤ T) :
    truncatedRadialFrame U A β b R (n+1) =
      prefixRadialLoss T n A β b R (fun i => U (blockUnit (Fin.castLE (by omega) i) (1:ℝ))) := by
  rw [truncatedRadialFrame, truncatedFrameCore_eq_prefix U A β hn]
  rfl

end SampleReuse.RandomFrame
