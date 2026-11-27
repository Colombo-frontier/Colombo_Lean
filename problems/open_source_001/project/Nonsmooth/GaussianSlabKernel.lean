import Nonsmooth.GaussianSlabCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def gaussianSlabKernel (u : E) : Kernel (ℝ × ℝ) E :=
  parametricEventKernel (gaussianAmbientRowLaw E)
    {p : (ℝ × ℝ) × E | p.1.1 ≤ ⟪p.2, u⟫_ℝ ∧ ⟪p.2, u⟫_ℝ ≤ p.1.2}
    ((measurableSet_le measurable_fst.fst (continuous_snd.inner continuous_const).measurable).inter
      (measurableSet_le (continuous_snd.inner continuous_const).measurable measurable_fst.snd))

instance gaussianSlabKernel_markov (u : E) : IsMarkovKernel (gaussianSlabKernel u) := by
  unfold gaussianSlabKernel
  infer_instance

theorem gaussianSlabKernel_apply (u : E) (a b : ℝ)
    (hp : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} ≠ 0) :
    gaussianSlabKernel u (a, b) =
      (gaussianAmbientRowLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}] :=
  parametricEventKernel_apply _ _ _ _ hp

theorem gaussianSlabKernel_apply_zero (u : E) (a b : ℝ)
    (hp : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0) :
    gaussianSlabKernel u (a, b) = gaussianAmbientRowLaw E := by
  change (if gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0 then _ else _) = _
  rw [if_pos hp]

theorem gaussianSlabKernel_absolutelyContinuous (u : E) (a b : ℝ) :
    gaussianSlabKernel u (a, b) ≪ gaussianAmbientRowLaw E :=
  parametricEventKernel_absolutelyContinuous _ _ _ _

theorem gaussianSlabKernel_covariance {u : E} (hu : ‖u‖ = 1) (a b : ℝ) (v : E) :
    variance (fun z : E => ⟪v, z⟫_ℝ) (gaussianSlabKernel u (a, b)) ≤
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  by_cases hp : gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0
  · rw [gaussianSlabKernel_apply_zero u a b hp]
    exact (variance_le_expectation_sq (gaussianAmbientRowLaw_memLp.const_inner v).aestronglyMeasurable).trans
      (gaussianAmbientRow_inner_second_le v)
  · rw [gaussianSlabKernel_apply u a b hp]
    exact gaussianAmbientRow_slab_covariance hu a b v

theorem gaussianSlabKernel_neg (u : E) (a b : ℝ) :
    gaussianSlabKernel (-u) (-b, -a) = gaussianSlabKernel u (a, b) := by
  have he : {z : E | -b ≤ ⟪z, -u⟫_ℝ ∧ ⟪z, -u⟫_ℝ ≤ -a} =
      {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} := by
    ext z
    simp only [mem_setOf_eq, inner_neg_right]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  change (if gaussianAmbientRowLaw E {z : E | -b ≤ ⟪z, -u⟫_ℝ ∧ ⟪z, -u⟫_ℝ ≤ -a} = 0
    then gaussianAmbientRowLaw E else (gaussianAmbientRowLaw E)[|{z : E | -b ≤ ⟪z, -u⟫_ℝ ∧ ⟪z, -u⟫_ℝ ≤ -a}]) =
    (if gaussianAmbientRowLaw E {z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b} = 0
    then gaussianAmbientRowLaw E else (gaussianAmbientRowLaw E)[|{z : E | a ≤ ⟪z, u⟫_ℝ ∧ ⟪z, u⟫_ℝ ≤ b}])
  rw [he]

theorem gaussianSlabKernel_hyperplane_zero (u : E) (a b : ℝ) {v : E} (hv : v ≠ 0) (t : ℝ) :
    gaussianSlabKernel u (a, b) {z : E | ⟪z, v⟫_ℝ = t} = 0 := by
  apply gaussianSlabKernel_absolutelyContinuous u a b
  simpa only [real_inner_comm v] using gaussianAmbientRow_hyperplane_zero hv t

end
end Nonsmooth
