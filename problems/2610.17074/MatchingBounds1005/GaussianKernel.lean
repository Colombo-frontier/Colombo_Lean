import MatchingBounds1005.LinearGaussianKL
import MatchingBounds1005.KernelKL

/-!
# Measurable Gaussian observation kernels

Kernels are built by pushing an actual independent standard Gaussian through
a jointly measurable observation. Linear Gaussian kernels inherit the proved
singular KL identity, absolute continuity and likelihood integrability.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MatchingBounds1005.GaussianKernel
open GaussianVector LinearGaussianKL

variable {H F : Type*} [MeasurableSpace H] [MeasurableSpace F] {d : ℕ}

def observationKernel (f : H × Vec d → F) (hf : Measurable f) : Kernel H F where
  toFun h := (standardGaussian d).map (fun z => f (h, z))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hp : Measurable (fun h => standardGaussian d (Prod.mk h ⁻¹' (f ⁻¹' s))) :=
      measurable_measure_prodMk_left (hf hs)
    convert hp using 1
    funext h
    have hm : Measurable (fun z : Vec d => f (h, z)) := hf.comp measurable_prodMk_left
    rw [Measure.map_apply hm hs]
    rfl

@[simp] theorem observationKernel_apply (f : H × Vec d → F) (hf : Measurable f) (h : H) :
    observationKernel f hf h = (standardGaussian d).map (fun z => f (h, z)) := rfl

instance observationKernel_markov (f : H × Vec d → F) (hf : Measurable f) :
    IsMarkovKernel (observationKernel f hf) :=
  ⟨fun h => isProbabilityMeasure_map
    (show Measurable (fun z : Vec d => f (h, z)) from hf.comp measurable_prodMk_left).aemeasurable⟩

/-- The kernel transition is exactly the experiment using a fresh independent
Gaussian seed while retaining the complete previous history. -/
theorem observationKernel_compProd (P : Measure H) [SFinite P]
    (f : H × Vec d → F) (hf : Measurable f) :
    P ⊗ₘ observationKernel f hf =
      (P.prod (standardGaussian d)).map (fun p => (p.1, f p)) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (measurable_fst.prodMk hf) hs,
    Measure.prod_apply ((measurable_fst.prodMk hf) hs)]
  apply lintegral_congr
  intro h
  have hm : Measurable (fun z : Vec d => f (h, z)) := hf.comp measurable_prodMk_left
  rw [observationKernel_apply,
    Measure.map_apply hm (measurable_prodMk_left hs)]
  rfl

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [BorelSpace F]

def linearGaussianKernel (B : H → Vec d →L[ℝ] F) (m : H → Vec d) (σ : ℝ)
    (hf : Measurable (fun p : H × Vec d => B p.1 (m p.1 + σ • p.2))) : Kernel H F :=
  observationKernel (fun p => B p.1 (m p.1 + σ • p.2)) hf

instance linearGaussianKernel_markov (B : H → Vec d →L[ℝ] F) (m : H → Vec d) (σ : ℝ)
    (hf : Measurable (fun p : H × Vec d => B p.1 (m p.1 + σ • p.2))) :
    IsMarkovKernel (linearGaussianKernel B m σ hf) := inferInstanceAs
      (IsMarkovKernel (observationKernel (fun p => B p.1 (m p.1 + σ • p.2)) hf))

/-- Exact conditional KL of the actual measurable linear observation
kernels, valid for singular and history-dependent observation maps. -/
theorem linearGaussianKernel_klDiv (B : H → Vec d →L[ℝ] F) (m m' : H → Vec d)
    {σ : ℝ} (hσ : σ ≠ 0)
    (hf : Measurable (fun p : H × Vec d => B p.1 (m p.1 + σ • p.2)))
    (hf' : Measurable (fun p : H × Vec d => B p.1 (m' p.1 + σ • p.2))) (h : H) :
    klDiv (linearGaussianKernel B m σ hf h) (linearGaussianKernel B m' σ hf' h) =
      ENNReal.ofReal (‖(LinearMap.ker (B h))ᗮ.orthogonalProjection (m h - m' h)‖ ^ 2 /
        (2 * σ ^ 2)) :=
  linearObservation_klDiv (B h) (m h) (m' h) hσ

theorem linearGaussianKernel_ac_integrable (B : H → Vec d →L[ℝ] F) (m m' : H → Vec d)
    {σ : ℝ} (hσ : σ ≠ 0)
    (hf : Measurable (fun p : H × Vec d => B p.1 (m p.1 + σ • p.2)))
    (hf' : Measurable (fun p : H × Vec d => B p.1 (m' p.1 + σ • p.2))) (h : H) :
    linearGaussianKernel B m σ hf h ≪ linearGaussianKernel B m' σ hf' h ∧
      Integrable (llr (linearGaussianKernel B m σ hf h) (linearGaussianKernel B m' σ hf' h))
        (linearGaussianKernel B m σ hf h) := by
  apply klDiv_ne_top_iff.mp
  rw [linearGaussianKernel_klDiv B m m' hσ hf hf' h]
  exact ENNReal.ofReal_ne_top

end MatchingBounds1005.GaussianKernel
