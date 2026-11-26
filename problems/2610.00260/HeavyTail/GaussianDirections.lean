import HeavyTail.GaussianEstimates
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection

/-! A concrete standard Gaussian law in finite-dimensional real Hilbert space,
with exact directional second and fourth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace Topology
namespace HeavyTail.GaussianEstimates

def gaussianVector (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance gaussianVector_probability (d : ℕ) : IsProbabilityMeasure (gaussianVector d) := by
  unfold gaussianVector
  infer_instance

theorem gaussianVector_exp_linear (d : ℕ) (t : Fin d → ℝ) :
    (∫ v, Real.exp (∑ i, t i * v i) ∂gaussianVector d) =
      Real.exp ((∑ i, (t i) ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  have hp : (∫ v : Fin d → ℝ, ∏ i, Real.exp (t i * v i) ∂gaussianVector d) =
      ∏ i, ∫ z : ℝ, Real.exp (t i * z) ∂gaussianReal 0 1 := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
    letI : SigmaFinite (volume : Measure ℝ) := by
      change SigmaFinite (gaussianReal 0 1)
      infer_instance
    exact integral_fintype_prod_eq_prod (Fin d) (fun i (z : ℝ) => Real.exp (t i * z))
  rw [hp]
  have hi (r : ℝ) : (∫ z : ℝ, Real.exp (r * z) ∂gaussianReal 0 1) = Real.exp (r ^ 2 / 2) :=
    standard_mgf r
  simp_rw [hi]
  rw [← Real.exp_sum, Finset.sum_div]

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def gaussianSynthesis (v : Fin (Module.finrank ℝ E) → ℝ) : E :=
  ∑ i, v i • stdOrthonormalBasis ℝ E i

theorem gaussianSynthesis_continuous : Continuous (gaussianSynthesis E) := by
  unfold gaussianSynthesis
  exact continuous_finset_sum _ (fun i _ => (continuous_apply i).smul continuous_const)

def euclideanGaussianLaw : Measure E :=
  (gaussianVector (Module.finrank ℝ E)).map (gaussianSynthesis E)

instance euclideanGaussian_probability : IsProbabilityMeasure (euclideanGaussianLaw E) := by
  unfold euclideanGaussianLaw
  exact isProbabilityMeasure_map (gaussianSynthesis_continuous E).measurable.aemeasurable

theorem gaussian_exp_inner (u : E) :
    (∫ z, Real.exp ⟪u, z⟫_ℝ ∂euclideanGaussianLaw E) = Real.exp (‖u‖ ^ 2 / 2) := by
  rw [euclideanGaussianLaw]
  have hf : StronglyMeasurable (fun z : E => Real.exp ⟪u, z⟫_ℝ) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  rw [integral_map_of_stronglyMeasurable (gaussianSynthesis_continuous E).measurable hf]
  have he (v : Fin (Module.finrank ℝ E) → ℝ) :
      ⟪u, gaussianSynthesis E v⟫_ℝ = ∑ i, ⟪stdOrthonormalBasis ℝ E i, u⟫_ℝ * v i := by
    simp only [gaussianSynthesis, inner_sum, inner_smul_right, real_inner_comm u, mul_comm]
  simp_rw [he]
  rw [gaussianVector_exp_linear]
  have hn : (∑ i, ⟪stdOrthonormalBasis ℝ E i, u⟫_ℝ ^ 2) = ‖u‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (stdOrthonormalBasis ℝ E).sum_sq_norm_inner u
  rw [hn]

theorem gaussian_inner_mgf (u : E) (t : ℝ) :
    mgf (fun z => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E) t =
      Real.exp (t ^ 2 * ‖u‖ ^ 2 / 2) := by
  have h := gaussian_exp_inner E (t • u)
  simpa only [mgf, real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using h

theorem gaussian_inner_exp_integrable (u : E) (t : ℝ) :
    Integrable (fun z => Real.exp (t * ⟪u, z⟫_ℝ)) (euclideanGaussianLaw E) := by
  by_contra hn
  have hz := integral_undef hn
  change mgf (fun z => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E) t = 0 at hz
  rw [gaussian_inner_mgf] at hz
  exact (Real.exp_ne_zero _) hz

theorem gaussian_inner_exp_interior (u : E) (t : ℝ) :
    t ∈ interior (integrableExpSet (fun z => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E)) := by
  have he : integrableExpSet (fun z => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E) = Set.univ :=
    Set.eq_univ_of_forall (gaussian_inner_exp_integrable E u)
  rw [he, interior_univ]
  trivial

theorem gaussian_inner_power_integrable (u : E) (n : ℕ) :
    Integrable (fun z => ⟪u, z⟫_ℝ ^ n) (euclideanGaussianLaw E) :=
  integrable_pow_of_mem_interior_integrableExpSet (gaussian_inner_exp_interior E u 0) n

theorem gaussian_inner_mean_zero (u : E) :
    (∫ z, ⟪u, z⟫_ℝ ∂euclideanGaussianLaw E) = 0 := by
  have he : mgf (fun z => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E) =
      fun t => Real.exp (t ^ 2 * ‖u‖ ^ 2 / 2) := funext (gaussian_inner_mgf E u)
  have hd : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * ‖u‖ ^ 2 / 2)) 0 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖u‖ ^ 2)).div_const 2).exp
      using 1 <;> simp
  have h := deriv_mgf_zero (gaussian_inner_exp_interior E u 0)
  rw [he, hd.deriv] at h
  exact h.symm

theorem gaussian_inner_second_fourth (u : E) :
    (∫ z, ⟪u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) = ‖u‖ ^ 2 ∧
    (∫ z, ⟪u, z⟫_ℝ ^ 4 ∂euclideanGaussianLaw E) = 3 * ‖u‖ ^ 4 := by
  let s := ‖u‖ ^ 2
  let g : ℝ → ℝ := fun t => Real.exp (t ^ 2 * s / 2)
  let M := mgf (fun z => ⟪u, z⟫_ℝ) (euclideanGaussianLaw E)
  have he0 : M = g := funext (gaussian_inner_mgf E u)
  have h0 (t : ℝ) : HasDerivAt g (g t * s * t) t := by
    dsimp only [g]
    convert ((((hasDerivAt_id t).pow 2).mul_const s).div_const 2).exp
      using 1 <;> simp only [id_eq] <;> ring
  have h1 (t : ℝ) : HasDerivAt (fun x => g x * s * x)
      (g t * (s + s ^ 2 * t ^ 2)) t := by
    convert ((h0 t).mul_const s).mul (hasDerivAt_id t)
      using 1 <;> simp only [id_eq] <;> ring
  have h2 (t : ℝ) : HasDerivAt (fun x => g x * (s + s ^ 2 * x ^ 2))
      (g t * (3 * s ^ 2 * t + s ^ 3 * t ^ 3)) t := by
    convert (h0 t).mul (((hasDerivAt_id t).pow 2).const_mul (s ^ 2) |>.const_add s)
      using 1 <;> simp only [id_eq] <;> ring
  have h3 (t : ℝ) : HasDerivAt (fun x => g x * (3 * s ^ 2 * x + s ^ 3 * x ^ 3))
      (g t * (3 * s ^ 2 + 6 * s ^ 3 * t ^ 2 + s ^ 4 * t ^ 4)) t := by
    convert (h0 t).mul (((hasDerivAt_id t).const_mul (3 * s ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (s ^ 3)))
      using 1 <;> simp only [id_eq] <;> ring
  have he1 : iteratedDeriv 1 M = fun t => g t * s * t := by
    rw [iteratedDeriv_one, he0]
    exact funext (fun t => (h0 t).deriv)
  have he2 : iteratedDeriv 2 M = fun t => g t * (s + s ^ 2 * t ^ 2) := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, he1]
    exact funext (fun t => (h1 t).deriv)
  have he3 : iteratedDeriv 3 M = fun t => g t * (3 * s ^ 2 * t + s ^ 3 * t ^ 3) := by
    rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, he2]
    exact funext (fun t => (h2 t).deriv)
  constructor
  · have hm := hasDerivAt_iteratedDeriv_mgf (gaussian_inner_exp_interior E u 0) 1
    change HasDerivAt (iteratedDeriv 1 M) _ 0 at hm
    rw [he1] at hm
    simpa [g, s] using hm.unique (h1 0)
  · have hm := hasDerivAt_iteratedDeriv_mgf (gaussian_inner_exp_interior E u 0) 3
    change HasDerivAt (iteratedDeriv 3 M) _ 0 at hm
    rw [he3] at hm
    simpa [g, s, ← pow_mul] using hm.unique (h3 0)

theorem gaussian_inner_second (u : E) :
    (∫ z, ⟪u, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) = ‖u‖ ^ 2 :=
  (gaussian_inner_second_fourth E u).1

theorem gaussian_inner_fourth (u : E) :
    (∫ z, ⟪u, z⟫_ℝ ^ 4 ∂euclideanGaussianLaw E) = 3 * ‖u‖ ^ 4 :=
  (gaussian_inner_second_fourth E u).2

end HeavyTail.GaussianEstimates
