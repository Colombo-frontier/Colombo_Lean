import MatchingBounds1005.GaussianConcentration
import MatchingBounds1005.GaussianNets
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.Complex.ExponentialBounds

/-! # Gaussian matrix synthesis and exponential singular-value bounds

The law is a literal product of independent Euclidean standard Gaussians.
Fixed unit combinations have their Gaussian law proved by product-coordinate
transposition, and the uniform bound follows from a finite sphere net.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace BigOperators
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianConcentration
open MatchingBounds1005.GaussianNets

namespace MatchingBounds1005.GaussianMatrix

def matrixFlattenEquiv (ι κ α : Type*) [MeasurableSpace α] :
    (ι → κ → α) ≃ᵐ (ι × κ → α) where
  toEquiv := (Equiv.curry ι κ α).symm
  measurable_toFun := measurable_pi_lambda _ (fun ij =>
    (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))
  measurable_invFun := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun j => measurable_pi_apply (i, j)))

theorem matrixFlatten_preserving (ι κ α : Type*) [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (matrixFlattenEquiv ι κ α)
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : ι × κ => μ)) := by
  refine ⟨(matrixFlattenEquiv ι κ α).measurable, ?_⟩
  apply (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (matrixFlattenEquiv ι κ α).measurable (MeasurableSet.univ_pi hs)]
  have he : (matrixFlattenEquiv ι κ α) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i, j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      matrixFlattenEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk]
    exact ⟨fun h i j => h (i, j), fun h ij => h ij.1 ij.2⟩
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : ι × κ => μ (s ij))).symm

def matrixTransposeEquiv (ι κ α : Type*) [MeasurableSpace α] :
    (ι → κ → α) ≃ᵐ (κ → ι → α) where
  toFun := fun x j i => x i j
  invFun := fun x i j => x j i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := measurable_pi_lambda _ (fun j =>
    measurable_pi_lambda _ (fun i => (measurable_pi_apply j).comp (measurable_pi_apply i)))
  measurable_invFun := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)))

theorem matrixTranspose_preserving (ι κ α : Type*) [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (matrixTransposeEquiv ι κ α)
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ)))
      (Measure.pi (fun _ : κ => Measure.pi (fun _ : ι => μ))) := by
  have hswap := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have hflat := matrixFlatten_preserving ι κ α μ
  have hunflat := (matrixFlatten_preserving κ ι α μ).symm
  convert hunflat.comp (hswap.comp hflat) using 1

def gaussianMatrixLaw (d k : ℕ) : Measure (Fin k → Vec d) :=
  Measure.pi (fun _ => standardGaussian d)

instance (d k : ℕ) : IsProbabilityMeasure (gaussianMatrixLaw d k) := by
  unfold gaussianMatrixLaw
  infer_instance

def synthesis {d k : ℕ} (a : Fin k → Vec d) : Vec k →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => ∑ i, u i • a i
      map_add' := by intros; simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp only [PiLp.smul_apply, smul_eq_mul, mul_smul,
        Finset.smul_sum, RingHom.id_apply] }

theorem synthesis_continuous {d k : ℕ} (u : Vec k) :
    Continuous (fun a : Fin k → Vec d => synthesis a u) := by
  change Continuous (fun a : Fin k → Vec d => ∑ i, u i • a i)
  apply continuous_finset_sum
  intro i _
  exact continuous_const.smul (continuous_apply i)

/-- Every unit combination of the independent Gaussian columns is an actual
standard Gaussian vector, with no nondegeneracy hypothesis on the dimensions. -/
theorem unit_synthesis_preserving {d k : ℕ} (u : Vec k) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun a : Fin k → Vec d => synthesis a u)
      (gaussianMatrixLaw d k) (standardGaussian d) := by
  have hequiv (m : ℕ) : MeasurePreserving (EuclideanSpace.measurableEquiv (Fin m))
      (standardGaussian m) (gaussianVector m) :=
    ⟨(EuclideanSpace.measurableEquiv (Fin m)).measurable, standardGaussian_coordinate_law m⟩
  have hrows := measurePreserving_pi (fun _ : Fin k => standardGaussian d)
    (fun _ : Fin k => gaussianVector d) (fun _ => hequiv d)
  have htranspose := matrixTranspose_preserving (Fin k) (Fin d) ℝ (gaussianReal 0 1)
  have hcolumns := measurePreserving_pi (fun _ : Fin d => gaussianVector k)
    (fun _ : Fin d => standardGaussian k) (fun _ => (hequiv k).symm)
  have hscalar : MeasurePreserving (fun x : Vec k => ⟪u, x⟫_ℝ)
      (standardGaussian k) (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    convert standardGaussian_inner_law u using 1
    simp [hu]
  have hlinear := measurePreserving_pi (fun _ : Fin d => standardGaussian k)
    (fun _ : Fin d => gaussianReal 0 1) (fun _ => hscalar)
  have hlast := MeasurePreserving.symm (EuclideanSpace.measurableEquiv (Fin d)) (hequiv d)
  have h := hlast.comp (hlinear.comp (hcolumns.comp (htranspose.comp hrows)))
  convert h using 1
  funext a
  ext j
  change (∑ i, u i • a i) j =
    ⟪u, (EuclideanSpace.measurableEquiv (Fin k)).symm (fun i => a i j)⟫_ℝ
  have heval : ∀ s : Finset (Fin k), (∑ i ∈ s, u i • a i) j =
      ∑ i ∈ s, u i * a i j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, PiLp.add_apply, ih]
  rw [heval]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i, u i * a i j) = ∑ i, a i j * u i
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

def scaledSynthesis {d k : ℕ} (a : Fin k → Vec d) : Vec k →L[ℝ] Vec d :=
  (Real.sqrt (d : ℝ))⁻¹ • synthesis a

theorem scaledSynthesis_norm_sq {d k : ℕ} (a : Fin k → Vec d) (u : Vec k) :
    ‖scaledSynthesis a u‖ ^ 2 = ‖synthesis a u‖ ^ 2 / (d : ℝ) := by
  simp only [scaledSynthesis, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

theorem unit_synthesis_tail {d k : ℕ} (hd : 0 < d) (u : Vec k) (hu : ‖u‖ = 1) :
    (gaussianMatrixLaw d k).real {a | (1 : ℝ) / 2 < |‖scaledSynthesis a u‖ ^ 2 - 1|} ≤
      2 * Real.exp (-(d : ℝ) / 32) := by
  have h := norm_square_two_sided hd (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hp := unit_synthesis_preserving (d := d) u hu
  have hs : MeasurableSet {x : Vec d | (1 : ℝ) / 2 < |‖x‖ ^ 2 / (d : ℝ) - 1|} := by
    apply measurableSet_lt measurable_const
    fun_prop
  rw [← hp.measureReal_preimage hs.nullMeasurableSet] at h
  simpa only [Set.preimage_setOf_eq, scaledSynthesis_norm_sq,
    show (-(d : ℝ) * (1 / 2) ^ 2 / 8) = -(d : ℝ) / 32 by ring] using h

def WellConditioned {d k : ℕ} (a : Fin k → Vec d) : Prop :=
  ‖scaledSynthesis a‖ ≤ 10 / 7 ∧ ∀ v : Vec k, ‖v‖ / 2 ≤ ‖scaledSynthesis a v‖

/-- A real finite-net union bound for a genuine Gaussian matrix. The
dependence is exponential in the block multiplicity and linear in the
number of columns in the exponent. -/
theorem singular_failure_bound {d k : ℕ} (hd : 0 < d) :
    (gaussianMatrixLaw d k).real {a | ¬ WellConditioned a} ≤
      (17 : ℝ) ^ k * (2 * Real.exp (-(d : ℝ) / 32)) := by
  classical
  obtain ⟨s, hcard, hs, hnet⟩ := spectral_sphere_net (E := Vec k)
  let bad (u : Vec k) : Set (Fin k → Vec d) :=
    {a | (1 : ℝ) / 2 < |‖scaledSynthesis a u‖ ^ 2 - 1|}
  have hsub : {a : Fin k → Vec d | ¬ WellConditioned a} ⊆ ⋃ u ∈ s, bad u := by
    intro a ha
    by_contra hn
    have hb : ∀ u ∈ s, (1 : ℝ) / 2 ≤ ‖scaledSynthesis a u‖ ^ 2 ∧
        ‖scaledSynthesis a u‖ ^ 2 ≤ (3 : ℝ) / 2 := by
      intro u hu
      have hnu : a ∉ bad u := fun h => hn (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, h⟩⟩)
      have hab : |‖scaledSynthesis a u‖ ^ 2 - 1| ≤ (1 : ℝ) / 2 := le_of_not_gt hnu
      have hh := abs_le.mp hab
      constructor <;> linarith
    exact ha (operator_bounds_of_net (scaledSynthesis a) s hnet hb)
  calc
    _ ≤ (gaussianMatrixLaw d k).real (⋃ u ∈ s, bad u) := measureReal_mono hsub
    _ ≤ ∑ u ∈ s, (gaussianMatrixLaw d k).real (bad u) := measureReal_biUnion_finset_le s bad
    _ ≤ ∑ _u ∈ s, 2 * Real.exp (-(d : ℝ) / 32) :=
      Finset.sum_le_sum (fun u hu => unit_synthesis_tail hd u (hs u hu))
    _ = (s.card : ℝ) * (2 * Real.exp (-(d : ℝ) / 32)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hc : s.card ≤ 17 ^ k := by simpa using hcard
      exact_mod_cast hc

theorem log_seventeen_le_three : Real.log 17 ≤ 3 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 17 ^ 4)
    (by norm_num : (17 : ℝ) ^ 4 ≤ 2 ^ 17)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_lt_d9]

theorem singular_failure_exponential {d k : ℕ} (hd : 0 < d)
    (hk : (k : ℝ) ≤ (d : ℝ) / 192) :
    (gaussianMatrixLaw d k).real {a | ¬ WellConditioned a} ≤
      2 * Real.exp (-(d : ℝ) / 64) := by
  apply (singular_failure_bound hd).trans
  have he : (17 : ℝ) = Real.exp (Real.log 17) := (Real.exp_log (by norm_num)).symm
  conv_lhs => rw [he, ← Real.exp_nat_mul]
  have hlog := mul_le_mul_of_nonneg_left log_seventeen_le_three (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hx : (k : ℝ) * Real.log 17 + -(d : ℝ) / 32 ≤ -(d : ℝ) / 64 := by linarith
  have hh := Real.exp_le_exp.mpr hx
  rw [Real.exp_add] at hh
  nlinarith

/-- Scalar Gaussian observations of every contraction direction have their
sub-Gaussian MGF derived from the actual Gaussian law. -/
theorem inner_subgaussian {d : ℕ} (a : Vec d) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun x => ⟪a, x⟫_ℝ) 1 (standardGaussian d) := by
  have hm (t : ℝ) : mgf (fun x : Vec d => ⟪a, x⟫_ℝ) (standardGaussian d) t =
      Real.exp (‖a‖ ^ 2 * t ^ 2 / 2) := by
    simpa only [zero_mul, zero_add, NNReal.coe_mk] using
      mgf_gaussianReal (standardGaussian_inner_law a) t
  constructor
  · intro t
    by_contra h
    have he := hm t
    rw [mgf, integral_undef h] at he
    exact (Real.exp_ne_zero _) he.symm
  · intro t
    rw [hm]
    apply Real.exp_le_exp.mpr
    have hs : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
    have hmul := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
    norm_num only [NNReal.coe_one]
    nlinarith

theorem inner_absolute_tail {d : ℕ} (a : Vec d) (ha : ‖a‖ ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian d).real {x | r ≤ |⟪a, x⟫_ℝ|} ≤ 2 * Real.exp (-r ^ 2 / 2) := by
  have hpos := (inner_subgaussian a ha).measure_ge_le hr
  have hneg := (inner_subgaussian (-a) (by simpa using ha)).measure_ge_le hr
  have he : {x : Vec d | r ≤ |⟪a, x⟫_ℝ|} =
      {x | r ≤ ⟪a, x⟫_ℝ} ∪ {x | r ≤ ⟪-a, x⟫_ℝ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, inner_neg_left, le_abs]
  rw [he]
  have h := measureReal_union_le (μ := standardGaussian d)
    {x | r ≤ ⟪a, x⟫_ℝ} {x | r ≤ ⟪-a, x⟫_ℝ}
  norm_num only [NNReal.coe_one, mul_one] at hpos hneg
  linarith

end MatchingBounds1005.GaussianMatrix
