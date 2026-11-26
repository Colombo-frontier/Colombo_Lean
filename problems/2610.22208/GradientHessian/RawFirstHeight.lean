import GradientHessian.ConditionedSource
import GradientHessian.LeafSource
import GradientHessian.ReadoutMarks
import GradientHessian.FirstHeightLeafData
import GradientHessian.SphereGaussian
import Mathlib.MeasureTheory.Constructions.Pi

/-! Independent primitive sampling and coefficient assembly at height one.
Matrices and task marks are separate coordinates, and all memory directions
are independent sphere coordinates. The coefficient certificates below are
derived from the actual conditioned source event. -/

noncomputable section
namespace GradientHessian.RawFirstHeight
open MeasureTheory Matrix LowRank SourceOperator ReadoutMarks
open scoped InnerProductSpace

abbrev Raw (d n r J : ℕ) (E : Type) :=
  (Fin 8 → Matrix (Fin d) (Fin n) ℝ) ×
  (Fin 8 → Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin r)) ×
  (Fin 8 → Fin (4096*J^2+1) → Fin (Inner.absoluteDepth+2) → E) ×
  (Fin 8 → Fin (FirstHeight.depth (4096*J^2+1)+2) → E)

variable {d n r J : ℕ} {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (x : Raw d n r J E) :
    FirstHeight.Data (EuclideanSpace ℝ (Fin d)) E (4096*J^2) where
  A i := matrixEuclideanMap (MatrixGoodSpectrum.sourceMatrix P J (x.1 i))
  b i j := InverseGate.H₀ • matrixEuclideanMap B (x.2.1 i j)
  a i j := readoutVector J P (x.1 i) fallback (matrixEuclideanMap B (x.2.1 i j))
  innerDirections := x.2.2.1
  outerDirections := x.2.2.2

def Good (P : Matrix (Fin d) (Fin d) ℝ) (x : Raw d n r J E) : Prop :=
  (∀ i, x.1 i ∈ MatrixKernelConcentration.sourceGoodEvent P J) ∧
  (∀ i j, ‖x.2.1 i j‖ = 1) ∧
  (∀ i j k, ‖x.2.2.1 i j k‖ = 1) ∧
  (∀ i j, ‖x.2.2.2 i j‖ = 1)

theorem assemble_valid (hJ : 4≤J) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (B : Matrix (Fin d) (Fin r) ℝ)
    (hB : Bᵀ*B=1) (hPB : P*B=B) (fallback : Fin d → ℝ)
    (x : Raw d n r J E) (hx : Good P x) : FirstHeight.Valid (assemble P B fallback x) := by
  have hmark (i j) : ‖matrixEuclideanMap B (x.2.1 i j)‖ = 1 :=
    (mark_norm B hB _).trans (hx.2.1 i j)
  have hin (i j) := source_inner_inputs hJ hP (hx.1 i) fallback
    (matrixEuclideanMap B (x.2.1 i j)) (hmark i j) (mark_in_range P B hPB _)
  refine ⟨fun i => source_lowerBound hP J (x.1 i), ?_, ?_, ?_, ?_, ?_, hx.2.2.1, hx.2.2.2⟩
  · intro i
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      Leaf.source_matrix_norm hJ hP (hx.1 i)
  · intro i a b
    exact matrixMap_symmetric (MatrixGoodSpectrum.sourceMatrix_posDef (x.1 i) hP J).isHermitian a b
  · exact fun i j => (hin i j).1
  · exact fun i j => (hin i j).2.1
  · exact fun i j => (hin i j).2.2

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def law (P : Matrix (Fin d) (Fin d) ℝ) (J r : ℕ) : Measure (Raw d n r J E) :=
  (Measure.pi (fun _ : Fin 8 => ConditionedSource.sourceLaw (n := n) P J)).prod
    ((Measure.pi (fun _ : Fin 8 => Measure.pi (fun _ : Fin (4096*J^2+1) =>
      SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))))).prod
      ((Measure.pi (fun _ : Fin 8 => Measure.pi (fun _ : Fin (4096*J^2+1) =>
        Measure.pi (fun _ : Fin (Inner.absoluteDepth+2) => SphereGaussian.sphereLaw E)))).prod
        (Measure.pi (fun _ : Fin 8 => Measure.pi
          (fun _ : Fin (FirstHeight.depth (4096*J^2+1)+2) => SphereGaussian.sphereLaw E)))))

set_option synthInstance.maxSize 512 in
theorem law_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    IsProbabilityMeasure (law (E := E) (n := n) P J r) := by
  unfold law
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 =>
      ConditionedSource.sourceLaw (n := n) P J)) := inferInstance
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin (4096*J^2+1) =>
      SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))) := inferInstance
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin (Inner.absoluteDepth+2) =>
      SphereGaussian.sphereLaw E)) := inferInstance
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin (4096*J^2+1) =>
      Measure.pi (fun _ : Fin (Inner.absoluteDepth+2) => SphereGaussian.sphereLaw E))) := inferInstance
  infer_instance

theorem pi_ae_all {ι : Type*} [Fintype ι] {T : ι → Type*}
    [∀ i, MeasurableSpace (T i)] (μ : ∀ i, Measure (T i)) [∀ i, SigmaFinite (μ i)]
    (p : ∀ i, T i → Prop) (h : ∀ i, ∀ᵐ x ∂μ i, p i x) :
    ∀ᵐ x ∂Measure.pi μ, ∀ i, p i (x i) := by
  apply Filter.eventually_all.mpr
  intro i
  exact MeasureTheory.Measure.tendsto_eval_ae_ae.eventually (h i)

theorem prod_ae_pair {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    {p : A → Prop} {q : B → Prop} (hp : ∀ᵐ a ∂μ, p a) (hq : ∀ᵐ b ∂ν, q b) :
    ∀ᵐ x ∂μ.prod ν, p x.1 ∧ q x.2 :=
  (Measure.quasiMeasurePreserving_fst.ae hp).and (Measure.quasiMeasurePreserving_snd.ae hq)

set_option synthInstance.maxSize 512 in
theorem law_good [Nontrivial E] [NeZero r] (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ᵐ x ∂law (E := E) (n := n) P J r, Good P x := by
  have hX := pi_ae_all (fun _ : Fin 8 => ConditionedSource.sourceLaw (n := n) P J)
    _ (fun _ => ConditionedSource.sourceLaw_good P J)
  have hz := pi_ae_all (fun _ : Fin 8 => Measure.pi (fun _ : Fin (4096*J^2+1) =>
    SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))) _
    (fun _ => pi_ae_all _ _ (fun _ => SphereGaussian.sphereLaw_unit))
  have hi := pi_ae_all (fun _ : Fin 8 => Measure.pi (fun _ : Fin (4096*J^2+1) =>
    Measure.pi (fun _ : Fin (Inner.absoluteDepth+2) => SphereGaussian.sphereLaw E))) _
    (fun _ => pi_ae_all _ _ (fun _ => pi_ae_all _ _ (fun _ => SphereGaussian.sphereLaw_unit)))
  have ho := pi_ae_all (fun _ : Fin 8 => Measure.pi
    (fun _ : Fin (FirstHeight.depth (4096*J^2+1)+2) => SphereGaussian.sphereLaw E)) _
    (fun _ => pi_ae_all _ _ (fun _ => SphereGaussian.sphereLaw_unit))
  exact prod_ae_pair _ _ hX (prod_ae_pair _ _ hz (prod_ae_pair _ _ hi ho))

theorem law_assemble_valid [Nontrivial E] [NeZero r] (hJ : 4≤J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B=1) (hPB : P*B=B) (fallback : Fin d → ℝ) :
    ∀ᵐ x ∂law (E := E) (n := n) P J r, FirstHeight.Valid (assemble P B fallback x) := by
  filter_upwards [law_good (E := E) (n := n) (r := r) P] with x hx
  exact assemble_valid hJ hP B hB hPB fallback x hx

end GradientHessian.RawFirstHeight
