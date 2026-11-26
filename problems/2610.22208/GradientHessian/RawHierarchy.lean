import GradientHessian.RawFirstHeight
import GradientHessian.HigherHierarchyData

/-! The finite presampled product underlying the actual hierarchy. Every
coefficient is sampled before a policy seed is appended. Child labels index
independent data, while assembly retains the common physical prefix. -/

noncomputable section
namespace GradientHessian.RawHierarchy
open MeasureTheory Matrix LowRank

variable (d n r J : ℕ) (E : Type) (H : ℕ → Type)

def Raw : ℕ → Type
  | 0 => RawFirstHeight.Raw d n r J E
  | t+1 => (Fin 8 → Raw t) × (Fin 8 → H t)

variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

def rawMeasurable : (t : ℕ) → MeasurableSpace (Raw d n r J E H t)
  | 0 => inferInstanceAs (MeasurableSpace (RawFirstHeight.Raw d n r J E))
  | t+1 => by
    letI := rawMeasurable t
    exact inferInstanceAs (MeasurableSpace ((Fin 8 → Raw d n r J E H t) × (Fin 8 → H t)))
attribute [instance] rawMeasurable

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

variable {d n r J E H}

def law (P : Matrix (Fin d) (Fin d) ℝ) : (t : ℕ) → Measure (Raw d n r J E H t)
  | 0 => RawFirstHeight.law P J r
  | t+1 => (Measure.pi (fun _ : Fin 8 => law P t)).prod
      (Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H t)))

theorem law_probability (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ t, IsProbabilityMeasure (law (n := n) (r := r) (J := J) (E := E) (H := H) P t)
  | 0 => RawFirstHeight.law_probability P
  | t+1 => by
    letI := law_probability P t
    change IsProbabilityMeasure ((Measure.pi (fun _ : Fin 8 =>
      law (n := n) (r := r) (J := J) (E := E) (H := H) P t)).prod
      (Measure.pi (fun _ : Fin 8 => SphereGaussian.sphereLaw (H t))))
    infer_instance

def assemble (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : (t : ℕ) → Raw d n r J E H t →
      HigherHierarchy.Data (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t
  | 0, x => RawFirstHeight.assemble P B fallback x
  | t+1, x => ⟨fun i => assemble P B fallback t (x.1 i), x.2⟩

def Good (P : Matrix (Fin d) (Fin d) ℝ) : (t : ℕ) → Raw d n r J E H t → Prop
  | 0, x => RawFirstHeight.Good P x
  | t+1, x => (∀ i, Good P t (x.1 i)) ∧ ∀ i, ‖x.2 i‖=1

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, MeasurableSpace (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)] in
theorem assemble_valid (hJ : 4≤J) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (B : Matrix (Fin d) (Fin r) ℝ)
    (hB : Bᵀ*B=1) (hPB : P*B=B) (fallback : Fin d → ℝ) :
    ∀ t (x : Raw d n r J E H t), Good P t x →
      HigherHierarchy.Valid _ _ _ _ t (assemble P B fallback t x)
  | 0, x, hx => RawFirstHeight.assemble_valid hJ hP B hB hPB fallback x hx
  | t+1, x, hx => ⟨fun i => assemble_valid hJ hP B hB hPB fallback t (x.1 i) (hx.1 i), hx.2⟩

theorem law_good [Nontrivial E] [NeZero r] [∀ t, Nontrivial (H t)]
    (P : Matrix (Fin d) (Fin d) ℝ)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] :
    ∀ t, ∀ᵐ x ∂law (n := n) (r := r) (J := J) (E := E) (H := H) P t, Good P t x
  | 0 => RawFirstHeight.law_good P
  | t+1 => by
    letI := law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
    exact RawFirstHeight.prod_ae_pair _ _
      (RawFirstHeight.pi_ae_all _ _ (fun _ => law_good P t))
      (RawFirstHeight.pi_ae_all _ _ (fun _ => SphereGaussian.sphereLaw_unit))

theorem law_assemble_valid [Nontrivial E] [NeZero r] [∀ t, Nontrivial (H t)]
    (hJ : 4≤J) {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)]
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B=1) (hPB : P*B=B) (fallback : Fin d → ℝ) (t : ℕ) :
    ∀ᵐ x ∂law (n := n) (r := r) (J := J) (E := E) (H := H) P t,
      HigherHierarchy.Valid _ _ _ _ t (assemble P B fallback t x) := by
  filter_upwards [law_good (n := n) (r := r) (J := J) (E := E) (H := H) P t] with x hx
  exact assemble_valid hJ hP B hB hPB fallback t x hx

end GradientHessian.RawHierarchy
