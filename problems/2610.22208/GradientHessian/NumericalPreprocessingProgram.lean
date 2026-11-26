import GradientHessian.NumericalPreprocessorMeasurability

noncomputable section
namespace GradientHessian.NumericalPreprocessor
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

def program {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d (RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) where
  mode := mode t leaf j
  think := fun s => stepReply P B fallback t leaf policy K j s 0
  query := query t
  mark := requestedMark B t leaf j
  next := fun q => stepReply P B fallback t leaf policy K j q.1 q.2
  disclosed := fun q => accept t leaf j q.1 q.2
  mode_measurable := mode_measurable t leaf j
  think_measurable := (stepReply_measurable P B fallback t leaf policy hK j).comp
    (measurable_id.prodMk measurable_const)
  query_measurable := query_measurable t
  mark_measurable := requestedMark_measurable B t leaf j
  next_measurable := stepReply_measurable P B fallback t leaf policy hK j
  disclosed_measurable := accept_measurable t leaf j

def cappedProgram {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    DisclosureCompiler.Program d ((RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) × ℕ × ℕ) :=
  DisclosureCappedProgram.cap (program P B fallback t leaf policy hK j)

theorem capped_calls {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1))
    (A : Matrix (Fin d) (Fin d) ℝ) (readout : (Fin d → ℝ) → Fin d → ℝ)
    (N q R : ℕ) (s : RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :
    (cappedProgram P B fallback t leaf policy hK j).ordinaryCalls A readout N (s,q,R) ≤ q ∧
    (cappedProgram P B fallback t leaf policy hK j).disclosures A readout N (s,q,R) ≤ R :=
  DisclosureCappedProgram.calls_le (program P B fallback t leaf policy hK j) A readout N s q R

end GradientHessian.NumericalPreprocessor